//! Definitions for registers, operands, etc. Provides a thin
//! interface over the register allocator so that we can more easily
//! swap it out or shim it when necessary.

use alloc::{string::String, vec::Vec};
use core::{convert::AsMut, fmt::Debug, hash::Hash};
use regalloc2::{
    Allocation, Operand, OperandConstraint, OperandKind, OperandPos, PReg, PRegSet, VReg,
};

#[cfg(feature = "enable-serde")]
use serde_derive::{Deserialize, Serialize};

/// The first 192 vregs (64 int, 64 float, 64 vec) are "pinned" to
/// physical registers: this means that they are always constrained to
/// the corresponding register at all use/mod/def sites.
///
/// Arbitrary vregs can also be constrained to physical registers at
/// particular use/def/mod sites, and this is preferable; but pinned
/// vregs allow us to migrate code that has been written using
/// RealRegs directly.
const PINNED_VREGS: usize = 192;

/// Convert a `VReg` to its pinned `PReg`, if any.
pub fn pinned_vreg_to_preg(vreg: VReg) -> Option<PReg> {
    if vreg.vreg() < PINNED_VREGS {
        Some(PReg::from_index(vreg.vreg()))
    } else {
        None
    }
}

/// Give the first available vreg for generated code (i.e., after all
/// pinned vregs).
pub fn first_user_vreg_index() -> usize {
    // This is just the constant defined above, but we keep the
    // constant private and expose only this helper function with the
    // specific name in order to ensure other parts of the code don't
    // open-code and depend on the index-space scheme.
    PINNED_VREGS
}

/// A register named in an instruction. This register can be either a
/// virtual register or a fixed physical register. It does not have
/// any constraints applied to it: those can be added later in
/// `MachInst::get_operands()` when the `Reg`s are converted to
/// `Operand`s.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct Reg(VReg);

impl Reg {
    /// Get the physical register (`RealReg`), if this register is
    /// one.
    pub fn to_real_reg(self) -> Option<RealReg> {
        pinned_vreg_to_preg(self.0).map(RealReg)
    }

    /// Get the virtual (non-physical) register, if this register is
    /// one.
    pub fn to_virtual_reg(self) -> Option<VirtualReg> {
        if pinned_vreg_to_preg(self.0).is_none() {
            Some(VirtualReg(self.0))
        } else {
            None
        }
    }

    /// Get the class of this register.
    pub fn class(self) -> RegClass {
        self.0.class()
    }

    /// Is this a real (physical) reg?
    pub fn is_real(self) -> bool {
        self.to_real_reg().is_some()
    }

    /// Is this a virtual reg?
    pub fn is_virtual(self) -> bool {
        self.to_virtual_reg().is_some()
    }
}

impl std::fmt::Debug for Reg {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        if let Some(rreg) = self.to_real_reg() {
            let preg: PReg = rreg.into();
            write!(f, "{}", preg)
        } else if let Some(vreg) = self.to_virtual_reg() {
            let vreg: VReg = vreg.into();
            write!(f, "{}", vreg)
        } else {
            unreachable!()
        }
    }
}

impl AsMut<Reg> for Reg {
    fn as_mut(&mut self) -> &mut Reg {
        self
    }
}

/// A real (physical) register. This corresponds to one of the target
/// ISA's named registers and can be used as an instruction operand.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct RealReg(PReg);

impl RealReg {
    /// Get the class of this register.
    pub fn class(self) -> RegClass {
        self.0.class()
    }

    /// The physical register number.
    pub fn hw_enc(self) -> u8 {
        self.0.hw_enc() as u8
    }
}

impl std::fmt::Debug for RealReg {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        Reg::from(*self).fmt(f)
    }
}

/// A virtual register. This can be allocated into a real (physical)
/// register of the appropriate register class, but which one is not
/// specified. Virtual registers are used when generating `MachInst`s,
/// before register allocation occurs, in order to allow us to name as
/// many register-carried values as necessary.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct VirtualReg(VReg);

impl VirtualReg {
    /// Get the class of this register.
    pub fn class(self) -> RegClass {
        self.0.class()
    }

    pub fn index(self) -> usize {
        self.0.vreg()
    }
}

impl std::fmt::Debug for VirtualReg {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        Reg::from(*self).fmt(f)
    }
}

/// A type wrapper that indicates a register type is writable. The
/// underlying register can be extracted, and the type wrapper can be
/// built using an arbitrary register. Hence, this type-level wrapper
/// is not strictly a guarantee. However, "casting" to a writable
/// register is an explicit operation for which we can
/// audit. Ordinarily, internal APIs in the compiler backend should
/// take a `Writable<Reg>` whenever the register is written, and the
/// usual, frictionless way to get one of these is to allocate a new
/// temporary.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct Writable<T> {
    reg: T,
}

impl<T> Writable<T> {
    /// Explicitly construct a `Writable<T>` from a `T`. As noted in
    /// the documentation for `Writable`, this is not hidden or
    /// disallowed from the outside; anyone can perform the "cast";
    /// but it is explicit so that we can audit the use sites.
    pub fn from_reg(reg: T) -> Writable<T> {
        Writable { reg }
    }

    /// Get the underlying register, which can be read.
    pub fn to_reg(self) -> T {
        self.reg
    }

    /// Map the underlying register to another value or type.
    pub fn map<U, F>(self, f: F) -> Writable<U>
    where
        F: Fn(T) -> U,
    {
        Writable { reg: f(self.reg) }
    }
}

// Conversions between regalloc2 types (VReg, PReg) and our types
// (VirtualReg, RealReg, Reg).

impl std::convert::From<regalloc2::VReg> for Reg {
    fn from(vreg: regalloc2::VReg) -> Reg {
        Reg(vreg)
    }
}

impl std::convert::From<regalloc2::VReg> for VirtualReg {
    fn from(vreg: regalloc2::VReg) -> VirtualReg {
        debug_assert!(pinned_vreg_to_preg(vreg).is_none());
        VirtualReg(vreg)
    }
}

impl std::convert::From<Reg> for regalloc2::VReg {
    /// Extract the underlying `regalloc2::VReg`. Note that physical
    /// registers also map to particular (special) VRegs, so this
    /// method can be used either on virtual or physical `Reg`s.
    fn from(reg: Reg) -> regalloc2::VReg {
        reg.0
    }
}
impl std::convert::From<&Reg> for regalloc2::VReg {
    fn from(reg: &Reg) -> regalloc2::VReg {
        reg.0
    }
}

impl std::convert::From<VirtualReg> for regalloc2::VReg {
    fn from(reg: VirtualReg) -> regalloc2::VReg {
        reg.0
    }
}

impl std::convert::From<RealReg> for regalloc2::VReg {
    fn from(reg: RealReg) -> regalloc2::VReg {
        // This representation is redundant: the class is implied in the vreg
        // index as well as being in the vreg class field.
        VReg::new(reg.0.index(), reg.0.class())
    }
}

impl std::convert::From<RealReg> for regalloc2::PReg {
    fn from(reg: RealReg) -> regalloc2::PReg {
        reg.0
    }
}

impl std::convert::From<regalloc2::PReg> for RealReg {
    fn from(preg: regalloc2::PReg) -> RealReg {
        RealReg(preg)
    }
}

impl std::convert::From<regalloc2::PReg> for Reg {
    fn from(preg: regalloc2::PReg) -> Reg {
        RealReg(preg).into()
    }
}

impl std::convert::From<RealReg> for Reg {
    fn from(reg: RealReg) -> Reg {
        Reg(reg.into())
    }
}

impl std::convert::From<VirtualReg> for Reg {
    fn from(reg: VirtualReg) -> Reg {
        Reg(reg.0)
    }
}

/// A spill slot.
pub type SpillSlot = regalloc2::SpillSlot;

/// A register class. Each register in the ISA has one class, and the
/// classes are disjoint. Most modern ISAs will have just two classes:
/// the integer/general-purpose registers (GPRs), and the float/vector
/// registers (typically used for both).
///
/// Note that unlike some other compiler backend/register allocator
/// designs, we do not allow for overlapping classes, i.e. registers
/// that belong to more than one class, because doing so makes the
/// allocation problem significantly more complex. Instead, when a
/// register can be addressed under different names for different
/// sizes (for example), the backend author should pick classes that
/// denote some fundamental allocation unit that encompasses the whole
/// register. For example, always allocate 128-bit vector registers
/// `v0`..`vN`, even though `f32` and `f64` values may use only the
/// low 32/64 bits of those registers and name them differently.
pub type RegClass = regalloc2::RegClass;

/// An OperandCollector is a wrapper around a Vec of Operands
/// (flattened array for a whole sequence of instructions) that
/// gathers operands from a single instruction and provides the range
/// in the flattened array.
#[derive(Debug)]
pub struct OperandCollector<'a, F: Fn(VReg) -> VReg> {
    operands: &'a mut Vec<Operand>,
    operands_start: usize,
    clobbers: PRegSet,

    /// The subset of physical registers that are allocatable.
    allocatable: PRegSet,

    renamer: F,
}

impl<'a, F: Fn(VReg) -> VReg> OperandCollector<'a, F> {
    /// Start gathering operands into one flattened operand array.
    pub fn new(operands: &'a mut Vec<Operand>, allocatable: PRegSet, renamer: F) -> Self {
        let operands_start = operands.len();
        Self {
            operands,
            operands_start,
            clobbers: PRegSet::default(),
            allocatable,
            renamer,
        }
    }

    /// Finish the operand collection and return the tuple giving the
    /// range of indices in the flattened operand array, and the
    /// clobber set.
    pub fn finish(self) -> ((u32, u32), PRegSet) {
        let start = self.operands_start as u32;
        let end = self.operands.len() as u32;
        ((start, end), self.clobbers)
    }
}

pub trait OperandVisitor {
    fn visit(
        &mut self,
        reg: &mut Reg,
        constraint: OperandConstraint,
        kind: OperandKind,
        pos: OperandPos,
    );

    fn is_allocatable_preg(&self, reg: PReg) -> bool;

    /// Add a register clobber set. This is a set of registers that
    /// are written by the instruction, so must be reserved (not used)
    /// for the whole instruction, but are not used afterward.
    fn reg_clobbers(&mut self, regs: PRegSet);
}

pub trait OperandVisitorImpl {
    /// Add a use of a fixed, nonallocatable physical register.
    fn reg_fixed_nonallocatable(&mut self, preg: PReg);

    /// Add a register use, at the start of the instruction (`Before`
    /// position).
    fn reg_use(&mut self, reg: impl AsMut<Reg>);

    /// Add a register use, at the end of the instruction (`After` position).
    fn reg_late_use(&mut self, reg: impl AsMut<Reg>);

    /// Add multiple register uses.
    fn reg_uses(&mut self, regs: &mut [Reg]);

    /// Add a register def, at the end of the instruction (`After`
    /// position). Use only when this def will be written after all
    /// uses are read.
    fn reg_def(&mut self, reg: &mut Writable<impl AsMut<Reg>>);

    /// Add multiple register defs.
    fn reg_defs(&mut self, regs: &mut [Writable<Reg>]);

    /// Add a register "early def", which logically occurs at the
    /// beginning of the instruction, alongside all uses. Use this
    /// when the def may be written before all uses are read; the
    /// regalloc will ensure that it does not overwrite any uses.
    fn reg_early_def(&mut self, reg: &mut Writable<impl AsMut<Reg>>);

    /// Add a register "fixed use", which ties a vreg to a particular
    /// RealReg at the end of the instruction.
    fn reg_fixed_late_use(&mut self, reg: impl AsMut<Reg>, rreg: Reg);

    /// Add a register "fixed use", which ties a vreg to a particular
    /// RealReg at this point.
    fn reg_fixed_use(&mut self, reg: impl AsMut<Reg>, rreg: Reg);

    /// Add a register "fixed def", which ties a vreg to a particular
    /// RealReg at this point.
    fn reg_fixed_def(&mut self, reg: &mut Writable<impl AsMut<Reg>>, rreg: Reg);

    /// Add a register def that reuses an earlier use-operand's
    /// allocation. The index of that earlier operand (relative to the
    /// current instruction's start of operands) must be known.
    fn reg_reuse_def(&mut self, reg: &mut Writable<impl AsMut<Reg>>, idx: usize);
}

impl<T: OperandVisitor> OperandVisitorImpl for T {
    /// Add a use of a fixed, nonallocatable physical register.
    fn reg_fixed_nonallocatable(&mut self, preg: PReg) {
        debug_assert!(!self.is_allocatable_preg(preg));
        let mut reg = Reg::from(VReg::new(VReg::MAX, preg.class()));
        let constraint = OperandConstraint::FixedReg(preg);
        self.visit(&mut reg, constraint, OperandKind::Use, OperandPos::Early);
    }

    /// Add a register use, at the start of the instruction (`Before`
    /// position).
    fn reg_use(&mut self, mut reg: impl AsMut<Reg>) {
        maybe_fixed(self, reg.as_mut(), OperandKind::Use, OperandPos::Early);
    }

    /// Add a register use, at the end of the instruction (`After` position).
    fn reg_late_use(&mut self, mut reg: impl AsMut<Reg>) {
        maybe_fixed(self, reg.as_mut(), OperandKind::Use, OperandPos::Late);
    }

    /// Add multiple register uses.
    fn reg_uses(&mut self, regs: &mut [Reg]) {
        for reg in regs {
            self.reg_use(reg);
        }
    }

    /// Add a register def, at the end of the instruction (`After`
    /// position). Use only when this def will be written after all
    /// uses are read.
    fn reg_def(&mut self, reg: &mut Writable<impl AsMut<Reg>>) {
        maybe_fixed(self, reg.reg.as_mut(), OperandKind::Def, OperandPos::Late);
    }

    /// Add multiple register defs.
    fn reg_defs(&mut self, regs: &mut [Writable<Reg>]) {
        for reg in regs {
            self.reg_def(reg);
        }
    }

    /// Add a register "early def", which logically occurs at the
    /// beginning of the instruction, alongside all uses. Use this
    /// when the def may be written before all uses are read; the
    /// regalloc will ensure that it does not overwrite any uses.
    fn reg_early_def(&mut self, reg: &mut Writable<impl AsMut<Reg>>) {
        maybe_fixed(self, reg.reg.as_mut(), OperandKind::Def, OperandPos::Early);
    }

    /// Add a register "fixed use", which ties a vreg to a particular
    /// RealReg at the end of the instruction.
    fn reg_fixed_late_use(&mut self, mut reg: impl AsMut<Reg>, rreg: Reg) {
        let reg = reg.as_mut();
        debug_assert!(reg.is_virtual());
        let rreg = rreg.to_real_reg().expect("fixed reg is not a RealReg");
        debug_assert!(self.is_allocatable_preg(rreg.into()));
        let constraint = OperandConstraint::FixedReg(rreg.into());
        self.visit(reg, constraint, OperandKind::Use, OperandPos::Late);
    }

    /// Add a register "fixed use", which ties a vreg to a particular
    /// RealReg at this point.
    fn reg_fixed_use(&mut self, mut reg: impl AsMut<Reg>, rreg: Reg) {
        let reg = reg.as_mut();
        debug_assert!(reg.is_virtual());
        let rreg = rreg.to_real_reg().expect("fixed reg is not a RealReg");
        debug_assert!(self.is_allocatable_preg(rreg.into()));
        let constraint = OperandConstraint::FixedReg(rreg.into());
        self.visit(reg, constraint, OperandKind::Use, OperandPos::Early);
    }

    /// Add a register "fixed def", which ties a vreg to a particular
    /// RealReg at this point.
    fn reg_fixed_def(&mut self, reg: &mut Writable<impl AsMut<Reg>>, rreg: Reg) {
        let reg = reg.reg.as_mut();
        debug_assert!(reg.is_virtual());
        let rreg = rreg.to_real_reg().expect("fixed reg is not a RealReg");
        debug_assert!(
            self.is_allocatable_preg(rreg.into()),
            "{rreg:?} is not allocatable"
        );
        let constraint = OperandConstraint::FixedReg(rreg.into());
        self.visit(reg, constraint, OperandKind::Def, OperandPos::Late);
    }

    /// Add a register def that reuses an earlier use-operand's
    /// allocation. The index of that earlier operand (relative to the
    /// current instruction's start of operands) must be known.
    fn reg_reuse_def(&mut self, reg: &mut Writable<impl AsMut<Reg>>, idx: usize) {
        let reg = reg.reg.as_mut();
        if let Some(rreg) = reg.to_real_reg() {
            // In some cases we see real register arguments to a reg_reuse_def
            // constraint. We assume the creator knows what they're doing
            // here, though we do also require that the real register be a
            // fixed-nonallocatable register.
            self.reg_fixed_nonallocatable(rreg.into());
        } else {
            // The operand we're reusing must not be fixed-nonallocatable, as
            // that would imply that the register has been allocated to a
            // virtual register.
            let constraint = OperandConstraint::Reuse(idx);
            self.visit(reg, constraint, OperandKind::Def, OperandPos::Late);
        }
    }
}

fn maybe_fixed(
    visitor: &mut impl OperandVisitor,
    reg: &mut Reg,
    kind: OperandKind,
    pos: OperandPos,
) {
    if let Some(rreg) = reg.to_real_reg() {
        visitor.reg_fixed_nonallocatable(rreg.into());
    } else {
        debug_assert!(reg.is_virtual());
        visitor.visit(reg, OperandConstraint::Reg, kind, pos);
    }
}

impl<'a, F: Fn(VReg) -> VReg> OperandVisitor for OperandCollector<'a, F> {
    fn visit(
        &mut self,
        reg: &mut Reg,
        constraint: OperandConstraint,
        kind: OperandKind,
        pos: OperandPos,
    ) {
        let vreg = &mut reg.0;
        *vreg = (self.renamer)(*vreg);
        let operand = Operand::new(*vreg, constraint, kind, pos);
        self.operands.push(operand);
    }

    fn is_allocatable_preg(&self, reg: PReg) -> bool {
        self.allocatable.contains(reg)
    }

    fn reg_clobbers(&mut self, regs: PRegSet) {
        self.clobbers.union_from(regs);
    }
}

/// Pretty-print part of a disassembly, with knowledge of
/// operand/instruction size, and optionally with regalloc
/// results. This can be used, for example, to print either `rax` or
/// `eax` for the register by those names on x86-64, depending on a
/// 64- or 32-bit context.
pub trait PrettyPrint {
    fn pretty_print(&self, size_bytes: u8, allocs: &mut AllocationConsumer<'_>) -> String;

    fn pretty_print_default(&self) -> String {
        self.pretty_print(0, &mut AllocationConsumer::new(&[]))
    }
}

/// A consumer of an (optional) list of Allocations along with Regs
/// that provides RealRegs where available.
///
/// This is meant to be used during code emission or
/// pretty-printing. In at least the latter case, regalloc results may
/// or may not be available, so we may end up printing either vregs or
/// rregs. Even pre-regalloc, though, some registers may be RealRegs
/// that were provided when the instruction was created.
///
/// This struct should be used in a specific way: when matching on an
/// instruction, provide it the Regs in the same order as they were
/// provided to the OperandCollector.
#[derive(Clone)]
pub struct AllocationConsumer<'a> {
    allocs: std::slice::Iter<'a, Allocation>,
}

impl<'a> AllocationConsumer<'a> {
    pub fn new(allocs: &'a [Allocation]) -> Self {
        Self {
            allocs: allocs.iter(),
        }
    }

    pub fn next_fixed_nonallocatable(&mut self, preg: PReg) {
        let alloc = self.allocs.next();
        let alloc = alloc.map(|alloc| {
            Reg::from(
                alloc
                    .as_reg()
                    .expect("Should not have gotten a stack allocation"),
            )
        });

        match alloc {
            Some(alloc) => {
                assert_eq!(preg, alloc.to_real_reg().unwrap().into());
            }
            None => {}
        }
    }

    pub fn next(&mut self, pre_regalloc_reg: Reg) -> Reg {
        let alloc = self.allocs.next();
        let alloc = alloc.map(|alloc| {
            Reg::from(
                alloc
                    .as_reg()
                    .expect("Should not have gotten a stack allocation"),
            )
        });

        match (pre_regalloc_reg.to_real_reg(), alloc) {
            (Some(rreg), None) => rreg.into(),
            (Some(rreg), Some(alloc)) => {
                debug_assert_eq!(Reg::from(rreg), alloc);
                alloc
            }
            (None, Some(alloc)) => alloc,
            _ => pre_regalloc_reg,
        }
    }

    pub fn next_writable(&mut self, pre_regalloc_reg: Writable<Reg>) -> Writable<Reg> {
        Writable::from_reg(self.next(pre_regalloc_reg.to_reg()))
    }
}

impl<'a> std::default::Default for AllocationConsumer<'a> {
    fn default() -> Self {
        Self { allocs: [].iter() }
    }
}

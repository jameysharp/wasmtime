//! Evaluating const expressions.

use crate::runtime::vm::{Instance, VMGcRef, ValRaw, I31};
use anyhow::{anyhow, bail, Result};
use smallvec::SmallVec;
use wasmtime_environ::{ConstExpr, FuncIndex, GlobalIndex};

/// An interpreter for const expressions.
///
/// This can be reused across many const expression evaluations to reuse
/// allocated resources, if any.
#[derive(Default)]
pub struct ConstExprEvaluator {
    stack: SmallVec<[ValRaw; 2]>,
}

/// The context within which a particular const expression is evaluated.
pub trait ConstEvalContext {
    fn global_get(&mut self, index: GlobalIndex) -> Result<ValRaw>;
    fn ref_func(&mut self, index: FuncIndex) -> Result<ValRaw>;
}

impl ConstEvalContext for () {
    fn global_get(&mut self, _index: GlobalIndex) -> Result<ValRaw> {
        Err(anyhow!("can't evaluate global.get without an instance"))
    }

    fn ref_func(&mut self, _index: FuncIndex) -> Result<ValRaw> {
        Err(anyhow!("can't evaluate ref.func without an instance"))
    }
}

impl ConstEvalContext for Instance {
    fn global_get(&mut self, index: GlobalIndex) -> Result<ValRaw> {
        unsafe {
            let gc_store = (*self.store()).gc_store();
            let global = self.defined_or_imported_global_ptr(index).as_ref().unwrap();
            Ok(global.to_val_raw(gc_store, self.module().globals[index].wasm_ty))
        }
    }

    fn ref_func(&mut self, index: FuncIndex) -> Result<ValRaw> {
        Ok(ValRaw::funcref(self.get_func_ref(index).unwrap().cast()))
    }
}

impl ConstExprEvaluator {
    /// Evaluate the given const expression in the given context.
    ///
    /// # Unsafety
    ///
    /// The given const expression must be valid within the given context,
    /// e.g. the const expression must be well-typed and the context must return
    /// global values of the expected types. This evaluator operates directly on
    /// untyped `ValRaw`s and does not and cannot check that its operands are of
    /// the correct type.
    pub unsafe fn eval(
        &mut self,
        context: &mut impl ConstEvalContext,
        expr: &ConstExpr,
    ) -> Result<ValRaw> {
        self.stack.clear();

        for op in expr.ops() {
            match op {
                wasmtime_environ::ConstOp::I32Const(i) => self.stack.push(ValRaw::i32(*i)),
                wasmtime_environ::ConstOp::I64Const(i) => self.stack.push(ValRaw::i64(*i)),
                wasmtime_environ::ConstOp::F32Const(f) => self.stack.push(ValRaw::f32(*f)),
                wasmtime_environ::ConstOp::F64Const(f) => self.stack.push(ValRaw::f64(*f)),
                wasmtime_environ::ConstOp::V128Const(v) => self.stack.push(ValRaw::v128(*v)),
                wasmtime_environ::ConstOp::GlobalGet(g) => self.stack.push(context.global_get(*g)?),
                wasmtime_environ::ConstOp::RefNull => self.stack.push(ValRaw::null()),
                wasmtime_environ::ConstOp::RefFunc(f) => self.stack.push(context.ref_func(*f)?),
                wasmtime_environ::ConstOp::RefI31 => {
                    let i = self.pop()?.get_i32();
                    let i31 = I31::wrapping_i32(i);
                    let raw = VMGcRef::from_i31(i31).as_raw_u32();
                    self.stack.push(ValRaw::anyref(raw));
                }
            }
        }

        if self.stack.len() == 1 {
            Ok(self.stack[0])
        } else {
            bail!(
                "const expr evaluation error: expected 1 resulting value, found {}",
                self.stack.len()
            )
        }
    }

    fn pop(&mut self) -> Result<ValRaw> {
        self.stack.pop().ok_or_else(|| {
            anyhow!(
                "const expr evaluation error: attempted to pop from an empty \
                 evaluation stack"
            )
        })
    }
}

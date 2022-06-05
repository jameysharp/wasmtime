use crate::component::Func;
use crate::store::StoreOpaque;
use crate::{AsContext, AsContextMut, StoreContext, StoreContextMut, ValRaw};
use anyhow::{bail, Result};
use std::borrow::Cow;
use std::marker;
use std::mem::{self, MaybeUninit};
use std::str;
use wasmtime_environ::component::{ComponentTypes, InterfaceType, StringEncoding};

const MAX_STACK_PARAMS: usize = 16;
const MAX_STACK_RESULTS: usize = 1;

/// A helper macro to safely map `MaybeUninit<T>` to `MaybeUninit<U>` where `U`
/// is a field projection within `T`.
///
/// This is intended to be invoked as:
///
/// ```ignore
/// struct MyType {
///     field: u32,
/// }
///
/// let initial: &mut MaybeUninit<MyType> = ...;
/// let field: &mut MaybeUninit<u32> = map_maybe_uninit!(initial.field);
/// ```
///
/// Note that array accesses are also supported:
///
/// ```ignore
///
/// let initial: &mut MaybeUninit<[u32; 2]> = ...;
/// let element: &mut MaybeUninit<u32> = map_maybe_uninit!(initial[1]);
/// ```
macro_rules! map_maybe_uninit {
    ($maybe_uninit:ident $($field:tt)*) => (#[allow(unused_unsafe)] unsafe {
        let m: &mut MaybeUninit<_> = $maybe_uninit;
        // Note the usage of `addr_of_mut!` here which is an attempt to "stay
        // safe" here where we never accidentally create `&mut T` where `T` is
        // actually uninitialized, hopefully appeasing the Rust unsafe
        // guidelines gods.
        m.map(|p| std::ptr::addr_of_mut!((*p)$($field)*))
    })
}

trait MaybeUninitExt<T> {
    /// Maps `MaybeUninit<T>` to `MaybeUninit<U>` using the closure provided.
    ///
    /// Note that this is `unsafe` as there is no guarantee that `U` comes from
    /// `T`.
    unsafe fn map<U>(&mut self, f: impl FnOnce(*mut T) -> *mut U) -> &mut MaybeUninit<U>;
}

impl<T> MaybeUninitExt<T> for MaybeUninit<T> {
    unsafe fn map<U>(&mut self, f: impl FnOnce(*mut T) -> *mut U) -> &mut MaybeUninit<U> {
        let new_ptr = f(self.as_mut_ptr());
        mem::transmute::<*mut U, &mut MaybeUninit<U>>(new_ptr)
    }
}

/// A statically-typed version of [`Func`] which takes `Params` as input and
/// returns `Return`.
///
/// This is an efficient way to invoke a WebAssembly component where if the
/// inputs and output are statically known this can eschew the vast majority of
/// machinery and checks when calling WebAssembly. This is the most optimized
/// way to call a WebAssembly component.
///
/// Note that like [`Func`] this is a pointer within a [`Store`](crate::Store)
/// and usage will panic if used with the wrong store.
///
/// This type is primarily created with the [`Func::typed`] API.
pub struct TypedFunc<Params, Return> {
    func: Func,

    // The definition of this field is somewhat subtle and may be surprising.
    // Naively one might expect something like
    //
    //      _marker: marker::PhantomData<fn(Params) -> Return>,
    //
    // Since this is a function pointer after all. The problem with this
    // definition though is that it imposes the wrong variance on `Params` from
    // what we want. Abstractly a `fn(Params)` is able to store `Params` within
    // it meaning you can only give it `Params` that live longer than the
    // function pointer.
    //
    // With a component model function, however, we're always copying data from
    // the host into the guest, so we are never storing pointers to `Params`
    // into the guest outside the duration of a `call`, meaning we can actually
    // accept values in `TypedFunc::call` which live for a shorter duration
    // than the `Params` argument on the struct.
    //
    // This all means that we don't use a phantom function pointer, but instead
    // feign phantom storage here to get the variance desired.
    _marker: marker::PhantomData<(Params, Return)>,
}

impl<Params, Return> Copy for TypedFunc<Params, Return> {}

impl<Params, Return> Clone for TypedFunc<Params, Return> {
    fn clone(&self) -> TypedFunc<Params, Return> {
        *self
    }
}

impl<Params, Return> TypedFunc<Params, Return>
where
    Params: ComponentParams,
    Return: ComponentValue,
{
    /// Creates a new [`TypedFunc`] from the provided component [`Func`],
    /// unsafely asserting that the underlying function takes `Params` as
    /// input and returns `Return`.
    ///
    /// # Unsafety
    ///
    /// This is an unsafe function because it does not verify that the [`Func`]
    /// provided actually implements this signature. It's up to the caller to
    /// have performed some other sort of check to ensure that the signature is
    /// correct.
    pub unsafe fn new_unchecked(func: Func) -> TypedFunc<Params, Return> {
        TypedFunc {
            _marker: marker::PhantomData,
            func,
        }
    }

    /// Returns the underlying un-typed [`Func`] that this [`TypedFunc`]
    /// references.
    pub fn func(&self) -> &Func {
        &self.func
    }

    /// Calls the underlying WebAssembly component function using the provided
    /// `params` as input.
    ///
    /// This method is used to enter into a component. Execution happens within
    /// the `store` provided. The `params` are copied into WebAssembly memory
    /// as appropriate and a core wasm function is invoked.
    ///
    /// # Errors
    ///
    /// This function can return an error for a number of reasons:
    ///
    /// * If the wasm itself traps during execution.
    /// * If the wasm traps while copying arguments into memory.
    /// * If the wasm provides bad allocation pointers when copying arguments
    ///   into memory.
    /// * If the wasm returns a value which violates the canonical ABI.
    ///
    /// In general there are many ways that things could go wrong when copying
    /// types in and out of a wasm module with the canonical ABI, and certain
    /// error conditions are specific to certain types. For example a
    /// WebAssembly module can't return an invalid `char`. When allocating space
    /// for this host to copy a string into the returned pointer must be
    /// in-bounds in memory.
    ///
    /// If an error happens then the error should contain detailed enough
    /// information to understand which part of the canonical ABI went wrong
    /// and what to inspect.
    ///
    /// # Panics
    ///
    /// This function will panic if `store` does not own this function.
    pub fn call(&self, mut store: impl AsContextMut, params: Params) -> Result<Return> {
        let store = &mut store.as_context_mut();
        // Note that this is in theory simpler than it might read at this time.
        // Here we're doing a runtime dispatch on the `flatten_count` for the
        // params/results to see whether they're inbounds. This creates 4 cases
        // to handle. In reality this is a highly optimizable branch where LLVM
        // will easily figure out that only one branch here is taken.
        //
        // Otherwise this current construction is done to ensure that the stack
        // space reserved for the params/results is always of the appropriate
        // size (as the params/results needed differ depending on the "flatten"
        // count)
        if <Params::AsTuple as ComponentValue>::flatten_count() <= MAX_STACK_PARAMS {
            if Return::flatten_count() <= MAX_STACK_RESULTS {
                self.call_raw(
                    store,
                    &params,
                    Self::lower_stack_args,
                    Self::lift_stack_result,
                )
            } else {
                self.call_raw(
                    store,
                    &params,
                    Self::lower_stack_args,
                    Self::lift_heap_result,
                )
            }
        } else {
            if Return::flatten_count() <= MAX_STACK_RESULTS {
                self.call_raw(
                    store,
                    &params,
                    Self::lower_heap_args,
                    Self::lift_stack_result,
                )
            } else {
                self.call_raw(
                    store,
                    &params,
                    Self::lower_heap_args,
                    Self::lift_heap_result,
                )
            }
        }
    }

    /// Lower parameters directly onto the stack specified by the `dst`
    /// location.
    ///
    /// This is only valid to call when the "flatten count" is small enough, or
    /// when the canonical ABI says arguments go through the stack rather than
    /// the heap.
    fn lower_stack_args<T>(
        &self,
        store: &mut StoreContextMut<'_, T>,
        params: &Params,
        dst: &mut MaybeUninit<<Params::AsTuple as ComponentValue>::Lower>,
    ) -> Result<()> {
        assert!(<Params::AsTuple as ComponentValue>::flatten_count() <= MAX_STACK_PARAMS);
        params.lower(store, &self.func, dst)?;
        Ok(())
    }

    /// Lower parameters onto a heap-allocated location.
    ///
    /// This is used when the stack space to be used for the arguments is above
    /// the `MAX_STACK_PARAMS` threshold. Here the wasm's `realloc` function is
    /// invoked to allocate space and then parameters are stored at that heap
    /// pointer location.
    fn lower_heap_args<T>(
        &self,
        store: &mut StoreContextMut<'_, T>,
        params: &Params,
        dst: &mut MaybeUninit<ValRaw>,
    ) -> Result<()> {
        assert!(<Params::AsTuple as ComponentValue>::flatten_count() > MAX_STACK_PARAMS);

        // Memory must exist via validation if the arguments are stored on the
        // heap, so we can create a `MemoryMut` at this point. Afterwards
        // `realloc` is used to allocate space for all the arguments and then
        // they're all stored in linear memory.
        //
        // Note that `realloc` will bake in a check that the returned pointer is
        // in-bounds.
        let mut memory = MemoryMut::new(store.as_context_mut(), &self.func);
        let ptr = memory.realloc(0, 0, Params::align(), Params::size())?;
        params.store(&mut memory, ptr)?;

        // Note that the pointer here is stored as a 64-bit integer. This allows
        // this to work with either 32 or 64-bit memories. For a 32-bit memory
        // it'll just ignore the upper 32 zero bits, and for 64-bit memories
        // this'll have the full 64-bits. Note that for 32-bit memories the call
        // to `realloc` above guarantees that the `ptr` is in-bounds meaning
        // that we will know that the zero-extended upper bits of `ptr` are
        // guaranteed to be zero.
        //
        // This comment about 64-bit integers is also referred to below with
        // "WRITEPTR64".
        dst.write(ValRaw::i64(ptr as i64));

        Ok(())
    }

    /// Lift the result of a function directly from the stack result.
    ///
    /// This is only used when the result fits in the maximum number of stack
    /// slots.
    fn lift_stack_result(&self, store: &StoreOpaque, dst: &Return::Lower) -> Result<Return> {
        assert!(Return::flatten_count() <= MAX_STACK_RESULTS);
        Return::lift(store, &self.func, dst)
    }

    /// Lift the result of a function where the result is stored indirectly on
    /// the heap.
    fn lift_heap_result(&self, store: &StoreOpaque, dst: &ValRaw) -> Result<Return> {
        assert!(Return::flatten_count() > MAX_STACK_RESULTS);
        // FIXME: needs to read an i64 for memory64
        let ptr = usize::try_from(dst.get_u32()).unwrap();
        let memory = Memory::new(store, &self.func);
        let bytes = memory
            .as_slice()
            .get(ptr..)
            .and_then(|b| b.get(..Return::size()))
            .ok_or_else(|| anyhow::anyhow!("pointer out of bounds of memory"))?;
        Return::load(&memory, bytes)
    }

    /// Invokes the underlying wasm function, lowering arguments and lifting the
    /// result.
    ///
    /// The `lower` function and `lift` function provided here are what actually
    /// do the lowering and lifting. The `LowerParams` and `LowerReturn` types
    /// are what will be allocated on the stack for this function call. They
    /// should be appropriately sized for the lowering/lifting operation
    /// happening.
    fn call_raw<T, LowerParams, LowerReturn>(
        &self,
        store: &mut StoreContextMut<'_, T>,
        params: &Params,
        lower: impl FnOnce(
            &Self,
            &mut StoreContextMut<'_, T>,
            &Params,
            &mut MaybeUninit<LowerParams>,
        ) -> Result<()>,
        lift: impl FnOnce(&Self, &StoreOpaque, &LowerReturn) -> Result<Return>,
    ) -> Result<Return>
    where
        LowerParams: Copy,
        LowerReturn: Copy,
    {
        let super::FuncData {
            trampoline, export, ..
        } = store.0[self.func.0];

        let space = &mut MaybeUninit::<ParamsAndResults<LowerParams, LowerReturn>>::uninit();

        // Double-check the size/alignemnt of `space`, just in case.
        //
        // Note that this alone is not enough to guarantee the validity of the
        // `unsafe` block below, but it's definitely required. In any case LLVM
        // should be able to trivially see through these assertions and remove
        // them in release mode.
        let val_size = mem::size_of::<ValRaw>();
        let val_align = mem::align_of::<ValRaw>();
        assert!(mem::size_of_val(space) % val_size == 0);
        assert!(mem::size_of_val(map_maybe_uninit!(space.params)) % val_size == 0);
        assert!(mem::size_of_val(map_maybe_uninit!(space.ret)) % val_size == 0);
        assert!(mem::align_of_val(space) == val_align);
        assert!(mem::align_of_val(map_maybe_uninit!(space.params)) == val_align);
        assert!(mem::align_of_val(map_maybe_uninit!(space.ret)) == val_align);

        lower(self, store, params, map_maybe_uninit!(space.params))?;

        unsafe {
            // This is unsafe as we are providing the guarantee that all the
            // inputs are valid. The various pointers passed in for the function
            // are all valid since they're coming from our store, and the
            // `params_and_results` should have the correct layout for the core
            // wasm function we're calling. Note that this latter point relies
            // on the correctness of this module and `ComponentValue`
            // implementations, hence `ComponentValue` being an `unsafe` trait.
            crate::Func::call_unchecked_raw(
                store,
                export.anyfunc,
                trampoline,
                space.as_mut_ptr().cast(),
            )?;

            // Note that `.assume_init_ref()` here is unsafe but we're relying
            // on the correctness of the structure of `LowerReturn` and the
            // type-checking performed to acquire the `TypedFunc` to make this
            // safe. It should be the case that `LowerReturn` is the exact
            // representation of the return value when interpreted as
            // `[ValRaw]`, and additionally they should have the correct types
            // for the function we just called (which filled in the return
            // values).
            lift(
                self,
                store.0,
                map_maybe_uninit!(space.ret).assume_init_ref(),
            )
        }
    }
}

#[repr(C)]
union ParamsAndResults<Params: Copy, Return: Copy> {
    params: Params,
    ret: Return,
}

/// A trait representing a static list of parameters that can be passed to a
/// [`TypedFunc`].
///
/// This trait is implemented for a number of tuple types and is not expected
/// to be implemented externally. The contents of this trait are hidden as it's
/// intended to be an implementation detail of Wasmtime. The contents of this
/// trait are not covered by Wasmtime's stability guarantees.
///
/// For more information about this trait see [`Func::typed`] and
/// [`TypedFunc`].
//
// Note that this is an `unsafe` trait, and the unsafety means that
// implementations of this trait must be correct or otherwise [`TypedFunc`]
// would not be memory safe. The main reason this is `unsafe` is the
// `typecheck` function which must operate correctly relative to the `AsTuple`
// interpretation of the implementor.
pub unsafe trait ComponentParams {
    /// The tuple type corresponding to this list of parameters if this list is
    /// interpreted as a tuple in the canonical ABI.
    #[doc(hidden)]
    type AsTuple: ComponentValue;

    /// Performs a typecheck to ensure that this `ComponentParams` implementor
    /// matches the types of the types in `params`.
    #[doc(hidden)]
    fn typecheck(params: &[(Option<String>, InterfaceType)], types: &ComponentTypes) -> Result<()>;

    /// Views this instance of `ComponentParams` as a tuple, allowing
    /// delegation to all of the methods in `ComponentValue`.
    #[doc(hidden)]
    fn as_tuple(&self) -> &Self::AsTuple;

    /// Convenience method to `ComponentValue::lower` when viewing this
    /// parameter list as a tuple.
    #[doc(hidden)]
    fn lower<T>(
        &self,
        store: &mut StoreContextMut<T>,
        func: &Func,
        dst: &mut MaybeUninit<<Self::AsTuple as ComponentValue>::Lower>,
    ) -> Result<()> {
        self.as_tuple().lower(store, func, dst)
    }

    /// Convenience method to `ComponentValue::store` when viewing this
    /// parameter list as a tuple.
    #[doc(hidden)]
    fn store<T>(&self, memory: &mut MemoryMut<'_, T>, offset: usize) -> Result<()> {
        self.as_tuple().store(memory, offset)
    }

    /// Convenience function to return the canonical abi alignment of this list
    /// of parameters when viewed as a tuple.
    #[doc(hidden)]
    #[inline]
    fn align() -> u32 {
        Self::AsTuple::align()
    }

    /// Convenience function to return the canonical abi byte size of this list
    /// of parameters when viewed as a tuple.
    #[doc(hidden)]
    #[inline]
    fn size() -> usize {
        Self::AsTuple::size()
    }
}

// Macro to generate an implementation of `ComponentParams` for all supported
// lengths of tuples of types in Wasmtime.
macro_rules! impl_component_params {
    ($n:tt $($t:ident)*) => {paste::paste!{
        #[allow(non_snake_case)]
        unsafe impl<$($t,)*> ComponentParams for ($($t,)*) where $($t: ComponentValue),* {
            type AsTuple = ($($t,)*);

            fn typecheck(
                params: &[(Option<String>, InterfaceType)],
                _types: &ComponentTypes,
            ) -> Result<()> {
                if params.len() != $n {
                    bail!("expected {} types, found {}", $n, params.len());
                }
                let mut params = params.iter().map(|i| &i.1);
                $($t::typecheck(params.next().unwrap(), _types, Op::Lower)?;)*
                debug_assert!(params.next().is_none());
                Ok(())
            }

            #[inline]
            fn as_tuple(&self) -> &Self::AsTuple {
                self
            }
        }
    }};
}

for_each_function_signature!(impl_component_params);

/// A trait representing types which can be passed to and read from components
/// with the canonical ABI.
///
/// This trait is implemented for Rust types which can be communicated to
/// components. This is implemented for Rust types which correspond to
/// interface types in the component model of WebAssembly. The [`Func::typed`]
/// and [`TypedFunc`] Rust items are the main consumers of this trait.
///
/// For more information on this trait see the examples in [`Func::typed`].
///
/// The contents of this trait are hidden as it's intended to be an
/// implementation detail of Wasmtime. The contents of this trait are not
/// covered by Wasmtime's stability guarantees.
//
// Note that this is an `unsafe` trait as `TypedFunc`'s safety heavily relies on
// the correctness of the implementations of this trait. Some ways in which this
// trait must be correct to be safe are:
//
// * The `Lower` associated type must be a `ValRaw` sequence. It doesn't have to
//   literally be `[ValRaw; N]` but when laid out in memory it must be adjacent
//   `ValRaw` values and have a multiple of the size of `ValRaw` and the same
//   alignment.
//
// * The `lower` function must initialize the bits within `Lower` that are going
//   to be read by the trampoline that's used to enter core wasm. A trampoline
//   is passed `*mut Lower` and will read the canonical abi arguments in
//   sequence, so all of the bits must be correctly initialized.
//
// * The `size` and `align` functions must be correct for this value stored in
//   the canonical ABI. The `Cursor<T>` iteration of these bytes rely on this
//   for correctness as they otherwise eschew bounds-checking.
//
// There are likely some other correctness issues which aren't documented as
// well, this isn't intended to be an exhaustive list. It suffices to say,
// though, that correctness bugs in this trait implementation are highly likely
// to lead to security bugs, which again leads to the `unsafe` in the trait.
//
// Also note that this trait specifically is not sealed because we'll
// eventually have a proc macro that generates implementations of this trait
// for external types in a `#[derive]`-like fashion.
//
// FIXME: need to write a #[derive(ComponentValue)]
pub unsafe trait ComponentValue {
    /// Representation of the "lowered" form of this component value.
    ///
    /// Lowerings lower into core wasm values which are represented by `ValRaw`.
    /// This `Lower` type must be a list of `ValRaw` as either a literal array
    /// or a struct where every field is a `ValRaw`. This must be `Copy` (as
    /// `ValRaw` is `Copy`) and support all byte patterns. This being correct is
    /// one reason why the trait is unsafe.
    #[doc(hidden)]
    type Lower: Copy;

    /// Returns the number of core wasm abi values will be used to represent
    /// this type in its lowered form.
    ///
    /// This divides the size of `Self::Lower` by the size of `ValRaw`.
    #[doc(hidden)]
    fn flatten_count() -> usize {
        assert!(mem::size_of::<Self::Lower>() % mem::size_of::<ValRaw>() == 0);
        assert!(mem::align_of::<Self::Lower>() == mem::align_of::<ValRaw>());
        mem::size_of::<Self::Lower>() / mem::size_of::<ValRaw>()
    }

    /// Performs a type-check to see whether this comopnent value type matches
    /// the interface type `ty` provided.
    ///
    /// The `op` provided is the operations which could be performed with this
    /// type if the typecheck passes, either lifting or lowering. Some Rust
    /// types are only valid for one operation and we can't prevent the wrong
    /// one from being used at compile time so we rely on the runtime check
    /// here.
    #[doc(hidden)]
    fn typecheck(ty: &InterfaceType, types: &ComponentTypes, op: Op) -> Result<()>;

    /// Returns the size, in bytes, that this type has in the canonical ABI.
    ///
    /// Note that it's expected that this function is "simple" to be easily
    /// optimizable by LLVM (e.g. inlined and const-evaluated).
    //
    // FIXME: needs some sort of parameter indicating the memory size
    #[doc(hidden)]
    fn size() -> usize;

    /// Returns the alignment, in bytes, that this type has in the canonical
    /// ABI.
    ///
    /// Note that it's expected that this function is "simple" to be easily
    /// optimizable by LLVM (e.g. inlined and const-evaluated).
    #[doc(hidden)]
    fn align() -> u32;

    /// Performs the "lower" function in the canonical ABI.
    ///
    /// This method will lower the given value into wasm linear memory. The
    /// `store` and `func` are provided in case memory is needed (e.g. for
    /// strings/lists) so `realloc` can be called. The `dst` is the destination
    /// to store the lowered results.
    ///
    /// Note that `dst` is a pointer to uninitialized memory. It's expected
    /// that `dst` is fully initialized by the time this function returns, hence
    /// the `unsafe` on the trait implementation.
    ///
    /// This will only be called if `typecheck` passes for `Op::Lower`.
    #[doc(hidden)]
    fn lower<T>(
        &self,
        store: &mut StoreContextMut<T>,
        func: &Func,
        dst: &mut MaybeUninit<Self::Lower>,
    ) -> Result<()>;

    /// Performs the "lift" oepration in the canonical ABI.
    ///
    /// This will read the core wasm values from `src` and use the memory
    /// specified by `func` and `store` optionally if necessary. An instance of
    /// `Self` is then created from the values, assuming validation succeeds.
    ///
    /// Note that this has a default implementation but if `typecheck` passes
    /// for `Op::Lift` this needs to be overridden.
    #[doc(hidden)]
    fn lift(store: &StoreOpaque, func: &Func, src: &Self::Lower) -> Result<Self>
    where
        Self: Sized,
    {
        // NB: ideally there would be no default implementation here but to
        // enable `impl ComponentValue for str` this is the way we get it today.
        drop((store, func, src));
        unreachable!("this should be rejected during typechecking")
    }

    /// Performs the "store" operation in the canonical ABI.
    ///
    /// This function will store `self` into the linear memory described by
    /// `memory` at the `offset` provided.
    ///
    /// It is expected that `offset` is a valid offset in memory for
    /// `Self::size()` bytes. At this time that's not an unsafe contract as it's
    /// always re-checked on all stores, but this is something that will need to
    /// be improved in the future to remove extra bounds checks. For now this
    /// function will panic if there's a bug and `offset` isn't valid within
    /// memory.
    ///
    /// This will only be called if `typecheck` passes for `Op::Lower`.
    #[doc(hidden)]
    fn store<T>(&self, memory: &mut MemoryMut<'_, T>, offset: usize) -> Result<()>;

    /// Performs the "load" operation in the canonical ABI.
    ///
    /// This is given the linear-memory representation of `Self` in the `bytes`
    /// array provided which is guaranteed to be `Self::size()` bytes large. All
    /// of memory is then also described with `Memory` for bounds-checks and
    /// such as necessary for strings/lists.
    ///
    /// Note that this has a default implementation but if `typecheck` passes
    /// for `Op::Lift` this needs to be overridden.
    #[doc(hidden)]
    fn load(memory: &Memory<'_>, bytes: &[u8]) -> Result<Self>
    where
        Self: Sized,
    {
        // See `lift` above for why there's a default implementation here
        drop((memory, bytes));
        unreachable!("this should be rejected during typechecking")
    }
}

/// Operational parameter passed to `ComponentValue::typecheck` indicating how a
/// value will be used in a particular context.
///
/// This is used to disallow, at runtime, loading a `&Vec<String>` from wasm
/// since that can't be done. Instead that has to be `WasmList<WasmStr>`.
#[doc(hidden)]
#[derive(Copy, Clone)]
pub enum Op {
    /// A "lift" operation will be performed, meaning values will be read from
    /// wasm.
    Lift,
    /// A "lower" operation will be performed, meaning values will be written to
    /// wasm.
    Lower,
}

/// A helper structure to package up proof-of-memory. This holds a store pointer
/// and a `Func` pointer where the function has the pointers to memory.
///
/// Note that one of the purposes of this type is to make `lower_list`
/// vectorizable by "caching" the last view of memory. CUrrently it doesn't do
/// that, though, because I couldn't get `lower_list::<u8>` to vectorize. I've
/// left this in for convenience in the hope that this can be updated in the
/// future.
#[doc(hidden)]
pub struct MemoryMut<'a, T> {
    store: StoreContextMut<'a, T>,
    func: &'a Func,
}

impl<'a, T> MemoryMut<'a, T> {
    fn new(store: StoreContextMut<'a, T>, func: &'a Func) -> MemoryMut<'a, T> {
        MemoryMut { func, store }
    }

    #[inline]
    fn string_encoding(&self) -> StringEncoding {
        self.store.0[self.func.0].options.string_encoding
    }

    #[inline]
    fn memory(&mut self) -> &mut [u8] {
        self.func.memory_mut(self.store.0)
    }

    fn realloc(
        &mut self,
        old: usize,
        old_size: usize,
        old_align: u32,
        new_size: usize,
    ) -> Result<usize> {
        let ret = self
            .func
            .realloc(&mut self.store, old, old_size, old_align, new_size)
            .map(|(_, ptr)| ptr);
        return ret;
    }

    fn get<const N: usize>(&mut self, offset: usize) -> &mut [u8; N] {
        // FIXME: this bounds check shouldn't actually be necessary, all
        // callers of `ComponentValue::store` have already performed a bounds
        // check so we're guaranteed that `offset..offset+N` is in-bounds. That
        // being said we at least should do bounds checks in debug mode and
        // it's not clear to me how to easily structure this so that it's
        // "statically obvious" the bounds check isn't necessary.
        //
        // For now I figure we can leave in this bounds check and if it becomes
        // an issue we can optimize further later, probably with judicious use
        // of `unsafe`.
        (&mut self.memory()[offset..][..N]).try_into().unwrap()
    }
}

/// Like `MemoryMut` but for a read-only version that's used during lifting.
#[doc(hidden)]
pub struct Memory<'a> {
    store: &'a StoreOpaque,
    func: &'a Func,
}

impl<'a> Memory<'a> {
    fn new(store: &'a StoreOpaque, func: &'a Func) -> Memory<'a> {
        Memory { store, func }
    }

    fn as_slice(&self) -> &'a [u8] {
        self.func.memory(self.store)
    }

    fn string_encoding(&self) -> StringEncoding {
        self.store[self.func.0].options.string_encoding
    }
}

// Macro to help generate "forwarding implementations" of `ComponentValue` to
// another type, used for wrappers in Rust like `&T`, `Box<T>`, etc.
macro_rules! forward_component_param {
    ($(($($generics:tt)*) $a:ty => $b:ty,)*) => ($(
        unsafe impl <$($generics)*> ComponentValue for $a
        {
            type Lower = <$b as ComponentValue>::Lower;

            #[inline]
            fn typecheck(ty: &InterfaceType, types: &ComponentTypes, op: Op) -> Result<()> {
                match op {
                    // Lowering rust wrappers is ok since we know how to
                    // traverse the host to lower the item.
                    Op::Lower => {}

                    // Lifting, however, is not ok and has no meaning. For
                    // example we can't create a `&str` from wasm. It also
                    // doesn't really make sense to create `Arc<T>`, for
                    // example. In these cases different types need to be used
                    // such as `WasmList` or `WasmStr`.
                    Op::Lift => bail!("this type cannot be lifted from wasm"),
                }
                <$b as ComponentValue>::typecheck(ty, types, op)
            }

            fn lower<U>(
                &self,
                store: &mut StoreContextMut<U>,
                func: &Func,
                dst: &mut MaybeUninit<Self::Lower>,
            ) -> Result<()> {
                <$b as ComponentValue>::lower(self, store, func, dst)
            }

            #[inline]
            fn size() -> usize {
                <$b as ComponentValue>::size()
            }

            #[inline]
            fn align() -> u32 {
                <$b as ComponentValue>::align()
            }

            fn store<U>(&self, memory: &mut MemoryMut<'_, U>, offset: usize) -> Result<()> {
                <$b as ComponentValue>::store(self, memory, offset)
            }

            fn lift(_store: &StoreOpaque, _func: &Func,_src: &Self::Lower) -> Result<Self> {
                unreachable!()
            }

            fn load(_mem: &Memory, _bytes: &[u8]) -> Result<Self> {
                unreachable!()
            }
        }
    )*)
}

forward_component_param! {
    (T: ComponentValue + ?Sized) &'_ T => T,
    (T: ComponentValue + ?Sized) Box<T> => T,
    (T: ComponentValue + ?Sized) std::rc::Rc<T> => T,
    (T: ComponentValue + ?Sized) std::sync::Arc<T> => T,
    () String => str,
    (T: ComponentValue) Vec<T> => [T],
}

unsafe impl ComponentValue for () {
    // A 0-sized array is used here to represent that it has zero-size but it
    // still has the alignment of `ValRaw`.
    type Lower = [ValRaw; 0];

    fn typecheck(ty: &InterfaceType, _types: &ComponentTypes, _op: Op) -> Result<()> {
        match ty {
            // FIXME(WebAssembly/component-model#21) this may either want to
            // match more types, not actually exist as a trait impl, or
            // something like that. Figuring out on that issue about the
            // relationship between the 0-tuple, unit, and empty structs.
            InterfaceType::Unit => Ok(()),
            other => bail!("expected `unit` found `{}`", desc(other)),
        }
    }

    #[inline]
    fn lower<T>(
        &self,
        _store: &mut StoreContextMut<T>,
        _func: &Func,
        _dst: &mut MaybeUninit<Self::Lower>,
    ) -> Result<()> {
        Ok(())
    }

    #[inline]
    fn size() -> usize {
        0
    }

    #[inline]
    fn align() -> u32 {
        1
    }

    #[inline]
    fn store<T>(&self, _memory: &mut MemoryMut<'_, T>, _offset: usize) -> Result<()> {
        Ok(())
    }

    #[inline]
    fn lift(_store: &StoreOpaque, _func: &Func, _src: &Self::Lower) -> Result<Self> {
        Ok(())
    }

    #[inline]
    fn load(_mem: &Memory, _bytes: &[u8]) -> Result<Self> {
        Ok(())
    }
}

// Macro to help generate `ComponentValue` implementations for primitive types
// such as integers, char, bool, etc.
macro_rules! integers {
    ($($primitive:ident = $ty:ident in $field:ident/$get:ident,)*) => ($(
        unsafe impl ComponentValue for $primitive {
            type Lower = ValRaw;

            fn typecheck(ty: &InterfaceType, _types: &ComponentTypes, _op: Op) -> Result<()> {
                match ty {
                    InterfaceType::$ty => Ok(()),
                    other => bail!("expected `{}` found `{}`", desc(&InterfaceType::$ty), desc(other))
                }
            }

            fn lower<T>(
                &self,
                _store: &mut StoreContextMut<T>,
                _func: &Func,
                dst: &mut MaybeUninit<Self::Lower>,
            ) -> Result<()> {
                dst.write(ValRaw::$field(*self as $field));
                Ok(())
            }

            #[inline]
            fn size() -> usize { mem::size_of::<$primitive>() }

            // Note that this specifically doesn't use `align_of` as some
            // host platforms have a 4-byte alignment for primitive types but
            // the canonical abi always has the same size/alignment for these
            // types.
            #[inline]
            fn align() -> u32 { mem::size_of::<$primitive>() as u32 }

            fn store<T>(&self, memory: &mut MemoryMut<'_, T>, offset: usize) -> Result<()> {
                *memory.get(offset) = self.to_le_bytes();
                Ok(())
            }

            #[inline]
            fn lift(_store: &StoreOpaque, _func: &Func, src: &Self::Lower) -> Result<Self> {
                // Perform a lossless cast from our field storage to the
                // destination type. Note that `try_from` here is load bearing
                // which rejects conversions like `500u32` to `u8` because
                // that's out-of-bounds for `u8`.
                Ok($primitive::try_from(src.$get())?)
            }

            #[inline]
            fn load(_mem: &Memory<'_>, bytes: &[u8]) -> Result<Self> {
                Ok($primitive::from_le_bytes(bytes.try_into().unwrap()))
            }
        }
    )*)
}

integers! {
    i8 = S8 in i32/get_i32,
    u8 = U8 in u32/get_u32,
    i16 = S16 in i32/get_i32,
    u16 = U16 in u32/get_u32,
    i32 = S32 in i32/get_i32,
    u32 = U32 in u32/get_u32,
    i64 = S64 in i64/get_i64,
    u64 = U64 in u64/get_u64,
}

macro_rules! floats {
    ($($float:ident/$get_float:ident = $ty:ident)*) => ($(const _: () = {
        /// All floats in-and-out of the canonical abi always have their nan
        /// payloads canonicalized. conveniently the `NAN` constant in rust has
        /// the same representation as canonical nan, so we can use that for the
        /// nan value.
        #[inline]
        fn canonicalize(float: $float) -> $float {
            if float.is_nan() {
                $float::NAN
            } else {
                float
            }
        }

        unsafe impl ComponentValue for $float {
            type Lower = ValRaw;

            fn typecheck(ty: &InterfaceType, _types: &ComponentTypes, _op: Op) -> Result<()> {
                match ty {
                    InterfaceType::$ty => Ok(()),
                    other => bail!("expected `{}` found `{}`", desc(&InterfaceType::$ty), desc(other))
                }
            }

            fn lower<T>(
                &self,
                _store: &mut StoreContextMut<T>,
                _func: &Func,
                dst: &mut MaybeUninit<Self::Lower>,
            ) -> Result<()> {
                dst.write(ValRaw::$float(canonicalize(*self).to_bits()));
                Ok(())
            }

            #[inline]
            fn size() -> usize { mem::size_of::<$float>() }

            // note that like integers size is used here instead of alignment to
            // respect the canonical abi, not host platforms.
            #[inline]
            fn align() -> u32 { mem::size_of::<$float>() as u32 }

            fn store<T>(&self, memory: &mut MemoryMut<'_, T>, offset: usize) -> Result<()> {
                let ptr = memory.get(offset);
                *ptr = canonicalize(*self).to_bits().to_le_bytes();
                Ok(())
            }

            #[inline]
            fn lift(_store: &StoreOpaque, _func: &Func, src: &Self::Lower) -> Result<Self> {
                Ok(canonicalize($float::from_bits(src.$get_float())))
            }

            #[inline]
            fn load(_mem: &Memory<'_>, bytes: &[u8]) -> Result<Self> {
                Ok(canonicalize($float::from_le_bytes(bytes.try_into().unwrap())))
            }
        }
    };)*)
}

floats! {
    f32/get_f32 = Float32
    f64/get_f64 = Float64
}

unsafe impl ComponentValue for bool {
    type Lower = ValRaw;

    fn typecheck(ty: &InterfaceType, _types: &ComponentTypes, _op: Op) -> Result<()> {
        match ty {
            InterfaceType::Bool => Ok(()),
            other => bail!("expected `bool` found `{}`", desc(other)),
        }
    }

    fn lower<T>(
        &self,
        _store: &mut StoreContextMut<T>,
        _func: &Func,
        dst: &mut MaybeUninit<Self::Lower>,
    ) -> Result<()> {
        dst.write(ValRaw::i32(*self as i32));
        Ok(())
    }

    #[inline]
    fn size() -> usize {
        1
    }

    #[inline]
    fn align() -> u32 {
        1
    }

    fn store<T>(&self, memory: &mut MemoryMut<'_, T>, offset: usize) -> Result<()> {
        memory.get::<1>(offset)[0] = *self as u8;
        Ok(())
    }

    #[inline]
    fn lift(_store: &StoreOpaque, _func: &Func, src: &Self::Lower) -> Result<Self> {
        match src.get_i32() {
            0 => Ok(false),
            1 => Ok(true),
            _ => bail!("invalid boolean value"),
        }
    }

    #[inline]
    fn load(_mem: &Memory<'_>, bytes: &[u8]) -> Result<Self> {
        match bytes[0] {
            0 => Ok(false),
            1 => Ok(true),
            _ => bail!("invalid boolean value"),
        }
    }
}

unsafe impl ComponentValue for char {
    type Lower = ValRaw;

    fn typecheck(ty: &InterfaceType, _types: &ComponentTypes, _op: Op) -> Result<()> {
        match ty {
            InterfaceType::Char => Ok(()),
            other => bail!("expected `char` found `{}`", desc(other)),
        }
    }

    fn lower<T>(
        &self,
        _store: &mut StoreContextMut<T>,
        _func: &Func,
        dst: &mut MaybeUninit<Self::Lower>,
    ) -> Result<()> {
        dst.write(ValRaw::u32(u32::from(*self)));
        Ok(())
    }

    #[inline]
    fn size() -> usize {
        4
    }

    #[inline]
    fn align() -> u32 {
        4
    }

    fn store<T>(&self, memory: &mut MemoryMut<'_, T>, offset: usize) -> Result<()> {
        *memory.get::<4>(offset) = u32::from(*self).to_le_bytes();
        Ok(())
    }

    #[inline]
    fn lift(_store: &StoreOpaque, _func: &Func, src: &Self::Lower) -> Result<Self> {
        Ok(char::try_from(src.get_u32())?)
    }

    #[inline]
    fn load(_memory: &Memory<'_>, bytes: &[u8]) -> Result<Self> {
        let bits = u32::from_le_bytes(bytes.try_into().unwrap());
        Ok(char::try_from(bits)?)
    }
}

// Note that this is similar to `ComponentValue for WasmStr` except it can only
// be used for lowering, not lifting.
unsafe impl ComponentValue for str {
    type Lower = [ValRaw; 2];

    fn typecheck(ty: &InterfaceType, _types: &ComponentTypes, op: Op) -> Result<()> {
        match op {
            Op::Lower => {}
            Op::Lift => {
                bail!("strings in Rust cannot be lifted from wasm, use `WasmStr` instead")
            }
        }
        match ty {
            InterfaceType::String => Ok(()),
            other => bail!("expected `string` found `{}`", desc(other)),
        }
    }

    fn lower<T>(
        &self,
        store: &mut StoreContextMut<T>,
        func: &Func,
        dst: &mut MaybeUninit<[ValRaw; 2]>,
    ) -> Result<()> {
        let (ptr, len) = lower_string(&mut MemoryMut::new(store.as_context_mut(), func), self)?;
        // See "WRITEPTR64" above for why this is always storing a 64-bit
        // integer.
        map_maybe_uninit!(dst[0]).write(ValRaw::i64(ptr as i64));
        map_maybe_uninit!(dst[1]).write(ValRaw::i64(len as i64));
        Ok(())
    }

    fn size() -> usize {
        8
    }

    fn align() -> u32 {
        4
    }

    fn store<T>(&self, mem: &mut MemoryMut<'_, T>, offset: usize) -> Result<()> {
        let (ptr, len) = lower_string(mem, self)?;
        // FIXME: needs memory64 handling
        *mem.get(offset + 0) = (ptr as i32).to_le_bytes();
        *mem.get(offset + 4) = (len as i32).to_le_bytes();
        Ok(())
    }
}

fn lower_string<T>(mem: &mut MemoryMut<'_, T>, string: &str) -> Result<(usize, usize)> {
    match mem.string_encoding() {
        StringEncoding::Utf8 => {
            let ptr = mem.realloc(0, 0, 1, string.len())?;
            mem.memory()[ptr..][..string.len()].copy_from_slice(string.as_bytes());
            Ok((ptr, string.len()))
        }
        StringEncoding::Utf16 => {
            let size = string.len() * 2;
            let mut ptr = mem.realloc(0, 0, 2, size)?;
            let bytes = &mut mem.memory()[ptr..][..size];
            let mut copied = 0;
            for (u, bytes) in string.encode_utf16().zip(bytes.chunks_mut(2)) {
                let u_bytes = u.to_le_bytes();
                bytes[0] = u_bytes[0];
                bytes[1] = u_bytes[1];
                copied += 1;
            }
            if (copied * 2) < size {
                ptr = mem.realloc(ptr, size, 2, copied * 2)?;
            }
            Ok((ptr, copied))
        }
        StringEncoding::CompactUtf16 => {
            unimplemented!("compact-utf-16");
        }
    }
}

/// Representation of a string located in linear memory in a WebAssembly
/// instance.
///
/// This type is used with [`TypedFunc`], for example, when WebAssembly returns
/// a string. This type cannot be used to give a string to WebAssembly, instead
/// `&str` should be used for that (since it's coming from the host).
///
/// Note that this type represents an in-bounds string in linear memory, but it
/// does not represent a valid string (e.g. valid utf-8). Validation happens
/// when [`WasmStr::to_str`] is called.
//
// TODO: should probably expand this with examples
pub struct WasmStr {
    ptr: usize,
    len: usize,
    func: Func,
}

impl WasmStr {
    fn new(ptr: usize, len: usize, memory: &Memory<'_>) -> Result<WasmStr> {
        let byte_len = match memory.string_encoding() {
            StringEncoding::Utf8 => Some(len),
            StringEncoding::Utf16 => len.checked_mul(2),
            StringEncoding::CompactUtf16 => unimplemented!(),
        };
        match byte_len.and_then(|len| ptr.checked_add(len)) {
            Some(n) if n <= memory.as_slice().len() => {}
            _ => bail!("string pointer/length out of bounds of memory"),
        }
        Ok(WasmStr {
            ptr,
            len,
            func: *memory.func,
        })
    }

    /// Returns the underlying string that this cursor points to.
    ///
    /// Note that this will internally decode the string from the wasm's
    /// encoding to utf-8 and additionally perform validation.
    ///
    /// The `store` provided must be the store where this string lives to
    /// access the correct memory.
    ///
    /// # Errors
    ///
    /// Returns an error if the string wasn't encoded correctly (e.g. invalid
    /// utf-8).
    ///
    /// # Panics
    ///
    /// Panics if this string is not owned by `store`.
    //
    // TODO: should add accessors for specifically utf-8 and utf-16 that perhaps
    // in an opt-in basis don't do validation. Additionally there should be some
    // method that returns `[u16]` after validating to avoid the utf16-to-utf8
    // transcode.
    pub fn to_str<'a, T: 'a>(&self, store: impl Into<StoreContext<'a, T>>) -> Result<Cow<'a, str>> {
        self._to_str(store.into().0)
    }

    fn _to_str<'a>(&self, store: &'a StoreOpaque) -> Result<Cow<'a, str>> {
        match store[self.func.0].options.string_encoding {
            StringEncoding::Utf8 => self.decode_utf8(store),
            StringEncoding::Utf16 => self.decode_utf16(store),
            StringEncoding::CompactUtf16 => unimplemented!(),
        }
    }

    fn decode_utf8<'a>(&self, store: &'a StoreOpaque) -> Result<Cow<'a, str>> {
        let memory = self.func.memory(store);
        // Note that bounds-checking already happen in construction of `WasmStr`
        // so this is never expected to panic. This could theoretically be
        // unchecked indexing if we're feeling wild enough.
        Ok(str::from_utf8(&memory[self.ptr..][..self.len])?.into())
    }

    fn decode_utf16<'a>(&self, store: &'a StoreOpaque) -> Result<Cow<'a, str>> {
        let memory = self.func.memory(store);
        // See notes in `decode_utf8` for why this is panicking indexing.
        let memory = &memory[self.ptr..][..self.len * 2];
        Ok(std::char::decode_utf16(
            memory
                .chunks(2)
                .map(|chunk| u16::from_le_bytes(chunk.try_into().unwrap())),
        )
        .collect::<Result<String, _>>()?
        .into())
    }
}

// Note that this is similar to `ComponentValue for str` except it can only be
// used for lifting, not lowering.
unsafe impl ComponentValue for WasmStr {
    type Lower = [ValRaw; 2];

    fn size() -> usize {
        8
    }

    fn align() -> u32 {
        4
    }

    fn typecheck(ty: &InterfaceType, _types: &ComponentTypes, op: Op) -> Result<()> {
        match op {
            Op::Lift => {}
            Op::Lower => {
                bail!("wasm strings cannot be lowered back to wasm, use `&str` instead")
            }
        }
        match ty {
            InterfaceType::String => Ok(()),
            other => bail!("expected `string` found `{}`", desc(other)),
        }
    }

    fn lower<T>(
        &self,
        _store: &mut StoreContextMut<T>,
        _func: &Func,
        _dst: &mut MaybeUninit<[ValRaw; 2]>,
    ) -> Result<()> {
        unreachable!()
    }

    fn store<T>(&self, _mem: &mut MemoryMut<'_, T>, _offset: usize) -> Result<()> {
        unreachable!()
    }

    fn lift(store: &StoreOpaque, func: &Func, src: &Self::Lower) -> Result<Self> {
        // FIXME: needs memory64 treatment
        let ptr = src[0].get_u32();
        let len = src[1].get_u32();
        let (ptr, len) = (usize::try_from(ptr)?, usize::try_from(len)?);
        WasmStr::new(ptr, len, &Memory::new(store, func))
    }

    fn load(memory: &Memory<'_>, bytes: &[u8]) -> Result<Self> {
        // FIXME: needs memory64 treatment
        let ptr = u32::from_le_bytes(bytes[..4].try_into().unwrap());
        let len = u32::from_le_bytes(bytes[4..].try_into().unwrap());
        let (ptr, len) = (usize::try_from(ptr)?, usize::try_from(len)?);
        WasmStr::new(ptr, len, memory)
    }
}

unsafe impl<T> ComponentValue for [T]
where
    T: ComponentValue,
{
    type Lower = [ValRaw; 2];

    fn typecheck(ty: &InterfaceType, types: &ComponentTypes, op: Op) -> Result<()> {
        match op {
            Op::Lower => {}
            Op::Lift => {
                bail!("slices in Rust cannot be lifted from wasm, use `WasmList<T>` instead")
            }
        }
        match ty {
            InterfaceType::List(t) => T::typecheck(&types[*t], types, op),
            other => bail!("expected `list` found `{}`", desc(other)),
        }
    }

    fn lower<U>(
        &self,
        store: &mut StoreContextMut<U>,
        func: &Func,
        dst: &mut MaybeUninit<[ValRaw; 2]>,
    ) -> Result<()> {
        let (ptr, len) = lower_list(&mut MemoryMut::new(store.as_context_mut(), func), self)?;
        // See "WRITEPTR64" above for why this is always storing a 64-bit
        // integer.
        map_maybe_uninit!(dst[0]).write(ValRaw::i64(ptr as i64));
        map_maybe_uninit!(dst[1]).write(ValRaw::i64(len as i64));
        Ok(())
    }

    #[inline]
    fn size() -> usize {
        8
    }

    #[inline]
    fn align() -> u32 {
        4
    }

    fn store<U>(&self, mem: &mut MemoryMut<'_, U>, offset: usize) -> Result<()> {
        let (ptr, len) = lower_list(mem, self)?;
        *mem.get(offset + 0) = (ptr as i32).to_le_bytes();
        *mem.get(offset + 4) = (len as i32).to_le_bytes();
        Ok(())
    }
}

// FIXME: this is not a memcpy for `T` where `T` is something like `u8`.
//
// Some attempts to fix this have proved not fruitful. In isolation an attempt
// was made where:
//
// * `MemoryMut` stored a `*mut [u8]` as its "last view" of memory to avoid
//   reloading the base pointer constantly. This view is reset on `realloc`.
// * The bounds-checks in `MemoryMut::get` were removed (replaced with unsafe
//   indexing)
//
// Even then though this didn't correctly vectorized for `Vec<u8>`. It's not
// entirely clear why but it appeared that it's related to reloading the base
// pointer fo memory (I guess from `MemoryMut` itself?). Overall I'm not really
// clear on what's happening there, but this is surely going to be a performance
// bottleneck in the future.
fn lower_list<T, U>(mem: &mut MemoryMut<'_, U>, list: &[T]) -> Result<(usize, usize)>
where
    T: ComponentValue,
{
    let elem_size = T::size();
    let size = list
        .len()
        .checked_mul(elem_size)
        .ok_or_else(|| anyhow::anyhow!("size overflow copying a list"))?;
    let ptr = mem.realloc(0, 0, T::align(), size)?;
    let mut cur = ptr;
    for item in list {
        item.store(mem, cur)?;
        cur += elem_size;
    }
    Ok((ptr, list.len()))
}

/// Representation of a list of values that are owned by a WebAssembly instance.
///
/// This type is used whenever a `(list T)` is returned from a [`TypedFunc`],
/// for example. This type represents a list of values that are stored in linear
/// memory which are waiting to be read.
///
/// Note that this type represents only a valid range of bytes for the list
/// itself, it does not represent validity of the elements themselves and that's
/// performed when they're iterated.
pub struct WasmList<T> {
    ptr: usize,
    len: usize,
    func: Func,
    _marker: marker::PhantomData<T>,
}

impl<T: ComponentValue> WasmList<T> {
    fn new(ptr: usize, len: usize, memory: &Memory<'_>) -> Result<WasmList<T>> {
        match len
            .checked_mul(T::size())
            .and_then(|len| ptr.checked_add(len))
        {
            Some(n) if n <= memory.as_slice().len() => {}
            _ => bail!("list pointer/length out of bounds of memory"),
        }
        Ok(WasmList {
            ptr,
            len,
            func: *memory.func,
            _marker: marker::PhantomData,
        })
    }

    /// Returns the item length of this vector
    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Gets the `n`th element of this list.
    ///
    /// Returns `None` if `index` is out of bounds. Returns `Some(Err(..))` if
    /// the value couldn't be decoded (it was invalid). Returns `Some(Ok(..))`
    /// if the value is valid.
    //
    // TODO: given that interface values are intended to be consumed in one go
    // should we even expose a random access iteration API? In theory all
    // consumers should be validating through the iterator.
    pub fn get(&self, store: impl AsContext, index: usize) -> Option<Result<T>> {
        self._get(store.as_context().0, index)
    }

    fn _get(&self, store: &StoreOpaque, index: usize) -> Option<Result<T>> {
        if index >= self.len {
            return None;
        }
        let memory = Memory::new(store, &self.func);
        // Note that this is using panicking indexing and this is expected to
        // never fail. The bounds-checking here happened during the construction
        // of the `WasmList` itself which means these should always be in-bounds
        // (and wasm memory can only grow). This could theoretically be
        // unchecked indexing if we're confident enough and it's actually a perf
        // issue one day.
        let bytes = &memory.as_slice()[self.ptr + index * T::size()..][..T::size()];
        Some(T::load(&memory, bytes))
    }

    /// Returns an iterator over the elements of this list.
    ///
    /// Each item of the list may fail to decode and is represented through the
    /// `Result` value of the iterator.
    pub fn iter<'a, U: 'a>(
        &'a self,
        store: impl Into<StoreContext<'a, U>>,
    ) -> impl ExactSizeIterator<Item = Result<T>> + 'a {
        let store = store.into().0;
        (0..self.len).map(move |i| self._get(store, i).unwrap())
    }
}

impl WasmList<u8> {
    /// Get access to the raw underlying memory for this byte slice.
    ///
    /// Note that this is specifically only implemented for a `(list u8)` type
    /// since it's known to be valid in terms of alignment and representation
    /// validity.
    pub fn as_slice<'a, T: 'a>(&self, store: impl Into<StoreContext<'a, T>>) -> &'a [u8] {
        // See comments in `WasmList::get` for the panicking indexing
        &self.func.memory(store.into().0)[self.ptr..][..self.len]
    }
}

// Note that this is similar to `ComponentValue for str` except it can only be
// used for lifting, not lowering.
unsafe impl<T: ComponentValue> ComponentValue for WasmList<T> {
    type Lower = [ValRaw; 2];

    fn size() -> usize {
        8
    }

    fn align() -> u32 {
        4
    }

    fn typecheck(ty: &InterfaceType, types: &ComponentTypes, op: Op) -> Result<()> {
        match op {
            Op::Lift => {}
            Op::Lower => {
                bail!("wasm lists cannot be lowered back to wasm, use `&[T]` instead")
            }
        }
        match ty {
            InterfaceType::List(t) => T::typecheck(&types[*t], types, op),
            other => bail!("expected `list` found `{}`", desc(other)),
        }
    }

    fn lower<U>(
        &self,
        _store: &mut StoreContextMut<U>,
        _func: &Func,
        _dst: &mut MaybeUninit<[ValRaw; 2]>,
    ) -> Result<()> {
        unreachable!()
    }

    fn store<U>(&self, _mem: &mut MemoryMut<'_, U>, _offset: usize) -> Result<()> {
        unreachable!()
    }

    fn lift(store: &StoreOpaque, func: &Func, src: &Self::Lower) -> Result<Self> {
        // FIXME: needs memory64 treatment
        let ptr = src[0].get_u32();
        let len = src[1].get_u32();
        let (ptr, len) = (usize::try_from(ptr)?, usize::try_from(len)?);
        WasmList::new(ptr, len, &Memory::new(store, func))
    }

    fn load(memory: &Memory<'_>, bytes: &[u8]) -> Result<Self> {
        // FIXME: needs memory64 treatment
        let ptr = u32::from_le_bytes(bytes[..4].try_into().unwrap());
        let len = u32::from_le_bytes(bytes[4..].try_into().unwrap());
        let (ptr, len) = (usize::try_from(ptr)?, usize::try_from(len)?);
        WasmList::new(ptr, len, memory)
    }
}

/// Round `a` up to the next multiple of `align`, assuming that `align` is a power of 2.
#[inline]
const fn align_to(a: usize, align: u32) -> usize {
    debug_assert!(align.is_power_of_two());
    let align = align as usize;
    (a + (align - 1)) & !(align - 1)
}

/// For a field of type T starting after `offset` bytes, updates the offset to reflect the correct
/// alignment and size of T. Returns the correctly aligned offset for the start of the field.
#[inline]
pub fn next_field<T: ComponentValue>(offset: &mut usize) -> usize {
    *offset = align_to(*offset, T::align());
    let result = *offset;
    *offset += T::size();
    result
}

/// Verify that the given wasm type is a tuple with the expected fields in the right order.
#[inline]
fn typecheck_tuple(
    ty: &InterfaceType,
    types: &ComponentTypes,
    op: Op,
    expected: &[fn(&InterfaceType, &ComponentTypes, Op) -> Result<()>],
) -> Result<()> {
    match ty {
        InterfaceType::Tuple(t) => {
            let tuple = &types[*t];
            if tuple.types.len() != expected.len() {
                bail!(
                    "expected {}-tuple, found {}-tuple",
                    expected.len(),
                    tuple.types.len()
                );
            }
            for (ty, check) in tuple.types.iter().zip(expected) {
                check(ty, types, op)?;
            }
            Ok(())
        }
        other => bail!("expected `tuple` found `{}`", desc(other)),
    }
}

/// Verify that the given wasm type is a record with the expected fields in the right order, and
/// having the right names.
#[inline]
pub fn typecheck_record(
    ty: &InterfaceType,
    types: &ComponentTypes,
    op: Op,
    expected: &[(&str, fn(&InterfaceType, &ComponentTypes, Op) -> Result<()>)],
) -> Result<()> {
    match ty {
        InterfaceType::Record(r) => {
            let record = &types[*r];
            if record.fields.len() != expected.len() {
                bail!(
                    "expected record of {} fields, found {} fields",
                    expected.len(),
                    record.fields.len()
                );
            }
            for (field, &(name, check)) in record.fields.iter().zip(expected) {
                check(&field.ty, types, op)?;
                if field.name != name {
                    bail!("expected record field named {}, found {}", name, field.name);
                }
            }
            Ok(())
        }
        other => bail!("expected `record` found `{}`", desc(other)),
    }
}

/// Verify that the given wasm type is an enum with the expected variants in the right order, and
/// having the right names.
#[inline]
pub fn typecheck_enum(ty: &InterfaceType, types: &ComponentTypes, expected: &[&str]) -> Result<()> {
    match ty {
        InterfaceType::Enum(e) => {
            let names = &*types[*e].names;
            if names.len() != expected.len() {
                bail!(
                    "expected enum of {} variants, found {} variants",
                    expected.len(),
                    names.len()
                );
            }
            for (variant, &name) in names.iter().zip(expected) {
                if variant != name {
                    bail!("expected enum variant named {}, found {}", name, variant);
                }
            }
            Ok(())
        }
        other => bail!("expected `enum` found `{}`", desc(other)),
    }
}

unsafe impl<T> ComponentValue for Option<T>
where
    T: ComponentValue,
{
    type Lower = TupleLower2<<u32 as ComponentValue>::Lower, T::Lower>;

    fn typecheck(ty: &InterfaceType, types: &ComponentTypes, op: Op) -> Result<()> {
        match ty {
            InterfaceType::Option(t) => T::typecheck(&types[*t], types, op),
            other => bail!("expected `option` found `{}`", desc(other)),
        }
    }

    fn lower<U>(
        &self,
        store: &mut StoreContextMut<U>,
        func: &Func,
        dst: &mut MaybeUninit<Self::Lower>,
    ) -> Result<()> {
        match self {
            None => {
                map_maybe_uninit!(dst.A1).write(ValRaw::i32(0));
                // Note that this is unsafe as we're writing an arbitrary
                // bit-pattern to an arbitrary type, but part of the unsafe
                // contract of the `ComponentValue` trait is that we can assign
                // any bit-pattern. By writing all zeros here we're ensuring
                // that the core wasm arguments this translates to will all be
                // zeros (as the canonical ABI requires).
                unsafe {
                    map_maybe_uninit!(dst.A2).as_mut_ptr().write_bytes(0u8, 1);
                }
            }
            Some(val) => {
                map_maybe_uninit!(dst.A1).write(ValRaw::i32(1));
                val.lower(store, func, map_maybe_uninit!(dst.A2))?;
            }
        }
        Ok(())
    }

    #[inline]
    fn size() -> usize {
        align_to(1, T::align()) + T::size()
    }

    #[inline]
    fn align() -> u32 {
        T::align()
    }

    fn store<U>(&self, mem: &mut MemoryMut<'_, U>, offset: usize) -> Result<()> {
        match self {
            None => {
                mem.get::<1>(offset)[0] = 0;
            }
            Some(val) => {
                mem.get::<1>(offset)[0] = 1;
                val.store(mem, offset + align_to(1, T::align()))?;
            }
        }
        Ok(())
    }

    fn lift(store: &StoreOpaque, func: &Func, src: &Self::Lower) -> Result<Self> {
        Ok(match src.A1.get_i32() {
            0 => None,
            1 => Some(T::lift(store, func, &src.A2)?),
            _ => bail!("invalid option discriminant"),
        })
    }

    fn load(memory: &Memory<'_>, bytes: &[u8]) -> Result<Self> {
        let discrim = bytes[0];
        let payload = &bytes[align_to(1, T::align())..];
        match discrim {
            0 => Ok(None),
            1 => Ok(Some(T::load(memory, payload)?)),
            _ => bail!("invalid option discriminant"),
        }
    }
}

#[derive(Clone, Copy)]
#[repr(C)]
pub struct ResultLower<T: Copy, E: Copy> {
    tag: ValRaw,
    payload: ResultLowerPayload<T, E>,
}

#[derive(Clone, Copy)]
#[repr(C)]
union ResultLowerPayload<T: Copy, E: Copy> {
    ok: T,
    err: E,
}

unsafe impl<T, E> ComponentValue for Result<T, E>
where
    T: ComponentValue,
    E: ComponentValue,
{
    type Lower = ResultLower<T::Lower, E::Lower>;

    fn typecheck(ty: &InterfaceType, types: &ComponentTypes, op: Op) -> Result<()> {
        match ty {
            InterfaceType::Expected(r) => {
                let expected = &types[*r];
                T::typecheck(&expected.ok, types, op)?;
                E::typecheck(&expected.err, types, op)?;
                Ok(())
            }
            other => bail!("expected `expected` found `{}`", desc(other)),
        }
    }

    fn lower<U>(
        &self,
        store: &mut StoreContextMut<U>,
        func: &Func,
        dst: &mut MaybeUninit<Self::Lower>,
    ) -> Result<()> {
        // Start out by zeroing out the payload. This will ensure that if either
        // arm doesn't initialize some values then everything is still
        // deterministically set.
        //
        // Additionally, this initialization of zero means that the specific
        // types written by each `lower` call below on each arm still has the
        // correct value even when "joined" with the other arm.
        //
        // Finally note that this is required by the canonical ABI to some
        // degree where if the `Ok` arm initializes fewer values than the `Err`
        // arm then all the remaining values must be initialized to zero, and
        // that's what this does.
        unsafe {
            map_maybe_uninit!(dst.payload)
                .as_mut_ptr()
                .write_bytes(0u8, 1);
        }

        match self {
            Ok(e) => {
                map_maybe_uninit!(dst.tag).write(ValRaw::i32(0));
                e.lower(store, func, map_maybe_uninit!(dst.payload.ok))?;
            }
            Err(e) => {
                map_maybe_uninit!(dst.tag).write(ValRaw::i32(1));
                e.lower(store, func, map_maybe_uninit!(dst.payload.err))?;
            }
        }
        Ok(())
    }

    #[inline]
    fn size() -> usize {
        align_to(1, Self::align()) + T::size().max(E::size())
    }

    #[inline]
    fn align() -> u32 {
        T::align().max(E::align())
    }

    fn store<U>(&self, mem: &mut MemoryMut<'_, U>, offset: usize) -> Result<()> {
        match self {
            Ok(e) => {
                mem.get::<1>(offset)[0] = 0;
                e.store(mem, offset + align_to(1, Self::align()))?;
            }
            Err(e) => {
                mem.get::<1>(offset)[0] = 1;
                e.store(mem, offset + align_to(1, Self::align()))?;
            }
        }
        Ok(())
    }

    fn lift(store: &StoreOpaque, func: &Func, src: &Self::Lower) -> Result<Self> {
        // TODO: need to make a case that upper-bits are not validated to be
        // zero.
        //
        // * `Result<u32, u64>` flattens as `i32 i64`
        // * This impl wants to say `0 u64::MAX` is a valid flattening of
        //   `Ok(u32::MAX)`.
        // * Otherwise validation needs to be performed that, where necessary,
        //   upper bits are zero.
        // * Points in favor:
        //   * `Result<u32, (u32, u32)>` flattens as `i32 i32 i32` and
        //     `Ok(0)` doesn't  validate that the third `i32` is any
        //     particular value.
        //   * Padding bytes are ignored in the in-memory representation.
        //
        // Otherwise I don't know how to implement the validation for now. This
        // would need to, at compile time via the Rust trait system, figure out
        // the flatten lowering for `Result<T, E>` for `T` and `E` and then ask
        // `T`'s lowered type to validate that it's valid within the context of
        // the the overall lowered type. This... is trait trickery that is
        // beyond me but seems like it should be possible. Would be nice if we
        // didn't have to do that though.

        Ok(match src.tag.get_i32() {
            0 => Ok(unsafe { T::lift(store, func, &src.payload.ok)? }),
            1 => Err(unsafe { E::lift(store, func, &src.payload.err)? }),
            _ => bail!("invalid expected discriminant"),
        })
    }

    fn load(memory: &Memory<'_>, bytes: &[u8]) -> Result<Self> {
        let align = <Result<T, E> as ComponentValue>::align();
        let discrim = bytes[0];
        let payload = &bytes[align_to(1, align)..];
        match discrim {
            0 => Ok(Ok(T::load(memory, &payload[..T::size()])?)),
            1 => Ok(Err(E::load(memory, &payload[..E::size()])?)),
            _ => bail!("invalid expected discriminant"),
        }
    }
}

macro_rules! impl_component_ty_for_tuples {
    // the unit tuple goes to the `Unit` type, not the `Tuple` type
    //
    // FIXME(WebAssembly/component-model#21) there's some active discussion on
    // the relationship between the 0-tuple and the unit type in the component
    // model.
    (0) => {};

    ($n:tt $($t:ident)*) => {paste::paste!{
        #[allow(non_snake_case)]
        #[doc(hidden)]
        #[derive(Clone, Copy)]
        #[repr(C)]
        pub struct [<TupleLower$n>]<$($t),*> {
            $($t: $t,)*
        }

        #[allow(non_snake_case)]
        unsafe impl<$($t,)*> ComponentValue for ($($t,)*)
        where $($t: ComponentValue),*
        {
            type Lower = [<TupleLower$n>]<$($t::Lower),*>;

            fn typecheck(
                ty: &InterfaceType,
                types: &ComponentTypes,
                op: Op,
            ) -> Result<()> {
                typecheck_tuple(ty, types, op, &[$($t::typecheck),*])
            }

            fn lower<U>(
                &self,
                store: &mut StoreContextMut<U>,
                func: &Func,
                dst: &mut MaybeUninit<Self::Lower>,
            ) -> Result<()> {
                let ($($t,)*) = self;
                $($t.lower(store, func, map_maybe_uninit!(dst.$t))?;)*
                Ok(())
            }

            #[inline]
            fn size() -> usize {
                let mut size = 0;
                $(next_field::<$t>(&mut size);)*
                size
            }

            #[inline]
            fn align() -> u32 {
                let mut align = 1;
                $(align = align.max($t::align());)*
                align
            }

            fn store<U>(&self, memory: &mut MemoryMut<'_, U>, mut offset: usize) -> Result<()> {
                let ($($t,)*) = self;
                // TODO: this requires that `offset` is aligned which we may not
                // want to do
                $($t.store(memory, next_field::<$t>(&mut offset))?;)*
                Ok(())
            }

            fn lift(store: &StoreOpaque, func: &Func, src: &Self::Lower) -> Result<Self> {
                Ok(($($t::lift(store, func, &src.$t)?,)*))
            }

            fn load(memory: &Memory<'_>, bytes: &[u8]) -> Result<Self> {
                let mut offset = 0;
                $(let $t = $t::load(memory, &bytes[next_field::<$t>(&mut offset)..][..$t::size()])?;)*
                Ok(($($t,)*))
            }
        }

    }};
}

for_each_function_signature!(impl_component_ty_for_tuples);

struct TestRecord {
    a: i32,
    b: u32,
}

#[derive(Clone, Copy)]
struct TestRecordLower {
    a: <i32 as ComponentValue>::Lower,
    b: <u32 as ComponentValue>::Lower,
}

unsafe impl ComponentValue for TestRecord {
    type Lower = TestRecordLower;

    fn typecheck(ty: &InterfaceType, types: &ComponentTypes, op: Op) -> Result<()> {
        typecheck_record(
            ty,
            types,
            op,
            &[
                ("a", <i32 as ComponentValue>::typecheck),
                ("b", <u32 as ComponentValue>::typecheck),
            ],
        )
    }

    #[inline]
    fn size() -> usize {
        let mut size = 0;
        next_field::<i32>(&mut size);
        next_field::<u32>(&mut size);
        size
    }

    #[inline]
    fn align() -> u32 {
        let mut align = 1;
        align = align.max(i32::align());
        align = align.max(u32::align());
        align
    }

    fn lower<T>(
        &self,
        store: &mut StoreContextMut<T>,
        func: &Func,
        dst: &mut MaybeUninit<Self::Lower>,
    ) -> Result<()> {
        self.a.lower(store, func, map_maybe_uninit!(dst.a))?;
        self.b.lower(store, func, map_maybe_uninit!(dst.b))?;
        Ok(())
    }

    fn store<T>(&self, memory: &mut MemoryMut<'_, T>, mut offset: usize) -> Result<()> {
        // TODO: this requires that `offset` is aligned which we may not
        // want to do
        self.a.store(memory, next_field::<i32>(&mut offset))?;
        self.b.store(memory, next_field::<u32>(&mut offset))?;
        Ok(())
    }

    fn lift(store: &StoreOpaque, func: &Func, src: &Self::Lower) -> Result<Self> {
        Ok(Self {
            a: <i32 as ComponentValue>::lift(store, func, &src.a)?,
            b: <u32 as ComponentValue>::lift(store, func, &src.b)?,
        })
    }

    fn load(memory: &Memory<'_>, bytes: &[u8]) -> Result<Self> {
        let mut offset = 0;
        let a = i32::load(
            memory,
            &bytes[next_field::<i32>(&mut offset)..][..i32::size()],
        )?;
        let b = u32::load(
            memory,
            &bytes[next_field::<u32>(&mut offset)..][..u32::size()],
        )?;
        Ok(Self { a, b })
    }
}

/// Returns a short description of the given type.
pub fn desc(ty: &InterfaceType) -> &'static str {
    match ty {
        InterfaceType::U8 => "u8",
        InterfaceType::S8 => "s8",
        InterfaceType::U16 => "u16",
        InterfaceType::S16 => "s16",
        InterfaceType::U32 => "u32",
        InterfaceType::S32 => "s32",
        InterfaceType::U64 => "u64",
        InterfaceType::S64 => "s64",
        InterfaceType::Float32 => "f32",
        InterfaceType::Float64 => "f64",
        InterfaceType::Unit => "unit",
        InterfaceType::Bool => "bool",
        InterfaceType::Char => "char",
        InterfaceType::String => "string",
        InterfaceType::List(_) => "list",
        InterfaceType::Tuple(_) => "tuple",
        InterfaceType::Option(_) => "option",
        InterfaceType::Expected(_) => "expected",

        InterfaceType::Record(_) => "record",
        InterfaceType::Variant(_) => "variant",
        InterfaceType::Flags(_) => "flags",
        InterfaceType::Enum(_) => "enum",
        InterfaceType::Union(_) => "union",
    }
}

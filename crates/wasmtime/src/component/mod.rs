//! In-progress implementation of the WebAssembly component model
//!
//! This module is a work-in-progress and currently represents an incomplete and
//! probably buggy implementation of the component model.

mod component;
mod func;
mod instance;
mod store;
pub use self::component::Component;
pub use self::func::{ComponentParams, ComponentValue, Func, Op, TypedFunc, WasmList, WasmStr};
pub use self::instance::Instance;
pub use wasmtime_component_derive::*;

// These items are expected to be used by an eventual
// `#[derive(ComponentValue)]`, they are not part of Wasmtime's API stability
// guarantees
#[doc(hidden)]
pub mod private {
    pub use super::func::{next_field, typecheck_enum, typecheck_record, Memory, MemoryMut};
    pub use crate::store::StoreOpaque;
    pub use anyhow;
    pub use wasmtime_environ::component::{ComponentTypes, InterfaceType};
}

pub(crate) use self::store::ComponentStoreData;

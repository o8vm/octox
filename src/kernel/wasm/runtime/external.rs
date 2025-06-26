use core::fmt;

use alloc::vec::Vec;

use crate::wasm::ast::ExternKind;
use crate::wasm::runtime::address::{
    FuncAddr, TableAddr, MemAddr, GlobalAddr,
};

/// External value
/// 
/// An external value is the runtime representation of an entity that can be imported or exported.
/// It is an address denoting either a function instance, table instance, memory instance,
/// or global instances in the shared store.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExternalValue {
    /// Function address
    Func(FuncAddr),
    /// Table address
    Table(TableAddr),
    /// Memory address
    Memory(MemAddr),
    /// Global address
    Global(GlobalAddr),
}

impl ExternalValue {
    /// Creates a new function external value
    pub const fn func(addr: FuncAddr) -> Self {
        Self::Func(addr)
    }

    /// Creates a new table external value
    pub const fn table(addr: TableAddr) -> Self {
        Self::Table(addr)
    }

    /// Creates a new memory external value
    pub const fn memory(addr: MemAddr) -> Self {
        Self::Memory(addr)
    }

    /// Creates a new global external value
    pub const fn global(addr: GlobalAddr) -> Self {
        Self::Global(addr)
    }

    /// Returns the kind of the external value
    pub const fn kind(&self) -> ExternKind {
        match self {
            Self::Func(_) => ExternKind::Func,
            Self::Table(_) => ExternKind::Table,
            Self::Memory(_) => ExternKind::Memory,
            Self::Global(_) => ExternKind::Global,
        }
    }

    /// Returns true if this is a function external value
    pub const fn is_func(&self) -> bool {
        matches!(self, Self::Func(_))
    }

    /// Returns true if this is a table external value
    pub const fn is_table(&self) -> bool {
        matches!(self, Self::Table(_))
    }

    /// Returns true if this is a memory external value
    pub const fn is_memory(&self) -> bool {
        matches!(self, Self::Memory(_))
    }

    /// Returns true if this is a global external value
    pub const fn is_global(&self) -> bool {
        matches!(self, Self::Global(_))
    }

    /// Returns the function address if this is a function external value
    pub const fn as_func(&self) -> Option<&FuncAddr> {
        match self {
            Self::Func(addr) => Some(addr),
            _ => None,
        }
    }

    /// Returns the table address if this is a table external value
    pub const fn as_table(&self) -> Option<&TableAddr> {
        match self {
            Self::Table(addr) => Some(addr),
            _ => None,
        }
    }

    /// Returns the memory address if this is a memory external value
    pub const fn as_memory(&self) -> Option<&MemAddr> {
        match self {
            Self::Memory(addr) => Some(addr),
            _ => None,
        }
    }

    /// Returns the global address if this is a global external value
    pub const fn as_global(&self) -> Option<&GlobalAddr> {
        match self {
            Self::Global(addr) => Some(addr),
            _ => None,
        }
    }
}

impl fmt::Display for ExternalValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Func(addr) => write!(f, "func {}", addr),
            Self::Table(addr) => write!(f, "table {}", addr),
            Self::Memory(addr) => write!(f, "memory {}", addr),
            Self::Global(addr) => write!(f, "global {}", addr),
        }
    }
}

/// Helper functions for filtering external values
pub mod external_values {
    use super::*;

    /// Returns all function addresses from a sequence of external values
    pub fn funcs(values: &[ExternalValue]) -> Vec<&FuncAddr> {
        values.iter()
            .filter_map(ExternalValue::as_func)
            .collect()
    }

    /// Returns all table addresses from a sequence of external values
    pub fn tables(values: &[ExternalValue]) -> Vec<&TableAddr> {
        values.iter()
            .filter_map(ExternalValue::as_table)
            .collect()
    }

    /// Returns all memory addresses from a sequence of external values
    pub fn mems(values: &[ExternalValue]) -> Vec<&MemAddr> {
        values.iter()
            .filter_map(ExternalValue::as_memory)
            .collect()
    }

    /// Returns all global addresses from a sequence of external values
    pub fn globals(values: &[ExternalValue]) -> Vec<&GlobalAddr> {
        values.iter()
            .filter_map(ExternalValue::as_global)
            .collect()
    }
}
 
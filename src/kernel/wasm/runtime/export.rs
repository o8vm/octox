use alloc::string::String;
use core::fmt;

use crate::wasm::ast::ExternKind;
use crate::wasm::runtime::value::Value;

/// External value that can be exported
#[derive(Debug, Clone, PartialEq)]
pub enum ExportValue {
    /// Function export
    Func(u32),
    /// Table export
    Table(u32),
    /// Memory export
    Memory(u32),
    /// Global export
    Global(u32),
}

impl ExportValue {
    /// Creates a new function export value
    pub const fn func(index: u32) -> Self {
        Self::Func(index)
    }

    /// Creates a new table export value
    pub const fn table(index: u32) -> Self {
        Self::Table(index)
    }

    /// Creates a new memory export value
    pub const fn memory(index: u32) -> Self {
        Self::Memory(index)
    }

    /// Creates a new global export value
    pub const fn global(index: u32) -> Self {
        Self::Global(index)
    }

    /// Returns the kind of the export value
    pub const fn kind(&self) -> ExternKind {
        match self {
            Self::Func(_) => ExternKind::Func,
            Self::Table(_) => ExternKind::Table,
            Self::Memory(_) => ExternKind::Memory,
            Self::Global(_) => ExternKind::Global,
        }
    }

    /// Returns the index of the exported item
    pub const fn index(&self) -> u32 {
        match self {
            Self::Func(index) => *index,
            Self::Table(index) => *index,
            Self::Memory(index) => *index,
            Self::Global(index) => *index,
        }
    }

    /// Returns true if this is a function export
    pub const fn is_func(&self) -> bool {
        matches!(self, Self::Func(_))
    }

    /// Returns true if this is a table export
    pub const fn is_table(&self) -> bool {
        matches!(self, Self::Table(_))
    }

    /// Returns true if this is a memory export
    pub const fn is_memory(&self) -> bool {
        matches!(self, Self::Memory(_))
    }

    /// Returns true if this is a global export
    pub const fn is_global(&self) -> bool {
        matches!(self, Self::Global(_))
    }
}

impl fmt::Display for ExportValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Func(index) => write!(f, "func[{}]", index),
            Self::Table(index) => write!(f, "table[{}]", index),
            Self::Memory(index) => write!(f, "memory[{}]", index),
            Self::Global(index) => write!(f, "global[{}]", index),
        }
    }
}

/// Export instance
/// 
/// An export instance is the runtime representation of an export.
/// It defines the export's name and the associated external value.
#[derive(Debug, Clone, PartialEq)]
pub struct ExportInstance {
    /// The name of the export
    name: String,
    /// The external value being exported
    value: ExportValue,
}

impl ExportInstance {
    /// Creates a new export instance
    pub fn new(name: String, value: ExportValue) -> Self {
        Self { name, value }
    }

    /// Returns the name of the export
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Returns the external value being exported
    pub fn value(&self) -> &ExportValue {
        &self.value
    }

    /// Returns the kind of the export
    pub fn kind(&self) -> ExternKind {
        self.value.kind()
    }

    /// Returns the index of the exported item
    pub fn index(&self) -> u32 {
        self.value.index()
    }

    /// Returns true if this is a function export
    pub fn is_func(&self) -> bool {
        self.value.is_func()
    }

    /// Returns true if this is a table export
    pub fn is_table(&self) -> bool {
        self.value.is_table()
    }

    /// Returns true if this is a memory export
    pub fn is_memory(&self) -> bool {
        self.value.is_memory()
    }

    /// Returns true if this is a global export
    pub fn is_global(&self) -> bool {
        self.value.is_global()
    }
}

impl fmt::Display for ExportInstance {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "export {} = {}", self.name, self.value)
    }
}

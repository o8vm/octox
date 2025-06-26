//! WebAssembly Abstract Syntax Tree (AST) definitions
//! 
//! This module defines the data structures that represent a WebAssembly module
//! in memory. These structures follow the WebAssembly specification's structure
//! definitions.

use core::fmt;
use alloc::format;
use alloc::vec::Vec;
use alloc::string::String;
use crate::alloc::string::ToString;
use crate::parser_debug_log;
use crate::wasm::parser::ParserConfig;
use crate::wasm::runtime::{
    FuncAddr, ExternAddr, FrameState,
};

/// WebAssembly page size in bytes (64 KiB)
pub const WASM_PAGE_SIZE: u32 = 65536;

/// Represents a limit on the size of a memory or table
/// 
/// A limit consists of a minimum size and an optional maximum size.
/// If no maximum is given, the storage can grow to any size.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Limits {
    /// The minimum size
    pub min: u32,
    /// The maximum size, if any
    pub max: Option<u32>,
}

impl Limits {
    /// Creates a new limit with a minimum size and no maximum
    pub const fn min(min: u32) -> Self {
        Self { min, max: None }
    }

    /// Creates a new limit with both minimum and maximum sizes
    pub const fn min_max(min: u32, max: u32) -> Self {
        Self { min, max: Some(max) }
    }

    /// Returns true if this limit has a maximum size
    pub const fn has_max(&self) -> bool {
        self.max.is_some()
    }

    /// Returns the maximum size, if any
    pub const fn max(&self) -> Option<u32> {
        self.max
    }

    /// Returns true if the given size is within the limits
    /// 
    /// Note: This method is not const because it uses non-const functions
    /// internally (Option::map_or).
    pub fn is_within(&self, size: u32) -> bool {
        size >= self.min && self.max.map_or(true, |max| size <= max)
    }

    /// Returns true if the limits are valid
    /// 
    /// Limits are valid if:
    /// - min <= max (when max is Some)
    /// - min < 2^32 (always true for u32)
    /// 
    /// # Specification
    /// 
    /// ⊢ limits ok
    /// (if limits = {min n, max m?}
    ///  ∧ n ≤ m (if m?)
    ///  ∧ n < 2^32)
    pub fn is_valid(&self) -> bool {
        // Check that min <= max when max is Some
        if let Some(max) = self.max {
            self.min <= max
        } else {
            // No maximum specified, so limits are always valid
            true
        }
    }
}

impl fmt::Display for Limits {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{min: {}, ", self.min)?;
        match self.max {
            Some(max) => write!(f, "max: {}}}", max),
            None => write!(f, "max: none}}"),
        }
    }
}

/// Represents a memory type in WebAssembly
/// 
/// A memory type consists of limits that constrain the minimum and optionally
/// the maximum size of a memory. The limits are given in units of page size
/// (64 KiB).
/// 
/// In the WebAssembly specification, this is written as `limits`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct MemoryType {
    /// The limits on the memory size in pages
    pub limits: Limits,
}

impl MemoryType {
    /// Creates a new memory type with the given limits
    pub const fn new(limits: Limits) -> Self {
        Self { limits }
    }

    /// Creates a new memory type with a minimum size in pages and no maximum
    pub const fn min(min_pages: u32) -> Self {
        Self::new(Limits::min(min_pages))
    }

    /// Creates a new memory type with both minimum and maximum sizes in pages
    pub const fn min_max(min_pages: u32, max_pages: u32) -> Self {
        Self::new(Limits::min_max(min_pages, max_pages))
    }

    /// Returns the minimum size of the memory in pages
    pub const fn min_pages(&self) -> u32 {
        self.limits.min
    }

    /// Returns the maximum size of the memory in pages, if any
    pub const fn max_pages(&self) -> Option<u32> {
        self.limits.max
    }

    /// Returns the minimum size of the memory in bytes
    pub const fn min_bytes(&self) -> u64 {
        self.min_pages() as u64 * WASM_PAGE_SIZE as u64
    }

    /// Returns the maximum size of the memory in bytes, if any
    /// 
    /// Note: This method is not const because it uses non-const functions
    /// internally (Option::map).
    pub fn max_bytes(&self) -> Option<u64> {
        self.max_pages().map(|pages| pages as u64 * WASM_PAGE_SIZE as u64)
    }

    /// Returns true if the given size in pages is within the memory limits
    pub fn is_within_pages(&self, pages: u32) -> bool {
        self.limits.is_within(pages)
    }

    /// Returns true if the given size in bytes is within the memory limits
    pub fn is_within_bytes(&self, bytes: u64) -> bool {
        let pages = bytes / WASM_PAGE_SIZE as u64;
        if pages > u32::MAX as u64 {
            return false;
        }
        self.is_within_pages(pages as u32)
    }
}

impl fmt::Display for MemoryType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "memory {}", self.limits)
    }
}

/// WebAssembly value types as defined in the specification
/// 
/// # Number Types
/// - `I32`: 32-bit integer
/// - `I64`: 64-bit integer
/// - `F32`: 32-bit floating-point (IEEE 754 single precision)
/// - `F64`: 64-bit floating-point (IEEE 754 double precision)
/// 
/// # Vector Types
/// - `V128`: 128-bit vector of packed integer or floating-point data (SIMD)
/// 
/// # Reference Types
/// - `FuncRef`: Reference to a function
/// - `ExternRef`: Reference to an external object
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ValType {
    /// 32-bit integer
    I32,
    /// 64-bit integer
    I64,
    /// 32-bit floating-point (IEEE 754 single precision)
    F32,
    /// 64-bit floating-point (IEEE 754 double precision)
    F64,
    /// 128-bit vector (SIMD)
    V128,
    /// Reference to a function
    FuncRef,
    /// Reference to an external object
    ExternRef,
}

impl ValType {
    /// Returns the bit width of the value type
    /// 
    /// # Examples
    /// ```
    /// use octox::kernel::wasm::ast::ValType;
    /// 
    /// assert_eq!(ValType::I32.bit_width(), 32);
    /// assert_eq!(ValType::F64.bit_width(), 64);
    /// assert_eq!(ValType::V128.bit_width(), 128);
    /// ```
    pub const fn bit_width(&self) -> u32 {
        match self {
            ValType::I32 | ValType::F32 => 32,
            ValType::I64 | ValType::F64 => 64,
            ValType::V128 => 128,
            // Reference types are opaque, so we don't define a bit width
            ValType::FuncRef | ValType::ExternRef => 0,
        }
    }

    /// Returns true if the value type is a number type
    pub const fn is_number_type(&self) -> bool {
        matches!(self, ValType::I32 | ValType::I64 | ValType::F32 | ValType::F64)
    }

    /// Returns true if the value type is an integer type
    pub const fn is_integer_type(&self) -> bool {
        matches!(self, ValType::I32 | ValType::I64)
    }

    /// Returns true if the value type is a floating-point type
    pub const fn is_float_type(&self) -> bool {
        matches!(self, ValType::F32 | ValType::F64)
    }

    /// Returns true if the value type is a vector type
    pub const fn is_vector_type(&self) -> bool {
        matches!(self, ValType::V128)
    }

    /// Returns true if the value type is a reference type
    pub const fn is_reference_type(&self) -> bool {
        matches!(self, ValType::FuncRef | ValType::ExternRef)
    }
}

impl fmt::Display for ValType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ValType::I32 => write!(f, "i32"),
            ValType::I64 => write!(f, "i64"),
            ValType::F32 => write!(f, "f32"),
            ValType::F64 => write!(f, "f64"),
            ValType::V128 => write!(f, "v128"),
            ValType::FuncRef => write!(f, "funcref"),
            ValType::ExternRef => write!(f, "externref"),
        }
    }
}

/// A result type is a sequence of value types, representing the types of values
/// returned by a function or block.
/// 
/// In the WebAssembly specification, this is written as [vec(valtype)].
pub type ResultType = Vec<ValType>;

/// Represents a function type (signature) in WebAssembly
/// 
/// A function type maps a vector of parameters to a vector of results.
/// In the WebAssembly specification, this is written as resulttype → resulttype.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FuncType {
    /// The types of the function's parameters (input result type)
    pub params: ResultType,
    /// The types of the function's results (output result type)
    pub results: ResultType,
}

impl FuncType {
    /// Creates a new function type with the given parameter and result types
    /// 
    /// # Arguments
    /// * `params` - The input result type (parameter types)
    /// * `results` - The output result type (result types)
    pub const fn new(params: ResultType, results: ResultType) -> Self {
        Self { params, results }
    }

    /// Returns true if this function type has no parameters
    pub fn is_nullary(&self) -> bool {
        self.params.is_empty()
    }

    /// Returns true if this function type has no results
    pub fn is_void(&self) -> bool {
        self.results.is_empty()
    }

    /// Returns the number of parameters
    pub fn param_count(&self) -> usize {
        self.params.len()
    }

    /// Returns the number of results
    pub fn result_count(&self) -> usize {
        self.results.len()
    }

    /// Returns true if this function type matches another function type
    /// 
    /// Two function types match if they have the same number of parameters and results,
    /// and each parameter and result type matches.
    pub fn matches(&self, other: &FuncType) -> bool {
        if self.param_count() != other.param_count() || self.result_count() != other.result_count() {
            return false;
        }
        self.params.iter().zip(other.params.iter()).all(|(a, b)| a == b)
            && self.results.iter().zip(other.results.iter()).all(|(a, b)| a == b)
    }

    /// Validates the function type according to the WebAssembly specification
    /// 
    /// # Returns
    /// * `true` if the function type is valid
    /// * `false` if the function type is invalid
    pub fn validate(&self) -> bool {
        // Currently, all function types are valid as long as they contain valid value types
        // This could be extended with additional validation rules if needed
        true
    }
}

impl fmt::Display for FuncType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Format as "resulttype → resulttype"
        write!(f, "{} → {}", 
            format_result_type(&self.params),
            format_result_type(&self.results))
    }
}

/// Helper function to format a result type
fn format_result_type(types: &[ValType]) -> String {
    if types.is_empty() {
        "[]".to_string()
    } else {
        let mut s = String::from("[");
        for (i, t) in types.iter().enumerate() {
            if i > 0 {
                s.push(' ');
            }
            s.push_str(&t.to_string());
        }
        s.push(']');
        s
    }
}

/// Represents a WebAssembly module
/// 
/// A module is the unit of deployment, loading, and compilation in WebAssembly.
/// It collects definitions for types, functions, tables, memories, and globals.
/// In addition, it can declare imports and exports and provide initialization
/// in the form of data and element segments, or a start function.
/// 
/// # Specification
/// WebAssembly programs are organized into modules, which are the unit of
/// deployment, loading, and compilation. A module collects definitions for
/// types, functions, tables, memories, and globals. In addition, it can
/// declare imports and exports and provide initialization in the form of
/// data and element segments, or a start function.
/// 
/// Each of the vectors – and thus the entire module – may be empty.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Module {
    /// The vector of function types defined in the module
    pub types: Vec<FuncType>,
    /// The vector of functions defined in the module
    pub funcs: Vec<Function>,
    /// The vector of tables defined in the module
    pub tables: Vec<TableType>,
    /// The vector of memories defined in the module
    pub mems: Vec<Memory>,
    /// The vector of globals defined in the module
    pub globals: Vec<Global>,
    /// The vector of element segments defined in the module
    pub elems: Vec<ElementSegment>,
    /// The vector of data segments defined in the module
    pub datas: Vec<DataSegment>,
    /// The optional start function of the module
    pub start: Option<StartFunction>,
    /// The vector of imports declared by the module
    pub imports: Vec<Import>,
    /// The vector of exports declared by the module
    pub exports: Vec<Export>,
}

impl Module {
    /// Creates a new empty module
    pub const fn new() -> Self {
        Self {
            types: Vec::new(),
            funcs: Vec::new(),
            tables: Vec::new(),
            mems: Vec::new(),
            globals: Vec::new(),
            elems: Vec::new(),
            datas: Vec::new(),
            start: None,
            imports: Vec::new(),
            exports: Vec::new(),
        }
    }

    /// Returns the number of function types defined in the module
    pub fn type_count(&self) -> usize {
        self.types.len()
    }

    /// Returns the number of functions defined in the module
    pub fn func_count(&self) -> usize {
        self.funcs.len()
    }

    /// Returns the number of tables defined in the module
    pub fn table_count(&self) -> usize {
        self.tables.len()
    }

    /// Returns the number of memories defined in the module
    pub fn memory_count(&self) -> usize {
        self.mems.len()
    }

    /// Returns the number of globals defined in the module
    pub fn global_count(&self) -> usize {
        self.globals.len()
    }

    /// Returns the number of element segments defined in the module
    pub fn element_count(&self) -> usize {
        self.elems.len()
    }

    /// Returns the number of data segments defined in the module
    pub fn data_count(&self) -> usize {
        self.datas.len()
    }

    /// Returns the number of imports declared by the module
    pub fn import_count(&self) -> usize {
        self.imports.len()
    }

    /// Returns the number of exports declared by the module
    pub fn export_count(&self) -> usize {
        self.exports.len()
    }

    /// Returns true if the module has a start function
    pub fn has_start(&self) -> bool {
        self.start.is_some()
    }

    /// Returns a reference to the start function if it exists
    pub fn start(&self) -> Option<&StartFunction> {
        self.start.as_ref()
    }

    /// Validates the module according to the WebAssembly specification
    /// 
    /// This performs various validation checks:
    /// * Validates that all function types are valid
    /// * Validates that all functions reference valid types
    /// * Validates that all tables are valid
    /// * Validates that all memories are valid
    /// * Validates that all globals are valid
    /// * Validates that all element segments are valid
    /// * Validates that all data segments are valid
    /// * Validates that the start function references a valid function
    /// * Validates that all imports are valid
    /// * Validates that all exports are valid
    /// 
    /// # Returns
    /// * `true` if the module is valid
    /// * `false` if the module is invalid
    pub fn validate(&self) -> bool {
        // Validate function types
        if !self.types.iter().all(|t| t.validate()) {
            parser_debug_log!(ParserConfig::default(), "Module validation failed: function types");
            return false;
        }

        // Validate functions
        if !self.funcs.iter().all(|f| f.validate(&self.types)) {
            parser_debug_log!(ParserConfig::default(), "Module validation failed: functions");
            return false;
        }

        // Validate tables
        if !self.tables.iter().all(|t| t.validate()) {
            parser_debug_log!(ParserConfig::default(), "Module validation failed: tables");
            return false;
        }

        // Validate memories
        if !self.mems.iter().all(|m| m.validate()) {
            parser_debug_log!(ParserConfig::default(), "Module validation failed: memories");
            return false;
        }

        // Validate globals
        if !self.globals.iter().all(|g| g.validate()) {
            parser_debug_log!(ParserConfig::default(), "Module validation failed: globals");
            return false;
        }

        // Validate element segments
        if !self.elems.iter().all(|e| e.validate()) {
            parser_debug_log!(ParserConfig::default(), "Module validation failed: element segments");
            return false;
        }

        // Validate data segments
        if !self.datas.iter().all(|d| d.validate()) {
            parser_debug_log!(ParserConfig::default(), "Module validation failed: data segments");
            return false;
        }

        // Validate start function
        if let Some(start) = &self.start {
            if !start.validate(self.funcs.len() as u32) {
                parser_debug_log!(ParserConfig::default(), "Module validation failed: start function");
                return false;
            }
        }

        // Validate imports
        if !self.imports.iter().all(|i| i.validate(&self.types)) {
            parser_debug_log!(ParserConfig::default(), "Module validation failed: imports");
            return false;
        }

        // Validate exports
        let total_func_count = self.funcs.len() + self.imports.iter().filter(|i| matches!(i.ty, ExternalType::Func(_))).count();
        let total_table_count = self.tables.len() + self.imports.iter().filter(|i| matches!(i.ty, ExternalType::Table(_))).count();
        let total_memory_count = self.mems.len() + self.imports.iter().filter(|i| matches!(i.ty, ExternalType::Memory(_))).count();
        let total_global_count = self.globals.len() + self.imports.iter().filter(|i| matches!(i.ty, ExternalType::Global(_))).count();
        
        parser_debug_log!(ParserConfig::default(), "Export validation: func_count={}, table_count={}, memory_count={}, global_count={}", 
                 total_func_count, total_table_count, total_memory_count, total_global_count);
        parser_debug_log!(ParserConfig::default(), "Exports: {:?}", self.exports);
        
        if !self.exports.iter().all(|e| e.validate(total_func_count, total_table_count, total_memory_count, total_global_count)) {
            parser_debug_log!(ParserConfig::default(), "Module validation failed: exports");
            return false;
        }

        true
    }
}

impl fmt::Display for Module {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "module {{")?;
        writeln!(f, "  types: {} types", self.type_count())?;
        writeln!(f, "  funcs: {} functions", self.func_count())?;
        writeln!(f, "  tables: {} tables", self.table_count())?;
        writeln!(f, "  mems: {} memories", self.memory_count())?;
        writeln!(f, "  globals: {} globals", self.global_count())?;
        writeln!(f, "  elems: {} element segments", self.element_count())?;
        writeln!(f, "  datas: {} data segments", self.data_count())?;
        if let Some(start) = &self.start {
            writeln!(f, "  start: {}", start)?;
        }
        writeln!(f, "  imports: {} imports", self.import_count())?;
        writeln!(f, "  exports: {} exports", self.export_count())?;
        write!(f, "}}")
    }
}

/// Represents the mutability of a global variable
/// 
/// In the WebAssembly specification, this is written as:
/// * `const` for immutable globals
/// * `var` for mutable globals
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Mutability {
    /// Immutable global (const)
    Const,
    /// Mutable global (var)
    Var,
}

impl Mutability {
    /// Returns true if the global is mutable
    pub const fn is_mutable(&self) -> bool {
        matches!(self, Mutability::Var)
    }

    /// Returns true if the global is immutable
    pub const fn is_immutable(&self) -> bool {
        matches!(self, Mutability::Const)
    }
}

impl fmt::Display for Mutability {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Mutability::Const => write!(f, "const"),
            Mutability::Var => write!(f, "var"),
        }
    }
}

/// Represents a global type in WebAssembly
/// 
/// A global type consists of a value type and a mutability flag.
/// In the WebAssembly specification, this is written as `mut valtype`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct GlobalType {
    /// The mutability of the global variable
    pub mutability: Mutability,
    /// The type of value stored in the global variable
    pub value_type: ValType,
}

impl GlobalType {
    /// Creates a new global type with the given mutability and value type
    pub const fn new(mutability: Mutability, value_type: ValType) -> Self {
        Self { mutability, value_type }
    }

    /// Creates a new immutable global type
    pub const fn immutable(value_type: ValType) -> Self {
        Self::new(Mutability::Const, value_type)
    }

    /// Creates a new mutable global type
    pub const fn mutable(value_type: ValType) -> Self {
        Self::new(Mutability::Var, value_type)
    }

    /// Returns true if the global is mutable
    pub const fn is_mutable(&self) -> bool {
        self.mutability.is_mutable()
    }

    /// Returns true if the global is immutable
    pub const fn is_immutable(&self) -> bool {
        self.mutability.is_immutable()
    }

    /// Returns the value type of the global
    pub const fn value_type(&self) -> ValType {
        self.value_type
    }

    /// Returns the mutability of the global
    pub const fn mutability(&self) -> Mutability {
        self.mutability
    }
}

impl fmt::Display for GlobalType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", self.mutability, self.value_type)
    }
}

/// Represents a table type in WebAssembly
/// 
/// A table type consists of limits that constrain the minimum and optionally
/// the maximum size of a table, and a reference type that specifies the type
/// of elements stored in the table.
/// 
/// In the WebAssembly specification, this is written as `limits reftype`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TableType {
    /// The limits on the table size in number of entries
    pub limits: Limits,
    /// The type of elements stored in the table
    pub element_type: ValType,
}

impl TableType {
    /// Creates a new table type with the given limits and element type
    /// 
    /// # Arguments
    /// * `limits` - The limits on the table size
    /// * `element_type` - The type of elements stored in the table (must be a reference type)
    /// 
    /// # Panics
    /// Panics if `element_type` is not a reference type (funcref or externref)
    pub const fn new(limits: Limits, element_type: ValType) -> Self {
        // Note: We can't validate element_type in const fn, so we'll do it in non-const methods
        Self { limits, element_type }
    }

    /// Creates a new table type with a minimum size and no maximum, storing function references
    pub const fn funcref_min(min_entries: u32) -> Self {
        Self::new(Limits::min(min_entries), ValType::FuncRef)
    }

    /// Creates a new table type with both minimum and maximum sizes, storing function references
    pub const fn funcref_min_max(min_entries: u32, max_entries: u32) -> Self {
        Self::new(Limits::min_max(min_entries, max_entries), ValType::FuncRef)
    }

    /// Creates a new table type with a minimum size and no maximum, storing external references
    pub const fn externref_min(min_entries: u32) -> Self {
        Self::new(Limits::min(min_entries), ValType::ExternRef)
    }

    /// Creates a new table type with both minimum and maximum sizes, storing external references
    pub const fn externref_min_max(min_entries: u32, max_entries: u32) -> Self {
        Self::new(Limits::min_max(min_entries, max_entries), ValType::ExternRef)
    }

    /// Returns the minimum number of entries in the table
    pub const fn min_entries(&self) -> u32 {
        self.limits.min
    }

    /// Returns the maximum number of entries in the table, if any
    pub const fn max_entries(&self) -> Option<u32> {
        self.limits.max
    }

    /// Returns true if the element type is a function reference
    pub const fn is_funcref(&self) -> bool {
        matches!(self.element_type, ValType::FuncRef)
    }

    /// Returns true if the element type is an external reference
    pub const fn is_externref(&self) -> bool {
        matches!(self.element_type, ValType::ExternRef)
    }

    /// Returns true if the given number of entries is within the table limits
    pub fn is_within_entries(&self, entries: u32) -> bool {
        self.limits.is_within(entries)
    }

    /// Validates that the element type is a reference type
    /// 
    /// # Returns
    /// Returns `true` if the element type is a valid reference type (funcref or externref)
    pub fn validate_element_type(&self) -> bool {
        self.element_type.is_reference_type()
    }

    /// Validates the table type according to the WebAssembly specification
    /// 
    /// # Returns
    /// * `true` if the table type is valid
    /// * `false` if the table type is invalid
    pub fn validate(&self) -> bool {
        // Check that the element type is a reference type
        if !self.element_type.is_reference_type() {
            return false;
        }

        // Check that the limits are valid
        if let Some(max) = self.max_entries() {
            if max < self.min_entries() {
                return false;
            }
        }

        true
    }
}

impl fmt::Display for TableType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "table {} {}", self.limits, self.element_type)
    }
}

/// Represents an external type in WebAssembly
/// 
/// External types classify imports and external values with their respective types.
/// In the WebAssembly specification, this is written as:
/// * `func functype` for function imports
/// * `table tabletype` for table imports
/// * `mem memtype` for memory imports
/// * `global globaltype` for global imports
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ExternalType {
    /// Function import (func functype)
    Func(FuncType),
    /// Table import (table tabletype)
    Table(TableType),
    /// Memory import (mem memtype)
    Memory(MemoryType),
    /// Global import (global globaltype)
    Global(GlobalType),
}

impl ExternalType {
    /// Returns true if this is a function import
    pub const fn is_func(&self) -> bool {
        matches!(self, ExternalType::Func(_))
    }

    /// Returns true if this is a table import
    pub const fn is_table(&self) -> bool {
        matches!(self, ExternalType::Table(_))
    }

    /// Returns true if this is a memory import
    pub const fn is_memory(&self) -> bool {
        matches!(self, ExternalType::Memory(_))
    }

    /// Returns true if this is a global import
    pub const fn is_global(&self) -> bool {
        matches!(self, ExternalType::Global(_))
    }

    /// Returns the function type if this is a function import
    pub fn as_func(&self) -> Option<&FuncType> {
        match self {
            ExternalType::Func(ty) => Some(ty),
            _ => None,
        }
    }

    /// Returns the table type if this is a table import
    pub fn as_table(&self) -> Option<&TableType> {
        match self {
            ExternalType::Table(ty) => Some(ty),
            _ => None,
        }
    }

    /// Returns the memory type if this is a memory import
    pub fn as_memory(&self) -> Option<&MemoryType> {
        match self {
            ExternalType::Memory(ty) => Some(ty),
            _ => None,
        }
    }

    /// Returns the global type if this is a global import
    pub fn as_global(&self) -> Option<&GlobalType> {
        match self {
            ExternalType::Global(ty) => Some(ty),
            _ => None,
        }
    }
}

impl fmt::Display for ExternalType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ExternalType::Func(ty) => write!(f, "func {}", ty),
            ExternalType::Table(ty) => write!(f, "table {}", ty),
            ExternalType::Memory(ty) => write!(f, "memory {}", ty),
            ExternalType::Global(ty) => write!(f, "global {}", ty),
        }
    }
}

/// Helper functions for working with sequences of external types
pub mod external_types {
    use super::*;

    /// Filters out function types from a sequence of external types
    /// 
    /// This implements the `funcs(externtype*)` notation from the specification.
    pub fn funcs(types: &[ExternalType]) -> Vec<&FuncType> {
        types.iter()
            .filter_map(ExternalType::as_func)
            .collect()
    }

    /// Filters out table types from a sequence of external types
    /// 
    /// This implements the `tables(externtype*)` notation from the specification.
    pub fn tables(types: &[ExternalType]) -> Vec<&TableType> {
        types.iter()
            .filter_map(ExternalType::as_table)
            .collect()
    }

    /// Filters out memory types from a sequence of external types
    /// 
    /// This implements the `mems(externtype*)` notation from the specification.
    pub fn mems(types: &[ExternalType]) -> Vec<&MemoryType> {
        types.iter()
            .filter_map(ExternalType::as_memory)
            .collect()
    }

    /// Filters out global types from a sequence of external types
    /// 
    /// This implements the `globals(externtype*)` notation from the specification.
    pub fn globals(types: &[ExternalType]) -> Vec<&GlobalType> {
        types.iter()
            .filter_map(ExternalType::as_global)
            .collect()
    }
}

/// Represents the kind of an exported or imported item
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ExternKind {
    /// Function export/import
    Func,
    /// Table export/import
    Table,
    /// Memory export/import
    Memory,
    /// Global export/import
    Global,
}

impl ExternKind {
    /// Returns the index space identifier for this kind
    /// 
    /// This is used to determine which index space an import/export belongs to.
    pub const fn index_space(&self) -> &'static str {
        match self {
            ExternKind::Func => "function",
            ExternKind::Table => "table",
            ExternKind::Memory => "memory",
            ExternKind::Global => "global",
        }
    }
}

impl fmt::Display for ExternKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.index_space())
    }
}

/// Represents an export in a WebAssembly module
/// 
/// An export consists of a unique name and a reference to an exported item
/// (function, table, memory, or global) by its kind and index.
/// 
/// # Specification
/// The exports component of a module defines a set of exports that become
/// accessible to the host environment once the module has been instantiated.
/// Each export is labeled by a unique name. Exportable definitions are
/// functions, tables, memories, and globals.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Export {
    /// The unique name of the export
    pub name: String,
    /// The kind of the exported item
    pub kind: ExternKind,
    /// The index of the exported item in its respective index space
    pub index: u32,
}

impl Export {
    /// Creates a new export
    /// 
    /// # Arguments
    /// * `name` - The unique name of the export
    /// * `kind` - The kind of the exported item
    /// * `index` - The index of the exported item in its respective index space
    /// 
    /// # Note
    /// The name must be unique among all exports in the module.
    pub fn new(name: String, kind: ExternKind, index: u32) -> Self {
        Self { name, kind, index }
    }

    /// Returns the index space identifier for this export
    pub fn index_space(&self) -> &'static str {
        self.kind.index_space()
    }

    /// Validates the export according to the WebAssembly specification
    /// 
    /// # Arguments
    /// * `func_count` - The number of functions defined in the module
    /// * `table_count` - The number of tables defined in the module
    /// * `memory_count` - The number of memories defined in the module
    /// * `global_count` - The number of globals defined in the module
    /// 
    /// # Returns
    /// * `true` if the export is valid
    /// * `false` if the export is invalid
    pub fn validate(&self, func_count: usize, table_count: usize, memory_count: usize, global_count: usize) -> bool {
        // Check that the name is not empty
        if self.name.is_empty() {
            parser_debug_log!(ParserConfig::default(), "Export validation failed: empty name");
            return false;
        }

        match self.kind {
            ExternKind::Func => {
                let valid = (self.index as usize) < func_count;
                if !valid {
                    parser_debug_log!(ParserConfig::default(), "Export validation failed: function index {} >= function count {}", self.index, func_count);
                }
                valid
            }
            ExternKind::Table => {
                let valid = (self.index as usize) < table_count;
                if !valid {
                    parser_debug_log!(ParserConfig::default(), "Export validation failed: table index {} >= table count {}", self.index, table_count);
                }
                valid
            }
            ExternKind::Memory => {
                let valid = self.index == 0 && memory_count > 0;
                if !valid {
                    parser_debug_log!(ParserConfig::default(), "Export validation failed: memory index {} != 0 or memory count {}", self.index, memory_count);
                }
                valid
            }
            ExternKind::Global => {
                let valid = (self.index as usize) < global_count;
                if !valid {
                    parser_debug_log!(ParserConfig::default(), "Export validation failed: global index {} >= global count {}", self.index, global_count);
                }
                valid
            }
        }
    }
}

impl fmt::Display for Export {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "export \"{}\" {} {}", self.name, self.kind, self.index)
    }
}

/// Represents an import in a WebAssembly module
/// 
/// An import consists of a module name, a field name, and the type
/// of the imported item (function, table, memory, or global).
/// 
/// # Specification
/// The imports component of a module defines a set of imports that are
/// required for instantiation. Each import is labeled by a two-level name
/// space, consisting of a module name and a field name for an entity within
/// that module. Importable definitions are functions, tables, memories, and
/// globals. Each import is specified by a descriptor with a respective type
/// that a definition provided during instantiation is required to match.
/// 
/// Every import defines an index in the respective index space. In each index
/// space, the indices of imports go before the first index of any definition
/// contained in the module itself.
/// 
/// # Note
/// Unlike export names, import names are not necessarily unique. It is possible
/// to import the same module_name/field_name pair multiple times; such imports
/// may even have different type descriptions, including different kinds of
/// entities.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Import {
    /// The module name of the import
    pub module: String,
    /// The field name of the import
    pub field: String,
    /// The type of the imported item
    pub ty: ExternalType,
}

impl Import {
    /// Creates a new import
    /// 
    /// # Arguments
    /// * `module` - The module name of the import
    /// * `field` - The field name of the import
    /// * `ty` - The type of the imported item
    /// 
    /// # Note
    /// The module_name/field_name pair does not need to be unique. Multiple
    /// imports can use the same pair, even with different types.
    pub fn new(module: String, field: String, ty: ExternalType) -> Self {
        Self { module, field, ty }
    }

    /// Returns the kind of the imported item
    pub fn kind(&self) -> ExternKind {
        match &self.ty {
            ExternalType::Func(_) => ExternKind::Func,
            ExternalType::Table(_) => ExternKind::Table,
            ExternalType::Memory(_) => ExternKind::Memory,
            ExternalType::Global(_) => ExternKind::Global,
        }
    }

    /// Returns the index space identifier for this import
    pub fn index_space(&self) -> &'static str {
        self.kind().index_space()
    }

    /// Returns true if this import matches another import by module and field name
    /// 
    /// This is used to identify imports that share the same module_name/field_name
    /// pair, which is allowed by the specification.
    pub fn matches_name(&self, other: &Import) -> bool {
        self.module == other.module && self.field == other.field
    }

    /// Validates the import according to the WebAssembly specification
    /// 
    /// # Arguments
    /// * `types` - The vector of function types defined in the module
    /// 
    /// # Returns
    /// * `true` if the import is valid
    /// * `false` if the import is invalid
    pub fn validate(&self, types: &[FuncType]) -> bool {
        // Check that the module and field names are not empty
        if self.module.is_empty() || self.field.is_empty() {
            return false;
        }

        // Check that the external type is valid
        match &self.ty {
            ExternalType::Func(func_type) => {
                // For function imports, we don't need to validate against types
                // as the function type is provided directly
                true
            }
            ExternalType::Table(table_type) => table_type.validate(),
            ExternalType::Memory(memory_type) => {
                // In the current version of WebAssembly, we only have one memory
                true
            }
            ExternalType::Global(global_type) => {
                // For global imports, we don't need additional validation
                true
            }
        }
    }
}

impl fmt::Display for Import {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "import \"{}\" \"{}\" {}", self.module, self.field, self.ty)
    }
}

/// Helper functions for working with sequences of imports and exports
pub mod external_items {
    use super::*;
    use alloc::vec::Vec;

    /// Filters out function imports/exports from a sequence
    /// 
    /// This implements the `funcs(external*)` notation from the specification.
    pub fn funcs<T: AsRef<[ExternalType]>>(items: &[(String, String, T)]) -> Vec<&FuncType> {
        items.iter()
            .filter_map(|(_, _, ty)| match ty.as_ref() {
                [ExternalType::Func(ft)] => Some(ft),
                _ => None,
            })
            .collect()
    }

    /// Filters out table imports/exports from a sequence
    /// 
    /// This implements the `tables(external*)` notation from the specification.
    pub fn tables<T: AsRef<[ExternalType]>>(items: &[(String, String, T)]) -> Vec<&TableType> {
        items.iter()
            .filter_map(|(_, _, ty)| match ty.as_ref() {
                [ExternalType::Table(tt)] => Some(tt),
                _ => None,
            })
            .collect()
    }

    /// Filters out memory imports/exports from a sequence
    /// 
    /// This implements the `mems(external*)` notation from the specification.
    pub fn mems<T: AsRef<[ExternalType]>>(items: &[(String, String, T)]) -> Vec<&MemoryType> {
        items.iter()
            .filter_map(|(_, _, ty)| match ty.as_ref() {
                [ExternalType::Memory(mt)] => Some(mt),
                _ => None,
            })
            .collect()
    }

    /// Filters out global imports/exports from a sequence
    /// 
    /// This implements the `globals(external*)` notation from the specification.
    pub fn globals<T: AsRef<[ExternalType]>>(items: &[(String, String, T)]) -> Vec<&GlobalType> {
        items.iter()
            .filter_map(|(_, _, ty)| match ty.as_ref() {
                [ExternalType::Global(gt)] => Some(gt),
                _ => None,
            })
            .collect()
    }
}

/// Represents a local variable declaration in a function
/// 
/// A local declaration consists of a count and a value type, indicating
/// that the function has `count` local variables of the given type.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LocalDecl {
    /// The number of local variables of this type
    pub count: u32,
    /// The type of the local variables
    pub ty: ValType,
}

/// Represents a function in a WebAssembly module
/// 
/// A function consists of its type index, local variable declarations,
/// and the raw bytes of its code.
/// 
/// # Specification
/// The functions component of a module defines a vector of functions with
/// the following structure:
/// 
/// * The type of a function declares its signature by reference to a type
///   defined in the module. The parameters of the function are referenced
///   through 0-based local indices in the function's body; they are mutable.
/// 
/// * The locals declare a vector of mutable local variables and their types.
///   These variables are referenced through local indices in the function's
///   body. The index of the first local is the smallest index not referencing
///   a parameter.
/// 
/// * The code is an instruction sequence that upon termination must produce
///   a stack matching the function type's result type.
/// 
/// Functions are referenced through function indices, starting with the
/// smallest index not referencing a function import.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Function {
    /// The index of the function's type in the type section
    pub type_index: u32,
    /// The local variable declarations
    pub locals: Vec<LocalDecl>,
    /// The raw bytes of the function's code
    pub code: Vec<u8>,
}

impl Function {
    /// Creates a new function
    /// 
    /// # Arguments
    /// * `type_index` - The index of the function's type in the type section
    /// * `locals` - The local variable declarations
    /// * `code` - The raw bytes of the function's code
    pub fn new(type_index: u32, locals: Vec<LocalDecl>, code: Vec<u8>) -> Self {
        Self { type_index, locals, code }
    }

    /// Returns the total number of local variables in the function
    /// 
    /// This includes both parameters and declared locals.
    pub fn total_local_count(&self) -> u32 {
        self.locals.iter().map(|local| local.count).sum()
    }

    /// Returns the number of parameters in the function
    /// 
    /// This is determined by the function's type, which must be looked up
    /// in the type section using `type_index`.
    pub fn param_count(&self) -> Option<u32> {
        // Note: This is a placeholder. The actual implementation would need
        // access to the type section to look up the function type.
        None
    }

    /// Returns the index of the first local variable
    /// 
    /// This is the smallest index not referencing a parameter.
    pub fn first_local_index(&self) -> Option<u32> {
        self.param_count().map(|params| params)
    }

    /// Returns the size of the function's code in bytes
    pub fn code_size(&self) -> usize {
        self.code.len()
    }

    /// Returns an iterator over the local variable declarations
    pub fn local_decls(&self) -> impl Iterator<Item = &LocalDecl> {
        self.locals.iter()
    }

    /// Returns the total number of local variable declarations
    pub fn local_decl_count(&self) -> usize {
        self.locals.len()
    }

    /// Returns true if the function has no local variables
    pub fn has_no_locals(&self) -> bool {
        self.locals.is_empty()
    }

    /// Returns true if the function has no code
    pub fn has_no_code(&self) -> bool {
        self.code.is_empty()
    }

    /// Validates the function according to the WebAssembly specification
    /// 
    /// # Arguments
    /// * `types` - The vector of function types defined in the module
    /// 
    /// # Returns
    /// * `true` if the function is valid
    /// * `false` if the function is invalid
    pub fn validate(&self, types: &[FuncType]) -> bool {
        // Check that the type index is valid
        if self.type_index as usize >= types.len() {
            return false;
        }

        // Check that all local declarations are valid
        if !self.locals.iter().all(|local| local.count > 0) {
            return false;
        }

        // Check that the code is not empty
        if self.code.is_empty() {
            return false;
        }

        true
    }
}

impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "func[{}] (", self.type_index)?;
        
        // Note: We can't display parameter types without access to the type section
        write!(f, "...)")?;
        
        if !self.locals.is_empty() {
            write!(f, " locals ")?;
            for (i, local) in self.locals.iter().enumerate() {
                if i > 0 {
                    write!(f, " ")?;
                }
                write!(f, "{} {}", local.count, local.ty)?;
            }
        }
        
        write!(f, " code[{} bytes]", self.code.len())
    }
}

impl fmt::Display for LocalDecl {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", self.count, self.ty)
    }
}

/// Represents the mode of a data segment
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum DataMode {
    /// Passive data segment
    /// 
    /// Contents can be copied into a memory using the memory.init instruction.
    Passive,
    /// Active data segment
    /// 
    /// Contents are copied into a memory during instantiation, as specified
    /// by a memory index and a constant expression defining an offset.
    /// 
    /// # Note
    /// In the current version of WebAssembly, at most one memory is allowed
    /// in a module. Consequently, the only valid memory index is 0.
    Active {
        /// The index of the memory to initialize
        /// 
        /// # Note
        /// In the current version of WebAssembly, this must be 0 as only
        /// one memory is allowed per module.
        memory_index: u32,
        /// The offset expression
        offset: ConstExpr,
    },
}

impl DataMode {
    /// Creates a new passive data segment mode
    pub const fn passive() -> Self {
        Self::Passive
    }

    /// Creates a new active data segment mode
    /// 
    /// # Arguments
    /// * `memory_index` - The index of the memory to initialize
    /// * `offset` - The offset expression
    /// 
    /// # Note
    /// In the current version of WebAssembly, `memory_index` must be 0 as
    /// only one memory is allowed per module.
    pub fn active(memory_index: u32, offset: ConstExpr) -> Self {
        Self::Active { memory_index, offset }
    }

    /// Returns true if this is a passive data segment
    pub const fn is_passive(&self) -> bool {
        matches!(self, Self::Passive)
    }

    /// Returns true if this is an active data segment
    pub const fn is_active(&self) -> bool {
        matches!(self, Self::Active { .. })
    }

    /// Returns the memory index if this is an active data segment
    /// 
    /// # Note
    /// In the current version of WebAssembly, this will always return
    /// Some(0) for active segments as only one memory is allowed per module.
    pub const fn memory_index(&self) -> Option<u32> {
        match self {
            Self::Active { memory_index, .. } => Some(*memory_index),
            _ => None,
        }
    }

    /// Returns the offset expression if this is an active data segment
    pub fn offset(&self) -> Option<&ConstExpr> {
        match self {
            Self::Active { offset, .. } => Some(offset),
            _ => None,
        }
    }

    /// Validates the data mode according to the WebAssembly specification
    /// 
    /// # Returns
    /// * `true` if the mode is valid
    /// * `false` if the mode is invalid (e.g., active mode with memory index != 0)
    pub fn validate(&self) -> bool {
        match self {
            Self::Passive => true,
            Self::Active { memory_index, .. } => *memory_index == 0,
        }
    }
}

impl fmt::Display for DataMode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Passive => write!(f, "passive"),
            Self::Active { memory_index, offset } => {
                write!(f, "active {{memory {}, offset {}}}", memory_index, offset)
            }
        }
    }
}

/// Represents a data segment in a WebAssembly module
/// 
/// A data segment defines a vector of bytes that can be used to initialize
/// a range of memory.
/// 
/// # Specification
/// The datas component of a module defines a vector of data segments.
/// Like element segments, data segments have a mode that identifies them
/// as either passive or active. A passive data segment's contents can be
/// copied into a memory using the memory.init instruction. An active data
/// segment copies its contents into a memory during instantiation, as
/// specified by a memory index and a constant expression defining an offset
/// into that memory.
/// 
/// Data segments are referenced through data indices.
/// 
/// # Note
/// In the current version of WebAssembly, at most one memory is allowed
/// in a module. Consequently, the only valid memory index is 0.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DataSegment {
    /// The vector of bytes to initialize memory with
    pub data: Vec<u8>,
    /// The mode of the data segment
    pub mode: DataMode,
}

impl DataSegment {
    /// Creates a new data segment
    /// 
    /// # Arguments
    /// * `data` - The vector of bytes to initialize memory with
    /// * `mode` - The mode of the data segment
    pub fn new(data: Vec<u8>, mode: DataMode) -> Self {
        Self { data, mode }
    }

    /// Creates a new passive data segment
    pub fn passive(data: Vec<u8>) -> Self {
        Self::new(data, DataMode::passive())
    }

    /// Creates a new active data segment
    /// 
    /// # Arguments
    /// * `data` - The vector of bytes to initialize memory with
    /// * `memory_index` - The index of the memory to initialize
    /// * `offset` - The offset expression
    /// 
    /// # Note
    /// In the current version of WebAssembly, `memory_index` must be 0 as
    /// only one memory is allowed per module.
    pub fn active(data: Vec<u8>, memory_index: u32, offset: ConstExpr) -> Self {
        Self::new(data, DataMode::active(memory_index, offset))
    }

    /// Returns the number of bytes in the data segment
    pub fn size(&self) -> usize {
        self.data.len()
    }

    /// Returns true if the data segment is empty
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    /// Returns an iterator over the bytes in the data segment
    pub fn bytes(&self) -> impl Iterator<Item = &u8> {
        self.data.iter()
    }

    /// Returns a slice of the data segment's bytes
    pub fn as_bytes(&self) -> &[u8] {
        &self.data
    }

    /// Validates the data segment according to the WebAssembly specification
    /// 
    /// # Returns
    /// * `true` if the segment is valid
    /// * `false` if the segment is invalid (e.g., active mode with memory index != 0)
    pub fn validate(&self) -> bool {
        self.mode.validate()
    }
}

impl fmt::Display for DataSegment {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "data {} [{} bytes]", self.mode, self.size())
    }
}

/// Represents a memory in a WebAssembly module
/// 
/// A memory is a vector of raw uninterpreted bytes. The minimum size in
/// the limits of the memory type specifies the initial size of that memory,
/// while its maximum, if present, restricts the size to which it can grow
/// later. Both are in units of page size.
/// 
/// # Specification
/// The memories component of a module defines a vector of linear memories
/// (or memories for short) as described by their memory type.
/// 
/// Memories can be initialized through data segments.
/// 
/// Memories are referenced through memory indices, starting with the smallest
/// index not referencing a memory import. Most constructs implicitly reference
/// memory index 0.
/// 
/// # Note
/// In the current version of WebAssembly, at most one memory may be defined
/// or imported in a single module, and all constructs implicitly reference
/// this memory 0. This restriction may be lifted in future versions.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Memory {
    /// The type of the memory
    pub ty: MemoryType,
    /// The data segments used to initialize this memory
    pub data: Vec<DataSegment>,
}

impl Memory {
    /// Creates a new memory with the given type
    pub const fn new(ty: MemoryType) -> Self {
        Self { ty, data: Vec::new() }
    }

    /// Creates a new memory with the given type and data segments
    pub fn with_data(ty: MemoryType, data: Vec<DataSegment>) -> Self {
        Self { ty, data }
    }

    /// Returns the initial size of the memory in pages
    pub const fn initial_pages(&self) -> u32 {
        self.ty.min_pages()
    }

    /// Returns the maximum size of the memory in pages, if any
    pub const fn maximum_pages(&self) -> Option<u32> {
        self.ty.max_pages()
    }

    /// Returns the initial size of the memory in bytes
    pub const fn initial_bytes(&self) -> u64 {
        self.ty.min_bytes()
    }

    /// Returns the maximum size of the memory in bytes, if any
    pub fn maximum_bytes(&self) -> Option<u64> {
        self.ty.max_bytes()
    }

    /// Returns true if the memory has a maximum size
    pub const fn has_maximum(&self) -> bool {
        self.ty.limits.has_max()
    }

    /// Returns true if the given size in pages is within the memory limits
    pub fn is_within_pages(&self, pages: u32) -> bool {
        self.ty.is_within_pages(pages)
    }

    /// Returns true if the given size in bytes is within the memory limits
    pub fn is_within_bytes(&self, bytes: u64) -> bool {
        self.ty.is_within_bytes(bytes)
    }

    /// Returns an iterator over the data segments
    pub fn data_segments(&self) -> impl Iterator<Item = &DataSegment> {
        self.data.iter()
    }

    /// Returns the number of data segments
    pub fn data_segment_count(&self) -> usize {
        self.data.len()
    }

    /// Returns true if the memory has no data segments
    pub fn has_no_data(&self) -> bool {
        self.data.is_empty()
    }

    /// Adds a data segment to the memory
    pub fn add_data_segment(&mut self, segment: DataSegment) {
        self.data.push(segment);
    }

    /// Returns the total size of all data segments in bytes
    pub fn total_data_size(&self) -> usize {
        self.data.iter().map(|segment| segment.size()).sum()
    }

    /// Validates the memory according to the WebAssembly specification
    /// 
    /// # Returns
    /// * `true` if the memory is valid
    /// * `false` if the memory is invalid
    pub fn validate(&self) -> bool {
        // Check that the memory type is valid
        if let Some(max) = self.maximum_pages() {
            if max < self.initial_pages() {
                return false;
            }
        }

        // Check that all data segments are valid
        if !self.data.iter().all(|segment| segment.validate()) {
            return false;
        }

        true
    }
}

impl fmt::Display for Memory {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "memory {}", self.ty)?;
        
        if !self.data.is_empty() {
            write!(f, " with {} data segments", self.data.len())?;
        }
        
        Ok(())
    }
}

/// Represents a constant expression in WebAssembly
/// 
/// A constant expression is used to initialize global variables.
/// Currently, only a few basic forms are supported, but this can be
/// extended as needed.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ConstExpr {
    /// A constant value (i32, i64, f32, f64)
    Const(ValType, Vec<u8>), // TODO: Replace with proper value representation
    /// A reference to a global variable
    GlobalGet(u32),
    /// A reference to a function
    RefFunc(u32),
    /// A null reference
    RefNull(ValType),
}

impl ConstExpr {
    /// Creates a new constant expression with a constant value
    pub fn const_value(ty: ValType, value: Vec<u8>) -> Self {
        Self::Const(ty, value)
    }

    /// Creates a new constant expression that gets a global's value
    pub fn global_get(global_index: u32) -> Self {
        Self::GlobalGet(global_index)
    }

    /// Creates a new constant expression that references a function
    pub fn ref_func(func_index: u32) -> Self {
        Self::RefFunc(func_index)
    }

    /// Creates a new constant expression that creates a null reference
    pub fn ref_null(ty: ValType) -> Self {
        Self::RefNull(ty)
    }

    /// Returns the type of the value produced by this expression
    pub fn result_type(&self) -> ValType {
        match self {
            ConstExpr::Const(ty, _) => *ty,
            ConstExpr::GlobalGet(_) => {
                // Note: This is a placeholder. The actual implementation would need
                // access to the global section to look up the global type.
                ValType::I32 // Default to i32 for now
            }
            ConstExpr::RefFunc(_) => ValType::FuncRef,
            ConstExpr::RefNull(ty) => *ty,
        }
    }

    /// Returns true if this is a constant value expression
    pub fn is_const(&self) -> bool {
        matches!(self, ConstExpr::Const(_, _))
    }

    /// Returns true if this is a global get expression
    pub fn is_global_get(&self) -> bool {
        matches!(self, ConstExpr::GlobalGet(_))
    }

    /// Returns true if this is a function reference expression
    pub fn is_ref_func(&self) -> bool {
        matches!(self, ConstExpr::RefFunc(_))
    }

    /// Returns true if this is a null reference expression
    pub fn is_ref_null(&self) -> bool {
        matches!(self, ConstExpr::RefNull(_))
    }
}

impl fmt::Display for ConstExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ConstExpr::Const(ty, value) => {
                write!(f, "const.{} [{} bytes]", ty, value.len())
            }
            ConstExpr::GlobalGet(idx) => {
                write!(f, "global.get {}", idx)
            }
            ConstExpr::RefFunc(idx) => {
                write!(f, "ref.func {}", idx)
            }
            ConstExpr::RefNull(ty) => {
                write!(f, "ref.null {}", ty)
            }
        }
    }
}

/// Represents a global variable in a WebAssembly module
/// 
/// A global variable consists of its type and an initializer expression.
/// 
/// # Specification
/// The globals component of a module defines a vector of global variables
/// (or globals for short). Each global stores a single value of the given
/// global type. Its type also specifies whether a global is immutable or
/// mutable. Moreover, each global is initialized with an init value given
/// by a constant initializer expression.
/// 
/// Globals are referenced through global indices, starting with the smallest
/// index not referencing a global import.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Global {
    /// The type of the global variable
    pub ty: GlobalType,
    /// The initializer expression
    pub init: ConstExpr,
}

impl Global {
    /// Creates a new global variable
    /// 
    /// # Arguments
    /// * `ty` - The type of the global variable
    /// * `init` - The initializer expression
    /// 
    /// # Note
    /// The initializer expression must be a constant expression that produces
    /// a value of the global's type.
    pub fn new(ty: GlobalType, init: ConstExpr) -> Self {
        Self { ty, init }
    }

    /// Returns the value type of the global
    pub const fn value_type(&self) -> ValType {
        self.ty.value_type()
    }

    /// Returns true if the global is mutable
    pub const fn is_mutable(&self) -> bool {
        self.ty.is_mutable()
    }

    /// Returns true if the global is immutable
    pub const fn is_immutable(&self) -> bool {
        self.ty.is_immutable()
    }

    /// Returns true if the initializer expression is valid for this global
    /// 
    /// This checks that the initializer expression produces a value of the
    /// global's type.
    pub fn validate_init(&self) -> bool {
        self.init.result_type() == self.value_type()
    }

    /// Validates the global according to the WebAssembly specification
    /// 
    /// # Returns
    /// * `true` if the global is valid
    /// * `false` if the global is invalid
    pub fn validate(&self) -> bool {
        // Check that the initializer expression is valid
        self.validate_init()
    }
}

impl fmt::Display for Global {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "global {} = {}", self.ty, self.init)
    }
}

/// Represents the mode of an element segment
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ElementMode {
    /// Passive element segment
    /// 
    /// Elements can be copied to a table using the table.init instruction.
    Passive,
    /// Active element segment
    /// 
    /// Elements are copied into a table during instantiation, as specified
    /// by a table index and a constant expression defining an offset.
    Active {
        /// The index of the table to initialize
        table_index: u32,
        /// The offset expression
        offset: ConstExpr,
    },
    /// Declarative element segment
    /// 
    /// Not available at runtime, but serves to forward-declare references
    /// that are formed in code with instructions like ref.func.
    Declarative,
}

impl ElementMode {
    /// Creates a new passive element segment mode
    pub const fn passive() -> Self {
        Self::Passive
    }

    /// Creates a new active element segment mode
    pub fn active(table_index: u32, offset: ConstExpr) -> Self {
        Self::Active { table_index, offset }
    }

    /// Creates a new declarative element segment mode
    pub const fn declarative() -> Self {
        Self::Declarative
    }

    /// Returns true if this is a passive element segment
    pub const fn is_passive(&self) -> bool {
        matches!(self, Self::Passive)
    }

    /// Returns true if this is an active element segment
    pub const fn is_active(&self) -> bool {
        matches!(self, Self::Active { .. })
    }

    /// Returns true if this is a declarative element segment
    pub const fn is_declarative(&self) -> bool {
        matches!(self, Self::Declarative)
    }

    /// Returns the table index if this is an active element segment
    pub const fn table_index(&self) -> Option<u32> {
        match self {
            Self::Active { table_index, .. } => Some(*table_index),
            _ => None,
        }
    }

    /// Returns the offset expression if this is an active element segment
    pub fn offset(&self) -> Option<&ConstExpr> {
        match self {
            Self::Active { offset, .. } => Some(offset),
            _ => None,
        }
    }
}

impl fmt::Display for ElementMode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Passive => write!(f, "passive"),
            Self::Active { table_index, offset } => {
                write!(f, "active {{table {}, offset {}}}", table_index, offset)
            }
            Self::Declarative => write!(f, "declarative"),
        }
    }
}

/// Represents an element segment in a WebAssembly module
/// 
/// An element segment defines a reference type and a corresponding list
/// of constant element expressions.
/// 
/// # Specification
/// The elems component of a module defines a vector of element segments.
/// Each element segment defines a reference type and a corresponding list
/// of constant element expressions.
/// 
/// Element segments have a mode that identifies them as either passive,
/// active, or declarative. A passive element segment's elements can be
/// copied to a table using the table.init instruction. An active element
/// segment copies its elements into a table during instantiation, as
/// specified by a table index and a constant expression defining an offset
/// into that table. A declarative element segment is not available at
/// runtime but merely serves to forward-declare references that are formed
/// in code with instructions like ref.func.
/// 
/// Element segments are referenced through element indices.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ElementSegment {
    /// The reference type of the elements
    pub element_type: ValType,
    /// The list of constant element expressions
    pub elements: Vec<ConstExpr>,
    /// The mode of the element segment
    pub mode: ElementMode,
}

impl ElementSegment {
    /// Creates a new element segment
    /// 
    /// # Arguments
    /// * `element_type` - The reference type of the elements
    /// * `elements` - The list of constant element expressions
    /// * `mode` - The mode of the element segment
    /// 
    /// # Note
    /// The element type must be a reference type (funcref or externref).
    pub fn new(element_type: ValType, elements: Vec<ConstExpr>, mode: ElementMode) -> Self {
        Self { element_type, elements, mode }
    }

    /// Creates a new passive element segment
    pub fn passive(element_type: ValType, elements: Vec<ConstExpr>) -> Self {
        Self::new(element_type, elements, ElementMode::passive())
    }

    /// Creates a new active element segment
    pub fn active(element_type: ValType, elements: Vec<ConstExpr>, table_index: u32, offset: ConstExpr) -> Self {
        Self::new(element_type, elements, ElementMode::active(table_index, offset))
    }

    /// Creates a new declarative element segment
    pub fn declarative(element_type: ValType, elements: Vec<ConstExpr>) -> Self {
        Self::new(element_type, elements, ElementMode::declarative())
    }

    /// Returns the number of elements in the segment
    pub fn element_count(&self) -> usize {
        self.elements.len()
    }

    /// Returns true if the element segment is empty
    pub fn is_empty(&self) -> bool {
        self.elements.is_empty()
    }

    /// Returns true if the element type is valid
    /// 
    /// The element type must be a reference type (funcref or externref).
    pub fn validate_element_type(&self) -> bool {
        self.element_type.is_reference_type()
    }

    /// Returns true if all element expressions are valid for this segment
    /// 
    /// This checks that each element expression produces a value of the
    /// segment's element type.
    pub fn validate_elements(&self) -> bool {
        self.elements.iter().all(|expr| expr.result_type() == self.element_type)
    }

    /// Returns an iterator over the element expressions
    pub fn elements(&self) -> impl Iterator<Item = &ConstExpr> {
        self.elements.iter()
    }

    /// Validates the element segment according to the WebAssembly specification
    /// 
    /// # Returns
    /// * `true` if the element segment is valid
    /// * `false` if the element segment is invalid
    pub fn validate(&self) -> bool {
        // Check that the element type is valid
        if !self.validate_element_type() {
            return false;
        }

        // Check that all elements are valid
        if !self.validate_elements() {
            return false;
        }

        // Check that the mode is valid
        match &self.mode {
            ElementMode::Passive => true,
            ElementMode::Active { table_index, .. } => {
                // In the current version of WebAssembly, we only have one table
                *table_index == 0
            }
            ElementMode::Declarative => true,
        }
    }
}

impl fmt::Display for ElementSegment {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "elem {} {} [{} elements]", self.element_type, self.mode, self.element_count())
    }
}

/// Represents a start function in a WebAssembly module
/// 
/// The start function is automatically invoked when the module is instantiated,
/// after tables and memories have been initialized.
/// 
/// # Specification
/// The start component of a module declares the function index of a start
/// function that is automatically invoked when the module is instantiated,
/// after tables and memories have been initialized.
/// 
/// # Note
/// The start function is intended for initializing the state of a module.
/// The module and its exports are not accessible externally before this
/// initialization has completed.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StartFunction {
    /// The index of the function to be invoked during instantiation
    pub function_index: u32,
}

impl StartFunction {
    /// Creates a new start function
    /// 
    /// # Arguments
    /// * `function_index` - The index of the function to be invoked during instantiation
    pub const fn new(function_index: u32) -> Self {
        Self { function_index }
    }

    /// Returns the index of the function to be invoked
    pub const fn function_index(&self) -> u32 {
        self.function_index
    }

    /// Validates the start function according to the WebAssembly specification
    /// 
    /// # Arguments
    /// * `function_count` - The total number of functions in the module
    /// 
    /// # Returns
    /// * `true` if the function index is valid (i.e., less than the total number of functions)
    /// * `false` if the function index is invalid
    pub const fn validate(&self, function_count: u32) -> bool {
        self.function_index < function_count
    }
}

impl fmt::Display for StartFunction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "start {}", self.function_index)
    }
}

/// Numeric unary operations for integers
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IntUnOp {
    /// Count leading zeros
    Clz,
    /// Count trailing zeros
    Ctz,
    /// Count number of 1 bits
    Popcnt,
}

/// Numeric binary operations for integers
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IntBinOp {
    /// Addition
    Add,
    /// Subtraction
    Sub,
    /// Multiplication
    Mul,
    /// Division (signed/unsigned)
    Div { signed: bool },
    /// Remainder (signed/unsigned)
    Rem { signed: bool },
    /// Bitwise AND
    And,
    /// Bitwise OR
    Or,
    /// Bitwise XOR
    Xor,
    /// Shift left
    Shl,
    /// Shift right (signed/unsigned)
    Shr { signed: bool },
    /// Rotate left
    Rotl,
    /// Rotate right
    Rotr,
}

/// Numeric unary operations for floats
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FloatUnOp {
    /// Absolute value
    Abs,
    /// Negation
    Neg,
    /// Square root
    Sqrt,
    /// Ceiling
    Ceil,
    /// Floor
    Floor,
    /// Truncate
    Trunc,
    /// Round to nearest
    Nearest,
}

/// Numeric binary operations for floats
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FloatBinOp {
    /// Addition
    Add,
    /// Subtraction
    Sub,
    /// Multiplication
    Mul,
    /// Division
    Div,
    /// Minimum
    Min,
    /// Maximum
    Max,
    /// Copy sign
    Copysign,
}

/// Numeric test operations for integers
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IntTestOp {
    /// Equal to zero
    Eqz,
}

/// Numeric comparison operations for integers
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IntRelOp {
    /// Equal (signed/unsigned)
    Eq { signed: bool },
    /// Not equal (signed/unsigned)
    Ne { signed: bool },
    /// Less than (signed/unsigned)
    Lt { signed: bool },
    /// Greater than (signed/unsigned)
    Gt { signed: bool },
    /// Less than or equal (signed/unsigned)
    Le { signed: bool },
    /// Greater than or equal (signed/unsigned)
    Ge { signed: bool },
}

/// Numeric comparison operations for floats
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FloatRelOp {
    /// Equal
    Eq,
    /// Not equal
    Ne,
    /// Less than
    Lt,
    /// Greater than
    Gt,
    /// Less than or equal
    Le,
    /// Greater than or equal
    Ge,
}

/// Numeric conversion operations
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ConversionOp {
    /// Wrap i64 to i32
    Wrap,
    /// Extend i32 to i64 (signed/unsigned)
    Extend { signed: bool },
    /// Extend i8 to i32/i64
    Extend8S,
    /// Extend i16 to i32/i64
    Extend16S,
    /// Extend i32 to i64
    Extend32S,
    /// Truncate float to integer (signed/unsigned)
    Trunc { signed: bool },
    /// Truncate float to integer with saturation (signed/unsigned)
    TruncSat { signed: bool },
    /// Demote f64 to f32
    Demote,
    /// Promote f32 to f64
    Promote,
    /// Convert integer to float (signed/unsigned)
    Convert { signed: bool },
    /// Reinterpret bits
    Reinterpret,
}

/// Numeric instruction
#[derive(Debug, Clone, PartialEq)]
pub enum NumericInstruction {
    /// Integer constant
    I32Const(i32),
    /// 64-bit integer constant
    I64Const(i64),
    /// 32-bit float constant
    F32Const(f32),
    /// 64-bit float constant
    F64Const(f64),
    /// Integer unary operation
    I32UnOp(IntUnOp),
    /// 64-bit integer unary operation
    I64UnOp(IntUnOp),
    /// 32-bit float unary operation
    F32UnOp(FloatUnOp),
    /// 64-bit float unary operation
    F64UnOp(FloatUnOp),
    /// Integer binary operation
    I32BinOp(IntBinOp),
    /// 64-bit integer binary operation
    I64BinOp(IntBinOp),
    /// 32-bit float binary operation
    F32BinOp(FloatBinOp),
    /// 64-bit float binary operation
    F64BinOp(FloatBinOp),
    /// Integer test operation (eqz)
    I32TestOp,
    /// 64-bit integer test operation (eqz)
    I64TestOp,
    /// Integer comparison operation
    I32RelOp(IntRelOp),
    /// 64-bit integer comparison operation
    I64RelOp(IntRelOp),
    /// 32-bit float comparison operation
    F32RelOp(FloatRelOp),
    /// 64-bit float comparison operation
    F64RelOp(FloatRelOp),
    /// Integer conversion operation
    I32ConversionOp(ConversionOp),
    /// 64-bit integer conversion operation
    I64ConversionOp(ConversionOp),
    /// 32-bit float conversion operation
    F32ConversionOp(ConversionOp),
    /// 64-bit float conversion operation
    F64ConversionOp(ConversionOp),
}

impl NumericInstruction {
    /// Returns the number of operands consumed by this instruction
    pub fn operand_count(&self) -> usize {
        match self {
            // Constants consume no operands
            NumericInstruction::I32Const(_) |
            NumericInstruction::I64Const(_) |
            NumericInstruction::F32Const(_) |
            NumericInstruction::F64Const(_) => 0,
            
            // Unary operations consume one operand
            NumericInstruction::I32UnOp(_) |
            NumericInstruction::I64UnOp(_) |
            NumericInstruction::F32UnOp(_) |
            NumericInstruction::F64UnOp(_) => 1,
            
            // Binary operations and comparisons consume two operands
            NumericInstruction::I32BinOp(_) |
            NumericInstruction::I64BinOp(_) |
            NumericInstruction::F32BinOp(_) |
            NumericInstruction::F64BinOp(_) |
            NumericInstruction::I32RelOp(_) |
            NumericInstruction::I64RelOp(_) |
            NumericInstruction::F32RelOp(_) |
            NumericInstruction::F64RelOp(_) => 2,
            
            // Conversion operations consume one operand
            NumericInstruction::I32ConversionOp(_) |
            NumericInstruction::I64ConversionOp(_) |
            NumericInstruction::F32ConversionOp(_) |
            NumericInstruction::F64ConversionOp(_) => 1,
            NumericInstruction::I32TestOp => 0,
            NumericInstruction::I64TestOp => 0,
        }
    }

    /// Returns the number of results produced by this instruction
    pub fn result_count(&self) -> usize {
        match self {
            // All numeric instructions produce exactly one result
            _ => 1,
        }
    }

    /// Returns the type of the result produced by this instruction
    pub fn result_type(&self) -> ValType {
        match self {
            NumericInstruction::I32Const(_) |
            NumericInstruction::I32UnOp(_) |
            NumericInstruction::I32BinOp(_) |
            NumericInstruction::I32RelOp(_) |
            NumericInstruction::I32TestOp |
            NumericInstruction::I32ConversionOp(_) => ValType::I32,
            
            NumericInstruction::I64Const(_) |
            NumericInstruction::I64UnOp(_) |
            NumericInstruction::I64BinOp(_) |
            NumericInstruction::I64RelOp(_) |
            NumericInstruction::I64TestOp |
            NumericInstruction::I64ConversionOp(_) => ValType::I64,
            
            NumericInstruction::F32Const(_) |
            NumericInstruction::F32UnOp(_) |
            NumericInstruction::F32BinOp(_) |
            NumericInstruction::F32RelOp(_) |
            NumericInstruction::F32ConversionOp(_) => ValType::F32,
            
            NumericInstruction::F64Const(_) |
            NumericInstruction::F64UnOp(_) |
            NumericInstruction::F64BinOp(_) |
            NumericInstruction::F64RelOp(_) |
            NumericInstruction::F64ConversionOp(_) => ValType::F64,
        }
    }
}

/// Vector shape for integer types
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IntVectorShape {
    /// 16 lanes of i8
    I8X16,
    /// 8 lanes of i16
    I16X8,
    /// 4 lanes of i32
    I32X4,
    /// 2 lanes of i64
    I64X2,
}

/// Vector shape for float types
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FloatVectorShape {
    /// 4 lanes of f32
    F32X4,
    /// 2 lanes of f64
    F64X2,
}

/// Vector shape
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VectorShape {
    /// Integer vector shape
    Int(IntVectorShape),
    /// Float vector shape
    Float(FloatVectorShape),
}

/// Vector half for extension operations
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VectorHalf {
    /// Lower half
    Low,
    /// Upper half
    High,
}

/// Vector unary operations for v128
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VectorVUnOp {
    /// Bitwise NOT
    Not,
}

/// Vector binary operations for v128
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VectorVBinOp {
    /// Bitwise AND
    And,
    /// Bitwise AND-NOT
    AndNot,
    /// Bitwise OR
    Or,
    /// Bitwise XOR
    Xor,
}

/// Vector ternary operations for v128
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VectorVTernOp {
    /// Bit select
    BitSelect,
}

/// Vector test operations for v128
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VectorVTestOp {
    /// Any true
    AnyTrue,
}

/// Vector test operations for integer vectors
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VectorIntTestOp {
    /// All true
    AllTrue,
}

/// Vector comparison operations for integer vectors
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VectorIntRelOp {
    /// Equal
    Eq,
    /// Not equal
    Ne,
    /// Less than (signed/unsigned)
    Lt { signed: bool },
    /// Greater than (signed/unsigned)
    Gt { signed: bool },
    /// Less than or equal (signed/unsigned)
    Le { signed: bool },
    /// Greater than or equal (signed/unsigned)
    Ge { signed: bool },
}

/// Vector comparison operations for float vectors
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VectorFloatRelOp {
    /// Equal
    Eq,
    /// Not equal
    Ne,
    /// Less than
    Lt,
    /// Greater than
    Gt,
    /// Less than or equal
    Le,
    /// Greater than or equal
    Ge,
}

/// Vector unary operations for integer vectors
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VectorIntUnOp {
    /// Absolute value
    Abs,
    /// Negation
    Neg,
}

/// Vector binary operations for integer vectors
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VectorIntBinOp {
    /// Addition
    Add,
    /// Subtraction
    Sub,
}

/// Vector min/max operations for integer vectors
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VectorIntMinMaxOp {
    /// Minimum (signed/unsigned)
    Min { signed: bool },
    /// Maximum (signed/unsigned)
    Max { signed: bool },
}

/// Vector saturating binary operations for integer vectors
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VectorIntSatBinOp {
    /// Saturating addition (signed/unsigned)
    AddSat { signed: bool },
    /// Saturating subtraction (signed/unsigned)
    SubSat { signed: bool },
}

/// Vector shift operations for integer vectors
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VectorIntShiftOp {
    /// Shift left
    Shl,
    /// Shift right (signed/unsigned)
    Shr { signed: bool },
}

/// Vector unary operations for float vectors
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VectorFloatUnOp {
    /// Absolute value
    Abs,
    /// Negation
    Neg,
    /// Square root
    Sqrt,
    /// Ceiling
    Ceil,
    /// Floor
    Floor,
    /// Truncate
    Trunc,
    /// Round to nearest
    Nearest,
}

/// Vector binary operations for float vectors
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VectorFloatBinOp {
    /// Addition
    Add,
    /// Subtraction
    Sub,
    /// Multiplication
    Mul,
    /// Division
    Div,
    /// Minimum
    Min,
    /// Maximum
    Max,
    /// Parallel minimum
    PMin,
    /// Parallel maximum
    PMax,
}

/// Vector instruction
#[derive(Debug, Clone, PartialEq)]
pub enum VectorInstruction {
    /// 128-bit vector constant
    V128Const(i128),
    /// Vector unary operation
    V128VUnOp(VectorVUnOp),
    /// Vector binary operation
    V128VBinOp(VectorVBinOp),
    /// Vector ternary operation
    V128VTernOp(VectorVTernOp),
    /// Vector test operation
    V128VTestOp(VectorVTestOp),
    /// Shuffle lanes (16 lane indices)
    I8X16Shuffle([u8; 16]),
    /// Swizzle lanes
    I8X16Swizzle,
    /// Splat value to all lanes
    Splat(VectorShape),
    /// Extract lane (signed/unsigned)
    ExtractLane {
        shape: VectorShape,
        lane: u8,
        signed: bool,
    },
    /// Replace lane
    ReplaceLane {
        shape: VectorShape,
        lane: u8,
    },
    /// Integer vector comparison
    IntRelOp {
        shape: IntVectorShape,
        op: VectorIntRelOp,
    },
    /// Float vector comparison
    FloatRelOp {
        shape: FloatVectorShape,
        op: VectorFloatRelOp,
    },
    /// Integer vector unary operation
    IntUnOp {
        shape: IntVectorShape,
        op: VectorIntUnOp,
    },
    /// Population count
    I8X16Popcnt,
    /// Q15 multiplication with rounding and saturation
    I16X8Q15MulrSatS,
    /// Dot product of i16x8 vectors
    I32X4DotI16X8S,
    /// Float vector unary operation
    FloatUnOp {
        shape: FloatVectorShape,
        op: VectorFloatUnOp,
    },
    /// Integer vector test operation
    IntTestOp {
        shape: IntVectorShape,
        op: VectorIntTestOp,
    },
    /// Bitmask
    Bitmask(IntVectorShape),
    /// Narrow integers
    Narrow {
        shape: IntVectorShape,
        signed: bool,
    },
    /// Extend half
    ExtendHalf {
        shape: IntVectorShape,
        half: VectorHalf,
        signed: bool,
    },
    /// Integer vector shift operation
    IntShiftOp {
        shape: IntVectorShape,
        op: VectorIntShiftOp,
    },
    /// Integer vector binary operation
    IntBinOp {
        shape: IntVectorShape,
        op: VectorIntBinOp,
    },
    /// Integer vector min/max operation
    IntMinMaxOp {
        shape: IntVectorShape,
        op: VectorIntMinMaxOp,
    },
    /// Integer vector saturating binary operation
    IntSatBinOp {
        shape: IntVectorShape,
        op: VectorIntSatBinOp,
    },
    /// Vector multiplication
    Mul(IntVectorShape),
    /// Average rounding
    AvgrU(IntVectorShape),
    /// Extended multiplication of half
    ExtMulHalf {
        shape: IntVectorShape,
        half: VectorHalf,
        signed: bool,
    },
    /// Extended addition of pairwise
    ExtAddPairwise {
        shape: IntVectorShape,
        signed: bool,
    },
    /// Float vector binary operation
    FloatBinOp {
        shape: FloatVectorShape,
        op: VectorFloatBinOp,
    },
    /// Truncate and saturate float to integer
    TruncSat {
        shape: IntVectorShape,
        signed: bool,
    },
    /// Convert integer to float
    Convert {
        shape: FloatVectorShape,
        signed: bool,
    },
    /// Demote float
    Demote(FloatVectorShape),
    /// Promote float
    Promote(FloatVectorShape),
    // Vector memory operations
    /// Load a 128-bit vector from memory
    V128Load { memarg: MemArg },
    /// Load 8x8 signed integers and extend to 16x8
    V128Load8x8S { memarg: MemArg },
    /// Load 8x8 unsigned integers and extend to 16x8
    V128Load8x8U { memarg: MemArg },
    /// Load 16x4 signed integers and extend to 32x4
    V128Load16x4S { memarg: MemArg },
    /// Load 16x4 unsigned integers and extend to 32x4
    V128Load16x4U { memarg: MemArg },
    /// Load 32x2 signed integers and extend to 64x2
    V128Load32x2S { memarg: MemArg },
    /// Load 32x2 unsigned integers and extend to 64x2
    V128Load32x2U { memarg: MemArg },
    /// Load 8-bit integer and splat to all lanes
    V128Load8Splat { memarg: MemArg },
    /// Load 16-bit integer and splat to all lanes
    V128Load16Splat { memarg: MemArg },
    /// Load 32-bit integer and splat to all lanes
    V128Load32Splat { memarg: MemArg },
    /// Load 64-bit integer and splat to all lanes
    V128Load64Splat { memarg: MemArg },
    /// Load 32-bit integer and zero-extend to 128-bit vector
    V128Load32Zero { memarg: MemArg },
    /// Load 64-bit integer and zero-extend to 128-bit vector
    V128Load64Zero { memarg: MemArg },
    /// Store a 128-bit vector to memory
    V128Store { memarg: MemArg },
    /// Load 8-bit integer into a specific lane
    V128Load8Lane { memarg: MemArg, lane: u8 },
    /// Load 16-bit integer into a specific lane
    V128Load16Lane { memarg: MemArg, lane: u8 },
    /// Load 32-bit integer into a specific lane
    V128Load32Lane { memarg: MemArg, lane: u8 },
    /// Load 64-bit integer into a specific lane
    V128Load64Lane { memarg: MemArg, lane: u8 },
    /// Store 8-bit integer from a specific lane
    V128Store8Lane { memarg: MemArg, lane: u8 },
    /// Store 16-bit integer from a specific lane
    V128Store16Lane { memarg: MemArg, lane: u8 },
    /// Store 32-bit integer from a specific lane
    V128Store32Lane { memarg: MemArg, lane: u8 },
    /// Store 64-bit integer from a specific lane
    V128Store64Lane { memarg: MemArg, lane: u8 },
}

impl VectorInstruction {
    /// Returns the number of operands consumed by this instruction
    pub fn operand_count(&self) -> usize {
        match self {
            // Vector constants
            VectorInstruction::V128Const(_) => 0,
            // Vector unary operations
            VectorInstruction::V128VUnOp(_) => 1,
            // Vector binary operations
            VectorInstruction::V128VBinOp(_) => 2,
            // Vector ternary operations
            VectorInstruction::V128VTernOp(_) => 3,
            // Vector test operations
            VectorInstruction::V128VTestOp(_) => 1,
            // Vector shuffle and swizzle
            VectorInstruction::I8X16Shuffle(_) => 2,
            VectorInstruction::I8X16Swizzle => 2,
            // Vector splat
            VectorInstruction::Splat(_) => 1,
            // Vector lane operations
            VectorInstruction::ExtractLane { .. } => 1,
            VectorInstruction::ReplaceLane { .. } => 2,
            // Vector comparisons
            VectorInstruction::IntRelOp { .. } => 2,
            VectorInstruction::FloatRelOp { .. } => 2,
            // Vector unary operations
            VectorInstruction::IntUnOp { .. } => 1,
            VectorInstruction::I8X16Popcnt => 1,
            VectorInstruction::I16X8Q15MulrSatS => 2,
            VectorInstruction::I32X4DotI16X8S => 2,
            VectorInstruction::FloatUnOp { .. } => 1,
            // Vector test operations
            VectorInstruction::IntTestOp { .. } => 1,
            VectorInstruction::Bitmask(_) => 1,
            // Vector narrowing and extension
            VectorInstruction::Narrow { .. } => 2,
            VectorInstruction::ExtendHalf { .. } => 1,
            // Vector shift operations
            VectorInstruction::IntShiftOp { .. } => 2,
            // Vector binary operations
            VectorInstruction::IntBinOp { .. } => 2,
            VectorInstruction::IntMinMaxOp { .. } => 2,
            VectorInstruction::IntSatBinOp { .. } => 2,
            VectorInstruction::Mul(_) => 2,
            VectorInstruction::AvgrU(_) => 2,
            VectorInstruction::ExtMulHalf { .. } => 2,
            VectorInstruction::ExtAddPairwise { .. } => 1,
            VectorInstruction::FloatBinOp { .. } => 2,
            // Vector conversions
            VectorInstruction::TruncSat { .. } => 1,
            VectorInstruction::Convert { .. } => 1,
            VectorInstruction::Demote(_) => 1,
            VectorInstruction::Promote(_) => 1,
            // Vector memory operations
            VectorInstruction::V128Load { .. } => 1, // memory index
            VectorInstruction::V128Load8x8S { .. } => 1,
            VectorInstruction::V128Load8x8U { .. } => 1,
            VectorInstruction::V128Load16x4S { .. } => 1,
            VectorInstruction::V128Load16x4U { .. } => 1,
            VectorInstruction::V128Load32x2S { .. } => 1,
            VectorInstruction::V128Load32x2U { .. } => 1,
            VectorInstruction::V128Load8Splat { .. } => 1,
            VectorInstruction::V128Load16Splat { .. } => 1,
            VectorInstruction::V128Load32Splat { .. } => 1,
            VectorInstruction::V128Load64Splat { .. } => 1,
            VectorInstruction::V128Load32Zero { .. } => 1,
            VectorInstruction::V128Load64Zero { .. } => 1,
            VectorInstruction::V128Store { .. } => 2, // memory index and vector value
            VectorInstruction::V128Load8Lane { .. } => 2, // memory index and vector value
            VectorInstruction::V128Load16Lane { .. } => 2,
            VectorInstruction::V128Load32Lane { .. } => 2,
            VectorInstruction::V128Load64Lane { .. } => 2,
            VectorInstruction::V128Store8Lane { .. } => 2,
            VectorInstruction::V128Store16Lane { .. } => 2,
            VectorInstruction::V128Store32Lane { .. } => 2,
            VectorInstruction::V128Store64Lane { .. } => 2,
        }
    }

    /// Returns the number of results produced by this instruction
    pub fn result_count(&self) -> usize {
        match self {
            // Most vector instructions produce one v128 result
            _ => 1,
        }
    }

    /// Returns the type of the result produced by this instruction
    pub fn result_type(&self) -> ValType {
        match self {
            // All vector instructions produce a v128 result
            _ => ValType::V128,
        }
    }
}

/// Parametric instruction
#[derive(Debug, Clone, PartialEq)]
pub enum ParametricInstruction {
    /// Drop the top operand from the stack
    Drop,
    /// Select one of two operands based on a condition
    /// 
    /// The optional value type determines the type of the operands.
    /// If missing, the operands must be of numeric or vector type.
    Select(Option<ValType>),
}

impl ParametricInstruction {
    /// Returns the number of operands consumed by this instruction
    pub fn operand_count(&self) -> usize {
        match self {
            // Drop consumes one operand
            ParametricInstruction::Drop => 1,
            // Select consumes three operands (two values and a condition)
            ParametricInstruction::Select(_) => 3,
        }
    }

    /// Returns the number of results produced by this instruction
    pub fn result_count(&self) -> usize {
        match self {
            // Drop produces no results
            ParametricInstruction::Drop => 0,
            // Select produces one result (the selected value)
            ParametricInstruction::Select(_) => 1,
        }
    }

    /// Returns the type of the result produced by this instruction
    /// 
    /// For Select, returns the type of the selected value.
    /// If operand_type is Some, returns that type.
    /// If operand_type is None, the type is determined at runtime.
    pub fn result_type(&self) -> Option<ValType> {
        match self {
            ParametricInstruction::Drop => None,
            ParametricInstruction::Select(operand_type) => *operand_type,
        }
    }
}

impl fmt::Display for ParametricInstruction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Drop => write!(f, "drop"),
            Self::Select(operand_type) => {
                write!(f, "select")?;
                if let Some(ty) = operand_type {
                    write!(f, " {}", ty)?;
                }
                Ok(())
            }
        }
    }
}

/// Memory argument for load/store instructions
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct MemArg {
    /// Static address offset
    pub offset: u32,
    /// Alignment (as the exponent of a power of 2)
    pub align: u32,
}

/// Memory instruction
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum MemoryInstruction {
    // Integer loads
    I32Load { memarg: MemArg },
    I64Load { memarg: MemArg },
    // Float loads
    F32Load { memarg: MemArg },
    F64Load { memarg: MemArg },
    // Integer stores
    I32Store { memarg: MemArg },
    I64Store { memarg: MemArg },
    // Float stores
    F32Store { memarg: MemArg },
    F64Store { memarg: MemArg },
    // Integer loads with sign extension
    I32Load8S { memarg: MemArg },
    I32Load8U { memarg: MemArg },
    I32Load16S { memarg: MemArg },
    I32Load16U { memarg: MemArg },
    I64Load8S { memarg: MemArg },
    I64Load8U { memarg: MemArg },
    I64Load16S { memarg: MemArg },
    I64Load16U { memarg: MemArg },
    I64Load32S { memarg: MemArg },
    I64Load32U { memarg: MemArg },
    // Integer stores with reduced width
    I32Store8 { memarg: MemArg },
    I32Store16 { memarg: MemArg },
    I64Store8 { memarg: MemArg },
    I64Store16 { memarg: MemArg },
    I64Store32 { memarg: MemArg },
    // Memory management
    MemorySize,
    MemoryGrow,
    MemoryFill,
    MemoryCopy,
    MemoryInit { data_index: u32 },
    DataDrop { data_index: u32 },
}

impl MemoryInstruction {
    /// Returns the number of operands consumed by this instruction
    pub fn operand_count(&self) -> usize {
        use MemoryInstruction::*;
        match self {
            // Loads: address operand
            I32Load { .. } | I64Load { .. } | F32Load { .. } | F64Load { .. } |
            I32Load8S { .. } | I32Load8U { .. } | I32Load16S { .. } | I32Load16U { .. } |
            I64Load8S { .. } | I64Load8U { .. } | I64Load16S { .. } | I64Load16U { .. } |
            I64Load32S { .. } | I64Load32U { .. } |
            // Stores: address and value
            I32Store { .. } | I64Store { .. } | F32Store { .. } | F64Store { .. } |
            I32Store8 { .. } | I32Store16 { .. } | I64Store8 { .. } | I64Store16 { .. } | I64Store32 { .. } => 2,
            // Memory management
            MemorySize => 0,
            MemoryGrow => 1,
            MemoryFill => 3,
            MemoryCopy => 3,
            MemoryInit { .. } => 3,
            DataDrop { .. } => 0,
        }
    }

    /// Returns the number of results produced by this instruction
    pub fn result_count(&self) -> usize {
        use MemoryInstruction::*;
        match self {
            // Loads produce one result
            I32Load { .. } | I64Load { .. } | F32Load { .. } | F64Load { .. } |
            I32Load8S { .. } | I32Load8U { .. } | I32Load16S { .. } | I32Load16U { .. } |
            I64Load8S { .. } | I64Load8U { .. } | I64Load16S { .. } | I64Load16U { .. } |
            I64Load32S { .. } | I64Load32U { .. } |
            // MemorySize and MemoryGrow produce one result
            MemorySize | MemoryGrow => 1,
            // Stores and other memory management produce no result
            I32Store { .. } | I64Store { .. } | F32Store { .. } | F64Store { .. } |
            I32Store8 { .. } | I32Store16 { .. } | I64Store8 { .. } | I64Store16 { .. } | I64Store32 { .. } |
            MemoryFill | MemoryCopy | MemoryInit { .. } | DataDrop { .. } => 0,
        }
    }

    /// Returns the type of the result produced by this instruction
    pub fn result_type(&self) -> Option<ValType> {
        use MemoryInstruction::*;
        match self {
            // Integer loads
            I32Load { .. } | I32Load8S { .. } | I32Load8U { .. } | I32Load16S { .. } | I32Load16U { .. } => Some(ValType::I32),
            I64Load { .. } | I64Load8S { .. } | I64Load8U { .. } | I64Load16S { .. } | I64Load16U { .. } | I64Load32S { .. } | I64Load32U { .. } => Some(ValType::I64),
            // Float loads
            F32Load { .. } => Some(ValType::F32),
            F64Load { .. } => Some(ValType::F64),
            // MemorySize and MemoryGrow produce i32
            MemorySize | MemoryGrow => Some(ValType::I32),
            // Stores and other memory management produce no result
            I32Store { .. } | I64Store { .. } | F32Store { .. } | F64Store { .. } |
            I32Store8 { .. } | I32Store16 { .. } | I64Store8 { .. } | I64Store16 { .. } | I64Store32 { .. } |
            MemoryFill | MemoryCopy | MemoryInit { .. } | DataDrop { .. } => None,
        }
    }
} 

/// Block type for structured control instructions
#[derive(Debug, Clone, PartialEq)]
pub enum BlockType {
    /// Type index referring to a function type
    TypeIndex(u32),
    /// Optional value type (shorthand for [] -> [valtype?])
    ValueType(Option<ValType>),
}

/// Control instruction
#[derive(Debug, Clone, PartialEq)]
pub enum ControlInstruction {
    /// No operation
    Nop,
    /// Unconditional trap
    Unreachable,
    /// Block of instructions with a block type
    Block {
        /// The block type
        block_type: BlockType,
        /// The instructions in the block
        instructions: Vec<Instruction>,
    },
    /// Loop with a block type
    Loop {
        /// The block type
        block_type: BlockType,
        /// The instructions in the loop
        instructions: Vec<Instruction>,
    },
    /// Conditional branch with a block type
    If {
        /// The block type
        block_type: BlockType,
        /// The instructions in the true branch
        true_instructions: Vec<Instruction>,
        /// The instructions in the false branch
        false_instructions: Vec<Instruction>,
    },
    /// Unconditional branch to a label
    Br {
        /// The label index (relative by nesting depth)
        label_index: u32,
    },
    /// Conditional branch to a label
    BrIf {
        /// The label index (relative by nesting depth)
        label_index: u32,
    },
    /// Indirect branch through a table of labels
    BrTable {
        /// The vector of label indices
        label_indices: Vec<u32>,
        /// The default label index
        default_index: u32,
    },
    /// Return from the current function
    Return,
    /// Call a function directly
    Call {
        /// The function index
        function_index: u32,
    },
    /// Call a function indirectly through a table
    CallIndirect {
        /// The table index
        table_index: u32,
        /// The type index of the expected function type
        type_index: u32,
    },
    /// End of a block, loop, or if instruction
    /// 
    /// # Specification
    /// 
    /// The `end` instruction marks the end of a block, loop, or if instruction.
    /// It is used to terminate the instruction sequence within these control structures.
    /// 
    /// # Examples
    /// 
    /// ```
    /// // End of a block
    /// block
    ///   i32.const 1
    /// end
    /// ```
    End,

    /// Else clause of an if instruction
    /// 
    /// # Specification
    /// 
    /// The `else` instruction marks the beginning of the else clause in an if instruction.
    /// This variant is used for error recovery during parsing when an else instruction
    /// is encountered outside of an if block.
    /// 
    /// # Examples
    /// 
    /// ```
    /// // Else clause in an if instruction
    /// if
    ///   i32.const 1
    /// else
    ///   i32.const 0
    /// end
    /// ```
    Else,
}

impl ControlInstruction {
    /// Returns the number of operands consumed by this instruction
    pub fn operand_count(&self) -> usize {
        use ControlInstruction::*;
        match self {
            // No operands
            Nop | Unreachable | Return => 0,
            // One operand (condition)
            BrIf { .. } => 1,
            // One operand (table index)
            BrTable { .. } => 1,
            // One operand (function index)
            Call { .. } => 0, // Operands are determined by the function type
            // Two operands (table index and function index)
            CallIndirect { .. } => 1, // Table index is an operand
            // No operands (branch targets are immediate)
            Br { .. } => 0,
            // No operands (block type is immediate)
            Block { .. } | Loop { .. } | If { .. } => 0,
            // No operands
            End | Else => 0,
        }
    }

    /// Returns the number of results produced by this instruction
    pub fn result_count(&self) -> usize {
        use ControlInstruction::*;
        match self {
            // No results
            Nop | Unreachable | Return | Br { .. } | BrIf { .. } | BrTable { .. } => 0,
            // Results are determined by the block type
            Block { block_type, .. } | Loop { block_type, .. } | If { block_type, .. } => {
                match block_type {
                    BlockType::TypeIndex(_) => 0, // TODO: Look up function type
                    BlockType::ValueType(Some(_)) => 1,
                    BlockType::ValueType(None) => 0,
                }
            }
            // Results are determined by the function type
            Call { .. } | CallIndirect { .. } => 0, // TODO: Look up function type
            // No results
            End | Else => 0,
        }
    }

    /// Returns the type of the result produced by this instruction
    pub fn result_type(&self) -> Option<ValType> {
        use ControlInstruction::*;
        match self {
            // No results
            Nop | Unreachable | Return | Br { .. } | BrIf { .. } | BrTable { .. } => None,
            // Results are determined by the block type
            Block { block_type, .. } | Loop { block_type, .. } | If { block_type, .. } => {
                match block_type {
                    BlockType::TypeIndex(_) => None, // TODO: Look up function type
                    BlockType::ValueType(ty) => *ty,
                    BlockType::ValueType(None) => None,
                }
            }
            // Results are determined by the function type
            Call { .. } | CallIndirect { .. } => None, // TODO: Look up function type
            // No results
            End | Else => None,
        }
    }
}

/// WebAssembly instruction
#[derive(Debug, Clone, PartialEq)]
pub enum Instruction {
    /// Numeric instruction
    Numeric(NumericInstruction),
    /// Vector instruction
    Vector(VectorInstruction),
    /// Parametric instruction
    Parametric(ParametricInstruction),
    /// Memory instruction
    Memory(MemoryInstruction),
    /// Table instruction
    Table(TableInstruction),
    /// Variable instruction
    Variable(VariableInstruction),
    /// Reference instruction
    Reference(ReferenceInstruction),
    /// Control instruction
    Control(ControlInstruction),
    /// Administrative instruction
    Administrative(AdministrativeInstruction),
}

impl Instruction {
    /// Returns the number of operands required by this instruction
    pub fn operand_count(&self) -> usize {
        match self {
            Self::Numeric(instr) => instr.operand_count(),
            Self::Vector(instr) => instr.operand_count(),
            Self::Parametric(instr) => instr.operand_count(),
            Self::Memory(instr) => instr.operand_count(),
            Self::Table(instr) => instr.operand_count(),
            Self::Variable(instr) => instr.operand_count(),
            Self::Reference(instr) => instr.operand_count(),
            Self::Control(instr) => instr.operand_count(),
            Self::Administrative(instr) => match instr {
                AdministrativeInstruction::Trap => 0,
                AdministrativeInstruction::Ref(_) => 0,
                AdministrativeInstruction::RefExtern(_) => 0,
                AdministrativeInstruction::Invoke(_) => 0,
                AdministrativeInstruction::Label { .. } => 0,
                AdministrativeInstruction::Frame { .. } => 0,
                AdministrativeInstruction::Value(_) => 0,
            },
        }
    }

    /// Returns the number of results produced by this instruction
    pub fn result_count(&self) -> usize {
        match self {
            Self::Numeric(instr) => instr.result_count(),
            Self::Vector(instr) => instr.result_count(),
            Self::Parametric(instr) => instr.result_count(),
            Self::Memory(instr) => instr.result_count(),
            Self::Table(instr) => instr.result_count(),
            Self::Variable(instr) => instr.result_count(),
            Self::Reference(instr) => instr.result_count(),
            Self::Control(instr) => instr.result_count(),
            Self::Administrative(instr) => match instr {
                AdministrativeInstruction::Trap => 0,
                AdministrativeInstruction::Ref(_) => 1,
                AdministrativeInstruction::RefExtern(_) => 1,
                AdministrativeInstruction::Invoke(_) => 0,
                AdministrativeInstruction::Label { arity, .. } => *arity,
                AdministrativeInstruction::Frame { arity, .. } => *arity,
                AdministrativeInstruction::Value(_) => 1,
            },
        }
    }

    /// Returns the result type of this instruction, if any
    pub fn result_type(&self) -> Option<ValType> {
        match self {
            Self::Numeric(instr) => Some(instr.result_type()),
            Self::Vector(instr) => Some(instr.result_type()),
            Self::Parametric(instr) => instr.result_type(),
            Self::Memory(instr) => instr.result_type(),
            Self::Table(instr) => instr.result_type(),
            Self::Variable(instr) => instr.result_type(),
            Self::Reference(instr) => instr.result_type(),
            Self::Control(instr) => instr.result_type(),
            Self::Administrative(instr) => match instr {
                AdministrativeInstruction::Trap => None,
                AdministrativeInstruction::Ref(_) => Some(ValType::FuncRef),
                AdministrativeInstruction::RefExtern(_) => Some(ValType::ExternRef),
                AdministrativeInstruction::Invoke(_) => None,
                AdministrativeInstruction::Label { .. } => None,
                AdministrativeInstruction::Frame { .. } => None,
                AdministrativeInstruction::Value(value) => Some(value.value_type().to_val_type()),
            },
        }
    }
}

impl fmt::Display for Instruction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Numeric(instr) => write!(f, "{:?}", instr),
            Self::Vector(instr) => write!(f, "{:?}", instr),
            Self::Parametric(instr) => write!(f, "{}", instr),
            Self::Memory(instr) => write!(f, "{:?}", instr),
            Self::Table(instr) => write!(f, "{}", instr),
            Self::Variable(instr) => write!(f, "{}", instr),
            Self::Reference(instr) => write!(f, "{}", instr),
            Self::Control(instr) => write!(f, "{:?}", instr),
            Self::Administrative(instr) => write!(f, "{:?}", instr),
        }
    }
}

/// WebAssembly expression
/// 
/// An expression is a sequence of instructions terminated by an end marker.
/// Expressions are used in function bodies, initialization values for globals,
/// elements and offsets of element segments, and offsets of data segments.
#[derive(Debug, Clone, PartialEq)]
pub enum Expression {
    /// A constant expression
    /// 
    /// Used for initialization values for globals,
    /// elements and offsets of element segments, and offsets of data segments.
    Constant {
        /// The original constant expression
        expr: ConstExpr,
        /// The converted instruction
        instruction: Instruction,
    },
    /// A general expression (sequence of instructions)
    General {
        /// The sequence of instructions in the expression
        instructions: Vec<Instruction>,
    },
}

impl Expression {
    /// Creates a new constant expression
    pub fn constant(expr: ConstExpr) -> Self {
        // Convert ConstExpr to a single instruction
        let instruction = match &expr {
            ConstExpr::Const(ty, _) => match ty {
                ValType::I32 => Instruction::Numeric(NumericInstruction::I32Const(0)),
                ValType::I64 => Instruction::Numeric(NumericInstruction::I64Const(0)),
                ValType::F32 => Instruction::Numeric(NumericInstruction::F32Const(0.0)),
                ValType::F64 => Instruction::Numeric(NumericInstruction::F64Const(0.0)),
                _ => panic!("Unsupported constant type"),
            },
            ConstExpr::GlobalGet(idx) => Instruction::Variable(VariableInstruction::GlobalGet(*idx)),
            ConstExpr::RefFunc(idx) => Instruction::Reference(ReferenceInstruction::RefFunc(*idx)),
            ConstExpr::RefNull(ty) => Instruction::Reference(ReferenceInstruction::RefNull(*ty)),
        };
        Self::Constant { expr, instruction }
    }

    /// Creates a new general expression with the given instructions
    pub fn general(instructions: Vec<Instruction>) -> Self {
        Self::General { instructions }
    }

    /// Returns whether this is a constant expression
    pub fn is_constant(&self) -> bool {
        matches!(self, Self::Constant { .. })
    }

    /// Returns whether this expression is empty
    pub fn is_empty(&self) -> bool {
        match self {
            Self::Constant { .. } => false,
            Self::General { instructions } => instructions.is_empty(),
        }
    }

    /// Returns the number of instructions in the expression
    pub fn instruction_count(&self) -> usize {
        match self {
            Self::Constant { .. } => 1,
            Self::General { instructions } => instructions.len(),
        }
    }

    /// Returns an iterator over the instructions in the expression
    pub fn instructions(&self) -> ExpressionIter<'_> {
        match self {
            Self::Constant { instruction, .. } => ExpressionIter::Constant(Some(instruction)),
            Self::General { instructions } => ExpressionIter::General(instructions.iter()),
        }
    }

    /// Returns the type of the result produced by this expression
    pub fn result_type(&self) -> Option<ValType> {
        match self {
            Self::Constant { expr, .. } => Some(expr.result_type()),
            Self::General { instructions } => instructions.last().and_then(|instr| instr.result_type()),
        }
    }
}

impl fmt::Display for Expression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Constant { expr, .. } => write!(f, "{}", expr),
            Self::General { instructions } => {
                for (i, instr) in instructions.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{:?}", instr)?;
                }
                Ok(())
            }
        }
    }
}

/// Iterator over instructions in an expression
pub enum ExpressionIter<'a> {
    /// Iterator for a constant expression
    Constant(Option<&'a Instruction>),
    /// Iterator for a general expression
    General(core::slice::Iter<'a, Instruction>),
}

impl<'a> Iterator for ExpressionIter<'a> {
    type Item = &'a Instruction;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Constant(instr) => instr.take(),
            Self::General(iter) => iter.next(),
        }
    }
}

/// Table instructions for manipulating tables and element segments
#[derive(Debug, Clone, PartialEq)]
pub enum TableInstruction {
    /// Get an element from a table
    Get(u32),
    /// Store an element in a table
    Set(u32),
    /// Get the current size of a table
    Size(u32),
    /// Grow a table by a given delta
    Grow(u32),
    /// Fill a range of a table with a value
    Fill(u32),
    /// Copy elements between tables
    Copy {
        /// The destination table index
        dst_table: u32,
        /// The source table index
        src_table: u32,
    },
    /// Initialize a table from an element segment
    Init {
        /// The table index
        table_index: u32,
        /// The element segment index
        elem_index: u32,
    },
    /// Drop an element segment
    ElemDrop(u32),
}

impl TableInstruction {
    /// Returns the number of operands required by this instruction
    pub fn operand_count(&self) -> usize {
        match self {
            Self::Get(_) => 1, // index
            Self::Set(_) => 2, // index + value
            Self::Size(_) => 0,
            Self::Grow(_) => 2, // delta + init value
            Self::Fill(_) => 3, // start + value + length
            Self::Copy { .. } => 3, // dst index + src index + length
            Self::Init { .. } => 3, // dst index + src index + length
            Self::ElemDrop(_) => 0,
        }
    }

    /// Returns the number of results produced by this instruction
    pub fn result_count(&self) -> usize {
        match self {
            Self::Get(_) => 1, // element
            Self::Set(_) => 0,
            Self::Size(_) => 1, // size
            Self::Grow(_) => 1, // previous size or -1
            Self::Fill(_) => 0,
            Self::Copy { .. } => 0,
            Self::Init { .. } => 0,
            Self::ElemDrop(_) => 0,
        }
    }

    /// Returns the result type of this instruction, if any
    pub fn result_type(&self) -> Option<ValType> {
        match self {
            Self::Get(_) => Some(ValType::FuncRef), // TODO: Get actual table element type
            Self::Set(_) => None,
            Self::Size(_) => Some(ValType::I32),
            Self::Grow(_) => Some(ValType::I32),
            Self::Fill(_) => None,
            Self::Copy { .. } => None,
            Self::Init { .. } => None,
            Self::ElemDrop(_) => None,
        }
    }
}

impl fmt::Display for TableInstruction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Get(idx) => write!(f, "table.get {}", idx),
            Self::Set(idx) => write!(f, "table.set {}", idx),
            Self::Size(idx) => write!(f, "table.size {}", idx),
            Self::Grow(idx) => write!(f, "table.grow {}", idx),
            Self::Fill(idx) => write!(f, "table.fill {}", idx),
            Self::Copy { dst_table, src_table } => write!(f, "table.copy {} {}", dst_table, src_table),
            Self::Init { table_index, elem_index } => write!(f, "table.init {} {}", table_index, elem_index),
            Self::ElemDrop(idx) => write!(f, "elem.drop {}", idx),
        }
    }
}

/// Variable instructions for accessing local and global variables
#[derive(Debug, Clone, PartialEq)]
pub enum VariableInstruction {
    /// Get the value of a local variable
    /// 
    /// # Specification
    /// 
    /// The `local.get` instruction pushes the value of a local variable onto the stack.
    /// The local index must be valid.
    /// 
    /// # Examples
    /// 
    /// ```
    /// // Get the value of local variable 0
    /// local.get 0
    /// ```
    LocalGet(u32),

    /// Set the value of a local variable
    /// 
    /// # Specification
    /// 
    /// The `local.set` instruction pops a value from the stack and stores it in a local variable.
    /// The local index must be valid.
    /// 
    /// # Examples
    /// 
    /// ```
    /// // Set local variable 0 to the value on top of the stack
    /// local.set 0
    /// ```
    LocalSet(u32),

    /// Set the value of a local variable and keep the value on the stack
    /// 
    /// # Specification
    /// 
    /// The `local.tee` instruction is like `local.set` but also keeps the value on the stack.
    /// This is equivalent to a `local.set` followed by a `local.get` of the same index.
    /// 
    /// # Examples
    /// 
    /// ```
    /// // Set local variable 0 and keep the value on the stack
    /// local.tee 0
    /// ```
    LocalTee(u32),

    /// Get the value of a global variable
    /// 
    /// # Specification
    /// 
    /// The `global.get` instruction pushes the value of a global variable onto the stack.
    /// The global index must be valid.
    /// 
    /// # Examples
    /// 
    /// ```
    /// // Get the value of global variable 0
    /// global.get 0
    /// ```
    GlobalGet(u32),

    /// Set the value of a global variable
    /// 
    /// # Specification
    /// 
    /// The `global.set` instruction pops a value from the stack and stores it in a global variable.
    /// The global index must be valid and the global must be mutable.
    /// 
    /// # Examples
    /// 
    /// ```
    /// // Set global variable 0 to the value on top of the stack
    /// global.set 0
    /// ```
    GlobalSet(u32),
}

impl VariableInstruction {
    /// Returns the number of operands required by this instruction
    pub fn operand_count(&self) -> usize {
        match self {
            Self::LocalGet(_) => 0,
            Self::LocalSet(_) => 1,
            Self::LocalTee(_) => 1,
            Self::GlobalGet(_) => 0,
            Self::GlobalSet(_) => 1,
        }
    }

    /// Returns the number of results produced by this instruction
    pub fn result_count(&self) -> usize {
        match self {
            Self::LocalGet(_) => 1,
            Self::LocalSet(_) => 0,
            Self::LocalTee(_) => 1,
            Self::GlobalGet(_) => 1,
            Self::GlobalSet(_) => 0,
        }
    }

    /// Returns the result type of this instruction, if any
    /// 
    /// Note: The actual result type depends on the type of the variable being accessed.
    /// This method returns None as the type information is not available at this level.
    pub fn result_type(&self) -> Option<ValType> {
        None // Type information is not available at this level
    }
}

impl fmt::Display for VariableInstruction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::LocalGet(idx) => write!(f, "local.get {}", idx),
            Self::LocalSet(idx) => write!(f, "local.set {}", idx),
            Self::LocalTee(idx) => write!(f, "local.tee {}", idx),
            Self::GlobalGet(idx) => write!(f, "global.get {}", idx),
            Self::GlobalSet(idx) => write!(f, "global.set {}", idx),
        }
    }
}

/// Administrative instruction
/// 
/// Administrative instructions are used to express the reduction of traps,
/// calls, and control instructions in the formal notation.
#[derive(Debug, Clone, PartialEq)]
pub enum AdministrativeInstruction {
    /// Represents the occurrence of a trap
    Trap,
    /// Represents a function reference value
    Ref(FuncAddr),
    /// Represents an external reference value
    RefExtern(ExternAddr),
    /// Represents the imminent invocation of a function instance
    Invoke(FuncAddr),
    /// Represents a label on the stack
    Label {
        /// The arity of the label
        arity: usize,
        /// The instructions in the label
        instructions: Vec<Instruction>,
    },
    /// Represents a frame on the stack
    Frame {
        /// The arity of the frame
        arity: usize,
        /// The frame state
        state: FrameState,
        /// The instructions in the frame
        instructions: Vec<Instruction>,
    },
    /// Represents a value in an evaluation context
    Value(crate::wasm::runtime::Value),
}

impl fmt::Display for AdministrativeInstruction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Trap => write!(f, "trap"),
            Self::Ref(addr) => write!(f, "ref {}", addr),
            Self::RefExtern(addr) => write!(f, "ref.extern {}", addr),
            Self::Invoke(addr) => write!(f, "invoke {}", addr),
            Self::Label { arity, instructions } => {
                write!(f, "label{} {{ ", arity)?;
                for (i, instr) in instructions.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{}", instr)?;
                }
                write!(f, " }}")
            }
            Self::Frame { arity, state, instructions } => {
                write!(f, "frame{} {{ {} ", arity, state)?;
                for (i, instr) in instructions.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{}", instr)?;
                }
                write!(f, " }}")
            }
            Self::Value(value) => write!(f, "{}", value),
        }
    }
}

/// Reference instruction
/// 
/// Reference instructions are used to create and manipulate references.
#[derive(Debug, Clone, PartialEq)]
pub enum ReferenceInstruction {
    /// Create a null reference of the given reference type
    /// 
    /// # Specification
    /// 
    /// The `ref.null` instruction creates a null reference of the given reference type.
    /// The type must be a reference type (funcref or externref).
    /// 
    /// # Examples
    /// 
    /// ```
    /// // Create a null function reference
    /// ref.null funcref
    /// 
    /// // Create a null external reference
    /// ref.null externref
    /// ```
    RefNull(ValType),

    /// Check if a reference is null
    /// 
    /// # Specification
    /// 
    /// The `ref.is_null` instruction checks if a reference is null.
    /// It pops a reference from the stack and pushes an i32 value:
    /// 1 if the reference is null, 0 otherwise.
    /// 
    /// # Examples
    /// 
    /// ```
    /// // Check if a function reference is null
    /// ref.is_null
    /// ```
    RefIsNull,

    /// Create a reference to a function
    /// 
    /// # Specification
    /// 
    /// The `ref.func` instruction creates a reference to a function.
    /// The function index must be valid.
    /// 
    /// # Examples
    /// 
    /// ```
    /// // Create a reference to function 0
    /// ref.func 0
    /// ```
    RefFunc(u32),
}

impl ReferenceInstruction {
    /// Returns the number of operands consumed by this instruction
    pub fn operand_count(&self) -> usize {
        match self {
            Self::RefNull(_) => 0,
            Self::RefIsNull => 1,
            Self::RefFunc(_) => 0,
        }
    }

    /// Returns the number of results produced by this instruction
    pub fn result_count(&self) -> usize {
        match self {
            Self::RefNull(_) => 1,
            Self::RefIsNull => 1,
            Self::RefFunc(_) => 1,
        }
    }

    /// Returns the type of the result produced by this instruction
    pub fn result_type(&self) -> Option<ValType> {
        match self {
            Self::RefNull(ty) => Some(*ty),
            Self::RefIsNull => Some(ValType::I32),
            Self::RefFunc(_) => Some(ValType::FuncRef),
        }
    }
}

impl fmt::Display for ReferenceInstruction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::RefNull(ty) => write!(f, "ref.null {}", ty),
            Self::RefIsNull => write!(f, "ref.is_null"),
            Self::RefFunc(idx) => write!(f, "ref.func {}", idx),
        }
    }
}
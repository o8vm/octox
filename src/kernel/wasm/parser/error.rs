//! Error types for WebAssembly binary parser

use core::fmt;
use core::result;
use alloc::string::String;

/// Error type for WebAssembly binary parsing
#[derive(Debug, Clone, PartialEq)]
pub enum ParseError {
    /// End of input reached unexpectedly
    UnexpectedEof,
    /// Invalid magic number (must be "\0asm")
    InvalidMagic,
    /// Invalid version number
    InvalidVersion,
    /// Invalid section ID
    InvalidSectionId,
    /// Invalid section size
    InvalidSectionSize,
    /// Invalid type code
    InvalidTypeCode,
    /// Invalid value type
    InvalidValueType,
    /// Invalid function type
    InvalidFunctionType,
    /// Invalid import/export kind
    InvalidExternalKind,
    /// Invalid memory limits
    InvalidLimits,
    /// Invalid table type
    InvalidTableType,
    /// Invalid global type
    InvalidGlobalType,
    /// Invalid instruction
    InvalidInstruction,
    /// Invalid constant expression
    InvalidConstExpr,
    /// Invalid UTF-8 string
    InvalidUtf8,
    /// Invalid integer encoding (LEB128)
    InvalidIntegerEncoding,
    /// Invalid float encoding
    InvalidFloatEncoding,
    /// Invalid vector encoding
    InvalidVectorEncoding,
    /// Invalid alignment
    InvalidAlignment,
    /// Invalid memory index
    InvalidMemoryIndex,
    /// Invalid table index
    InvalidTableIndex,
    /// Invalid function index
    InvalidFunctionIndex,
    /// Invalid global index
    InvalidGlobalIndex,
    /// Invalid local index
    InvalidLocalIndex,
    /// Invalid label index
    InvalidLabelIndex,
    /// Invalid type index
    InvalidTypeIndex,
    /// Invalid data segment
    InvalidDataSegment,
    /// Invalid element segment
    InvalidElementSegment,
    /// Invalid start function
    InvalidStartFunction,
    /// Invalid export
    InvalidExport,
    /// Invalid import
    InvalidImport,
    /// Invalid function
    InvalidFunction,
    /// Invalid memory
    InvalidMemory,
    /// Invalid table
    InvalidTable,
    /// Invalid global
    InvalidGlobal,
    /// Invalid module
    InvalidModule,
    /// Custom error message
    Custom(String),
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnexpectedEof => write!(f, "unexpected end of input"),
            Self::InvalidMagic => write!(f, "invalid magic number"),
            Self::InvalidVersion => write!(f, "invalid version number"),
            Self::InvalidSectionId => write!(f, "invalid section ID"),
            Self::InvalidSectionSize => write!(f, "invalid section size"),
            Self::InvalidTypeCode => write!(f, "invalid type code"),
            Self::InvalidValueType => write!(f, "invalid value type"),
            Self::InvalidFunctionType => write!(f, "invalid function type"),
            Self::InvalidExternalKind => write!(f, "invalid import/export kind"),
            Self::InvalidLimits => write!(f, "invalid memory/table limits"),
            Self::InvalidTableType => write!(f, "invalid table type"),
            Self::InvalidGlobalType => write!(f, "invalid global type"),
            Self::InvalidInstruction => write!(f, "invalid instruction"),
            Self::InvalidConstExpr => write!(f, "invalid constant expression"),
            Self::InvalidUtf8 => write!(f, "invalid UTF-8 string"),
            Self::InvalidIntegerEncoding => write!(f, "invalid integer encoding"),
            Self::InvalidFloatEncoding => write!(f, "invalid float encoding"),
            Self::InvalidVectorEncoding => write!(f, "invalid vector encoding"),
            Self::InvalidAlignment => write!(f, "invalid alignment"),
            Self::InvalidMemoryIndex => write!(f, "invalid memory index"),
            Self::InvalidTableIndex => write!(f, "invalid table index"),
            Self::InvalidFunctionIndex => write!(f, "invalid function index"),
            Self::InvalidGlobalIndex => write!(f, "invalid global index"),
            Self::InvalidLocalIndex => write!(f, "invalid local index"),
            Self::InvalidLabelIndex => write!(f, "invalid label index"),
            Self::InvalidTypeIndex => write!(f, "invalid type index"),
            Self::InvalidDataSegment => write!(f, "invalid data segment"),
            Self::InvalidElementSegment => write!(f, "invalid element segment"),
            Self::InvalidStartFunction => write!(f, "invalid start function"),
            Self::InvalidExport => write!(f, "invalid export"),
            Self::InvalidImport => write!(f, "invalid import"),
            Self::InvalidFunction => write!(f, "invalid function"),
            Self::InvalidMemory => write!(f, "invalid memory"),
            Self::InvalidTable => write!(f, "invalid table"),
            Self::InvalidGlobal => write!(f, "invalid global"),
            Self::InvalidModule => write!(f, "invalid module"),
            Self::Custom(msg) => write!(f, "{}", msg),
        }
    }
}

/// Result type for WebAssembly binary parsing
pub type ParseResult<T> = result::Result<T, ParseError>; 
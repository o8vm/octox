//! Intermediate Representation (IR) for syscall code generation.
//!
//! This module defines the intermediate representation used between the parsing
//! and code generation phases. It includes architecture specifications, type
//! definitions, and data structures that represent syscalls in a form suitable
//! for generating target code.

use core::fmt;
use proc_macro::Ident;
use std::str::FromStr;

/// Architecture-specific syscall specifications.
///
/// This trait defines the register layout and instruction format for making
/// system calls on different CPU architectures. It abstracts away architecture
/// differences to enable cross-platform syscall generation.
pub trait ArchSpec {
    /// CPU registers used for passing syscall arguments in order
    const IN_REGS: &'static [&'static str];
    /// CPU register that receives the syscall return value
    const OUT_REGS: &'static str;
    /// CPU register used to pass the syscall number to the kernel
    const SYSCALL_REGS: &'static str;
    /// Assembly instruction used to invoke system calls
    const INSN: &'static str;
}

/// ARM64/AArch64 architecture specification.
///
/// Implements the ARM64 system call ABI with appropriate register assignments
/// and the SVC (Supervisor Call) instruction for entering kernel mode.
#[allow(dead_code)]
pub struct Aarch64;

impl ArchSpec for Aarch64 {
    const IN_REGS: &'static [&'static str] = &["x0", "x1", "x2", "x3", "x4", "x5"];
    const OUT_REGS: &'static str = "x0";
    const SYSCALL_REGS: &'static str = "x8";
    const INSN: &'static str = "svc 0";
}

/// RISC-V 64-bit architecture specification.
///
/// Implements the RISC-V system call ABI using the standard argument registers
/// and the ECALL (Environment Call) instruction for system calls.
#[allow(dead_code)]
pub struct RiscV64;

impl ArchSpec for RiscV64 {
    const IN_REGS: &'static [&'static str] = &["a0", "a1", "a2", "a3", "a4", "a5"];
    const OUT_REGS: &'static str = "a0";
    const SYSCALL_REGS: &'static str = "a7";
    const INSN: &'static str = "ecall";
}

// === IR Types ===

/// Unique identifier for a system call.
///
/// This type wraps a u16 value that represents the syscall number used by the
/// kernel to identify which system call to execute. The use of u16 provides
/// a reasonable range (0-65535) for syscall numbers while keeping the
/// representation compact.
#[repr(transparent)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SyscallId(pub u16);

impl From<u16> for SyscallId {
    fn from(value: u16) -> Self {
        Self(value)
    }
}

/// Type representation for syscall parameters and return values
///
/// This enum represents all possible types that can be used in syscall
/// definitions, including primitive values, pointers, references, slices,
/// strings, and optional types.
#[derive(Debug, Clone)]
pub enum Type {
    /// A primitive value type
    Value(ValueType),
    /// A raw pointer type (e.g., *const T, *mut T)
    Ptr { inner: Box<Type>, mutable: bool },
    /// A reference type (e.g., &T, &mut T)
    Ref { inner: Box<Type>, mutable: bool },
    /// A slice type (e.g., &[T], &mut [T])
    Slice { inner: Box<Type>, mutable: bool },
    /// A string type (&str or &mut str)
    Str { mutable: bool },
    /// An optional type (Option<T>)
    Option { inner: Box<Type> },
    /// A custom type that preserves the original tokens
    /// This is used for types like Stat that implement AsBytes
    Custom(proc_macro::TokenStream),
}

/// Primitive value types supported in syscall definitions
///
/// This enum represents all the primitive types that can be passed as
/// syscall parameters or returned from syscalls. It includes standard
/// Rust primitive types as well as kernel-specific types like file
/// descriptors and process IDs.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ValueType {
    /// 8-bit signed integer
    I8,
    /// 16-bit signed integer
    I16,
    /// 32-bit signed integer
    I32,
    /// 64-bit signed integer
    I64,
    /// 128-bit signed integer
    I128,
    /// Pointer-sized signed integer
    Isize,
    /// 8-bit unsigned integer
    U8,
    /// 16-bit unsigned integer
    U16,
    /// 32-bit unsigned integer
    U32,
    /// 64-bit unsigned integer
    U64,
    /// 128-bit unsigned integer
    U128,
    /// Pointer-sized unsigned integer
    Usize,
    /// Boolean type
    Bool,
    /// Unicode character type
    Char,
    /// File descriptor (kernel-specific type)
    Fd,
    /// Process ID (kernel-specific type)
    PId,
}

/// Display implementation for ValueType
///
/// Converts each ValueType variant to its corresponding Rust type name string.
/// This is useful for code generation and error messages.
impl fmt::Display for ValueType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = match self {
            ValueType::I8 => "i8",
            ValueType::I16 => "i16",
            ValueType::I32 => "i32",
            ValueType::I64 => "i64",
            ValueType::I128 => "i128",
            ValueType::Isize => "isize",
            ValueType::U8 => "u8",
            ValueType::U16 => "u16",
            ValueType::U32 => "u32",
            ValueType::U64 => "u64",
            ValueType::U128 => "u128",
            ValueType::Usize => "usize",
            ValueType::Bool => "bool",
            ValueType::Char => "char",
            ValueType::Fd => "Fd",
            ValueType::PId => "PId",
        };
        write!(f, "{}", name)
    }
}

/// FromStr implementation for ValueType
///
/// Parses a string representation of a type name into the corresponding
/// ValueType variant. This is used during macro parsing to convert
/// type names from the input token stream.
impl FromStr for ValueType {
    type Err = ();
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "i8" => Ok(ValueType::I8),
            "i16" => Ok(ValueType::I16),
            "i32" => Ok(ValueType::I32),
            "i64" => Ok(ValueType::I64),
            "i128" => Ok(ValueType::I128),
            "isize" => Ok(ValueType::Isize),
            "u8" => Ok(ValueType::U8),
            "u16" => Ok(ValueType::U16),
            "u32" => Ok(ValueType::U32),
            "u64" => Ok(ValueType::U64),
            "u128" => Ok(ValueType::U128),
            "usize" => Ok(ValueType::Usize),
            "bool" => Ok(ValueType::Bool),
            "char" => Ok(ValueType::Char),
            "Fd" => Ok(ValueType::Fd),
            "PId" => Ok(ValueType::PId),
            _ => Err(()),
        }
    }
}

// === IR Structures ===

/// Registry containing all syscalls for a particular syscall enum
///
/// This is the main container for syscall definitions after they've been
/// parsed from the AST and converted to an intermediate representation.
#[derive(Debug, Clone)]
pub struct SyscallRegistry {
    /// Name of the syscall enum
    pub name: Ident,
    /// Collection of all syscalls in this registry
    pub syscalls: Vec<Syscall>,
}

impl SyscallRegistry {
    /// Create a new syscall registry
    pub fn new(name: Ident) -> Self {
        Self {
            name,
            syscalls: Vec::new(),
        }
    }

    /// Add a syscall to the registry
    pub fn add_syscall(&mut self, syscall: Syscall) {
        self.syscalls.push(syscall);
    }
}

/// Individual syscall definition in intermediate representation
///
/// Contains all information needed to generate syscall wrapper functions,
/// including parameter types, return types, and register allocation details.
#[derive(Debug, Clone)]
pub struct Syscall {
    /// Name used for the generated Rust function
    pub rust_name: Ident,
    /// Name of the variant in the syscall enum
    pub variant_name: Ident,
    /// Unique syscall identifier number
    pub id: SyscallId,
    /// List of syscall parameters
    pub params: Vec<Param>,
    /// Return type specification
    pub ret: ReturnType,
}

// === Parameters and Return Type ===

/// A single parameter for a syscall
///
/// Represents both the name and type information for parameters
/// that will be passed to the generated syscall function.
#[derive(Debug, Clone)]
pub struct Param {
    /// Name of the parameter in the generated Rust function
    pub rust_name: Ident,
    /// Type information for the parameter
    pub ty: Type,
}

/// Return type specification for syscalls
///
/// Defines the possible return types that syscalls can have,
/// including success values, errors, and never-returning calls.
#[derive(Debug, Clone)]
pub enum ReturnType {
    /// Never returns (diverging function)
    Never,
    /// Returns a Result type, optionally wrapping a value type
    Result(Option<ValueType>),
}

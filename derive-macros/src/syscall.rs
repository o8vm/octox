mod error;
mod ir;
mod ast;
mod parser;
mod lowering;
mod codegen;

use error::Result;
use kernel;
use proc_macro::TokenStream;

/// Main entry point for the syscalls derive macro
/// 
/// This function processes the input TokenStream representing a syscall enum
/// and generates the corresponding syscall wrapper functions and implementations.
pub fn derive_syscalls_impl(input: TokenStream) -> TokenStream {
    match process(input) {
        Ok(tokens) => {
            eprintln!("=== Output ===");
            eprintln!("{}", tokens);
            tokens
        },
        Err(e) => {
            eprintln!("=== Error ===");
            eprintln!("{}", e.message);
            error::emit(e.message, e.span)
        }
    }
}

/// Process the input token stream and generate syscall implementations
/// 
/// This function parses the input enum, validates it, and generates
/// the appropriate syscall wrapper code.
fn process(input: TokenStream) -> Result<TokenStream> {
    let ast = parser::Parser::new(input).parse_enum()?;
    let ir = lowering::lower_to_ir(ast)?;
    Ok(codegen::emit(&ir))
}

/// Constants used throughout the syscall generation process
pub mod constants {
    /// Maximum number of argument registers available for syscalls
    pub const MAX_ARG_REGS: u8 = 6;
}

/// Syscall return value conversion utilities
/// 
/// This module provides traits for converting between Rust types and the raw
/// isize values that the kernel uses for syscall return values.
pub mod syscall_return {
    use super::*;

    /// Convert a Rust syscall return type into the raw kernel value (isize)
    /// 
    /// This trait enables conversion of high-level Rust types to the low-level
    /// isize representation that the kernel expects for system call returns.
    /// Success values are typically positive, while errors are negative.
    pub trait IntoSyscallRaw {
    /// Convert this value into a raw syscall return value
    fn into_syscall_raw(self) -> isize;
}

/// Implementations for basic types and unit type
impl IntoSyscallRaw for () {
    fn into_syscall_raw(self) -> isize {
        0
    }
}

/// Basic integer type implementations
impl IntoSyscallRaw for usize {
    fn into_syscall_raw(self) -> isize {
        self as isize
    }
}

impl IntoSyscallRaw for isize {
    fn into_syscall_raw(self) -> isize {
        self
    }
}

impl IntoSyscallRaw for u32 {
    fn into_syscall_raw(self) -> isize {
        self as isize
    }
}

impl IntoSyscallRaw for i32 {
    fn into_syscall_raw(self) -> isize {
        self as isize
    }
}

/// Kernel-specific type implementations
impl IntoSyscallRaw for kernel::syscall::Fd {
    fn into_syscall_raw(self) -> isize {
        self.0 as isize
    }
}

impl IntoSyscallRaw for kernel::syscall::PId {
    fn into_syscall_raw(self) -> isize {
        self.0 as isize
    }
}

/// Result type implementation - converts Ok to positive value, Err to negative
impl<T: IntoSyscallRaw> IntoSyscallRaw for kernel::error::Result<T> {
    fn into_syscall_raw(self) -> isize {
        match self {
            Ok(v) => v.into_syscall_raw(),
            Err(e) => -(e as isize),
        }
    }
}

    /// Convert raw kernel values (isize) back to Rust syscall return types
    /// 
    /// This trait enables conversion from the raw isize values returned
    /// by the kernel back to appropriate Rust types. Positive values typically
    /// represent success, while negative values represent error codes.
pub trait FromSyscallRaw: Sized {
    /// Convert a raw syscall return value into this type
    fn from_syscall_raw(val: isize) -> Self;
}

/// Basic type implementations for conversion from raw values
impl FromSyscallRaw for () {
    fn from_syscall_raw(_: isize) -> Self {
        ()
    }
}

impl FromSyscallRaw for usize {
    fn from_syscall_raw(val: isize) -> Self {
        val as usize
    }
}

impl FromSyscallRaw for isize {
    fn from_syscall_raw(val: isize) -> Self {
        val
    }
}

/// Kernel-specific type implementations for conversion from raw values
impl FromSyscallRaw for kernel::syscall::Fd {
    fn from_syscall_raw(val: isize) -> Self {
        kernel::syscall::Fd::from(val as usize)
    }
}

impl FromSyscallRaw for kernel::syscall::PId {
    fn from_syscall_raw(val: isize) -> Self {
        kernel::syscall::PId::from(val as usize)
    }
}

/// Result type implementation - converts positive values to Ok, negative to Err
impl<T: FromSyscallRaw> FromSyscallRaw for kernel::error::Result<T> {
    fn from_syscall_raw(val: isize) -> Self {
        if val >= 0 {
            Ok(T::from_syscall_raw(val))
        } else {
            Err(kernel::error::Error::from(val))
        }
    }
}
}

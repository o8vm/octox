//! Implementation of the SyscallError derive macro.
//!
//! This module provides functionality to automatically generate error conversion
//! implementations for syscall error enums. It processes `#[repr(isize)]` enums
//! and generates `From<isize>` implementations for seamless error handling.

mod ast;
mod codegen;
mod ir;
mod lowering;
mod parser;

use crate::common::error::{Result, emit};
use proc_macro::TokenStream;

/// Main entry point for the SyscallError derive macro.
///
/// This function processes the input TokenStream representing an error enum
/// and generates the corresponding `From<isize>` implementation and helper methods.
///
/// The generated code enables automatic conversion from syscall return values
/// (represented as `isize`) into structured error types, making error handling
/// more ergonomic and type-safe.
///
/// # Example Input
///
/// ```rust
/// #[derive(SysErrs)]
/// #[repr(isize)]
/// pub enum Error {
///     Uncategorized,
///     ResourceBusy = -2,
///     NotFound = -3,
///     OutOfMemory = -4,
/// }
/// ```
///
/// # Generated Output
///
/// ```rust
/// impl From<isize> for Error {
///     fn from(value: isize) -> Self {
///         match value {
///             -2 => Error::ResourceBusy,
///             -3 => Error::NotFound,
///             -4 => Error::OutOfMemory,
///             _ => Error::Uncategorized,
///         }
///     }
/// }
/// ```
pub fn derive_syscall_error_impl(input: TokenStream) -> TokenStream {
    match process(input) {
        Ok(tokens) => tokens,
        Err(e) => emit(&e),
    }
}

/// Processes the input token stream and generates error conversion implementations.
///
/// This function orchestrates the parsing, lowering, and code generation phases
/// to transform the input error enum into the appropriate conversion code.
///
/// # Arguments
/// * `input` - TokenStream representing the error enum definition
///
/// # Returns
/// * `Ok(TokenStream)` - Generated implementation code
/// * `Err(Error)` - Processing error with diagnostic information
fn process(input: TokenStream) -> Result<TokenStream> {
    let ast = parser::parse_error_enum(input)?;
    let ir = lowering::lower_to_ir(ast)?;
    Ok(codegen::emit(&ir))
}

//! Implementation of the Syscalls derive macro.
//!
//! This module provides the complete implementation for generating syscall
//! wrapper functions and kernel dispatch logic from enum definitions. It
//! processes syscall attribute syntax and generates appropriate code for
//! both userspace and kernel environments.
//!
//! # Architecture
//!
//! The implementation follows a multi-phase approach:
//! 1. **Parsing**: Convert TokenStream to AST representation
//! 2. **Lowering**: Transform AST to intermediate representation (IR)
//! 3. **Code Generation**: Emit final Rust code from IR
//!
//! # Generated Code
//!
//! For userspace, generates functions that make system calls using inline assembly.
//! For kernel, generates dispatch logic and parameter handling code.

mod ast;
mod codegen;
mod ir;
mod lowering;
mod parser;

use crate::common::error::{Result, emit};
use proc_macro::TokenStream;

/// Main entry point for the Syscalls derive macro.
///
/// This function processes the input TokenStream representing a syscall enum
/// and generates the corresponding syscall wrapper functions and implementations.
/// It handles both userspace syscall invocation code and kernel dispatch logic.
///
/// # Error Handling
///
/// Compilation errors are emitted directly using the `compile_error!` macro,
/// providing clear diagnostic information about any issues encountered during
/// macro expansion.
///
/// # Generated Output
///
/// The macro generates different code based on compilation features:
/// - `#[cfg(feature = "user")]`: Userspace syscall wrapper functions
/// - `#[cfg(feature = "kernel")]`: Kernel dispatch and handling logic
/// - Type conversion traits for seamless parameter and return value handling
pub fn derive_syscalls_impl(input: TokenStream) -> TokenStream {
    match process(input) {
        Ok(tokens) => {
            eprintln!("=== Generated Output ===");
            eprintln!("{}", tokens);
            tokens
        }
        Err(e) => {
            eprintln!("=== Error ===");
            eprintln!("{}", e.message);
            emit(&e)
        }
    }
}

/// Processes the input token stream and generates syscall implementations.
///
/// This function orchestrates the complete transformation pipeline from
/// input TokenStream to generated code, handling parsing, validation,
/// and code generation phases.
///
/// # Arguments
/// * `input` - TokenStream representing the syscall enum definition
///
/// # Returns
/// * `Ok(TokenStream)` - Successfully generated implementation code
/// * `Err(Error)` - Processing error with diagnostic information
fn process(input: TokenStream) -> Result<TokenStream> {
    let ast = parser::Parser::new(input).parse_enum()?;
    let ir = lowering::lower_to_ir(ast)?;
    Ok(codegen::emit(&ir))
}

/// Constants used throughout the syscall generation process.
pub mod constants {
    /// Maximum number of argument registers available for syscalls.
    ///
    /// This constant defines the architectural limit for the number of
    /// arguments that can be passed to a syscall through CPU registers.
    /// Syscalls with more parameters than this limit will be rejected
    /// during compilation.
    pub const MAX_ARG_REGS: u8 = 6;
}

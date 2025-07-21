//! Procedural macros for generating syscall wrappers and error handling in the Octox operating system.
//!
//! This crate provides two main derive macros:
//! - `Syscalls`: Generates syscall wrapper functions for both userspace and kernel
//! - `SyscallError`: Generates error conversion implementations for syscall error types
//!
//! # Example
//!
//! ```rust
//! #[derive(SysCalls)]
//! enum SysCalls {
//!     #[syscall(id = 0, params(fd: Fd, buf: &mut [u8]), ret(Result<usize>))]
//!     Read,
//!     #[syscall(id = 1, params(fd: Fd, buf: &[u8]), ret(Result<usize>))]
//!     Write,
//! }
//!
//! #[derive(SysErrs)]
//! #[repr(isize)]
//! pub enum Error {
//!     Uncategorized,
//!     ResourceBusy = -2,
//!     NotFound = -3,
//! }
//! ```

extern crate proc_macro;
use proc_macro::TokenStream;

mod common;
mod syserr;
mod syscall;

/// Derives syscall wrapper implementations for both userspace and kernel environments.
///
/// This macro processes an enum with syscall variants and generates:
/// - Userspace functions that make system calls using inline assembly
/// - Kernel dispatch logic for handling incoming syscalls
/// - Type conversion traits for syscall parameters and return values
///
/// # Attributes
///
/// Each variant must have a `#[syscall(...)]` attribute with:
/// - `id = N`: The syscall number
/// - `params(...)`: Parameter list with names and types
/// - `ret(...)`: Return type specification
///
/// # Example
///
/// ```rust
/// #[derive(Syscalls)]
/// enum SysCalls {
///     #[syscall(id = 0, params(fd: Fd, buf: &mut [u8]), ret(Result<usize>))]
///     Read,
/// }
/// ```
#[proc_macro_derive(SysCalls, attributes(syscall))]
pub fn derive_syscalls(input: TokenStream) -> TokenStream {
    syscall::derive_syscalls_impl(input)
}

/// Derives error conversion implementations for syscall error enums.
///
/// This macro generates `From<isize>` implementations that convert syscall
/// return values into structured error types. It's designed to work with
/// `#[repr(isize)]` enums where variants have explicit discriminant values.
///
/// # Example
///
/// ```rust
/// #[derive(SysErrs)]
/// #[repr(isize)]
/// pub enum Error {
///     Uncategorized,
///     ResourceBusy = -2,
///     NotFound = -3,
/// }
/// ```
///
/// This generates:
/// - `From<isize>` implementation for error conversion
#[proc_macro_derive(SysErrs)]
pub fn derive_syscall_error(input: TokenStream) -> TokenStream {
    syserr::derive_syscall_error_impl(input)
}

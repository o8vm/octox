//! Common utilities shared across derive macro implementations.
//!
//! This module provides shared functionality and types used by both the
//! `Syscalls` and `SyscallError` derive macros. It includes error handling,
//! utility functions, and common data structures.

/// Error handling utilities for derive macro processing.
///
/// This module contains unified error types and functions for handling
/// errors that occur during macro expansion, providing consistent error
/// reporting across all derive macros in this crate.
pub mod error;

//! Common error handling utilities for derive macros.
//!
//! This module provides unified error types and handling functions that are
//! shared across all derive macro implementations in this crate.

use proc_macro::{Ident, Literal, Span, TokenStream, TokenTree};

/// Unified error type for derive macro processing.
///
/// This structure represents errors that can occur during macro expansion,
/// including both the error message and source location information for
/// accurate diagnostic reporting.
#[derive(Debug, Clone)]
pub struct Error {
    /// Human-readable error message describing what went wrong
    pub message: String,
    /// Source code location where the error occurred
    pub span: Span,
}

impl Error {
    /// Creates a new error with the given message and source location.
    ///
    /// # Arguments
    /// * `message` - The error message (will be converted to String)
    /// * `span` - Source location for diagnostic reporting
    ///
    /// # Returns
    /// A new Error instance
    pub fn new(message: impl Into<String>, span: Span) -> Self {
        Self {
            message: message.into(),
            span,
        }
    }
}

/// Converts an error into a `compile_error!` macro invocation.
///
/// This function transforms our internal error representation into a TokenStream
/// that will cause a compile-time error with the appropriate message and location
/// when the generated code is compiled.
///
/// # Arguments
/// * `error` - The error to emit as a compile-time error
///
/// # Returns
/// A TokenStream containing a `compile_error!` macro invocation
pub fn emit(error: &Error) -> TokenStream {
    let lit = Literal::string(&error.message);
    let mut ts = TokenStream::new();
    ts.extend([
        TokenTree::Ident(Ident::new("compile_error", error.span)),
        TokenTree::Punct(proc_macro::Punct::new('!', proc_macro::Spacing::Alone)),
        TokenTree::Group(proc_macro::Group::new(
            proc_macro::Delimiter::Parenthesis,
            TokenStream::from(TokenTree::Literal(lit)),
        )),
    ]);
    ts
}

/// Standard Result type alias for derive macro operations.
///
/// This type alias provides a convenient way to work with Results throughout
/// the derive macro codebase, using our unified Error type.
pub type Result<T> = std::result::Result<T, Error>;

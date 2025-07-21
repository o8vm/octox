//! Abstract Syntax Tree definitions for error enum processing.
//!
//! This module defines the AST structures used to represent error enums
//! that will be processed by the SyscallError derive macro. It handles
//! enums with explicit discriminant values for error codes.

use proc_macro::{Ident, Span};

/// AST representation of an error enum with discriminant values.
///
/// This structure represents the parsed form of an error enum that will
/// be used to generate `From<isize>` implementations. It captures the
/// enum name and all its variants with their associated error codes.
#[derive(Debug)]
pub struct ErrorEnumAst {
    /// The identifier name of the error enum
    pub name: Ident,
    /// Collection of error variants with their discriminant values
    pub variants: Vec<ErrorVariantAst>,
}

/// AST representation of a single error variant.
///
/// Each variant represents one specific error condition and may have an
/// explicit negative discriminant value that corresponds to a syscall
/// error code.
#[derive(Debug)]
pub struct ErrorVariantAst {
    /// The identifier name of the error variant
    pub name: Ident,
    /// Optional explicit discriminant value (typically negative for errors)
    pub discriminant: Option<NegativeDiscriminant>,
    /// Source location for error reporting
    pub span: Span,
}

/// Represents a negative discriminant value for error codes.
///
/// This structure holds negative integer values that represent specific
/// error codes returned by system calls. These values are used to generate
/// the appropriate match arms in the `From<isize>` implementation.
#[derive(Debug)]
pub struct NegativeDiscriminant {
    /// The negative integer value representing this error code
    pub value: isize, // Always negative
}

//! Intermediate Representation (IR) for error enum processing.
//!
//! This module defines the validated intermediate representation used between
//! the parsing and code generation phases for the SyscallError derive macro.
//! The IR contains validated error enum information ready for code generation.

/// Validated intermediate representation of an error enum.
///
/// This structure represents a fully validated error enum that has passed
/// all validation checks and is ready for code generation. It contains
/// the enum name and all validated error variants with their discriminant values.
///
/// # Validation Rules
/// - All discriminant values must be non-positive (≤ 0)
/// - Each discriminant value should be unique
/// - The enum should have an "Uncategorized" variant for fallback cases
#[derive(Debug)]
pub struct ErrorRegistry {
    /// The name of the error enum as a string
    pub name: String,
    /// Collection of validated error variants
    pub variants: Vec<ErrorVariant>,
}

/// Validated representation of a single error variant.
///
/// This structure represents an individual error variant that has been
/// validated and prepared for code generation. It contains the variant
/// name and its associated error code value.
#[derive(Debug)]
pub struct ErrorVariant {
    /// The name of the error variant as a string
    pub name: String,
    /// The error code value (typically negative for errors, 0 for default)
    pub value: isize, // Negative or zero (for Uncategorized)
}

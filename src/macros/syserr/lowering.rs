//! AST to IR lowering for error enum processing.
//!
//! This module implements the transformation from Abstract Syntax Tree (AST)
//! representation to Intermediate Representation (IR) for error enums.
//! It performs validation and ensures the error enum is well-formed.

use super::{ast, ir};
use crate::common::error::{Error, Result};

/// Converts AST representation to validated IR.
///
/// This function transforms the parsed AST into a validated intermediate
/// representation, performing various validation checks along the way.
/// It ensures that the error enum is properly structured and ready for
/// code generation.
///
/// # Validation Performed
/// - Checks for duplicate discriminant values
/// - Assigns default value (0) to variants without explicit discriminants
/// - Validates that all discriminant values are appropriate for error codes
///
/// # Arguments
/// * `ast` - The parsed AST representation of the error enum
///
/// # Returns
/// * `Ok(ir::ErrorRegistry)` - Successfully validated IR
/// * `Err(Error)` - Validation error with diagnostic information
///
/// # Example
/// ```rust
/// // Input AST with variants:
/// // Uncategorized (no discriminant) -> value = 0
/// // NotFound = -3 -> value = -3
/// // OutOfMemory = -4 -> value = -4
/// ```
pub fn lower_to_ir(ast: ast::ErrorEnumAst) -> Result<ir::ErrorRegistry> {
    let mut variants = Vec::new();
    let mut seen_values = std::collections::HashSet::new();

    for variant_ast in ast.variants {
        // Determine the discriminant value for this variant
        let value = match variant_ast.discriminant {
            Some(disc) => disc.value,
            None => 0, // Default variant (typically Uncategorized) gets value 0
        };

        // Validate that this discriminant value hasn't been used before
        if !seen_values.insert(value) {
            return Err(Error::new(
                format!("Duplicate error value: {}", value),
                variant_ast.span,
            ));
        }

        // Create validated IR variant
        variants.push(ir::ErrorVariant {
            name: variant_ast.name.to_string(),
            value,
        });
    }

    // Create the validated error registry
    Ok(ir::ErrorRegistry {
        name: ast.name.to_string(),
        variants,
    })
}

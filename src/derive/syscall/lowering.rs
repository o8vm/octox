//! AST to IR lowering for syscall definitions.
//!
//! This module handles the transformation from Abstract Syntax Tree (AST)
//! representations to Intermediate Representation (IR). It performs semantic
//! analysis, validates constraints, and prepares the data structures needed
//! for code generation.

use std::iter::Peekable;

use crate::syscall::constants::MAX_ARG_REGS;

use super::ast;
use super::ir;
use super::parser::parse_generic_arg_iter;
use crate::common::error::{Error, Result};
use proc_macro::Ident;
use proc_macro::Span;
use proc_macro::TokenTree;

/// Converts an AST enum into an IR syscall registry.
///
/// This function performs the main lowering operation, transforming the parsed
/// AST representation into a structured IR that can be used for code generation.
/// It validates syscall definitions and builds the registry of all syscalls.
///
/// # Arguments
/// * `ast` - The parsed AST enum containing syscall definitions
///
/// # Returns
/// * `Ok(ir::SyscallRegistry)` - Successfully lowered syscall registry
/// * `Err(Error)` - Validation or lowering error
pub fn lower_to_ir(ast: ast::Enum) -> Result<ir::SyscallRegistry> {
    let mut registry = ir::SyscallRegistry::new(ast.name);

    for variant in ast.variants {
        let syscall = lower_variant(variant)?;
        registry.add_syscall(syscall);
    }

    Ok(registry)
}

/// Converts a single AST variant into an IR syscall definition.
///
/// This function processes one syscall variant, validating its parameters
/// and return type while converting them to the appropriate IR types.
/// It also enforces architecture constraints like maximum argument count.
///
/// # Arguments
/// * `variant` - The AST variant to convert
///
/// # Returns
/// * `Ok(ir::Syscall)` - Successfully converted syscall definition
/// * `Err(Error)` - Parameter validation or conversion error
fn lower_variant(variant: ast::Variant) -> Result<ir::Syscall> {
    // Require explicit discriminant for syscall ID
    let id_value = variant.id.ok_or_else(|| {
        Error::new(
            format!(
                "Syscall variant '{}' must have an explicit discriminant (e.g., '{}' = 42)",
                variant.name, variant.name
            ),
            variant.name.span(),
        )
    })?;
    let id = ir::SyscallId::from(id_value as u16);

    let mut params = Vec::new();

    for param in variant.params {
        let typ = lower_param_type(&param.ty)?;
        params.push(ir::Param {
            rust_name: param.name,
            ty: typ,
        });
    }

    if params.len() > MAX_ARG_REGS as usize {
        return Err(Error::new(
            format!(
                "too many parameters for syscall '{}': expected at most {} but got {}",
                variant.name,
                MAX_ARG_REGS,
                params.len()
            ),
            Span::call_site(),
        ));
    }

    let ret = lower_return(variant.ret)?;

    let rust_name = Ident::new(
        &variant.name.to_string().to_lowercase(),
        variant.name.span(),
    );

    Ok(ir::Syscall {
        id,
        variant_name: variant.name,
        rust_name,
        params,
        ret,
    })
}

/// Converts an AST parameter type to its IR representation.
///
/// This function performs type analysis and conversion from AST types to
/// IR types. It handles complex type parsing including references, slices,
/// optional types, and custom types while validating type constraints.
///
/// # Arguments
/// * `ast_ty` - The AST type to convert
///
/// # Returns
/// * `Ok(ir::Type)` - Successfully converted IR type
/// * `Err(Error)` - Type conversion or validation error
fn lower_param_type(ast_ty: &ast::Type) -> Result<ir::Type> {
    let mut tokens = ast_ty.tokens.clone().into_iter().peekable();
    let type_str = ast_ty.tokens.to_string();

    if let Ok(val) = type_str.parse::<ir::ValueType>() {
        return Ok(ir::Type::Value(val));
    }

    // Raw pointers
    if let Some(TokenTree::Punct(p)) = tokens.peek() {
        if p.as_char() == '*' {
            tokens.next();

            let is_mut = {
                let tt = tokens.peek().ok_or_else(|| {
                    Error::new("expected 'const' or 'mut' after '*'", ast_ty.span)
                })?;

                // Destructure into an Ident or bail out
                let TokenTree::Ident(ident) = tt else {
                    return Err(Error::new(
                        "expected 'const' or 'mut' after '*'",
                        ast_ty.span,
                    ));
                };

                // Match on the stringified identifier
                match ident.to_string().as_str() {
                    "const" => {
                        tokens.next(); // consume 'const'
                        false
                    }
                    "mut" => {
                        tokens.next(); // consume 'mut'
                        true
                    }
                    _ => {
                        return Err(Error::new(
                            "expected 'const' or 'mut' after '*'",
                            ast_ty.span,
                        ));
                    }
                }
            };

            let inner_type = lower_param_type(&ast::Type {
                tokens: tokens.collect(),
                span: ast_ty.span,
            })?;

            return Ok(ir::Type::Ptr {
                mutable: is_mut,
                inner: Box::new(inner_type),
            });
        }
    }

    // Handle references
    if let Some(TokenTree::Punct(p)) = tokens.peek() {
        if p.as_char() == '&' {
            tokens.next();

            let is_mut = if let Some(TokenTree::Ident(ident)) = tokens.peek() {
                if ident.to_string() == "mut" {
                    tokens.next(); // consume 'mut'
                    true
                } else {
                    false
                }
            } else {
                false
            };

            // &str => ir::Type::Str
            if let Some(TokenTree::Ident(ident)) = tokens.peek() {
                if ident.to_string() == "str" {
                    return Ok(ir::Type::Str { mutable: is_mut });
                }
            }

            // &[T] or &mut [T] => ir::Type::Slice
            if let Some(TokenTree::Group(g)) = tokens.peek() {
                if g.delimiter() == proc_macro::Delimiter::Bracket {
                    let inner_stream = g.stream();
                    let inner_type = if inner_stream.is_empty() {
                        ir::Type::Value(ir::ValueType::U8) // Default to u8 if empty
                    } else {
                        lower_param_type(&ast::Type {
                            tokens: inner_stream,
                            span: ast_ty.span,
                        })?
                    };

                    return Ok(ir::Type::Slice {
                        mutable: is_mut,
                        inner: Box::new(inner_type),
                    });
                }
            }

            // Handle other reference types
            let inner_type = lower_param_type(&ast::Type {
                tokens: tokens.collect(),
                span: ast_ty.span,
            })?;

            return Ok(ir::Type::Ref {
                mutable: is_mut,
                inner: Box::new(inner_type),
            });
        }
    }

    // Handle Option<T>
    if let Some(TokenTree::Ident(ident)) = tokens.peek()
        && ident.to_string() == "Option"
    {
        tokens.next(); // consume 'Option'
        if let Some(inner_ast) = parse_generic_arg_iter(&mut tokens)? {
            let inner_type = lower_param_type(&inner_ast)?;
            return Ok(ir::Type::Option {
                inner: Box::new(inner_type),
            });
        }
    }

    // Handle custom types (e.g., Stat, File)
    // Custom types are preserved as token streams for later validation
    // The AsBytes constraint is checked during compilation of generated code
    // This preserves type safety while allowing flexible custom type support
    Ok(ir::Type::Custom(ast_ty.tokens.clone()))
}

/// Converts an AST return type to its IR representation.
///
/// This function handles the conversion of return type specifications from
/// the AST form to the IR form, supporting both never-returning functions
/// and concrete return types.
///
/// # Arguments
/// * `ret` - The AST return type to convert
///
/// # Returns
/// * `Ok(ir::ReturnType)` - Successfully converted return type
/// * `Err(Error)` - Return type validation error
fn lower_return(ret: ast::ReturnType) -> Result<ir::ReturnType> {
    match ret {
        ast::ReturnType::Never => Ok(ir::ReturnType::Never),
        ast::ReturnType::Type(ast_ty) => lower_return_type(&ast_ty),
    }
}

/// Converts a concrete AST return type to its IR representation.
///
/// This function specifically handles Result types and their inner value types,
/// validating that the return type follows the expected pattern for syscalls.
///
/// # Arguments
/// * `typ` - The AST type representing the return type
///
/// # Returns
/// * `Ok(ir::ReturnType)` - Successfully converted return type
/// * `Err(Error)` - Invalid return type format
fn lower_return_type(typ: &ast::Type) -> Result<ir::ReturnType> {
    let mut tokens = typ.tokens.clone().into_iter().peekable();
    if let Some(TokenTree::Ident(i)) = tokens.peek()
        && i.to_string() == "Result"
    {
        tokens.next(); // consume 'Result'
        lower_result_type(tokens, typ.span)
    } else {
        Err(Error::new("expected 'Result' type", typ.span))
    }
}

/// Converts a Result type to its IR representation.
///
/// This function processes the generic arguments of Result types to extract
/// the success value type and validate the Result format for syscalls.
///
/// # Arguments
/// * `tokens` - Token iterator positioned after 'Result'
/// * `span` - Source span for error reporting
///
/// # Returns
/// * `Ok(ir::ReturnType)` - Successfully converted Result type
/// * `Err(Error)` - Invalid Result type format
fn lower_result_type(
    mut tokens: Peekable<impl Iterator<Item = TokenTree>>,
    span: Span,
) -> Result<ir::ReturnType> {
    // Extract generic arguments from Result<T, E>
    match parse_generic_arg_iter(&mut tokens) {
        Ok(Some(args)) => lower_result_type_param(&args, span),
        Ok(None) => Err(Error::new(
            "expected generic arguments for Result type",
            span,
        )),
        Err(e) => Err(e),
    }
}

/// Processes the type parameters within a Result type.
///
/// This function analyzes the generic parameters of Result<T, E> to extract
/// the success value type while ignoring the error type (assumed to be Error).
///
/// # Arguments
/// * `args` - AST type representing the Result generic arguments
/// * `span` - Source span for error reporting
///
/// # Returns
/// * `Ok(ir::ReturnType)` - Successfully processed Result parameters
/// * `Err(Error)` - Invalid parameter format
fn lower_result_type_param(args: &ast::Type, span: Span) -> Result<ir::ReturnType> {
    let mut tokens = args.tokens.clone().into_iter().peekable();
    let mut first_type_tokens = Vec::new();
    let mut depth = 0;
    let mut has_error_param = false;

    while let Some(token) = tokens.peek() {
        match token {
            TokenTree::Punct(p) => match p.as_char() {
                '<' => {
                    depth += 1;
                    first_type_tokens.push(tokens.next().unwrap());
                }
                '>' => {
                    depth -= 1;
                    first_type_tokens.push(tokens.next().unwrap());
                }
                ',' if depth == 0 => {
                    tokens.next(); // consume the comma
                    has_error_param = true;
                    break; // end of the first type
                }
                _ => {
                    first_type_tokens.push(tokens.next().unwrap());
                }
            },
            _ => {
                first_type_tokens.push(tokens.next().unwrap());
            }
        }
    }

    // Validate the second type parameter if present
    // For syscalls, Result<T, E> should always use Error as the error type
    // Single-parameter Result<T> is also accepted for convenience
    if has_error_param {
        let remaining: String = tokens
            .map(|tt| tt.to_string())
            .collect::<Vec<_>>()
            .join("")
            .trim()
            .to_string();

        if remaining != "Error" {
            return Err(Error::new(
                format!("expected 'Error' type in Result, found '{}'", remaining),
                span,
            ));
        }
    }

    // Convert the first type parameter to string and analyze it
    let first_type_str = first_type_tokens
        .iter()
        .map(|tt| tt.to_string())
        .collect::<Vec<_>>()
        .join("")
        .trim()
        .to_string();

    match first_type_str.as_str() {
        "()" => Ok(ir::ReturnType::Result(None)),
        s => {
            if let Ok(value_type) = s.parse::<ir::ValueType>() {
                Ok(ir::ReturnType::Result(Some(value_type)))
            } else {
                Err(Error::new(
                    format!("unsupported type in Result: {}", first_type_str),
                    span,
                ))
            }
        }
    }
}

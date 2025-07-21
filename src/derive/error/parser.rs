//! Parser implementation for error enum definitions.
//!
//! This module provides parsing functionality to convert proc_macro TokenStreams
//! representing error enums into structured AST representations. It handles
//! the parsing of enum attributes, variants, and discriminant values.

use super::ast;
use crate::common::error::{Error, Result};
use proc_macro::{Delimiter, TokenStream, TokenTree};

/// Parses a complete error enum definition from a TokenStream.
///
/// This function processes the input TokenStream and extracts an error enum
/// definition with its attributes, name, and variants. It performs validation
/// to ensure the enum is properly formatted for error code generation.
///
/// # Required Attributes
/// - `#[repr(isize)]` - Required for proper discriminant handling
///
/// # Arguments
/// * `input` - TokenStream representing the error enum definition
///
/// # Returns
/// * `Ok(ast::ErrorEnumAst)` - Successfully parsed error enum
/// * `Err(Error)` - Parse error with diagnostic information
///
/// # Example Input
/// ```rust
/// #[derive(SyscallError)]
/// #[repr(isize)]
/// pub enum Error {
///     Uncategorized,
///     NotFound = -3,
///     OutOfMemory = -4,
/// }
/// ```
pub fn parse_error_enum(input: TokenStream) -> Result<ast::ErrorEnumAst> {
    let mut tokens = input.into_iter().peekable();
    let span = tokens
        .peek()
        .map(|t| t.span())
        .unwrap_or(proc_macro::Span::call_site());

    // Parse attributes (looking for #[repr(isize)])
    let mut has_repr_isize = false;
    while let Some(TokenTree::Punct(p)) = tokens.peek() {
        if p.as_char() == '#' {
            tokens.next();
            if let Some(TokenTree::Group(g)) = tokens.next() {
                if g.delimiter() == Delimiter::Bracket {
                    let attr_tokens: Vec<_> = g.stream().into_iter().collect();
                    if is_repr_isize(&attr_tokens) {
                        has_repr_isize = true;
                    }
                }
            }
        } else {
            break;
        }
    }

    if !has_repr_isize {
        return Err(Error::new(
            "Error enum must have #[repr(isize)] attribute",
            span,
        ));
    }

    // Skip visibility if present
    skip_visibility(&mut tokens);

    // Parse 'enum'
    match tokens.next() {
        Some(TokenTree::Ident(ident)) if ident.to_string() == "enum" => {}
        _ => return Err(Error::new("Expected 'enum' keyword", span)),
    }

    // Parse enum name
    let name = match tokens.next() {
        Some(TokenTree::Ident(ident)) => ident,
        _ => return Err(Error::new("Expected enum name", span)),
    };

    // Parse enum body
    let body = match tokens.next() {
        Some(TokenTree::Group(g)) if g.delimiter() == Delimiter::Brace => g,
        _ => return Err(Error::new("Expected enum body in braces", span)),
    };

    let variants = parse_variants(body.stream())?;

    Ok(ast::ErrorEnumAst { name, variants })
}

/// Checks if a token sequence represents a `#[repr(isize)]` attribute.
///
/// This function examines attribute tokens to determine if they contain
/// the required `repr(isize)` specification needed for error enums.
///
/// # Arguments
/// * `tokens` - Slice of tokens from within an attribute group
///
/// # Returns
/// `true` if the tokens represent `repr(isize)`, `false` otherwise
fn is_repr_isize(tokens: &[TokenTree]) -> bool {
    if tokens.len() >= 2 {
        if let (Some(TokenTree::Ident(repr)), Some(TokenTree::Group(g))) =
            (tokens.get(0), tokens.get(1))
        {
            if repr.to_string() == "repr" && g.delimiter() == Delimiter::Parenthesis {
                let inner: Vec<_> = g.stream().into_iter().collect();
                if let Some(TokenTree::Ident(isize)) = inner.get(0) {
                    return isize.to_string() == "isize";
                }
            }
        }
    }
    false
}

/// Skips visibility modifiers in the token stream.
///
/// This function advances past `pub` visibility modifiers that may
/// appear before the `enum` keyword.
///
/// # Arguments
/// * `tokens` - Mutable iterator over the token stream
fn skip_visibility(tokens: &mut std::iter::Peekable<proc_macro::token_stream::IntoIter>) {
    if let Some(TokenTree::Ident(ident)) = tokens.peek() {
        if ident.to_string() == "pub" {
            tokens.next();
        }
    }
}

/// Parses all variants within an enum body.
///
/// This function processes the token stream inside enum braces and extracts
/// each variant with its optional discriminant value. It handles comma
/// separation and proper error reporting for malformed variants.
///
/// # Arguments
/// * `input` - TokenStream representing the enum body content
///
/// # Returns
/// * `Ok(Vec<ast::ErrorVariantAst>)` - Successfully parsed variants
/// * `Err(Error)` - Parse error for malformed variant syntax
///
/// # Supported Syntax
/// - `VariantName` - Variant without explicit discriminant
/// - `VariantName = -42` - Variant with negative discriminant
fn parse_variants(input: TokenStream) -> Result<Vec<ast::ErrorVariantAst>> {
    let mut variants = Vec::new();
    let mut tokens = input.into_iter().peekable();

    while tokens.peek().is_some() {
        // Parse variant name
        let name = match tokens.next() {
            Some(TokenTree::Ident(ident)) => ident,
            _ => continue, // Skip non-ident tokens (like commas)
        };

        let span = name.span();

        // Check for discriminant
        let discriminant = if let Some(TokenTree::Punct(p)) = tokens.peek() {
            if p.as_char() == '=' {
                tokens.next(); // consume '='
                parse_negative_literal(&mut tokens)?
            } else {
                None
            }
        } else {
            None
        };

        variants.push(ast::ErrorVariantAst {
            name,
            discriminant,
            span,
        });

        // Skip comma if present
        if let Some(TokenTree::Punct(p)) = tokens.peek() {
            if p.as_char() == ',' {
                tokens.next();
            }
        }
    }

    Ok(variants)
}

/// Parses a negative literal discriminant value.
///
/// This function processes negative integer literals that serve as
/// discriminant values for error enum variants. It handles the parsing
/// of the minus sign followed by a numeric literal.
///
/// # Arguments
/// * `tokens` - Mutable iterator over the token stream
///
/// # Returns
/// * `Ok(Some(NegativeDiscriminant))` - Successfully parsed negative value
/// * `Ok(None)` - No discriminant found (not an error)
/// * `Err(Error)` - Malformed negative literal syntax
///
/// # Example
/// For input `-42`, this returns `NegativeDiscriminant { value: -42 }`
fn parse_negative_literal(
    tokens: &mut std::iter::Peekable<proc_macro::token_stream::IntoIter>,
) -> Result<Option<ast::NegativeDiscriminant>> {
    let span = tokens
        .peek()
        .map(|t| t.span())
        .unwrap_or(proc_macro::Span::call_site());

    match tokens.next() {
        Some(TokenTree::Punct(p)) if p.as_char() == '-' => match tokens.next() {
            Some(TokenTree::Literal(lit)) => {
                let lit_str = lit.to_string();
                let value: isize = lit_str
                    .parse()
                    .map_err(|_| Error::new("Invalid negative literal", span))?;
                Ok(Some(ast::NegativeDiscriminant { value: -value }))
            }
            _ => Err(Error::new("Expected literal after '-'", span)),
        },
        _ => Ok(None), // No discriminant
    }
}

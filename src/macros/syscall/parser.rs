//! Parser implementation for syscall enum definitions.
//!
//! This module provides parsing functionality to convert proc_macro TokenStreams
//! into structured AST representations. It handles the complex task of parsing
//! syscall attribute syntax and enum variants.

use proc_macro::{Delimiter, Ident, Literal, TokenStream, TokenTree};
use std::iter::Peekable;

use crate::common::error::{Error, Result};
use crate::syscall::ast;

/// Represents the different kinds of tokens we care about during parsing.
///
/// This enum helps classify tokens for easier pattern matching during
/// the parsing process.
#[derive(Debug, Clone, PartialEq, Eq)]
enum TokenKind {
    /// An identifier token (variable names, keywords, etc.)
    Ident,
    /// A punctuation character token
    Punct(char),
    /// A literal value token (numbers, strings, etc.)
    Literal,
    /// A grouped token sequence (parentheses, brackets, braces)
    Group(proc_macro::Delimiter),
}

/// Main parser for syscall enum definitions.
///
/// This parser processes TokenStreams from the proc_macro and converts them
/// into structured AST representations that can be used for code generation.
pub struct Parser {
    /// Iterator over the input tokens with lookahead capability
    tokens: Peekable<proc_macro::token_stream::IntoIter>,
}

impl Parser {
    /// Creates a new parser instance from a TokenStream.
    ///
    /// # Arguments
    /// * `tokens` - The input TokenStream to parse
    pub fn new(tokens: proc_macro::TokenStream) -> Self {
        Self {
            tokens: tokens.into_iter().peekable(),
        }
    }

    /// Parses the top-level enum definition.
    ///
    /// This method expects to find an enum declaration with syscall variants
    /// and returns the structured AST representation.
    ///
    /// # Returns
    /// * `Ok(ast::Enum)` - Successfully parsed enum structure
    /// * `Err(Error)` - Parse error with diagnostic information
    pub fn parse_enum(&mut self) -> Result<ast::Enum> {
        let mut cursor = TokenCursor::new(&mut self.tokens);
        cursor.skip_attributes()?;

        // Skip optional visibility modifier (pub)
        cursor.eat_ident("pub");

        if !cursor.eat_ident("enum") {
            return Err(Error::new("Expected 'enum' keyword", cursor.span()));
        }

        let name = cursor.parse_ident()?;
        let body = cursor.parse_group(Delimiter::Brace)?;

        let variants = Self::parse_variants(body)?;

        Ok(ast::Enum { name, variants })
    }

    /// Parses all variants within an enum body.
    ///
    /// This method processes the tokens inside the enum braces and extracts
    /// each variant along with its syscall attributes.
    ///
    /// # Arguments
    /// * `body` - TokenStream representing the enum body content
    ///
    /// # Returns
    /// * `Ok(Vec<ast::Variant>)` - Successfully parsed variants
    /// * `Err(Error)` - Parse error if the variant syntax is invalid
    fn parse_variants(body: TokenStream) -> Result<Vec<ast::Variant>> {
        let mut body_tokens = body.into_iter().peekable();
        let mut cursor = TokenCursor::new(&mut body_tokens);
        let mut variants = Vec::new();

        while cursor.peek().is_some() {
            let mut syscall_attr = None;
            while let Some(TokenKind::Punct('#')) = cursor.peek_kind() {
                cursor.bump(); // Skip the `#`
                let attr_body = cursor.parse_group(Delimiter::Bracket)?;
                syscall_attr = Self::parse_syscall_attr(attr_body)?;
            }

            if cursor.peek().is_none() {
                break;
            }

            let variant_name = cursor.parse_ident()?;
            
            // Parse optional discriminant (= value)
            let discriminant = if cursor.check_punct('=') {
                cursor.bump(); // consume '='
                let lit = cursor.parse_literal()?;
                Some(lit.to_string().parse::<usize>()
                    .map_err(|_| Error::new("Invalid discriminant value", lit.span()))?)
            } else {
                None
            };
            
            cursor.expect_punct(',')?;

            if let Some((params, ret)) = syscall_attr {
                variants.push(ast::Variant {
                    name: variant_name,
                    id: discriminant,
                    params,
                    ret,
                });
            }
        }
        Ok(variants)
    }

    /// Parses a syscall attribute from an attribute token group.
    ///
    /// This method processes `#[syscall(...)]` attributes and extracts the
    /// syscall metadata including ID, parameters, and return type.
    ///
    /// # Arguments
    /// * `attr_body` - TokenStream containing the attribute content
    ///
    /// # Returns
    /// * `Ok(Some(...))` - Successfully parsed syscall attribute
    /// * `Ok(None)` - Not a syscall attribute (should be ignored)
    /// * `Err(Error)` - Malformed syscall attribute syntax
    fn parse_syscall_attr(
        attr_body: TokenStream,
    ) -> Result<Option<(Vec<ast::Param>, ast::ReturnType)>> {
        let mut attr_tokens = attr_body.into_iter().peekable();
        let mut cursor = TokenCursor::new(&mut attr_tokens);

        if !cursor.eat_ident("syscall") {
            return Ok(None);
        }

        let params_body = cursor.parse_group(Delimiter::Parenthesis)?;
        let (params, ret) = Self::parse_syscall_params(params_body)?;

        Ok(Some((params, ret)))
    }

    /// Parses the parameter list within a syscall attribute.
    ///
    /// This method processes the content inside `syscall(...)` and extracts:
    /// - Parameter specifications with names and types  
    /// - Return type specification
    ///
    /// # Arguments
    /// * `params_body` - TokenStream containing the syscall parameters
    ///
    /// # Returns
    /// * `Ok((params, ret))` - Parsed syscall metadata
    /// * `Err(Error)` - Invalid parameter syntax
    fn parse_syscall_params(
        params_body: TokenStream,
    ) -> Result<(Vec<ast::Param>, ast::ReturnType)> {
        let mut params_tokens = params_body.into_iter().peekable();
        let mut cursor = TokenCursor::new(&mut params_tokens);

        let mut params = Vec::new();
        let mut ret = None;

        while cursor.peek().is_some() {
            let key = cursor.parse_ident()?;

            match key.to_string().as_str() {
                "params" => {
                    let params_group = cursor.parse_group(Delimiter::Parenthesis)?;
                    params = Self::parse_params_list(params_group)?;
                }
                "ret" => {
                    let ret_group = cursor.parse_group(Delimiter::Parenthesis)?;
                    ret = Some(Self::parse_return_type(ret_group)?);
                }
                _ => {
                    return Err(Error::new(format!("Unexpected key: {}", key), key.span()));
                }
            }

            cursor.eat_punct(','); // Skip the comma
        }

        let ret = ret.ok_or_else(|| Error::new("Return type is required", cursor.span()))?;

        Ok((params, ret))
    }

    /// Parses a parameter list within the syscall attribute parameters section.
    ///
    /// This method processes the content inside `params(...)` and extracts each
    /// parameter with its name and type specification.
    ///
    /// # Arguments
    /// * `tokens` - TokenStream containing the parameter list
    ///
    /// # Returns
    /// * `Ok(Vec<ast::Param>)` - Successfully parsed parameter list
    /// * `Err(Error)` - Invalid parameter syntax
    fn parse_params_list(tokens: TokenStream) -> Result<Vec<ast::Param>> {
        let mut tokens = tokens.into_iter().peekable();
        let mut cursor = TokenCursor::new(&mut tokens);
        let mut params = Vec::new();

        while cursor.peek().is_some() {
            let name = cursor.parse_ident()?;
            cursor.expect_punct(':')?;
            let ty = Self::parse_type(&mut cursor)?;

            params.push(ast::Param { name: name, ty });

            cursor.eat_punct(',');
        }

        Ok(params)
    }

    /// Parses a type specification from the token stream.
    ///
    /// This method handles complex type parsing including generic types,
    /// references, and nested type constructs. It properly tracks bracket
    /// depth to handle complex generic type specifications.
    ///
    /// # Arguments
    /// * `cursor` - Token cursor positioned at the start of the type
    ///
    /// # Returns
    /// * `Ok(ast::Type)` - Successfully parsed type information
    /// * `Err(Error)` - Invalid type syntax
    fn parse_type(cursor: &mut TokenCursor) -> Result<ast::Type> {
        let mut tokens = Vec::new();
        let start_span = cursor.span();
        let mut depth = 0;

        while let Some(token) = cursor.peek() {
            match token {
                TokenTree::Punct(p) => match p.as_char() {
                    '<' => {
                        depth += 1;
                        tokens.push(cursor.bump().unwrap());
                    }
                    '>' => {
                        if depth == 0 {
                            break;
                        }
                        depth -= 1;
                        tokens.push(cursor.bump().unwrap());
                    }
                    ',' | ')' | ';' if depth == 0 => break,
                    _ => tokens.push(cursor.bump().unwrap()),
                },
                _ => tokens.push(cursor.bump().unwrap()),
            }
        }

        if tokens.is_empty() {
            return Err(Error::new("Expected type, found nothing", start_span));
        }

        Ok(ast::Type {
            tokens: TokenStream::from_iter(tokens),
            span: start_span,
        })
    }

    /// Parses a return type specification from the syscall attribute.
    ///
    /// This method processes the content inside `ret(...)` and handles both
    /// concrete return types and the never type (`!`) for syscalls that
    /// don't return normally.
    ///
    /// # Arguments
    /// * `tokens` - TokenStream containing the return type specification
    ///
    /// # Returns
    /// * `Ok(ast::ReturnType)` - Successfully parsed return type
    /// * `Err(Error)` - Invalid return type syntax
    fn parse_return_type(tokens: TokenStream) -> Result<ast::ReturnType> {
        let mut tokens = tokens.into_iter().peekable();
        let mut cursor = TokenCursor::new(&mut tokens);

        if cursor.peek().is_none() {
            return Err(Error::new(
                "Expected return type, found nothing",
                cursor.span(),
            ));
        }

        if let Some(TokenKind::Punct('!')) = cursor.peek_kind() {
            cursor.bump(); // Skip the '!'
            return Ok(ast::ReturnType::Never);
        }

        let ty = Self::parse_type(&mut cursor)?;
        Ok(ast::ReturnType::Type(ty))
    }
}

/// Token cursor utility for parsing operations.
///
/// This structure provides convenient methods for traversing and parsing
/// tokens with lookahead capabilities and proper error reporting.
struct TokenCursor<'a> {
    /// Reference to the token iterator with lookahead capability
    tokens: &'a mut Peekable<proc_macro::token_stream::IntoIter>,
    /// Current span for error reporting purposes
    current_span: proc_macro::Span,
}

impl<'a> TokenCursor<'a> {
    /// Creates a new token cursor from a token iterator.
    ///
    /// # Arguments
    /// * `tokens` - Mutable reference to a peekable token iterator
    pub fn new(tokens: &'a mut Peekable<proc_macro::token_stream::IntoIter>) -> Self {
        let current_span = proc_macro::Span::call_site();
        Self {
            tokens,
            current_span,
        }
    }

    /// Advances the cursor and returns the next token.
    ///
    /// Updates the current span for error reporting.
    ///
    /// # Returns
    /// * `Some(TokenTree)` - The next token in the stream
    /// * `None` - End of token stream reached
    pub fn bump(&mut self) -> Option<proc_macro::TokenTree> {
        self.tokens.next().map(|token| {
            self.current_span = token.span();
            token
        })
    }

    /// Peeks at the next token without consuming it.
    ///
    /// # Returns
    /// * `Some(&TokenTree)` - Reference to the next token
    /// * `None` - End of token stream reached
    pub fn peek(&mut self) -> Option<&proc_macro::TokenTree> {
        self.tokens.peek()
    }

    /// Gets the current source span for error reporting.
    ///
    /// # Returns
    /// The current span information
    pub fn span(&self) -> proc_macro::Span {
        self.current_span
    }

    /// Peeks at the next token and classifies its kind.
    ///
    /// # Returns
    /// * `Some(TokenKind)` - Classification of the next token
    /// * `None` - End of token stream reached
    pub fn peek_kind(&mut self) -> Option<TokenKind> {
        self.peek().map(|token| match token {
            TokenTree::Ident(_) => TokenKind::Ident,
            TokenTree::Punct(p) => TokenKind::Punct(p.as_char()),
            TokenTree::Literal(_) => TokenKind::Literal,
            TokenTree::Group(g) => TokenKind::Group(g.delimiter()),
        })
    }

    /// Skips over attribute tokens in the stream.
    ///
    /// This method is used to ignore attributes that are not relevant
    /// to syscall parsing.
    ///
    /// # Returns
    /// * `Ok(())` - Successfully skipped attributes
    /// * `Err(Error)` - Malformed attribute syntax
    pub fn skip_attributes(&mut self) -> Result<()> {
        while let Some(TokenKind::Punct('#')) = self.peek_kind() {
            self.bump(); // Skip '#'
            self.parse_group(Delimiter::Bracket)?; // Skip the attribute content
        }
        Ok(())
    }

    /// Parses a grouped token sequence (parentheses, brackets, braces).
    ///
    /// # Arguments
    /// * `expected_delimiter` - The expected delimiter type
    ///
    /// # Returns
    /// * `Ok(TokenStream)` - Content of the group
    /// * `Err(Error)` - Wrong delimiter or missing group
    pub fn parse_group(&mut self, expected_delimiter: Delimiter) -> Result<TokenStream> {
        match self.bump() {
            Some(TokenTree::Group(g)) => {
                if g.delimiter() == expected_delimiter {
                    Ok(g.stream())
                } else {
                    Err(Error::new(
                        format!("Expected {:?} group", expected_delimiter),
                        self.span(),
                    ))
                }
            }
            Some(token) => Err(Error::new(
                format!("Expected group, found {:?}", token),
                self.span(),
            )),
            None => Err(Error::new("Unexpected end of input", self.span())),
        }
    }

    /// Checks if the next token is a specific punctuation character without consuming it.
    ///
    /// # Arguments
    /// * `ch` - The punctuation character to check for
    ///
    /// # Returns
    /// * `true` - Character matches (cursor unchanged)
    /// * `false` - Character does not match
    fn check_punct(&mut self, ch: char) -> bool {
        if let Some(TokenKind::Punct(c)) = self.peek_kind() {
            c == ch
        } else {
            false
        }
    }

    /// Consumes a punctuation character if it matches the expected character.
    ///
    /// # Arguments
    /// * `ch` - The expected punctuation character
    ///
    /// # Returns
    /// * `true` - Character matched and consumed
    /// * `false` - Character did not match (cursor unchanged)
    fn eat_punct(&mut self, ch: char) -> bool {
        if let Some(TokenKind::Punct(c)) = self.peek_kind() {
            if c == ch {
                self.bump();
                return true;
            }
        }
        false
    }

    /// Expects and consumes a specific punctuation character.
    ///
    /// # Arguments
    /// * `ch` - The required punctuation character
    ///
    /// # Returns
    /// * `Ok(())` - Character found and consumed
    /// * `Err(Error)` - Character not found
    fn expect_punct(&mut self, ch: char) -> Result<()> {
        if !self.eat_punct(ch) {
            return Err(Error::new(
                format!("Expected punctuation '{}'", ch),
                self.span(),
            ));
        }
        Ok(())
    }

    /// Consumes an identifier if it matches the expected string.
    ///
    /// # Arguments
    /// * `expected` - The expected identifier string
    ///
    /// # Returns
    /// * `true` - Identifier matched and consumed
    /// * `false` - Identifier did not match (cursor unchanged)
    fn eat_ident(&mut self, expected: &str) -> bool {
        if let Some(TokenTree::Ident(i)) = self.tokens.peek() {
            if i.to_string() == expected {
                self.bump();
                return true;
            }
        }
        false
    }

    /// Parses and consumes an identifier token.
    ///
    /// # Returns
    /// * `Ok(Ident)` - Successfully parsed identifier
    /// * `Err(Error)` - Expected identifier but found something else
    fn parse_ident(&mut self) -> Result<Ident> {
        match self.bump() {
            Some(TokenTree::Ident(i)) => Ok(i),
            Some(token) => Err(Error::new(
                format!("Expected identifier, found {:?}", token),
                self.span(),
            )),
            None => Err(Error::new("Unexpected end of input", self.span())),
        }
    }

    /// Parses and consumes a literal token.
    ///
    /// # Returns
    /// * `Ok(Literal)` - Successfully parsed literal
    /// * `Err(Error)` - Expected literal but found something else
    fn parse_literal(&mut self) -> Result<Literal> {
        match self.bump() {
            Some(TokenTree::Literal(lit)) => Ok(lit),
            Some(token) => Err(Error::new(
                format!("Expected literal, found {:?}", token),
                self.span(),
            )),
            None => Err(Error::new("Unexpected end of input", self.span())),
        }
    }
}

/// Parses generic type arguments from angle brackets.
///
/// This function processes generic type syntax like `<T>` or `<T, U>` and
/// extracts the type parameters for further processing.
///
/// # Arguments
/// * `tokens` - Mutable iterator over tokens positioned before potential `<`
///
/// # Returns
/// * `Some(Type)` - Successfully parsed single type argument
/// * `None` - No generic arguments found
/// * `Err(Error)` - Malformed generic syntax
pub fn parse_generic_arg_iter(
    tokens: &mut Peekable<impl Iterator<Item = TokenTree>>,
) -> Result<Option<ast::Type>> {
    if let Some(TokenTree::Punct(p)) = tokens.peek() {
        if p.as_char() == '<' {
            tokens.next(); // consume '<'
            let mut depth = 1;
            let mut inner_tokens = Vec::new();

            while depth > 0 {
                match tokens.next() {
                    Some(TokenTree::Punct(p)) => {
                        match p.as_char() {
                            '<' => depth += 1,
                            '>' => {
                                depth -= 1;
                                if depth == 0 {
                                    break; // matched closing '>'
                                }
                            }
                            _ => {}
                        }
                        if depth > 0 {
                            inner_tokens.push(TokenTree::Punct(p));
                        }
                    }
                    Some(token) => inner_tokens.push(token),
                    None => return Err(Error::new("unmatched '<'", proc_macro::Span::call_site())),
                }
            }

            return Ok(Some(ast::Type {
                tokens: inner_tokens.into_iter().collect(),
                span: proc_macro::Span::call_site(),
            }));
        }
    }
    Ok(None)
}

use std::iter::Peekable;
use proc_macro::Delimiter;
use proc_macro::Literal;
use proc_macro::TokenStream;
use proc_macro::TokenTree;
use proc_macro::Ident;

use crate::syscall::ast;

use super::error::{Error, Result};

#[derive(Debug, Clone, PartialEq, Eq)]
enum TokenKind {
    Ident,
    Punct(char),
    Literal,
    Group(proc_macro::Delimiter),
}

pub struct Parser {
    tokens: Peekable<proc_macro::token_stream::IntoIter>,
}

impl Parser {
    pub fn new(tokens: proc_macro::TokenStream) -> Self {
        Self {
            tokens: tokens.into_iter().peekable(),
        }
    }

    pub fn parse_enum(&mut self) -> Result<ast::Enum> {
        let mut cursor = TokenCursor::new(&mut self.tokens);
        cursor.skip_attributes()?;

        if !cursor.eat_ident("enum") {
            return Err(Error::new("Expected 'enum' keyword", cursor.span()));
        }

        let name = cursor.parse_ident()?;
        let body = cursor.parse_group(Delimiter::Brace)?;

        let variants = Self::parse_variants(body)?;

        Ok(ast::Enum {
            name,
            variants,
        })
    }

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
            cursor.expect_punct(',');

            if let Some((id, params, ret)) = syscall_attr {
                variants.push(ast::Variant {
                    name: variant_name,
                    id,
                    params,
                    ret,
                });
            }
        }
        Ok(variants)
    }

    fn parse_syscall_attr(attr_body: TokenStream) -> Result<Option<(usize, Vec<ast::Param>, ast::ReturnType)>> {
        let mut attr_tokens = attr_body.into_iter().peekable();
        let mut cursor = TokenCursor::new(&mut attr_tokens);
        
        if !cursor.eat_ident("syscall") {
            return Ok(None);
        }

        let params_body = cursor.parse_group(Delimiter::Parenthesis)?;
        let (id, params, ret) = Self::parse_syscall_params(params_body)?;

        Ok(Some((id, params, ret)))
    }

    fn parse_syscall_params(params_body: TokenStream) -> Result<(usize, Vec<ast::Param>, ast::ReturnType)> {
        let mut params_tokens = params_body.into_iter().peekable();
        let mut cursor = TokenCursor::new(&mut params_tokens);
        
        let mut id = None;
        let mut params = Vec::new();
        let mut ret = None;

        while cursor.peek().is_some() {
            let key = cursor.parse_ident()?;

            match key.to_string().as_str() {
                "id" => {
                    cursor.expect_punct('=')?;
                    let id_lit = cursor.parse_literal()?;
                    id = Some(id_lit.to_string().parse::<usize>().map_err(|_| {
                        Error::new("Invalid syscall ID", id_lit.span())
                    })?);
                }
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

        let id = id.ok_or_else(|| Error::new("Syscall ID is required", cursor.span()))?;
        let ret = ret.ok_or_else(|| Error::new("Return type is required", cursor.span()))?;
        
        Ok((id, params, ret))
    }

    fn parse_params_list(tokens: TokenStream) -> Result<Vec<ast::Param>> {
        let mut tokens = tokens.into_iter().peekable();
        let mut cursor = TokenCursor::new(&mut tokens);
        let mut params = Vec::new();

        while cursor.peek().is_some() {
            let name = cursor.parse_ident()?;
            cursor.expect_punct(':')?;
            let ty = Self::parse_type(&mut cursor)?;

            params.push(ast::Param {
                name: name,
                ty,
            });

            cursor.eat_punct(',');
        }

        Ok(params)
    }

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

        Ok(
            ast::Type {
                tokens: TokenStream::from_iter(tokens),
                span: start_span,
            })
    }

    fn parse_return_type(tokens: TokenStream) -> Result<ast::ReturnType> {
        let mut tokens = tokens.into_iter().peekable();
        let mut cursor = TokenCursor::new(&mut tokens);

        if cursor.peek().is_none() {
            return Err(Error::new("Expected return type, found nothing", cursor.span()));
        }

        if let Some(TokenKind::Punct('!')) = cursor.peek_kind() {
            cursor.bump(); // Skip the '!'
            return Ok(ast::ReturnType::Never);
        }

        let ty = Self::parse_type(&mut cursor)?;
        Ok(ast::ReturnType::Type(ty))
    }
}

struct TokenCursor<'a> {
    tokens: &'a mut Peekable<proc_macro::token_stream::IntoIter>,
    current_span: proc_macro::Span,
}

impl<'a> TokenCursor<'a> {
    pub fn new(tokens: &'a mut Peekable<proc_macro::token_stream::IntoIter>) -> Self {
        let current_span = proc_macro::Span::call_site();
        Self {
            tokens,
            current_span,
        }
    }

    pub fn bump(&mut self) -> Option<proc_macro::TokenTree> {
         self.tokens.next().map(|token| {
            self.current_span = token.span();
            token
         })
    }

    pub fn peek(&mut self) -> Option<&proc_macro::TokenTree> {
        self.tokens.peek()
    }

    pub fn span(&self) -> proc_macro::Span {
        self.current_span
    } 

    fn peek_kind(&mut self) -> Option<TokenKind> {
        self.peek().map(|token| match token {
            proc_macro::TokenTree::Ident(_) => TokenKind::Ident,
            proc_macro::TokenTree::Punct(p) => TokenKind::Punct(p.as_char()),
            proc_macro::TokenTree::Literal(_) => TokenKind::Literal,
            proc_macro::TokenTree::Group(g) => TokenKind::Group(g.delimiter()),
        })
    }
    
    fn eat_punct(&mut self, ch: char) -> bool {
        if let Some(TokenKind::Punct(c)) = self.peek_kind() {
            if c == ch {
                self.bump();
                return true;
            }
        }
        false
    }

    fn expect_punct(&mut self, ch: char) -> Result<()> {
        if !self.eat_punct(ch) {
            return Err(Error::new(
                format!("Expected punctuation '{}'", ch),
                self.span(),
            ));
        }
        Ok(())
    }

    fn eat_ident(&mut self, expected: &str) -> bool {
        if let Some(TokenTree::Ident(i)) = self.tokens.peek() {
            if i.to_string() == expected {
                self.bump();
                return true;
            }
        }
        false
    }

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
    
    fn parse_group(&mut self, delimiter: Delimiter) -> Result<TokenStream> {
        match self.bump() {
            Some(TokenTree::Group(g)) if g.delimiter() == delimiter => Ok(g.stream()),
            Some(token) => Err(Error::new(
            format!("Expected group with delimiter {:?}, found {:?}", delimiter, token),
                self.span(),
            )),
            None => Err(Error::new("Unexpected end of input", self.span())),
        }
    }

    fn skip_attributes(&mut self) -> Result<()> {
        while let Some(TokenKind::Punct('#')) = self.peek_kind() {
            self.bump(); // Skip the `#`
            self.parse_group(Delimiter::Bracket)?; // Skip the attribute group
        }
        Ok(())
    }
}

/// `<T>` や `<T, U>` のようなジェネリック引数をパースする
/// 
/// # Returns
/// - `Some(Type)` - 単一の型引数の場合
/// - `None` - ジェネリック引数がない場合
pub fn parse_generic_arg_iter(tokens: &mut Peekable<impl Iterator<Item = TokenTree>>) -> Result<Option<ast::Type>> {
    if let Some(TokenTree::Punct(p)) = tokens.peek() {
        if p.as_char() == '<' {
            tokens.next(); // consume '<'
            let mut depth = 1;
            let mut inner_tokens = Vec::new();

            while depth > 0 {
                match tokens.next() {
                    Some(TokenTree::Punct(p)) => {
                        match p.as_char() {
                            '<' => depth +=1,
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
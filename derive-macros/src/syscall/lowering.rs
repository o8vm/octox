use std::iter::Peekable;

use crate::syscall::constants::MAX_ARG_REGS;

use super::ir;
use super::ast;
use super::error::{Error, Result};
use super::parser::parse_generic_arg_iter;
use proc_macro::Ident;
use proc_macro::Span;
use proc_macro::TokenTree;

pub fn lower_to_ir(ast: ast::Enum) -> Result<ir::SyscallRegistry> {
    let mut registry = ir::SyscallRegistry::new(ast.name);

    for variant in ast.variants {
        let syscall = lower_variant(variant)?;
        registry.add_syscall(syscall);
    }

    Ok(registry)
}

fn lower_variant(variant: ast::Variant) -> Result<ir::Syscall> {
    let id = ir::SyscallId::from(variant.id as u16);

    let mut params = Vec::new();

    for param in variant.params {
        let typ = lower_param_type(&param.ty)?;
        params.push(ir::Param {
            rust_name: param.name,
            ty: typ,
        });
    }

    let reg_count = params.len().min(MAX_ARG_REGS as usize) as u8;

    if reg_count < MAX_ARG_REGS {
        return Err(Error::new(
            format!(
                "too many parameters for syscall '{}': expected at most {} but got {}",
                variant.name, MAX_ARG_REGS, reg_count
            ),
            Span::call_site(),
        ));
    }

    let ret = lower_return(variant.ret)?;

    let rust_name = Ident::new(&variant.name.to_string().to_lowercase(), variant.name.span());

    Ok(ir::Syscall {
        id,
        variant_name: variant.name,
        rust_name,
        params,
        ret,
        reg_count,
    })
}

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
                let tt = tokens
                    .peek()
                    .ok_or_else(|| Error::new("expected 'const' or 'mut' after '*'", ast_ty.span))?;

                // Destructure into an Ident or bail out
                let TokenTree::Ident(ident) = tt else {
                    return Err(Error::new("expected 'const' or 'mut' after '*'", ast_ty.span));
                };

                // Match on the stringified identifier
                match ident.to_string().as_str() {
                    "const" => { 
                        tokens.next(); // consume 'const'
                        false 
                    },
                    "mut"   => {
                        tokens.next();  // consume 'mut'
                        true
                    },
                    _ => return Err(Error::new("expected 'const' or 'mut' after '*'", ast_ty.span)),
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
    if let Some(TokenTree::Ident(ident)) = tokens.peek() && ident.to_string() == "Option" {
        tokens.next(); // consume 'Option'
        if let Some(inner_ast) = parse_generic_arg_iter(&mut tokens)? {
            let inner_type = lower_param_type(&inner_ast)?;
            return Ok(ir::Type::Option{ inner: Box::new(inner_type)});
        }
    }

    Err(Error::new(
        format!("unsupported type: {}", type_str),
        ast_ty.span,
    ))
}

fn lower_return(ret: ast::ReturnType) -> Result<ir::ReturnType> {
    match ret {        
        ast::ReturnType::Never => Ok(ir::ReturnType::Never),
        ast::ReturnType::Type(ast_ty) => lower_return_type(&ast_ty)
    }
}

fn lower_return_type(typ: &ast::Type) -> Result<ir::ReturnType> {
    let mut tokens = typ.tokens.clone().into_iter().peekable();
    if let Some(TokenTree::Ident(i)) = tokens.peek() && i.to_string() == "Result" {
        tokens.next(); // consume 'Result'
        lower_result_type(tokens, typ.span)
    } else {
        Err(Error::new("expected 'Result' type", typ.span))
    }
}

fn lower_result_type(mut tokens: Peekable<impl Iterator<Item = TokenTree>>, span: Span) -> Result<ir::ReturnType> {
    // ジェネリクス引数を抽出
    match parse_generic_arg_iter(&mut tokens) {
        Ok(Some(args)) => lower_result_type_param(&args, span),
        Ok(None) => Err(Error::new("expected generic arguments for Result type", span)),
        Err(e) => Err(e),
    }
}

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

    // 二番目の引数がある場合、それが Error 型であることを確認する
    // has_error_param が true の場合、残りのトークンが "Error" であることを確認する
    // もし "Error" でなければエラーを返す
    // false の場合は、 Result<T> として受け入れる
    if has_error_param {
        let remainig: String = tokens
            .map(|tt| tt.to_string())
            .collect::<Vec<_>>()
            .join("")
            .trim()
            .to_string();

        if remainig != "Error" {
            return Err(Error::new(
                format!("expected 'Error' type in Result, found '{}'", remainig),
                span,
            ));
        }
    }

    // 最初の型を文字列に変換して評価
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
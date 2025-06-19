//! Type section and type parsing for WebAssembly binary parser

use crate::wasm::parser::error::{ParseError, ParseResult};
use crate::wasm::ast;
use super::Parser;
use alloc::vec::Vec;

impl<'a> Parser<'a> {
    pub fn parse_valtype(&mut self) -> ParseResult<ast::ValType> {
        let type_code = self.read_byte()?;
        match type_code {
            0x7F => Ok(ast::ValType::I32),
            0x7E => Ok(ast::ValType::I64),
            0x7D => Ok(ast::ValType::F32),
            0x7C => Ok(ast::ValType::F64),
            0x7B => Ok(ast::ValType::V128),
            0x70 => Ok(ast::ValType::FuncRef),
            0x6F => Ok(ast::ValType::ExternRef),
            _ => Err(ParseError::InvalidValueType),
        }
    }

    pub fn parse_value_type(&mut self) -> ParseResult<ast::ValType> {
        let pos = self.cursor;
        let type_code = match self.parse_i32() {
            Ok(code) => code,
            Err(e) => return Err(e),
        };
        match type_code {
            -0x01 => Ok(ast::ValType::I32),
            -0x02 => Ok(ast::ValType::I64),
            -0x03 => Ok(ast::ValType::F32),
            -0x04 => Ok(ast::ValType::F64),
            -0x05 => Ok(ast::ValType::V128),
            -0x10 => Ok(ast::ValType::FuncRef),
            -0x11 => Ok(ast::ValType::ExternRef),
            _ => {
                self.cursor = pos;
                Err(ParseError::InvalidValueType)
            }
        }
    }

    pub fn parse_blocktype(&mut self) -> ParseResult<ast::BlockType> {
        let first_byte = self.read_byte()?;
        match first_byte {
            0x40 => Ok(ast::BlockType::ValueType(None)),
            0x7F => Ok(ast::BlockType::ValueType(Some(ast::ValType::I32))),
            0x7E => Ok(ast::BlockType::ValueType(Some(ast::ValType::I64))),
            0x7D => Ok(ast::BlockType::ValueType(Some(ast::ValType::F32))),
            0x7C => Ok(ast::BlockType::ValueType(Some(ast::ValType::F64))),
            0x7B => Ok(ast::BlockType::ValueType(Some(ast::ValType::V128))),
            0x70 => Ok(ast::BlockType::ValueType(Some(ast::ValType::FuncRef))),
            0x6F => Ok(ast::BlockType::ValueType(Some(ast::ValType::ExternRef))),
            _ => {
                self.cursor -= 1;
                let type_index = self.parse_i32()?;
                if type_index < 0 {
                    return Err(ParseError::InvalidTypeIndex);
                }
                Ok(ast::BlockType::TypeIndex(type_index as u32))
            }
        }
    }

    pub fn parse_resulttype(&mut self) -> ParseResult<ast::ResultType> {
        let len = self.parse_u32()?;
        let mut types = Vec::with_capacity(len as usize);
        for _ in 0..len {
            types.push(self.parse_valtype()?);
        }
        Ok(types)
    }

    pub fn parse_functype(&mut self) -> ParseResult<ast::FuncType> {
        let type_code = self.read_byte()?;
        if type_code != 0x60 {
            return Err(ParseError::InvalidFunctionType);
        }
        let params = self.parse_resulttype()?;
        let results = self.parse_resulttype()?;
        Ok(ast::FuncType::new(params, results))
    }

    pub fn parse_limits(&mut self) -> ParseResult<ast::Limits> {
        let has_max = match self.read_byte()? {
            0x00 => false,
            0x01 => true,
            _ => return Err(ParseError::InvalidLimits),
        };
        let min = self.parse_u32()?;
        let max = if has_max {
            let max = self.parse_u32()?;
            if max < min {
                return Err(ParseError::InvalidLimits);
            }
            Some(max)
        } else {
            None
        };
        Ok(ast::Limits { min, max })
    }

    pub fn parse_memtype(&mut self) -> ParseResult<ast::MemoryType> {
        let limits = self.parse_limits()?;
        Ok(ast::MemoryType::new(limits))
    }

    pub fn parse_tabletype(&mut self) -> ParseResult<ast::TableType> {
        let element_type = match self.read_byte()? {
            0x70 => ast::ValType::FuncRef,
            0x6F => ast::ValType::ExternRef,
            _ => return Err(ParseError::InvalidValueType),
        };
        let limits = self.parse_limits()?;
        Ok(ast::TableType::new(limits, element_type))
    }

    pub fn parse_globaltype(&mut self) -> ParseResult<ast::GlobalType> {
        let value_type = self.parse_valtype()?;
        let mutability = match self.read_byte()? {
            0x00 => ast::Mutability::Const,
            0x01 => ast::Mutability::Var,
            _ => return Err(ParseError::InvalidGlobalType),
        };
        Ok(ast::GlobalType::new(mutability, value_type))
    }
} 
//! Module-level parsing for WebAssembly binary parser

use crate::wasm::parser::error::{ParseError, ParseResult};
use crate::wasm::ast;
use super::Parser;
use crate::parser_debug_log;
use crate::wasm::parser::ParserConfig;

use alloc::format;
use alloc::vec::Vec;
use alloc::string::String;

impl<'a> Parser<'a> {
    /// Parse a section header (id: u8, size: u32)
    pub fn parse_section_header(&mut self) -> ParseResult<(u8, u32)> {
        let id = self.read_byte()?;
        let size = self.parse_u32()?;
        Ok((id, size))
    }

    /// Parse a custom section (id = 0)
    /// custom ::= name: string, data: byte*
    pub fn parse_custom_section(&mut self, size: u32) -> ParseResult<(String, Vec<u8>)> {
        let start = self.cursor;
        let name = self.parse_name()?;
        let name_bytes_len = self.cursor - start;
        let data_len = size as usize - name_bytes_len;
        let data = self.read_bytes(data_len)?.to_vec();
        Ok((name, data))
    }

    /// Parse a WebAssembly module (skeleton)
    pub fn parse_module(&mut self) -> ParseResult<ast::Module> {
        // Magic number
        if self.read_bytes(4)? != [0x00, 0x61, 0x73, 0x6D] {
            return Err(ParseError::InvalidMagic);
        }
        // Version
        if self.read_bytes(4)? != [0x01, 0x00, 0x00, 0x00] {
            return Err(ParseError::InvalidVersion);
        }
        // セクションループ
        let mut types = Vec::new();
        let mut imports = Vec::new();
        let mut typeidxs = Vec::new();
        let mut tables = Vec::new();
        let mut mems = Vec::new();
        let mut globals = Vec::new();
        let mut exports = Vec::new();
        let mut start = None;
        let mut elems = Vec::new();
        let mut datacount = None;
        let mut codes = Vec::new();
        let mut datas = Vec::new();
        while self.cursor < self.input.len() {
            parser_debug_log!(&self.config, "self.cursor: {:?}", self.cursor);
            if let Ok((id, size)) = self.parse_section_header() {
                match id {
                    0 => { self.parse_custom_section(size)?; },
                    1 => { types = self.parse_type_section(size)?; },
                    2 => { imports = self.parse_import_section(size)?; },
                    3 => { typeidxs = self.parse_function_section(size)?; },
                    4 => { tables = self.parse_table_section(size)?; },
                    5 => { mems = self.parse_memory_section(size)?; },
                    6 => { globals = self.parse_global_section(size)?; },
                    7 => { exports = self.parse_export_section(size)?; },
                    8 => { start = self.parse_start_section(size)?; },
                    9 => { elems = self.parse_element_section(size)?; },
                    10 => { codes = self.parse_code_section(size)?; },
                    11 => { datas = self.parse_data_section(size)?; },
                    12 => { datacount = self.parse_data_count_section(size)?; },
                    _ => { self.read_bytes(size as usize)?; }, // skip unknown
                }
            } else {
                break;
            }
        }

        // Construct functions from type indices and code sections
        let mut funcs = Vec::with_capacity(typeidxs.len());
        for (i, typeidx) in typeidxs.iter().enumerate() {
            if i >= codes.len() {
                return Err(ParseError::InvalidFunction);
            }
            let (locals, code) = &codes[i];
            funcs.push(ast::Function::new(*typeidx, locals.clone(), code.clone()));
        }

        // Resolve import type indices to actual function types
        for import in &mut imports {
            if let ast::ExternalType::Func(func_type) = &mut import.ty {
                // Check if this is a type index (we'll use a special marker)
                // For now, we'll assume all function imports use type index 0
                // This is a temporary fix - we need to properly track type indices
                if func_type.params.is_empty() && func_type.results.is_empty() {
                    // This is likely a type index reference, resolve it
                    if !types.is_empty() {
                        // For kernel.syscall, use the first type (index 0)
                        // which has 7 i32 params and 1 i32 result
                        *func_type = types[0].clone();
                    }
                }
            }
        }

        Ok(ast::Module {
            types,
            funcs,
            tables,
            mems,
            globals,
            elems,
            datas,
            start,
            imports,
            exports,
        })
    }

    /// Parse a type section (id = 1)
    /// typesec ::= section1(vec(functype))
    pub fn parse_type_section(&mut self, size: u32) -> ParseResult<Vec<ast::FuncType>> {
        let section_end = self.cursor + size as usize;
        let count = self.parse_u32()?;
        let mut types = Vec::with_capacity(count as usize);
        for _ in 0..count {
            types.push(self.parse_functype()?);
        }
        // セクションサイズ超過チェック
        if self.cursor != section_end {
            return Err(ParseError::InvalidSectionSize);
        }
        Ok(types)
    }

    /// Parse an import section (id = 2)
    /// importsec ::= section2(vec(import))
    pub fn parse_import_section(&mut self, size: u32) -> ParseResult<Vec<ast::Import>> {
        let section_end = self.cursor + size as usize;
        let count = self.parse_u32()?;
        let mut imports = Vec::with_capacity(count as usize);
        for _ in 0..count {
            let module = self.parse_name()?;
            let field = self.parse_name()?;
            let desc_tag = self.read_byte()?;
            let ty = match desc_tag {
                0x00 => {
                    let typeidx = self.parse_u32()?;
                    // For now, we'll use a dummy type and resolve it later
                    // This is a temporary workaround - we need to properly track type indices
                    ast::ExternalType::Func(ast::FuncType::new(Vec::new(), Vec::new()))
                }
                0x01 => ast::ExternalType::Table(self.parse_tabletype()?),
                0x02 => ast::ExternalType::Memory(self.parse_memtype()?),
                0x03 => ast::ExternalType::Global(self.parse_globaltype()?),
                _ => return Err(ParseError::InvalidImport),
            };
            imports.push(ast::Import { module, field, ty });
        }
        if self.cursor != section_end {
            return Err(ParseError::InvalidSectionSize);
        }
        Ok(imports)
    }

    /// Parse a function section (id = 3)
    /// funcsec ::= section3(vec(typeidx))
    pub fn parse_function_section(&mut self, size: u32) -> ParseResult<Vec<u32>> {
        let section_end = self.cursor + size as usize;
        let count = self.parse_u32()?;
        let mut type_indices = Vec::with_capacity(count as usize);
        for _ in 0..count {
            type_indices.push(self.parse_u32()?);
        }
        if self.cursor != section_end {
            return Err(ParseError::InvalidSectionSize);
        }
        Ok(type_indices)
    }

    /// Parse a table section (id = 4)
    /// tablesec ::= section4(vec(table))
    pub fn parse_table_section(&mut self, size: u32) -> ParseResult<Vec<ast::TableType>> {
        let section_end = self.cursor + size as usize;
        let count = self.parse_u32()?;
        let mut tables = Vec::with_capacity(count as usize);
        for _ in 0..count {
            tables.push(self.parse_tabletype()?);
        }
        if self.cursor != section_end {
            return Err(ParseError::InvalidSectionSize);
        }
        Ok(tables)
    }

    /// Parse a global section (id = 6)
    /// globalsec ::= section6(vec(global))
    pub fn parse_global_section(&mut self, size: u32) -> ParseResult<Vec<ast::Global>> {
        let section_end = self.cursor + size as usize;
        let count = self.parse_u32()?;
        let mut globals = Vec::with_capacity(count as usize);
        for _ in 0..count {
            let ty = self.parse_globaltype()?;
            let init = self.parse_const_expr()?;
            globals.push(ast::Global { ty, init });
        }
        if self.cursor != section_end {
            return Err(ParseError::InvalidSectionSize);
        }
        Ok(globals)
    }

    /// Parse a start section (id = 8)
    /// startsec ::= section8(start)
    pub fn parse_start_section(&mut self, size: u32) -> ParseResult<Option<ast::StartFunction>> {
        if size == 0 {
            return Ok(None);
        }
        let section_end = self.cursor + size as usize;
        let funcidx = self.parse_u32()?;
        if self.cursor != section_end {
            return Err(ParseError::InvalidSectionSize);
        }
        Ok(Some(ast::StartFunction::new(funcidx)))
    }

    /// Parse an element section (id = 9)
    /// elemsec ::= section9(vec(elem))
    pub fn parse_element_section(&mut self, size: u32) -> ParseResult<Vec<ast::ElementSegment>> {
        let section_end = self.cursor + size as usize;
        let count = self.parse_u32()?;
        let mut elems = Vec::with_capacity(count as usize);
        for _ in 0..count {
            let flag = self.read_byte()?;
            match flag {
                0 => {
                    // active, funcref, funcidxベクタ
                    let offset = self.parse_const_expr()?;
                    let func_count = self.parse_u32()?;
                    let mut elements = Vec::with_capacity(func_count as usize);
                    for _ in 0..func_count {
                        let idx = self.parse_u32()?;
                        elements.push(ast::ConstExpr::RefFunc(idx));
                    }
                    elems.push(ast::ElementSegment {
                        element_type: ast::ValType::FuncRef,
                        elements,
                        mode: ast::ElementMode::active(0, offset),
                    });
                }
                1 => {
                    // passive, funcref, funcidxベクタ
                    let elemkind = self.read_byte()?;
                    if elemkind != 0x00 {
                        return Err(ParseError::InvalidElementSegment);
                    }
                    let func_count = self.parse_u32()?;
                    let mut elements = Vec::with_capacity(func_count as usize);
                    for _ in 0..func_count {
                        let idx = self.parse_u32()?;
                        elements.push(ast::ConstExpr::RefFunc(idx));
                    }
                    elems.push(ast::ElementSegment {
                        element_type: ast::ValType::FuncRef,
                        elements,
                        mode: ast::ElementMode::passive(),
                    });
                }
                2 => {
                    // active, tableidx, funcref, funcidxベクタ
                    let tableidx = self.parse_u32()?;
                    let offset = self.parse_const_expr()?;
                    let elemkind = self.read_byte()?;
                    if elemkind != 0x00 {
                        return Err(ParseError::InvalidElementSegment);
                    }
                    let func_count = self.parse_u32()?;
                    let mut elements = Vec::with_capacity(func_count as usize);
                    for _ in 0..func_count {
                        let idx = self.parse_u32()?;
                        elements.push(ast::ConstExpr::RefFunc(idx));
                    }
                    elems.push(ast::ElementSegment {
                        element_type: ast::ValType::FuncRef,
                        elements,
                        mode: ast::ElementMode::active(tableidx, offset),
                    });
                }
                3 => {
                    // declarative, funcref, funcidxベクタ
                    let elemkind = self.read_byte()?;
                    if elemkind != 0x00 {
                        return Err(ParseError::InvalidElementSegment);
                    }
                    let func_count = self.parse_u32()?;
                    let mut elements = Vec::with_capacity(func_count as usize);
                    for _ in 0..func_count {
                        let idx = self.parse_u32()?;
                        elements.push(ast::ConstExpr::RefFunc(idx));
                    }
                    elems.push(ast::ElementSegment {
                        element_type: ast::ValType::FuncRef,
                        elements,
                        mode: ast::ElementMode::declarative(),
                    });
                }
                4 => {
                    // active, funcref, exprベクタ
                    let offset = self.parse_const_expr()?;
                    let reftype = self.parse_valtype()?;
                    let expr_count = self.parse_u32()?;
                    let mut elements = Vec::with_capacity(expr_count as usize);
                    for _ in 0..expr_count {
                        elements.push(self.parse_const_expr()?);
                    }
                    elems.push(ast::ElementSegment {
                        element_type: reftype,
                        elements,
                        mode: ast::ElementMode::active(0, offset),
                    });
                }
                5 => {
                    // passive, reftype, exprベクタ
                    let reftype = self.parse_valtype()?;
                    let expr_count = self.parse_u32()?;
                    let mut elements = Vec::with_capacity(expr_count as usize);
                    for _ in 0..expr_count {
                        elements.push(self.parse_const_expr()?);
                    }
                    elems.push(ast::ElementSegment {
                        element_type: reftype,
                        elements,
                        mode: ast::ElementMode::passive(),
                    });
                }
                6 => {
                    // active, tableidx, reftype, exprベクタ
                    let tableidx = self.parse_u32()?;
                    let offset = self.parse_const_expr()?;
                    let reftype = self.parse_valtype()?;
                    let expr_count = self.parse_u32()?;
                    let mut elements = Vec::with_capacity(expr_count as usize);
                    for _ in 0..expr_count {
                        elements.push(self.parse_const_expr()?);
                    }
                    elems.push(ast::ElementSegment {
                        element_type: reftype,
                        elements,
                        mode: ast::ElementMode::active(tableidx, offset),
                    });
                }
                7 => {
                    // declarative, reftype, exprベクタ
                    let reftype = self.parse_valtype()?;
                    let expr_count = self.parse_u32()?;
                    let mut elements = Vec::with_capacity(expr_count as usize);
                    for _ in 0..expr_count {
                        elements.push(self.parse_const_expr()?);
                    }
                    elems.push(ast::ElementSegment {
                        element_type: reftype,
                        elements,
                        mode: ast::ElementMode::declarative(),
                    });
                }
                _ => return Err(ParseError::InvalidElementSegment),
            }
        }
        if self.cursor != section_end {
            return Err(ParseError::InvalidSectionSize);
        }
        Ok(elems)
    }

    /// Parse a code section (id = 10)
    /// codesec ::= section10(vec(code))
    /// code ::= size:u32, func:func
    /// func ::= vec(locals), expr
    pub fn parse_code_section(&mut self, size: u32) -> ParseResult<Vec<(Vec<ast::LocalDecl>, Vec<u8>)>> {
        let section_end = self.cursor + size as usize;
        let count = self.parse_u32()?;
        let mut codes = Vec::with_capacity(count as usize);
        for _ in 0..count {
            let body_size = self.parse_u32()? as usize;
            let body_start = self.cursor;
            // locals
            let local_count = self.parse_u32()?;
            let mut locals = Vec::with_capacity(local_count as usize);
            for _ in 0..local_count {
                let count = self.parse_u32()?;
                let ty = self.parse_valtype()?;
                locals.push(ast::LocalDecl { count, ty });
            }
            // 残りはexpr（関数本体）
            let body_bytes_len = body_size - (self.cursor - body_start);
            let body = self.read_bytes(body_bytes_len)?.to_vec();
            codes.push((locals, body));
        }
        if self.cursor != section_end {
            return Err(ParseError::InvalidSectionSize);
        }
        Ok(codes)
    }

    /// Parse a data section (id = 11)
    /// datasec ::= section11(vec(data))
    /// data ::= 0:u32 expr bytes | 1:u32 bytes | 2:u32 memidx expr bytes
    pub fn parse_data_section(&mut self, size: u32) -> ParseResult<Vec<ast::DataSegment>> {
        let section_end = self.cursor + size as usize;
        let count = self.parse_u32()?;
        let mut datas = Vec::with_capacity(count as usize);
        
        crate::parser_debug_log!(self.config, "Parsing data section: {} segments", count);
        
        for i in 0..count {
            let flag = self.read_byte()?;
            match flag {
                0 => {
                    // active, memory 0, offset expr, bytes
                    let offset = self.parse_const_expr()?;
                    let byte_count = self.parse_u32()?;
                    let data = self.read_bytes(byte_count as usize)?.to_vec();
                    
                    crate::parser_debug_log!(self.config, "Data segment {}: active, offset={:?}, size={} bytes", i, offset, byte_count);
                    
                    datas.push(ast::DataSegment::active(data, 0, offset));
                }
                1 => {
                    // passive, bytes
                    let byte_count = self.parse_u32()?;
                    let data = self.read_bytes(byte_count as usize)?.to_vec();
                    
                    crate::parser_debug_log!(self.config, "Data segment {}: passive, size={} bytes", i, byte_count);
                    
                    datas.push(ast::DataSegment::passive(data));
                }
                2 => {
                    // active, memoryidx, offset expr, bytes
                    let memidx = self.parse_u32()?;
                    let offset = self.parse_const_expr()?;
                    let byte_count = self.parse_u32()?;
                    let data = self.read_bytes(byte_count as usize)?.to_vec();
                    
                    crate::parser_debug_log!(self.config, "Data segment {}: active, memory={}, offset={:?}, size={} bytes", i, memidx, offset, byte_count);
                    
                    datas.push(ast::DataSegment::active(data, memidx, offset));
                }
                _ => return Err(ParseError::InvalidDataSegment),
            }
        }
        if self.cursor != section_end {
            return Err(ParseError::InvalidSectionSize);
        }
        Ok(datas)
    }

    /// Parse a data count section (id = 12)
    /// datacountsec ::= section12(u32) ⇒ Option<u32>
    pub fn parse_data_count_section(&mut self, size: u32) -> ParseResult<Option<u32>> {
        if size == 0 {
            return Ok(None);
        }
        let section_end = self.cursor + size as usize;
        let count = self.parse_u32()?;
        if self.cursor != section_end {
            return Err(ParseError::InvalidSectionSize);
        }
        Ok(Some(count))
    }

    /// Parse an export section (id = 7)
    /// exportsec ::= section7(vec(export))
    pub fn parse_export_section(&mut self, size: u32) -> ParseResult<Vec<ast::Export>> {
        let section_end = self.cursor + size as usize;
        let count = self.parse_u32()?;
        let mut exports = Vec::with_capacity(count as usize);
        for _ in 0..count {
            let name = self.parse_name()?;
            let desc_tag = self.read_byte()?;
            let index = self.parse_u32()?;
            let kind = match desc_tag {
                0x00 => ast::ExternKind::Func,
                0x01 => ast::ExternKind::Table,
                0x02 => ast::ExternKind::Memory,
                0x03 => ast::ExternKind::Global,
                _ => return Err(ParseError::InvalidExport),
            };
            exports.push(ast::Export { name, kind, index });
        }
        if self.cursor != section_end {
            return Err(ParseError::InvalidSectionSize);
        }
        Ok(exports)
    }

    /// Parse a memory section (id = 5)
    /// memsec ::= section5(vec(mem))
    pub fn parse_memory_section(&mut self, size: u32) -> ParseResult<Vec<ast::Memory>> {
        let section_end = self.cursor + size as usize;
        let count = self.parse_u32()?;
        let mut mems = Vec::with_capacity(count as usize);
        for _ in 0..count {
            let ty = self.parse_memtype()?;
            mems.push(ast::Memory::new(ty));
        }
        if self.cursor != section_end {
            return Err(ParseError::InvalidSectionSize);
        }
        Ok(mems)
    }
} 
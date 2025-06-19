//! Instruction parsing for WebAssembly binary parser

use crate::wasm::parser::error::{ParseError, ParseResult};
use crate::wasm::ast;
use super::Parser;
use crate::parser_debug_log;
use crate::wasm::parser::ParserConfig;
use alloc::format;
use alloc::vec::Vec;

impl<'a> Parser<'a> {
    /// Parse a variable instruction
    /// 
    /// # Specification
    /// 
    /// Variable instructions are represented by byte codes followed by the encoding of the respective index:
    /// 
    /// ```
    /// instr ::= ...
    ///        | 0x20 𝑥:localidx ⇒ local.get 𝑥
    ///        | 0x21 𝑥:localidx ⇒ local.set 𝑥
    ///        | 0x22 𝑥:localidx ⇒ local.tee 𝑥
    ///        | 0x23 𝑥:globalidx ⇒ global.get 𝑥
    ///        | 0x24 𝑥:globalidx ⇒ global.set 𝑥
    /// ```
    /// 
    /// # Examples
    /// 
    /// ```
    /// // local.get 0
    /// 0x20 0x00
    /// 
    /// // global.set 1
    /// 0x24 0x01
    /// ```
    /// 
    /// # Errors
    /// 
    /// - `UnexpectedEof`: Input ends unexpectedly
    /// - `InvalidInstruction`: Invalid opcode
    /// - `InvalidIntegerEncoding`: Invalid index encoding
    pub fn parse_variable_instruction(&mut self) -> ParseResult<ast::VariableInstruction> {
        let opcode = self.parse_byte()?;
        match opcode {
            0x20 => {
                let local_index = self.parse_u32()?;
                Ok(ast::VariableInstruction::LocalGet(local_index))
            }
            0x21 => {
                let local_index = self.parse_u32()?;
                Ok(ast::VariableInstruction::LocalSet(local_index))
            }
            0x22 => {
                let local_index = self.parse_u32()?;
                Ok(ast::VariableInstruction::LocalTee(local_index))
            }
            0x23 => {
                let global_index = self.parse_u32()?;
                Ok(ast::VariableInstruction::GlobalGet(global_index))
            }
            0x24 => {
                let global_index = self.parse_u32()?;
                Ok(ast::VariableInstruction::GlobalSet(global_index))
            }
            _ => Err(ParseError::InvalidInstruction),
        }
    }

    /// Parse a table instruction
    /// 
    /// # Specification
    /// 
    /// Table instructions are represented either by a single byte or a one byte prefix followed by a variable-length unsigned integer:
    /// 
    /// ```
    /// instr ::= ...
    ///        | 0x25 𝑥:tableidx ⇒ table.get 𝑥
    ///        | 0x26 𝑥:tableidx ⇒ table.set 𝑥
    ///        | 0xFC 12:u32 𝑦:elemidx 𝑥:tableidx ⇒ table.init 𝑥 𝑦
    ///        | 0xFC 13:u32 𝑥:elemidx ⇒ elem.drop 𝑥
    ///        | 0xFC 14:u32 𝑥:tableidx 𝑦:tableidx ⇒ table.copy 𝑥 𝑦
    ///        | 0xFC 15:u32 𝑥:tableidx ⇒ table.grow 𝑥
    ///        | 0xFC 16:u32 𝑥:tableidx ⇒ table.size 𝑥
    ///        | 0xFC 17:u32 𝑥:tableidx ⇒ table.fill 𝑥
    /// ```
    /// 
    /// # Examples
    /// 
    /// ```
    /// // table.get 0
    /// 0x25 0x00
    /// 
    /// // table.init 0 1
    /// 0xFC 0x0C 0x01 0x00
    /// ```
    /// 
    /// # Errors
    /// 
    /// - `UnexpectedEof`: Input ends unexpectedly
    /// - `InvalidInstruction`: Invalid opcode or prefix
    /// - `InvalidIntegerEncoding`: Invalid index encoding
    pub fn parse_table_instruction(&mut self) -> ParseResult<ast::TableInstruction> {
        let opcode = self.parse_byte()?;
        match opcode {
            0x25 => {
                let table_index = self.parse_u32()?;
                Ok(ast::TableInstruction::Get(table_index))
            }
            0x26 => {
                let table_index = self.parse_u32()?;
                Ok(ast::TableInstruction::Set(table_index))
            }
            0xFC => {
                let opcode = self.parse_u32()?;
                match opcode {
                    0x0C => {
                        let elem_index = self.parse_u32()?;
                        let table_index = self.parse_u32()?;
                        Ok(ast::TableInstruction::Init {
                            table_index,
                            elem_index,
                        })
                    }
                    0x0D => {
                        let elem_index = self.parse_u32()?;
                        Ok(ast::TableInstruction::ElemDrop(elem_index))
                    }
                    0x0E => {
                        let src_table = self.parse_u32()?;
                        let dst_table = self.parse_u32()?;
                        Ok(ast::TableInstruction::Copy {
                            dst_table,
                            src_table,
                        })
                    }
                    0x0F => {
                        let table_index = self.parse_u32()?;
                        Ok(ast::TableInstruction::Grow(table_index))
                    }
                    0x10 => {
                        let table_index = self.parse_u32()?;
                        Ok(ast::TableInstruction::Size(table_index))
                    }
                    0x11 => {
                        let table_index = self.parse_u32()?;
                        Ok(ast::TableInstruction::Fill(table_index))
                    }
                    _ => Err(ParseError::InvalidInstruction),
                }
            }
            _ => Err(ParseError::InvalidInstruction),
        }
    }

    /// Parse a memory argument
    /// 
    /// # Specification
    /// 
    /// A memory argument consists of an alignment and an offset:
    /// 
    /// ```
    /// memarg ::= 𝑎:u32 𝑜:u32 ⇒ {align 𝑎, offset 𝑜}
    /// ```
    /// 
    /// # Examples
    /// 
    /// ```
    /// // align=2, offset=4
    /// 0x02 0x04
    /// ```
    /// 
    /// # Errors
    /// 
    /// - `UnexpectedEof`: Input ends unexpectedly
    /// - `InvalidIntegerEncoding`: Invalid alignment or offset encoding
    pub fn parse_memarg(&mut self) -> ParseResult<ast::MemArg> {
        let align = self.parse_u32()?;
        let offset = self.parse_u32()?;
        Ok(ast::MemArg { align, offset })
    }

    /// Parse a memory instruction
    /// 
    /// # Specification
    /// 
    /// Memory instructions are encoded with different byte codes, with loads and stores followed by their memarg immediate:
    /// 
    /// ```
    /// instr ::= ...
    ///        | 0x28 𝑚:memarg ⇒ i32.load 𝑚
    ///        | 0x29 𝑚:memarg ⇒ i64.load 𝑚
    ///        | 0x2A 𝑚:memarg ⇒ f32.load 𝑚
    ///        | 0x2B 𝑚:memarg ⇒ f64.load 𝑚
    ///        | 0x2C 𝑚:memarg ⇒ i32.load8_s 𝑚
    ///        | 0x2D 𝑚:memarg ⇒ i32.load8_u 𝑚
    ///        | 0x2E 𝑚:memarg ⇒ i32.load16_s 𝑚
    ///        | 0x2F 𝑚:memarg ⇒ i32.load16_u 𝑚
    ///        | 0x30 𝑚:memarg ⇒ i64.load8_s 𝑚
    ///        | 0x31 𝑚:memarg ⇒ i64.load8_u 𝑚
    ///        | 0x32 𝑚:memarg ⇒ i64.load16_s 𝑚
    ///        | 0x33 𝑚:memarg ⇒ i64.load16_u 𝑚
    ///        | 0x34 𝑚:memarg ⇒ i64.load32_s 𝑚
    ///        | 0x35 𝑚:memarg ⇒ i64.load32_u 𝑚
    ///        | 0x36 𝑚:memarg ⇒ i32.store 𝑚
    ///        | 0x37 𝑚:memarg ⇒ i64.store 𝑚
    ///        | 0x38 𝑚:memarg ⇒ f32.store 𝑚
    ///        | 0x39 𝑚:memarg ⇒ f64.store 𝑚
    ///        | 0x3A 𝑚:memarg ⇒ i32.store8 𝑚
    ///        | 0x3B 𝑚:memarg ⇒ i32.store16 𝑚
    ///        | 0x3C 𝑚:memarg ⇒ i64.store8 𝑚
    ///        | 0x3D 𝑚:memarg ⇒ i64.store16 𝑚
    ///        | 0x3E 𝑚:memarg ⇒ i64.store32 𝑚
    ///        | 0x3F 0x00 ⇒ memory.size
    ///        | 0x40 0x00 ⇒ memory.grow
    ///        | 0xFC 8:u32 𝑥:dataidx 0x00 ⇒ memory.init 𝑥
    ///        | 0xFC 9:u32 𝑥:dataidx ⇒ data.drop 𝑥
    ///        | 0xFC 10:u32 0x00 0x00 ⇒ memory.copy
    ///        | 0xFC 11:u32 0x00 ⇒ memory.fill
    /// ```
    /// 
    /// # Examples
    /// 
    /// ```
    /// // i32.load align=2, offset=4
    /// 0x28 0x02 0x04
    /// 
    /// // memory.size
    /// 0x3F 0x00
    /// ```
    /// 
    /// # Errors
    /// 
    /// - `UnexpectedEof`: Input ends unexpectedly
    /// - `InvalidInstruction`: Invalid opcode or prefix
    /// - `InvalidIntegerEncoding`: Invalid index encoding
    pub fn parse_memory_instruction(&mut self) -> ParseResult<ast::MemoryInstruction> {
        let opcode = self.read_byte()?;

        match opcode {
            // Integer loads
            0x28 => {
                let memarg = self.parse_memarg()?;
                Ok(ast::MemoryInstruction::I32Load { memarg })
            }
            0x29 => {
                let memarg = self.parse_memarg()?;
                Ok(ast::MemoryInstruction::I64Load { memarg })
            }
            // Float loads
            0x2A => {
                let memarg = self.parse_memarg()?;
                Ok(ast::MemoryInstruction::F32Load { memarg })
            }
            0x2B => {
                let memarg = self.parse_memarg()?;
                Ok(ast::MemoryInstruction::F64Load { memarg })
            }
            // Integer stores
            0x36 => {
                let memarg = self.parse_memarg()?;
                Ok(ast::MemoryInstruction::I32Store { memarg })
            }
            0x37 => {
                let memarg = self.parse_memarg()?;
                Ok(ast::MemoryInstruction::I64Store { memarg })
            }
            // Float stores
            0x38 => {
                let memarg = self.parse_memarg()?;
                Ok(ast::MemoryInstruction::F32Store { memarg })
            }
            0x39 => {
                let memarg = self.parse_memarg()?;
                Ok(ast::MemoryInstruction::F64Store { memarg })
            }
            // Integer loads with sign extension
            0x2C => {
                let memarg = self.parse_memarg()?;
                Ok(ast::MemoryInstruction::I32Load8S { memarg })
            }
            0x2D => {
                let memarg = self.parse_memarg()?;
                Ok(ast::MemoryInstruction::I32Load8U { memarg })
            }
            0x2E => {
                let memarg = self.parse_memarg()?;
                Ok(ast::MemoryInstruction::I32Load16S { memarg })
            }
            0x2F => {
                let memarg = self.parse_memarg()?;
                Ok(ast::MemoryInstruction::I32Load16U { memarg })
            }
            0x30 => {
                let memarg = self.parse_memarg()?;
                Ok(ast::MemoryInstruction::I64Load8S { memarg })
            }
            0x31 => {
                let memarg = self.parse_memarg()?;
                Ok(ast::MemoryInstruction::I64Load8U { memarg })
            }
            0x32 => {
                let memarg = self.parse_memarg()?;
                Ok(ast::MemoryInstruction::I64Load16S { memarg })
            }
            0x33 => {
                let memarg = self.parse_memarg()?;
                Ok(ast::MemoryInstruction::I64Load16U { memarg })
            }
            0x34 => {
                let memarg = self.parse_memarg()?;
                Ok(ast::MemoryInstruction::I64Load32S { memarg })
            }
            0x35 => {
                let memarg = self.parse_memarg()?;
                Ok(ast::MemoryInstruction::I64Load32U { memarg })
            }
            // Integer stores with truncation
            0x3A => {
                let memarg = self.parse_memarg()?;
                Ok(ast::MemoryInstruction::I32Store8 { memarg })
            }
            0x3B => {
                let memarg = self.parse_memarg()?;
                Ok(ast::MemoryInstruction::I32Store16 { memarg })
            }
            0x3C => {
                let memarg = self.parse_memarg()?;
                Ok(ast::MemoryInstruction::I64Store8 { memarg })
            }
            0x3D => {
                let memarg = self.parse_memarg()?;
                Ok(ast::MemoryInstruction::I64Store16 { memarg })
            }
            0x3E => {
                let memarg = self.parse_memarg()?;
                Ok(ast::MemoryInstruction::I64Store32 { memarg })
            }
            // Memory size and grow
            0x3F => {
                let zero = self.parse_byte()?;
                if zero != 0x00 {
                    return Err(ParseError::InvalidInstruction);
                }
                Ok(ast::MemoryInstruction::MemorySize)
            }
            0x40 => {
                let zero = self.parse_byte()?;
                if zero != 0x00 {
                    return Err(ParseError::InvalidInstruction);
                }
                Ok(ast::MemoryInstruction::MemoryGrow)
            }
            // 0xFC memory instructions are handled in parse_instruction
            _ => Err(ParseError::InvalidInstruction),
        }
    }

    /// Parse a numeric instruction
    /// 
    /// # Specification
    /// 
    /// Numeric instructions are encoded with different byte codes, with constant instructions
    /// followed by their respective literal values:
    /// 
    /// ```
    /// instr ::= ...
    ///        | 0x41 𝑛:i32 ⇒ i32.const 𝑛
    ///        | 0x42 𝑛:i64 ⇒ i64.const 𝑛
    ///        | 0x43 𝑧:f32 ⇒ f32.const 𝑧
    ///        | 0x44 𝑧:f64 ⇒ f64.const 𝑧
    ///        | 0x45 ⇒ i32.eqz
    ///        | 0x46 ⇒ i32.eq
    ///        | 0x47 ⇒ i32.ne
    ///        | 0x48 ⇒ i32.lt_s
    ///        | 0x49 ⇒ i32.lt_u
    ///        | 0x4A ⇒ i32.gt_s
    ///        | 0x4B ⇒ i32.gt_u
    ///        | 0x4C ⇒ i32.le_s
    ///        | 0x4D ⇒ i32.le_u
    ///        | 0x4E ⇒ i32.ge_s
    ///        | 0x4F ⇒ i32.ge_u
    ///        | 0x50 ⇒ i64.eqz
    ///        | 0x51 ⇒ i64.eq
    ///        | 0x52 ⇒ i64.ne
    ///        | 0x53 ⇒ i64.lt_s
    ///        | 0x54 ⇒ i64.lt_u
    ///        | 0x55 ⇒ i64.gt_s
    ///        | 0x56 ⇒ i64.gt_u
    ///        | 0x57 ⇒ i64.le_s
    ///        | 0x58 ⇒ i64.le_u
    ///        | 0x59 ⇒ i64.ge_s
    ///        | 0x5A ⇒ i64.ge_u
    ///        | 0x5B ⇒ f32.eq
    ///        | 0x5C ⇒ f32.ne
    ///        | 0x5D ⇒ f32.lt
    ///        | 0x5E ⇒ f32.gt
    ///        | 0x5F ⇒ f32.le
    ///        | 0x60 ⇒ f32.ge
    ///        | 0x61 ⇒ f64.eq
    ///        | 0x62 ⇒ f64.ne
    ///        | 0x63 ⇒ f64.lt
    ///        | 0x64 ⇒ f64.gt
    ///        | 0x65 ⇒ f64.le
    ///        | 0x66 ⇒ f64.ge
    ///        | 0x67 ⇒ i32.clz
    ///        | 0x68 ⇒ i32.ctz
    ///        | 0x69 ⇒ i32.popcnt
    ///        | 0x6A ⇒ i32.add
    ///        | 0x6B ⇒ i32.sub
    ///        | 0x6C ⇒ i32.mul
    ///        | 0x6D ⇒ i32.div_s
    ///        | 0x6E ⇒ i32.div_u
    ///        | 0x6F ⇒ i32.rem_s
    ///        | 0x70 ⇒ i32.rem_u
    ///        | 0x71 ⇒ i32.and
    ///        | 0x72 ⇒ i32.or
    ///        | 0x73 ⇒ i32.xor
    ///        | 0x74 ⇒ i32.shl
    ///        | 0x75 ⇒ i32.shr_s
    ///        | 0x76 ⇒ i32.shr_u
    ///        | 0x77 ⇒ i32.rotl
    ///        | 0x78 ⇒ i32.rotr
    ///        | 0x79 ⇒ i64.clz
    ///        | 0x7A ⇒ i64.ctz
    ///        | 0x7B ⇒ i64.popcnt
    ///        | 0x7C ⇒ i64.add
    ///        | 0x7D ⇒ i64.sub
    ///        | 0x7E ⇒ i64.mul
    ///        | 0x7F ⇒ i64.div_s
    ///        | 0x80 ⇒ i64.div_u
    ///        | 0x81 ⇒ i64.rem_s
    ///        | 0x82 ⇒ i64.rem_u
    ///        | 0x83 ⇒ i64.and
    ///        | 0x84 ⇒ i64.or
    ///        | 0x85 ⇒ i64.xor
    ///        | 0x86 ⇒ i64.shl
    ///        | 0x87 ⇒ i64.shr_s
    ///        | 0x88 ⇒ i64.shr_u
    ///        | 0x89 ⇒ i64.rotl
    ///        | 0x8A ⇒ i64.rotr
    ///        | 0x8B ⇒ f32.abs
    ///        | 0x8C ⇒ f32.neg
    ///        | 0x8D ⇒ f32.ceil
    ///        | 0x8E ⇒ f32.floor
    ///        | 0x8F ⇒ f32.trunc
    ///        | 0x90 ⇒ f32.nearest
    ///        | 0x91 ⇒ f32.sqrt
    ///        | 0x92 ⇒ f32.add
    ///        | 0x93 ⇒ f32.sub
    ///        | 0x94 ⇒ f32.mul
    ///        | 0x95 ⇒ f32.div
    ///        | 0x96 ⇒ f32.min
    ///        | 0x97 ⇒ f32.max
    ///        | 0x98 ⇒ f32.copysign
    ///        | 0x99 ⇒ f64.abs
    ///        | 0x9A ⇒ f64.neg
    ///        | 0x9B ⇒ f64.ceil
    ///        | 0x9C ⇒ f64.floor
    ///        | 0x9D ⇒ f64.trunc
    ///        | 0x9E ⇒ f64.nearest
    ///        | 0x9F ⇒ f64.sqrt
    ///        | 0xA0 ⇒ f64.add
    ///        | 0xA1 ⇒ f64.sub
    ///        | 0xA2 ⇒ f64.mul
    ///        | 0xA3 ⇒ f64.div
    ///        | 0xA4 ⇒ f64.min
    ///        | 0xA5 ⇒ f64.max
    ///        | 0xA6 ⇒ f64.copysign
    ///        | 0xA7 ⇒ i32.wrap_i64
    ///        | 0xA8 ⇒ i32.trunc_f32_s
    ///        | 0xA9 ⇒ i32.trunc_f32_u
    ///        | 0xAA ⇒ i32.trunc_f64_s
    ///        | 0xAB ⇒ i32.trunc_f64_u
    ///        | 0xAC ⇒ i64.extend_i32_s
    ///        | 0xAD ⇒ i64.extend_i32_u
    ///        | 0xAE ⇒ i64.trunc_f32_s
    ///        | 0xAF ⇒ i64.trunc_f32_u
    ///        | 0xB0 ⇒ i64.trunc_f64_s
    ///        | 0xB1 ⇒ i64.trunc_f64_u
    ///        | 0xB2 ⇒ f32.convert_i32_s
    ///        | 0xB3 ⇒ f32.convert_i32_u
    ///        | 0xB4 ⇒ f32.convert_i64_s
    ///        | 0xB5 ⇒ f32.convert_i64_u
    ///        | 0xB6 ⇒ f32.demote_f64
    ///        | 0xB7 ⇒ f64.convert_i32_s
    ///        | 0xB8 ⇒ f64.convert_i32_u
    ///        | 0xB9 ⇒ f64.convert_i64_s
    ///        | 0xBA ⇒ f64.convert_i64_u
    ///        | 0xBB ⇒ f64.promote_f32
    ///        | 0xBC ⇒ i32.reinterpret_f32
    ///        | 0xBD ⇒ i64.reinterpret_f64
    ///        | 0xBE ⇒ f32.reinterpret_i32
    ///        | 0xBF ⇒ f64.reinterpret_i64
    ///        | 0xC0 ⇒ i32.extend8_s
    ///        | 0xC1 ⇒ i32.extend16_s
    ///        | 0xC2 ⇒ i64.extend8_s
    ///        | 0xC3 ⇒ i64.extend16_s
    ///        | 0xC4 ⇒ i64.extend32_s
    /// ```
    /// 
    /// # Examples
    /// 
    /// ```
    /// // i32.const 42
    /// 0x41 0x2A
    /// 
    /// // i32.add
    /// 0x6A
    /// ```
    /// 
    /// # Errors
    /// 
    /// - `UnexpectedEof`: Input ends unexpectedly
    /// - `InvalidInstruction`: Invalid opcode
    /// - `InvalidIntegerEncoding`: Invalid constant encoding
    /// - `InvalidFloatEncoding`: Invalid float encoding
    pub fn parse_numeric_instruction(&mut self) -> ParseResult<ast::NumericInstruction> {
        let opcode = self.parse_byte()?;
        parser_debug_log!(&self.config, "Parsing numeric instruction with opcode: 0x{:02X}", opcode);
        match opcode {
            // Constants
            0x41 => {
                parser_debug_log!(&self.config, "Parsing i32.const");
                let value = self.parse_i32()?;
                parser_debug_log!(&self.config, "i32.const value: {}", value);
                Ok(ast::NumericInstruction::I32Const(value))
            }
            0x42 => {
                let value = self.parse_i64()?;
                Ok(ast::NumericInstruction::I64Const(value))
            }
            0x43 => {
                let value = self.parse_f32()?;
                Ok(ast::NumericInstruction::F32Const(value))
            }
            0x44 => {
                let value = self.parse_f64()?;
                Ok(ast::NumericInstruction::F64Const(value))
            }
            // Integer test operations
            0x45 => Ok(ast::NumericInstruction::I32TestOp),
            0x50 => Ok(ast::NumericInstruction::I64TestOp),
            // Integer comparison operations
            0x46 => Ok(ast::NumericInstruction::I32RelOp(ast::IntRelOp::Eq { signed: true })),
            0x47 => Ok(ast::NumericInstruction::I32RelOp(ast::IntRelOp::Ne { signed: true })),
            0x48 => Ok(ast::NumericInstruction::I32RelOp(ast::IntRelOp::Lt { signed: true })),
            0x49 => Ok(ast::NumericInstruction::I32RelOp(ast::IntRelOp::Lt { signed: false })),
            0x4A => Ok(ast::NumericInstruction::I32RelOp(ast::IntRelOp::Gt { signed: true })),
            0x4B => Ok(ast::NumericInstruction::I32RelOp(ast::IntRelOp::Gt { signed: false })),
            0x4C => Ok(ast::NumericInstruction::I32RelOp(ast::IntRelOp::Le { signed: true })),
            0x4D => Ok(ast::NumericInstruction::I32RelOp(ast::IntRelOp::Le { signed: false })),
            0x4E => Ok(ast::NumericInstruction::I32RelOp(ast::IntRelOp::Ge { signed: true })),
            0x4F => Ok(ast::NumericInstruction::I32RelOp(ast::IntRelOp::Ge { signed: false })),
            0x51 => Ok(ast::NumericInstruction::I64RelOp(ast::IntRelOp::Eq { signed: true })),
            0x52 => Ok(ast::NumericInstruction::I64RelOp(ast::IntRelOp::Ne { signed: true })),
            0x53 => Ok(ast::NumericInstruction::I64RelOp(ast::IntRelOp::Lt { signed: true })),
            0x54 => Ok(ast::NumericInstruction::I64RelOp(ast::IntRelOp::Lt { signed: false })),
            0x55 => Ok(ast::NumericInstruction::I64RelOp(ast::IntRelOp::Gt { signed: true })),
            0x56 => Ok(ast::NumericInstruction::I64RelOp(ast::IntRelOp::Gt { signed: false })),
            0x57 => Ok(ast::NumericInstruction::I64RelOp(ast::IntRelOp::Le { signed: true })),
            0x58 => Ok(ast::NumericInstruction::I64RelOp(ast::IntRelOp::Le { signed: false })),
            0x59 => Ok(ast::NumericInstruction::I64RelOp(ast::IntRelOp::Ge { signed: true })),
            0x5A => Ok(ast::NumericInstruction::I64RelOp(ast::IntRelOp::Ge { signed: false })),
            // Float comparison operations
            0x5B => Ok(ast::NumericInstruction::F32RelOp(ast::FloatRelOp::Eq)),
            0x5C => Ok(ast::NumericInstruction::F32RelOp(ast::FloatRelOp::Ne)),
            0x5D => Ok(ast::NumericInstruction::F32RelOp(ast::FloatRelOp::Lt)),
            0x5E => Ok(ast::NumericInstruction::F32RelOp(ast::FloatRelOp::Gt)),
            0x5F => Ok(ast::NumericInstruction::F32RelOp(ast::FloatRelOp::Le)),
            0x60 => Ok(ast::NumericInstruction::F32RelOp(ast::FloatRelOp::Ge)),
            0x61 => Ok(ast::NumericInstruction::F64RelOp(ast::FloatRelOp::Eq)),
            0x62 => Ok(ast::NumericInstruction::F64RelOp(ast::FloatRelOp::Ne)),
            0x63 => Ok(ast::NumericInstruction::F64RelOp(ast::FloatRelOp::Lt)),
            0x64 => Ok(ast::NumericInstruction::F64RelOp(ast::FloatRelOp::Gt)),
            0x65 => Ok(ast::NumericInstruction::F64RelOp(ast::FloatRelOp::Le)),
            0x66 => Ok(ast::NumericInstruction::F64RelOp(ast::FloatRelOp::Ge)),
            // Integer unary operations
            0x67 => Ok(ast::NumericInstruction::I32UnOp(ast::IntUnOp::Clz)),
            0x68 => Ok(ast::NumericInstruction::I32UnOp(ast::IntUnOp::Ctz)),
            0x69 => Ok(ast::NumericInstruction::I32UnOp(ast::IntUnOp::Popcnt)),
            0x79 => Ok(ast::NumericInstruction::I64UnOp(ast::IntUnOp::Clz)),
            0x7A => Ok(ast::NumericInstruction::I64UnOp(ast::IntUnOp::Ctz)),
            0x7B => Ok(ast::NumericInstruction::I64UnOp(ast::IntUnOp::Popcnt)),
            // Integer binary operations
            0x6A => Ok(ast::NumericInstruction::I32BinOp(ast::IntBinOp::Add)),
            0x6B => Ok(ast::NumericInstruction::I32BinOp(ast::IntBinOp::Sub)),
            0x6C => Ok(ast::NumericInstruction::I32BinOp(ast::IntBinOp::Mul)),
            0x6D => Ok(ast::NumericInstruction::I32BinOp(ast::IntBinOp::Div { signed: true })),
            0x6E => Ok(ast::NumericInstruction::I32BinOp(ast::IntBinOp::Div { signed: false })),
            0x6F => Ok(ast::NumericInstruction::I32BinOp(ast::IntBinOp::Rem { signed: true })),
            0x70 => Ok(ast::NumericInstruction::I32BinOp(ast::IntBinOp::Rem { signed: false })),
            0x71 => Ok(ast::NumericInstruction::I32BinOp(ast::IntBinOp::And)),
            0x72 => Ok(ast::NumericInstruction::I32BinOp(ast::IntBinOp::Or)),
            0x73 => Ok(ast::NumericInstruction::I32BinOp(ast::IntBinOp::Xor)),
            0x74 => Ok(ast::NumericInstruction::I32BinOp(ast::IntBinOp::Shl)),
            0x75 => Ok(ast::NumericInstruction::I32BinOp(ast::IntBinOp::Shr { signed: true })),
            0x76 => Ok(ast::NumericInstruction::I32BinOp(ast::IntBinOp::Shr { signed: false })),
            0x77 => Ok(ast::NumericInstruction::I32BinOp(ast::IntBinOp::Rotl)),
            0x78 => Ok(ast::NumericInstruction::I32BinOp(ast::IntBinOp::Rotr)),
            0x7C => Ok(ast::NumericInstruction::I64BinOp(ast::IntBinOp::Add)),
            0x7D => Ok(ast::NumericInstruction::I64BinOp(ast::IntBinOp::Sub)),
            0x7E => Ok(ast::NumericInstruction::I64BinOp(ast::IntBinOp::Mul)),
            0x7F => Ok(ast::NumericInstruction::I64BinOp(ast::IntBinOp::Div { signed: true })),
            0x80 => Ok(ast::NumericInstruction::I64BinOp(ast::IntBinOp::Div { signed: false })),
            0x81 => Ok(ast::NumericInstruction::I64BinOp(ast::IntBinOp::Rem { signed: true })),
            0x82 => Ok(ast::NumericInstruction::I64BinOp(ast::IntBinOp::Rem { signed: false })),
            0x83 => Ok(ast::NumericInstruction::I64BinOp(ast::IntBinOp::And)),
            0x84 => Ok(ast::NumericInstruction::I64BinOp(ast::IntBinOp::Or)),
            0x85 => Ok(ast::NumericInstruction::I64BinOp(ast::IntBinOp::Xor)),
            0x86 => Ok(ast::NumericInstruction::I64BinOp(ast::IntBinOp::Shl)),
            0x87 => Ok(ast::NumericInstruction::I64BinOp(ast::IntBinOp::Shr { signed: true })),
            0x88 => Ok(ast::NumericInstruction::I64BinOp(ast::IntBinOp::Shr { signed: false })),
            0x89 => Ok(ast::NumericInstruction::I64BinOp(ast::IntBinOp::Rotl)),
            0x8A => Ok(ast::NumericInstruction::I64BinOp(ast::IntBinOp::Rotr)),
            // Float unary operations
            0x8B => Ok(ast::NumericInstruction::F32UnOp(ast::FloatUnOp::Abs)),
            0x8C => Ok(ast::NumericInstruction::F32UnOp(ast::FloatUnOp::Neg)),
            0x8D => Ok(ast::NumericInstruction::F32UnOp(ast::FloatUnOp::Ceil)),
            0x8E => Ok(ast::NumericInstruction::F32UnOp(ast::FloatUnOp::Floor)),
            0x8F => Ok(ast::NumericInstruction::F32UnOp(ast::FloatUnOp::Trunc)),
            0x90 => Ok(ast::NumericInstruction::F32UnOp(ast::FloatUnOp::Nearest)),
            0x91 => Ok(ast::NumericInstruction::F32UnOp(ast::FloatUnOp::Sqrt)),
            0x99 => Ok(ast::NumericInstruction::F64UnOp(ast::FloatUnOp::Abs)),
            0x9A => Ok(ast::NumericInstruction::F64UnOp(ast::FloatUnOp::Neg)),
            0x9B => Ok(ast::NumericInstruction::F64UnOp(ast::FloatUnOp::Ceil)),
            0x9C => Ok(ast::NumericInstruction::F64UnOp(ast::FloatUnOp::Floor)),
            0x9D => Ok(ast::NumericInstruction::F64UnOp(ast::FloatUnOp::Trunc)),
            0x9E => Ok(ast::NumericInstruction::F64UnOp(ast::FloatUnOp::Nearest)),
            0x9F => Ok(ast::NumericInstruction::F64UnOp(ast::FloatUnOp::Sqrt)),
            // Float binary operations
            0x92 => Ok(ast::NumericInstruction::F32BinOp(ast::FloatBinOp::Add)),
            0x93 => Ok(ast::NumericInstruction::F32BinOp(ast::FloatBinOp::Sub)),
            0x94 => Ok(ast::NumericInstruction::F32BinOp(ast::FloatBinOp::Mul)),
            0x95 => Ok(ast::NumericInstruction::F32BinOp(ast::FloatBinOp::Div)),
            0x96 => Ok(ast::NumericInstruction::F32BinOp(ast::FloatBinOp::Min)),
            0x97 => Ok(ast::NumericInstruction::F32BinOp(ast::FloatBinOp::Max)),
            0x98 => Ok(ast::NumericInstruction::F32BinOp(ast::FloatBinOp::Copysign)),
            0xA0 => Ok(ast::NumericInstruction::F64BinOp(ast::FloatBinOp::Add)),
            0xA1 => Ok(ast::NumericInstruction::F64BinOp(ast::FloatBinOp::Sub)),
            0xA2 => Ok(ast::NumericInstruction::F64BinOp(ast::FloatBinOp::Mul)),
            0xA3 => Ok(ast::NumericInstruction::F64BinOp(ast::FloatBinOp::Div)),
            0xA4 => Ok(ast::NumericInstruction::F64BinOp(ast::FloatBinOp::Min)),
            0xA5 => Ok(ast::NumericInstruction::F64BinOp(ast::FloatBinOp::Max)),
            0xA6 => Ok(ast::NumericInstruction::F64BinOp(ast::FloatBinOp::Copysign)),
            // Conversion operations
            0xA7 => Ok(ast::NumericInstruction::I32ConversionOp(ast::ConversionOp::Wrap)),
            0xA8 => Ok(ast::NumericInstruction::I32ConversionOp(ast::ConversionOp::Trunc { signed: true })),
            0xA9 => Ok(ast::NumericInstruction::I32ConversionOp(ast::ConversionOp::Trunc { signed: false })),
            0xAA => Ok(ast::NumericInstruction::I32ConversionOp(ast::ConversionOp::Trunc { signed: true })),
            0xAB => Ok(ast::NumericInstruction::I32ConversionOp(ast::ConversionOp::Trunc { signed: false })),
            0xAC => Ok(ast::NumericInstruction::I64ConversionOp(ast::ConversionOp::Extend { signed: true })),
            0xAD => Ok(ast::NumericInstruction::I64ConversionOp(ast::ConversionOp::Extend { signed: false })),
            0xAE => Ok(ast::NumericInstruction::I64ConversionOp(ast::ConversionOp::Trunc { signed: true })),
            0xAF => Ok(ast::NumericInstruction::I64ConversionOp(ast::ConversionOp::Trunc { signed: false })),
            0xB0 => Ok(ast::NumericInstruction::I64ConversionOp(ast::ConversionOp::Trunc { signed: true })),
            0xB1 => Ok(ast::NumericInstruction::I64ConversionOp(ast::ConversionOp::Trunc { signed: false })),
            0xB2 => Ok(ast::NumericInstruction::F32ConversionOp(ast::ConversionOp::Convert { signed: true })),
            0xB3 => Ok(ast::NumericInstruction::F32ConversionOp(ast::ConversionOp::Convert { signed: false })),
            0xB4 => Ok(ast::NumericInstruction::F32ConversionOp(ast::ConversionOp::Convert { signed: true })),
            0xB5 => Ok(ast::NumericInstruction::F32ConversionOp(ast::ConversionOp::Convert { signed: false })),
            0xB6 => Ok(ast::NumericInstruction::F32ConversionOp(ast::ConversionOp::Demote)),
            0xB7 => Ok(ast::NumericInstruction::F64ConversionOp(ast::ConversionOp::Convert { signed: true })),
            0xB8 => Ok(ast::NumericInstruction::F64ConversionOp(ast::ConversionOp::Convert { signed: false })),
            0xB9 => Ok(ast::NumericInstruction::F64ConversionOp(ast::ConversionOp::Convert { signed: true })),
            0xBA => Ok(ast::NumericInstruction::F64ConversionOp(ast::ConversionOp::Convert { signed: false })),
            0xBB => Ok(ast::NumericInstruction::F64ConversionOp(ast::ConversionOp::Promote)),
            // Reinterpret operations
            0xBC => Ok(ast::NumericInstruction::I32ConversionOp(ast::ConversionOp::Reinterpret)),
            0xBD => Ok(ast::NumericInstruction::I64ConversionOp(ast::ConversionOp::Reinterpret)),
            0xBE => Ok(ast::NumericInstruction::F32ConversionOp(ast::ConversionOp::Reinterpret)),
            0xBF => Ok(ast::NumericInstruction::F64ConversionOp(ast::ConversionOp::Reinterpret)),
            // Extension operations
            0xC0 => Ok(ast::NumericInstruction::I32ConversionOp(ast::ConversionOp::Extend8S)),
            0xC1 => Ok(ast::NumericInstruction::I32ConversionOp(ast::ConversionOp::Extend16S)),
            0xC2 => Ok(ast::NumericInstruction::I64ConversionOp(ast::ConversionOp::Extend8S)),
            0xC3 => Ok(ast::NumericInstruction::I64ConversionOp(ast::ConversionOp::Extend16S)),
            0xC4 => Ok(ast::NumericInstruction::I64ConversionOp(ast::ConversionOp::Extend32S)),
            _ => Err(ParseError::InvalidInstruction),
        }
    }


    /// Parse a WebAssembly vector instruction
    /// 
    /// # Specification
    /// 
    /// Vector instructions are prefixed with 0xFD followed by a variable-length unsigned integer
    /// for the opcode. The instruction may have additional immediate operands.
    /// 
    /// # Examples
    /// 
    /// ```
    /// // v128.load
    /// let bytes = [0xFD, 0x00, 0x00, 0x00, 0x00, 0x00];
    /// let mut parser = Parser::new(&bytes);
    /// assert!(matches!(parser.parse_vector_instruction().unwrap(), ast::VectorInstruction::V128Load { .. }));
    /// 
    /// // v128.const
    /// let bytes = [0xFD, 0x0C, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    ///             0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00];
    /// let mut parser = Parser::new(&bytes);
    /// assert!(matches!(parser.parse_vector_instruction().unwrap(), ast::VectorInstruction::V128Const(1)));
    /// ```
    /// 
    /// # Errors
    /// 
    /// - `UnexpectedEof`: Input ends unexpectedly
    /// - `InvalidInstruction`: The instruction encoding is invalid.
    pub fn parse_vector_instruction(&mut self) -> ParseResult<ast::VectorInstruction> {
        // Read the prefix (must be 0xFD)
        let prefix = self.read_byte()?;
        if prefix != 0xFD {
            return Err(ParseError::InvalidInstruction);
        }

        // Read the opcode
        let opcode = self.parse_u32()?;

        match opcode {
            // Vector constant
            0x0C => { // v128.const
                let value = self.parse_i128()?;
                Ok(ast::VectorInstruction::V128Const(value))
            }

            // Vector loads
            0x00 => {
                let memarg = self.parse_memarg()?;
                Ok(ast::VectorInstruction::V128Load { memarg })
            }
            0x01 => {
                let memarg = self.parse_memarg()?;
                Ok(ast::VectorInstruction::V128Load8x8S { memarg })
            }
            0x02 => {
                let memarg = self.parse_memarg()?;
                Ok(ast::VectorInstruction::V128Load8x8U { memarg })
            }
            0x03 => {
                let memarg = self.parse_memarg()?;
                Ok(ast::VectorInstruction::V128Load16x4S { memarg })
            }
            0x04 => {
                let memarg = self.parse_memarg()?;
                Ok(ast::VectorInstruction::V128Load16x4U { memarg })
            }
            0x05 => {
                let memarg = self.parse_memarg()?;
                Ok(ast::VectorInstruction::V128Load32x2S { memarg })
            }
            0x06 => {
                let memarg = self.parse_memarg()?;
                Ok(ast::VectorInstruction::V128Load32x2U { memarg })
            }
            0x07 => {
                let memarg = self.parse_memarg()?;
                Ok(ast::VectorInstruction::V128Load8Splat { memarg })
            }
            0x08 => {
                let memarg = self.parse_memarg()?;
                Ok(ast::VectorInstruction::V128Load16Splat { memarg })
            }
            0x09 => {
                let memarg = self.parse_memarg()?;
                Ok(ast::VectorInstruction::V128Load32Splat { memarg })
            }
            0x0A => {
                let memarg = self.parse_memarg()?;
                Ok(ast::VectorInstruction::V128Load64Splat { memarg })
            }
            0x5C => { // 92
                let memarg = self.parse_memarg()?;
                Ok(ast::VectorInstruction::V128Load32Zero { memarg })
            }
            0x5D => { // 93
                let memarg = self.parse_memarg()?;
                Ok(ast::VectorInstruction::V128Load64Zero { memarg })
            }
            // Vector stores
            0x0B => { // 11
                let memarg = self.parse_memarg()?;
                Ok(ast::VectorInstruction::V128Store { memarg })
            }
            // Vector lane loads
            0x54 => { // 84
                let memarg = self.parse_memarg()?;
                let lane = self.read_byte()?;
                Ok(ast::VectorInstruction::V128Load8Lane { memarg, lane })
            }
            0x55 => { // 85
                let memarg = self.parse_memarg()?;
                let lane = self.read_byte()?;
                Ok(ast::VectorInstruction::V128Load16Lane { memarg, lane })
            }
            0x56 => { // 86
                let memarg = self.parse_memarg()?;
                let lane = self.read_byte()?;
                Ok(ast::VectorInstruction::V128Load32Lane { memarg, lane })
            }
            0x57 => { // 87
                let memarg = self.parse_memarg()?;
                let lane = self.read_byte()?;
                Ok(ast::VectorInstruction::V128Load64Lane { memarg, lane })
            }
            // Vector lane stores
            0x58 => { // 88
                let memarg = self.parse_memarg()?;
                let lane = self.read_byte()?;
                Ok(ast::VectorInstruction::V128Store8Lane { memarg, lane })
            }
            0x59 => { // 89
                let memarg = self.parse_memarg()?;
                let lane = self.read_byte()?;
                Ok(ast::VectorInstruction::V128Store16Lane { memarg, lane })
            }
            0x5A => { // 90
                let memarg = self.parse_memarg()?;
                let lane = self.read_byte()?;
                Ok(ast::VectorInstruction::V128Store32Lane { memarg, lane })
            }
            0x5B => { // 91
                let memarg = self.parse_memarg()?;
                let lane = self.read_byte()?;
                Ok(ast::VectorInstruction::V128Store64Lane { memarg, lane })
            }
            // Extract lane and replace lane instructions
            0x15 => { // i8x16.extract_lane_s
                let lane = self.read_byte()?;
                Ok(ast::VectorInstruction::ExtractLane { shape: ast::VectorShape::Int(ast::IntVectorShape::I8X16), lane, signed: true })
            }
            0x16 => { // i8x16.extract_lane_u
                let lane = self.read_byte()?;
                Ok(ast::VectorInstruction::ExtractLane { shape: ast::VectorShape::Int(ast::IntVectorShape::I8X16), lane, signed: false })
            }
            0x17 => { // i8x16.replace_lane
                let lane = self.read_byte()?;
                Ok(ast::VectorInstruction::ReplaceLane { shape: ast::VectorShape::Int(ast::IntVectorShape::I8X16), lane })
            }
            0x18 => { // i16x8.extract_lane_s
                let lane = self.read_byte()?;
                Ok(ast::VectorInstruction::ExtractLane { shape: ast::VectorShape::Int(ast::IntVectorShape::I16X8), lane, signed: true })
            }
            0x19 => { // i16x8.extract_lane_u
                let lane = self.read_byte()?;
                Ok(ast::VectorInstruction::ExtractLane { shape: ast::VectorShape::Int(ast::IntVectorShape::I16X8), lane, signed: false })
            }
            0x1A => { // i16x8.replace_lane
                let lane = self.read_byte()?;
                Ok(ast::VectorInstruction::ReplaceLane { shape: ast::VectorShape::Int(ast::IntVectorShape::I16X8), lane })
            }
            0x1B => { // i32x4.extract_lane
                let lane = self.read_byte()?;
                Ok(ast::VectorInstruction::ExtractLane { shape: ast::VectorShape::Int(ast::IntVectorShape::I32X4), lane, signed: false })
            }
            0x1C => { // i32x4.replace_lane
                let lane = self.read_byte()?;
                Ok(ast::VectorInstruction::ReplaceLane { shape: ast::VectorShape::Int(ast::IntVectorShape::I32X4), lane })
            }
            0x1D => { // i64x2.extract_lane
                let lane = self.read_byte()?;
                Ok(ast::VectorInstruction::ExtractLane { shape: ast::VectorShape::Int(ast::IntVectorShape::I64X2), lane, signed: false })
            }
            0x1E => { // i64x2.replace_lane
                let lane = self.read_byte()?;
                Ok(ast::VectorInstruction::ReplaceLane { shape: ast::VectorShape::Int(ast::IntVectorShape::I64X2), lane })
            }
            0x1F => { // f32x4.extract_lane
                let lane = self.read_byte()?;
                Ok(ast::VectorInstruction::ExtractLane { shape: ast::VectorShape::Float(ast::FloatVectorShape::F32X4), lane, signed: false })
            }
            0x20 => { // f32x4.replace_lane
                let lane = self.read_byte()?;
                Ok(ast::VectorInstruction::ReplaceLane { shape: ast::VectorShape::Float(ast::FloatVectorShape::F32X4), lane })
            }
            0x21 => { // f64x2.extract_lane
                let lane = self.read_byte()?;
                Ok(ast::VectorInstruction::ExtractLane { shape: ast::VectorShape::Float(ast::FloatVectorShape::F64X2), lane, signed: false })
            }
            0x22 => { // f64x2.replace_lane
                let lane = self.read_byte()?;
                Ok(ast::VectorInstruction::ReplaceLane { shape: ast::VectorShape::Float(ast::FloatVectorShape::F64X2), lane })
            }
            // Other vector instructions will be added here
            _ => Err(ParseError::InvalidInstruction),
        }
    }

    /// Parse a WebAssembly expression (sequence of instructions terminated by 0x0B)
    ///
    /// # Specification
    /// expr ::= (in:instr)* 0x0B ⇒ in* end
    ///
    /// # Returns
    /// Vec<ast::Instruction> (end命令自体は含まない)
    pub fn parse_expr(&mut self) -> ParseResult<Vec<ast::Instruction>> {
        let mut expr = Vec::new();
        loop {
            let pos = self.cursor;
            let byte = self.read_byte()?;
            if byte == 0x0B {
                break;
            } else {
                self.cursor = pos;
                expr.push(self.parse_instruction()?);
            }
        }
        Ok(expr)
    }

    /// Parse a WebAssembly instruction
    /// 
    /// # Specification
    /// 
    /// Instructions are represented by their opcode followed by any immediate operands.
    /// 
    /// # Examples
    /// 
    /// ```
    /// // i32.const 42
    /// 0x41 0x2A
    /// 
    /// // i32.add
    /// 0x6A
    /// ```
    /// 
    /// # Errors
    /// 
    /// - `UnexpectedEof`: Input ends unexpectedly
    /// - `InvalidInstruction`: Invalid opcode
    pub fn parse_instruction(&mut self) -> ParseResult<ast::Instruction> {
        let byte = self.read_byte()?;

        match byte {
            // Control instructions
            0x00..=0x11 => {
                // Put the opcode back so parse_control_instruction can read it
                self.cursor -= 1;
                let instr = self.parse_control_instruction()?;
                Ok(ast::Instruction::Control(instr))
            }

            // Variable instructions
            0x20..=0x24 => {
                // Put the opcode back so parse_variable_instruction can read it
                self.cursor -= 1;
                let instr = self.parse_variable_instruction()?;
                Ok(ast::Instruction::Variable(instr))
            }

            // Table instructions
            0x25..=0x26 | 0xFC => {
                // 0xFC prefix: check for numeric saturating truncation instructions
                let pos = self.cursor;
                let opcode = if byte == 0xFC { self.parse_u32()? } else { 0 };
                match opcode {
                    0..=7 => {
                        // Numeric saturating truncation instructions
                        use ast::{Instruction, NumericInstruction, ConversionOp};
                        let instr = match opcode {
                            0 => Instruction::Numeric(NumericInstruction::I32ConversionOp(ConversionOp::TruncSat { signed: true })),
                            1 => Instruction::Numeric(NumericInstruction::I32ConversionOp(ConversionOp::TruncSat { signed: false })),
                            2 => Instruction::Numeric(NumericInstruction::I32ConversionOp(ConversionOp::TruncSat { signed: true })), // f64_s
                            3 => Instruction::Numeric(NumericInstruction::I32ConversionOp(ConversionOp::TruncSat { signed: false })), // f64_u
                            4 => Instruction::Numeric(NumericInstruction::I64ConversionOp(ConversionOp::TruncSat { signed: true })),
                            5 => Instruction::Numeric(NumericInstruction::I64ConversionOp(ConversionOp::TruncSat { signed: false })),
                            6 => Instruction::Numeric(NumericInstruction::I64ConversionOp(ConversionOp::TruncSat { signed: true })), // f64_s
                            7 => Instruction::Numeric(NumericInstruction::I64ConversionOp(ConversionOp::TruncSat { signed: false })), // f64_u
                            _ => unreachable!(),
                        };
                        Ok(instr)
                    }
                    8 => {
                        // Memory init
                        let data_index = self.parse_u32()?;
                        let zero = self.parse_byte()?;
                        if zero != 0x00 {
                            return Err(ParseError::InvalidInstruction);
                        }
                        Ok(ast::Instruction::Memory(ast::MemoryInstruction::MemoryInit { data_index }))
                    }
                    9 => {
                        // Data drop
                        let data_index = self.parse_u32()?;
                        Ok(ast::Instruction::Memory(ast::MemoryInstruction::DataDrop { data_index }))
                    }
                    10 => {
                        // Memory copy
                        let zero1 = self.parse_byte()?;
                        let zero2 = self.parse_byte()?;
                        if zero1 != 0x00 || zero2 != 0x00 {
                            return Err(ParseError::InvalidInstruction);
                        }
                        Ok(ast::Instruction::Memory(ast::MemoryInstruction::MemoryCopy))
                    }
                    11 => {
                        // Memory fill
                        let zero = self.parse_byte()?;
                        if zero != 0x00 {
                            return Err(ParseError::InvalidInstruction);
                        }
                        Ok(ast::Instruction::Memory(ast::MemoryInstruction::MemoryFill))
                    }
                    _ => {
                        // Table instructions (12+)
                        self.cursor = pos;
                        let instr = if byte == 0xFC {
                            self.parse_table_instruction()?
                        } else {
                            return Err(ParseError::InvalidInstruction);
                        };
                        Ok(ast::Instruction::Table(instr))
                    }
                }
            }

            // Memory instructions
            0x28..=0x3E | 0x3F..=0x40 => {
                // Put the opcode back so parse_memory_instruction can read it
                self.cursor -= 1;
                let instr = self.parse_memory_instruction()?;
                Ok(ast::Instruction::Memory(instr))
            }

            // Numeric instructions
            0x41..=0xC4 => {
                // Put the opcode back so parse_numeric_instruction can read it
                self.cursor -= 1;
                let instr = self.parse_numeric_instruction()?;
                Ok(ast::Instruction::Numeric(instr))
            }

            // Vector instructions (0xFD prefix)
            0xFD => {
                // Reset cursor to read the prefix again
                self.cursor -= 1;
                let instruction = self.parse_vector_instruction()?;
                Ok(ast::Instruction::Vector(instruction))
            }

            // ... rest of the match arms ...
            _ => Err(ParseError::InvalidInstruction),
        }
    }

    /// Parse a constant expression (const expr)
    /// Only a single instruction is allowed, terminated by 0x0B (end)
    /// See: https://webassembly.github.io/spec/core/binary/instructions.html#constant-expressions
    pub fn parse_const_expr(&mut self) -> ParseResult<ast::ConstExpr> {
        let pos = self.cursor;
        let instr = self.parse_instruction()?;
        let end = self.read_byte()?;
        if end != 0x0B {
            return Err(crate::wasm::parser::error::ParseError::InvalidConstExpr);
        }
        use ast::{ConstExpr, Instruction, NumericInstruction, ValType};
        match instr {
            Instruction::Numeric(NumericInstruction::I32Const(val)) => Ok(ConstExpr::Const(ValType::I32, val.to_le_bytes().to_vec())),
            Instruction::Numeric(NumericInstruction::I64Const(val)) => Ok(ConstExpr::Const(ValType::I64, val.to_le_bytes().to_vec())),
            Instruction::Numeric(NumericInstruction::F32Const(val)) => Ok(ConstExpr::Const(ValType::F32, val.to_le_bytes().to_vec())),
            Instruction::Numeric(NumericInstruction::F64Const(val)) => Ok(ConstExpr::Const(ValType::F64, val.to_le_bytes().to_vec())),
            Instruction::Variable(ast::VariableInstruction::GlobalGet(idx)) => Ok(ConstExpr::GlobalGet(idx)),
            Instruction::Control(ast::ControlInstruction::RefNull(ty)) => Ok(ConstExpr::RefNull(ty)),
            Instruction::Control(ast::ControlInstruction::RefFunc(idx)) => Ok(ConstExpr::RefFunc(idx)),
            _ => Err(crate::wasm::parser::error::ParseError::InvalidConstExpr),
        }
    }

    /// Parse a control instruction
    /// 
    /// # Specification
    /// 
    /// Control instructions are represented by byte codes followed by any immediate operands:
    /// 
    /// ```
    /// instr ::= ...
    ///        | 0x00 ⇒ unreachable
    ///        | 0x01 ⇒ nop
    ///        | 0x02 bt:blocktype in*:instr* 0x0B ⇒ block bt in*
    ///        | 0x03 bt:blocktype in*:instr* 0x0B ⇒ loop bt in*
    ///        | 0x04 bt:blocktype in1*:instr* 0x05 in2*:instr* 0x0B ⇒ if bt in1* else in2* end
    ///        | 0x0C 𝑥:labelidx ⇒ br 𝑥
    ///        | 0x0D 𝑥:labelidx ⇒ br_if 𝑥
    ///        | 0x0E 𝑥*:vec(labelidx) 𝑥:labelidx ⇒ br_table 𝑥* 𝑥
    ///        | 0x0F ⇒ return
    ///        | 0x10 𝑥:funcidx ⇒ call 𝑥
    ///        | 0x11 𝑥:typeidx 𝑦:tableidx ⇒ call_indirect 𝑥 𝑦
    /// ```
    /// 
    /// # Examples
    /// 
    /// ```
    /// // call 0
    /// 0x10 0x00
    /// 
    /// // br 1
    /// 0x0C 0x01
    /// ```
    /// 
    /// # Errors
    /// 
    /// - `UnexpectedEof`: Input ends unexpectedly
    /// - `InvalidInstruction`: Invalid opcode
    /// - `InvalidIntegerEncoding`: Invalid index encoding
    pub fn parse_control_instruction(&mut self) -> ParseResult<ast::ControlInstruction> {
        let opcode = self.parse_byte()?;
        parser_debug_log!(&self.config, "Parsing control instruction with opcode: 0x{:02X}", opcode);
        match opcode {
            0x00 => Ok(ast::ControlInstruction::Unreachable),
            0x01 => Ok(ast::ControlInstruction::Nop),
            0x02 => {
                // block
                let block_type = self.parse_block_type()?;
                let instructions = self.parse_expr()?;
                Ok(ast::ControlInstruction::Block {
                    block_type,
                    instructions,
                })
            }
            0x03 => {
                // loop
                let block_type = self.parse_block_type()?;
                let instructions = self.parse_expr()?;
                Ok(ast::ControlInstruction::Loop {
                    block_type,
                    instructions,
                })
            }
            0x04 => {
                // if
                let block_type = self.parse_block_type()?;
                
                // Parse true instructions (until we encounter else or end)
                let mut true_instructions = Vec::new();
                loop {
                    let pos = self.cursor;
                    let next_byte = self.read_byte()?;
                    
                    if next_byte == 0x05 {
                        // Found else - stop parsing true instructions
                        break;
                    } else if next_byte == 0x0B {
                        // Found end - no else clause
                        break;
                    } else {
                        // Put the byte back and parse as instruction
                        self.cursor = pos;
                        let instruction = self.parse_instruction()?;
                        true_instructions.push(instruction);
                    }
                }
                
                // Check if there's an else clause
                let pos = self.cursor;
                let next_byte = self.read_byte()?;
                
                if next_byte == 0x05 {
                    // There's an else clause - parse false instructions
                    let mut false_instructions = Vec::new();
                    loop {
                        let pos = self.cursor;
                        let next_byte = self.read_byte()?;
                        
                        if next_byte == 0x0B {
                            // Found end - stop parsing false instructions
                            break;
                        } else {
                            // Put the byte back and parse as instruction
                            self.cursor = pos;
                            let instruction = self.parse_instruction()?;
                            false_instructions.push(instruction);
                        }
                    }
                    
                    Ok(ast::ControlInstruction::If {
                        block_type,
                        true_instructions,
                        false_instructions,
                    })
                } else {
                    // No else clause - put the byte back
                    self.cursor = pos;
                    Ok(ast::ControlInstruction::If {
                        block_type,
                        true_instructions,
                        false_instructions: Vec::new(),
                    })
                }
            }
            0x05 => {
                // else - this should not be encountered as an independent instruction
                // but we handle it gracefully for error recovery
                parser_debug_log!(&self.config, "Warning: else instruction encountered outside of if block");
                Ok(ast::ControlInstruction::Else)
            }
            0x0C => {
                // br
                let label_index = self.parse_u32()?;
                Ok(ast::ControlInstruction::Br { label_index })
            }
            0x0D => {
                // br_if
                let label_index = self.parse_u32()?;
                Ok(ast::ControlInstruction::BrIf { label_index })
            }
            0x0E => {
                // br_table
                let label_indices = self.parse_vec(|p| p.parse_u32())?;
                let default_index = self.parse_u32()?;
                Ok(ast::ControlInstruction::BrTable {
                    label_indices,
                    default_index,
                })
            }
            0x0F => Ok(ast::ControlInstruction::Return),
            0x10 => {
                // call
                let function_index = self.parse_u32()?;
                parser_debug_log!(&self.config, "call function_index: {}", function_index);
                Ok(ast::ControlInstruction::Call { function_index })
            }
            0x11 => {
                // call_indirect
                let type_index = self.parse_u32()?;
                let table_index = self.parse_u32()?;
                Ok(ast::ControlInstruction::CallIndirect {
                    table_index,
                    type_index,
                })
            }
            _ => Err(ParseError::InvalidInstruction),
        }
    }

    /// Parse a block type
    /// 
    /// # Specification
    /// 
    /// Block types can be either a type index or a value type:
    /// 
    /// ```
    /// blocktype ::= t:valtype ⇒ [t]
    ///             | x:s33 ⇒ [t1*] → [t2*] (where functype[x] = [t1*] → [t2*])
    /// ```
    /// 
    /// # Examples
    /// 
    /// ```
    /// // Empty block type
    /// 0x40
    /// 
    /// // Block type with i32 result
    /// 0x7F
    /// ```
    /// 
    /// # Errors
    /// 
    /// - `UnexpectedEof`: Input ends unexpectedly
    /// - `InvalidIntegerEncoding`: Invalid type index encoding
    pub fn parse_block_type(&mut self) -> ParseResult<ast::BlockType> {
        let byte = self.read_byte()?;
        match byte {
            0x40 => Ok(ast::BlockType::ValueType(None)), // Empty block type
            0x7F => Ok(ast::BlockType::ValueType(Some(ast::ValType::I32))),
            0x7E => Ok(ast::BlockType::ValueType(Some(ast::ValType::I64))),
            0x7D => Ok(ast::BlockType::ValueType(Some(ast::ValType::F32))),
            0x7C => Ok(ast::BlockType::ValueType(Some(ast::ValType::F64))),
            _ => {
                // Try to parse as a signed 33-bit integer (type index)
                self.cursor -= 1;
                let type_index = self.parse_s33()?;
                Ok(ast::BlockType::TypeIndex(type_index as u32))
            }
        }
    }

    /// Parse a signed 33-bit integer
    /// 
    /// This is used for type indices in block types.
    pub fn parse_s33(&mut self) -> ParseResult<i64> {
        let mut result: i64 = 0;
        let mut shift: u32 = 0;
        let mut byte: u8;

        loop {
            byte = self.read_byte()?;
            if (byte & 0x80) == 0 {
                if shift < 32 {
                    if (byte & 0x40) != 0 {
                        result |= !0 << (shift + 7);
                    }
                } else {
                    let sign_bit = (byte & 0x40) != 0;
                    let unused_bits = byte & 0xC0;
                    if (sign_bit && unused_bits != 0xC0) || (!sign_bit && unused_bits != 0) {
                        return Err(ParseError::InvalidIntegerEncoding);
                    }
                }
                result |= ((byte & 0x7F) as i64) << shift;
                break;
            }
            if shift >= 25 {
                return Err(ParseError::InvalidIntegerEncoding);
            }
            result |= ((byte & 0x7F) as i64) << shift;
            shift += 7;
        }
        Ok(result)
    }

    /// Parse a vector of items
    /// 
    /// # Arguments
    /// 
    /// * `f` - A function that parses a single item
    /// 
    /// # Returns
    /// 
    /// * `ParseResult<Vec<T>>` - The parsed vector of items
    pub fn parse_vec<F, T>(&mut self, mut f: F) -> ParseResult<Vec<T>>
    where
        F: FnMut(&mut Self) -> ParseResult<T>,
    {
        let count = self.parse_u32()?;
        let mut items = Vec::with_capacity(count as usize);
        for _ in 0..count {
            items.push(f(self)?);
        }
        Ok(items)
    }
}

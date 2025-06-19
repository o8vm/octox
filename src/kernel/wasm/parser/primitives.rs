//! Primitive binary reading utilities for WebAssembly parser

use crate::wasm::parser::error::{ParseError, ParseResult};
use crate::parser_debug_log;
use crate::wasm::parser::ParserConfig;
use alloc::format;
use alloc::string::String;
use crate::alloc::string::ToString;
use super::Parser;

impl<'a> Parser<'a> {
    /// Returns the current position in the input
    pub const fn position(&self) -> usize {
        self.cursor
    }

    /// Returns the remaining length of the input
    pub const fn remaining(&self) -> usize {
        self.input.len() - self.cursor
    }

    /// Returns whether the parser has reached the end of the input
    pub const fn is_eof(&self) -> bool {
        self.cursor >= self.input.len()
    }

    /// Returns a slice of the remaining input
    pub fn remaining_slice(&self) -> &'a [u8] {
        &self.input[self.cursor..]
    }

    /// Read a LEB128-encoded unsigned 32-bit integer.
    pub fn read_u32(&mut self) -> ParseResult<u32> {
        let mut result: u32 = 0;
        let mut shift: u32 = 0;
        let mut byte: u8;

        loop {
            byte = self.read_byte()?;
            result |= ((byte & 0x7F) as u32) << shift;
            if (byte & 0x80) == 0 {
                break;
            }
            shift += 7;
            if shift >= 32 {
                return Err(ParseError::InvalidIntegerEncoding);
            }
        }

        Ok(result)
    }

    /// Read a LEB128-encoded signed 32-bit integer.
    pub fn read_i32(&mut self) -> ParseResult<i32> {
        let mut result: i32 = 0;
        let mut shift: u32 = 0;
        let mut byte: u8;

        loop {
            byte = self.read_byte()?;
            result |= ((byte & 0x7F) as i32) << shift;
            if (byte & 0x80) == 0 {
                // Sign extend if the last byte's sign bit is set
                if shift < 31 && (byte & 0x40) != 0 {
                    result |= !0 << (shift + 7);
                }
                break;
            }
            shift += 7;
            if shift >= 32 {
                return Err(ParseError::InvalidIntegerEncoding);
            }
        }

        Ok(result)
    }

    /// Read a UTF-8 encoded string.
    pub fn read_string(&mut self) -> ParseResult<String> {
        let len = self.read_u32()? as usize;
        let bytes = self.read_bytes(len)?;
        String::from_utf8(bytes.to_vec())
            .map_err(|_| ParseError::InvalidUtf8)
    }

    /// Read a single byte from the input.
    pub fn read_byte(&mut self) -> ParseResult<u8> {
        if self.cursor >= self.input.len() {
            return Err(ParseError::UnexpectedEof);
        }
        let byte = self.input[self.cursor];
        self.cursor += 1;
        Ok(byte)
    }

    /// Peek at the next byte without consuming it.
    pub fn peek_byte(&self) -> ParseResult<u8> {
        if self.cursor >= self.input.len() {
            return Err(ParseError::UnexpectedEof);
        }
        Ok(self.input[self.cursor])
    }

    /// Read a sequence of bytes from the input.
    pub fn read_bytes(&mut self, n: usize) -> ParseResult<&'a [u8]> {
        if self.remaining() < n {
            return Err(ParseError::UnexpectedEof);
        }
        let bytes = &self.input[self.cursor..self.cursor + n];
        self.cursor += n;
        Ok(bytes)
    }

    /// Parse a byte (direct encoding)
    pub fn parse_byte(&mut self) -> ParseResult<u8> {
        self.read_byte()
    }

    /// Parse a sequence of bytes (direct encoding)
    pub fn parse_bytes(&mut self, n: usize) -> ParseResult<&'a [u8]> {
        self.read_bytes(n)
    }

    /// Parse an unsigned 32-bit integer (LEB128)
    pub fn parse_u32(&mut self) -> ParseResult<u32> {
        let mut result: u32 = 0;
        let mut shift: u32 = 0;
        let mut byte: u8;

        loop {
            byte = self.read_byte()?;
            if (byte & 0x80) == 0 {
                if shift >= 25 && byte > 0x7F {
                    return Err(ParseError::InvalidIntegerEncoding);
                }
                result |= (byte as u32) << shift;
                break;
            }
            if shift >= 25 {
                return Err(ParseError::InvalidIntegerEncoding);
            }
            result |= ((byte & 0x7F) as u32) << shift;
            shift += 7;
        }
        Ok(result)
    }

    /// Parse a signed 32-bit integer (LEB128)
    pub fn parse_i32(&mut self) -> ParseResult<i32> {
        let mut result: i32 = 0;
        let mut shift: u32 = 0;
        let mut byte: u8;
        let start_cursor = self.cursor;

        loop {
            byte = self.read_byte()?;
            parser_debug_log!(&self.config, "parse_i32: byte 0x{:02X} at cursor {}", byte, self.cursor - 1);
            if (byte & 0x80) == 0 {
                if shift < 31 {
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
                result |= ((byte & 0x7F) as i32) << shift;
                parser_debug_log!(&self.config, "parse_i32: final result {} from bytes at cursor {} to {}", result, start_cursor, self.cursor);
                break;
            }
            if shift >= 25 {
                return Err(ParseError::InvalidIntegerEncoding);
            }
            result |= ((byte & 0x7F) as i32) << shift;
            shift += 7;
        }
        Ok(result)
    }

    /// Parse a 64-bit signed integer using LEB128 encoding
    pub fn parse_i64(&mut self) -> ParseResult<i64> {
        let mut result: i64 = 0;
        let mut shift: u32 = 0;
        let mut byte: u8;

        loop {
            byte = self.read_byte()?;
            result |= ((byte & 0x7F) as i64) << shift;
            shift += 7;
            if (byte & 0x80) == 0 {
                if shift < 64 && (byte & 0x40) != 0 {
                    result |= !0 << shift;
                }
                break;
            }
            if shift >= 70 {
                return Err(ParseError::InvalidIntegerEncoding);
            }
        }
        Ok(result)
    }

    /// Parse a 32-bit floating-point number (IEEE 754 single precision)
    pub fn parse_f32(&mut self) -> ParseResult<f32> {
        let bytes = self.read_bytes(4)?;
        let mut bits = [0u8; 4];
        bits.copy_from_slice(bytes);
        Ok(f32::from_le_bytes(bits))
    }

    /// Parse a 128-bit signed integer in little-endian byte order
    pub fn parse_i128(&mut self) -> ParseResult<i128> {
        let bytes = self.read_bytes(16)?;
        let mut result: i128 = 0;
        for (i, &byte) in bytes.iter().enumerate() {
            result |= (byte as i128) << (i * 8);
        }
        Ok(result)
    }

    /// Parse a 64-bit floating-point number (IEEE 754 double precision)
    pub fn parse_f64(&mut self) -> ParseResult<f64> {
        let bytes = self.read_bytes(8)?;
        let mut bits = [0u8; 8];
        bits.copy_from_slice(bytes);
        Ok(f64::from_le_bytes(bits))
    }

    /// Parse a name as a UTF-8 encoded string.
    pub fn parse_name(&mut self) -> ParseResult<String> {
        let len = self.parse_u32()?;
        if self.remaining() < len as usize {
            return Err(ParseError::UnexpectedEof);
        }
        let bytes = self.read_bytes(len as usize)?;
        match core::str::from_utf8(bytes) {
            Ok(s) => {
                if s.chars().any(|c| (0xD800..=0xDFFF).contains(&(c as u32))) {
                    return Err(ParseError::InvalidUtf8);
                }
                Ok(s.to_string())
            }
            Err(_) => Err(ParseError::InvalidUtf8),
        }
    }
} 
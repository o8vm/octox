use alloc::vec::Vec;
use alloc::format;
use alloc::string::String;
use alloc::string::ToString;
use core::fmt;
use core::iter;

use crate::wasm::ast::{MemoryType, WASM_PAGE_SIZE};

/// Memory instance
/// 
/// A memory instance is the runtime representation of a linear memory.
/// It records its type and holds a vector of bytes.
/// 
/// # Specification
/// 
/// The length of the vector always is a multiple of the WebAssembly page size (64 KiB).
/// The bytes can be mutated through memory instructions, the execution of an active data segment,
/// or by external means provided by the embedder.
/// 
/// It is an invariant of the semantics that the length of the byte vector, divided by page size,
/// never exceeds the maximum size of memtype, if present.
#[derive(Debug)]
pub struct MemoryInstance {
    /// Memory type (limits)
    ty: MemoryType,
    /// Memory data (vector of bytes)
    data: Vec<u8>,
}

impl MemoryInstance {
    /// Creates a new memory instance
    /// 
    /// # Arguments
    /// 
    /// * `ty` - The memory type defining the limits
    /// 
    /// # Returns
    /// 
    /// A new memory instance with the specified type and initialized data.
    /// The data vector is initialized to the minimum size specified by the type,
    /// with all bytes set to 0.
    pub fn new(ty: MemoryType) -> Self {
        let min_bytes = ty.min_bytes() as usize;
        let mut data = Vec::with_capacity(min_bytes);
        data.resize(min_bytes, 0);
        Self { ty, data }
    }

    /// Returns the memory type
    pub fn ty(&self) -> &MemoryType {
        &self.ty
    }

    /// Returns the current size of the memory in pages
    pub fn size(&self) -> u32 {
        (self.data.len() as u32) / WASM_PAGE_SIZE
    }

    /// Returns the current size of the memory in bytes
    pub fn size_bytes(&self) -> usize {
        self.data.len()
    }

    /// Returns the maximum size of the memory in pages, if any
    pub fn max_size(&self) -> Option<u32> {
        self.ty.max_pages()
    }

    /// Returns true if the memory has a maximum size limit
    pub fn has_max_size(&self) -> bool {
        self.ty.max_pages().is_some()
    }

    /// Reads a byte from memory
    /// 
    /// # Arguments
    /// 
    /// * `offset` - The byte offset to read from
    /// 
    /// # Returns
    /// 
    /// The byte at the given offset, or an error if the offset is out of bounds.
    pub fn read_byte(&self, offset: usize) -> Result<u8, String> {
        self.data.get(offset).copied().ok_or_else(|| {
            format!("memory access out of bounds: offset {}", offset)
        })
    }

    /// Writes a byte to memory
    /// 
    /// # Arguments
    /// 
    /// * `offset` - The byte offset to write to
    /// * `value` - The byte value to write
    /// 
    /// # Returns
    /// 
    /// An error if the offset is out of bounds.
    pub fn write_byte(&mut self, offset: usize, value: u8) -> Result<(), String> {
        if offset >= self.data.len() {
            return Err(format!("memory access out of bounds: offset {}", offset));
        }
        self.data[offset] = value;
        Ok(())
    }

    /// Reads a slice of bytes from memory
    /// 
    /// # Arguments
    /// 
    /// * `offset` - The starting byte offset
    /// * `len` - The number of bytes to read
    /// 
    /// # Returns
    /// 
    /// A slice of bytes from memory, or an error if the range is out of bounds.
    pub fn read_bytes(&self, offset: usize, len: usize) -> Result<&[u8], String> {
        let end = offset.checked_add(len).ok_or_else(|| {
            format!("memory access overflow: offset {} + len {}", offset, len)
        })?;
        if end > self.data.len() {
            return Err(format!(
                "memory access out of bounds: offset {} + len {} > {}",
                offset, len, self.data.len()
            ));
        }
        Ok(&self.data[offset..end])
    }

    /// Writes a slice of bytes to memory
    /// 
    /// # Arguments
    /// 
    /// * `offset` - The starting byte offset
    /// * `bytes` - The bytes to write
    /// 
    /// # Returns
    /// 
    /// An error if the range is out of bounds.
    pub fn write_bytes(&mut self, offset: usize, bytes: &[u8]) -> Result<(), String> {
        let len = bytes.len();
        let end = offset.checked_add(len).ok_or_else(|| {
            format!("memory access overflow: offset {} + len {}", offset, len)
        })?;
        if end > self.data.len() {
            return Err(format!(
                "memory access out of bounds: offset {} + len {} > {}",
                offset, len, self.data.len()
            ));
        }
        self.data[offset..end].copy_from_slice(bytes);
        Ok(())
    }

    /// Grows the memory by the given number of pages
    /// 
    /// # Specification (Growing memories)
    /// 
    /// 1. Let meminst be the memory instance to grow and n the number of pages by which to grow it.
    /// 2. Assert: The length of meminst.data is divisible by the page size 64 Ki.
    /// 3. Let len be n added to the length of meminst.data divided by the page size 64 Ki.
    /// 4. If len is larger than 2^16, then fail.
    /// 5. Let limits be the structure of memory type meminst.type.
    /// 6. Let limits' be limits with min updated to len.
    /// 7. If limits' is not valid, then fail.
    /// 8. Append n times 64 Ki bytes with value 0x00 to meminst.data.
    /// 9. Set meminst.type to the memory type limits'.
    /// 
    /// growmem(meminst, n) = meminst with type = limits' with data = meminst.data (0x00)^(n·64 Ki)
    /// (if len = n + |meminst.data|/64 Ki
    ///  ∧ len ≤ 2^16
    ///  ∧ limits = meminst.type
    ///  ∧ limits' = limits with min = len
    ///  ∧ ⊢ limits' ok)
    /// 
    /// # Arguments
    /// 
    /// * `delta` - The number of pages to grow by
    /// * `config` - Runtime configuration for debug logging
    /// 
    /// # Returns
    /// 
    /// The previous size in pages, or an error if the growth would exceed the maximum size.
    pub fn grow(&mut self, delta: u32, config: &crate::wasm::runtime::RuntimeConfig) -> Result<(), String> {
        let new_pages = self.size().checked_add(delta).ok_or_else(|| {
            "Memory size overflow".to_string()
        })?;

        // Check if the new size would exceed the maximum limit
        if let Some(max_pages) = self.max_size() {
            if new_pages > max_pages {
                return Err("Memory size exceeds maximum".to_string());
            }
        }

        // Check if the new size would exceed 2^16 pages (WebAssembly limit)
        if new_pages > 1u32 << 16 {
            return Err("Memory size exceeds WebAssembly limit of 2^16 pages".to_string());
        }

        let new_bytes = delta * WASM_PAGE_SIZE as u32;
        let new_data_size = self.data.len() + new_bytes as usize;

        crate::wasm::runtime::debug_log(config, &format!("MemoryInstance::grow: extending data by {} bytes (from {} to {})", new_bytes, self.data.len(), new_data_size));
        
        self.data.resize(new_data_size, 0);
        
        crate::wasm::runtime::debug_log(config, &format!("MemoryInstance::grow: data extended successfully, new size: {}", self.data.len()));
        Ok(())
    }

    /// Fills a range of memory with a byte value
    /// 
    /// # Arguments
    /// 
    /// * `offset` - The starting byte offset
    /// * `count` - The number of bytes to fill
    /// * `value` - The byte value to fill with
    /// * `config` - Runtime configuration for debug logging
    /// 
    /// # Returns
    /// 
    /// An error if the range is out of bounds.
    pub fn fill(&mut self, offset: usize, count: usize, value: u8, config: &crate::wasm::runtime::RuntimeConfig) -> Result<(), String> {
        let end = offset.checked_add(count).ok_or_else(|| {
            "Memory fill range overflow".to_string()
        })?;

        if end > self.data.len() {
            return Err(format!("Memory fill range {}..{} out of bounds (size: {})", offset, end, self.data.len()));
        }

        crate::wasm::runtime::debug_log(config, &format!("MemoryInstance::fill: filling range {}..{} with value 0x{:02x}", offset, end, value));
        
        for i in offset..end {
            self.data[i] = value;
        }
        
        crate::wasm::runtime::debug_log(config, &format!("MemoryInstance::fill: fill completed successfully"));
        Ok(())
    }

    /// Copies bytes between ranges of memory
    /// 
    /// # Arguments
    /// 
    /// * `dst` - The destination byte offset
    /// * `src` - The source byte offset
    /// * `len` - The number of bytes to copy
    /// 
    /// # Returns
    /// 
    /// An error if either range is out of bounds.
    pub fn copy(&mut self, dst: usize, src: usize, len: usize) -> Result<(), String> {
        let dst_end = dst.checked_add(len).ok_or_else(|| {
            format!("memory access overflow: dst {} + len {}", dst, len)
        })?;
        let src_end = src.checked_add(len).ok_or_else(|| {
            format!("memory access overflow: src {} + len {}", src, len)
        })?;
        if dst_end > self.data.len() {
            return Err(format!(
                "destination out of bounds: {} + {} > {}",
                dst, len, self.data.len()
            ));
        }
        if src_end > self.data.len() {
            return Err(format!(
                "source out of bounds: {} + {} > {}",
                src, len, self.data.len()
            ));
        }
        if dst <= src {
            // Copy forward
            self.data.copy_within(src..src_end, dst);
        } else {
            // Copy backward
            for i in 0..len {
                self.data[dst + i] = self.data[src + i];
            }
        }
        Ok(())
    }

    /// Initializes a range of memory with bytes
    /// 
    /// # Arguments
    /// 
    /// * `offset` - The starting byte offset
    /// * `bytes` - The bytes to write
    /// 
    /// # Returns
    /// 
    /// An error if the range is out of bounds.
    pub fn init(&mut self, offset: usize, bytes: &[u8]) -> Result<(), String> {
        self.write_bytes(offset, bytes)
    }
}

impl fmt::Display for MemoryInstance {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Memory {{")?;
        writeln!(f, "  type: {}", self.ty)?;
        writeln!(f, "  size: {} pages ({} bytes)", self.size(), self.size_bytes())?;
        writeln!(f, "  data: [")?;
        // Print first 32 bytes in hex
        let preview_len = self.data.len().min(32);
        for i in 0..preview_len {
            if i > 0 && i % 16 == 0 {
                writeln!(f)?;
            }
            write!(f, " {:02x}", self.data[i])?;
        }
        if self.data.len() > preview_len {
            writeln!(f, " ... {} more bytes", self.data.len() - preview_len)?;
        } else {
            writeln!(f)?;
        }
        writeln!(f, "  ]")?;
        write!(f, "}}")
    }
}

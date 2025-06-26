use alloc::vec::Vec;
use alloc::format;
use alloc::string::String;
use alloc::string::ToString;
use core::fmt;
use core::iter;

use crate::wasm::ast::{MemoryType, WASM_PAGE_SIZE};
use crate::debug_log;

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
        
        // Add a reasonable limit to prevent excessive memory usage in kernel space
        const MAX_KERNEL_MEMORY_PAGES: u32 = 4; // 4 pages = ~256KB (adjusted for prime.wasm)
        const MAX_KERNEL_MEMORY_BYTES: usize = MAX_KERNEL_MEMORY_PAGES as usize * WASM_PAGE_SIZE as usize;
        
        if min_bytes > MAX_KERNEL_MEMORY_BYTES {
            panic!("Initial memory size {} bytes exceeds kernel limit of {} bytes", min_bytes, MAX_KERNEL_MEMORY_BYTES);
        }
        
        // Create a default config for logging
        let config = crate::wasm::runtime::RuntimeConfig::default();
        debug_log!(&config, "MemoryInstance::new: creating memory with {} bytes ({} pages)", min_bytes, min_bytes / WASM_PAGE_SIZE as usize);
        
        let mut data = Vec::with_capacity(min_bytes);
        
        // Try to allocate memory in smaller chunks to avoid page faults
        let chunk_size = 4096; // 4KB chunks
        let mut allocated = 0;
        
        while allocated < min_bytes {
            let remaining = min_bytes - allocated;
            let current_chunk = core::cmp::min(chunk_size, remaining);
            
            // Try to extend the vector by the current chunk size
            let old_len = data.len();
            data.resize(old_len + current_chunk, 0);
            
            // Check if the resize was successful
            if data.len() == old_len + current_chunk {
                // Explicitly zero out the newly allocated chunk
                for i in old_len..data.len() {
                    data[i] = 0;
                }
                allocated += current_chunk;
                debug_log!(&config, "MemoryInstance::new: allocated {} bytes, total: {}", current_chunk, allocated);
            } else {
                // If allocation fails, try with a smaller chunk
                let smaller_chunk = current_chunk / 2;
                if smaller_chunk == 0 {
                    // If we can't allocate even 1 byte, this is a critical error
                    panic!("Failed to allocate initial WASM memory: could not allocate {} bytes", min_bytes);
                }
                data.resize(old_len + smaller_chunk, 0);
                // Explicitly zero out the newly allocated chunk
                for i in old_len..data.len() {
                    data[i] = 0;
                }
                allocated += smaller_chunk;
                debug_log!(&config, "MemoryInstance::new: allocated smaller chunk {} bytes, total: {}", smaller_chunk, allocated);
            }
        }
        
        debug_log!(&config, "MemoryInstance::new: memory created successfully with {} bytes", data.len());
        
        // Verify that the memory is accessible by testing a few bytes
        if data.len() > 0 {
            debug_log!(&config, "MemoryInstance::new: testing memory access...");
            for i in 0..core::cmp::min(10, data.len()) {
                if data[i] != 0 {
                    debug_log!(&config, "MemoryInstance::new: warning: byte at offset {} is not zero: 0x{:02x}", i, data[i]);
                }
            }
            debug_log!(&config, "MemoryInstance::new: memory access test completed");
        }
        
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
        
        // Test memory access before returning the slice
        if len > 0 {
            // Test the first byte
            let _ = self.data[offset];
            
            // Test the last byte if different from first
            if end > offset + 1 {
                let _ = self.data[end - 1];
            }
            
            // Test a few bytes in the middle if the range is large enough
            if end > offset + 100 {
                let mid = offset + (end - offset) / 2;
                let _ = self.data[mid];
            }
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

        // Add a reasonable limit to prevent excessive memory usage in kernel space
        const MAX_KERNEL_MEMORY_PAGES: u32 = 4; // 4 pages = ~256KB (adjusted for prime.wasm)
        const MAX_KERNEL_MEMORY_BYTES: usize = MAX_KERNEL_MEMORY_PAGES as usize * WASM_PAGE_SIZE as usize;
        
        if new_pages > MAX_KERNEL_MEMORY_PAGES {
            return Err(format!("Memory size exceeds kernel limit of {} pages", MAX_KERNEL_MEMORY_PAGES));
        }

        let new_bytes = delta * WASM_PAGE_SIZE as u32;
        let new_data_size = self.data.len() + new_bytes as usize;

        debug_log!(config, "MemoryInstance::grow: extending data by {} bytes (from {} to {})", new_bytes, self.data.len(), new_data_size);
        
        // Try to grow memory in much smaller chunks to avoid page faults
        let chunk_size = 256; // Reduced to 256 bytes for maximum safety
        let mut remaining_bytes = new_bytes as usize;
        let mut current_size = self.data.len();
        
        debug_log!(config, "MemoryInstance::grow: starting growth by {} bytes in {} chunks", new_bytes, (new_bytes as usize + chunk_size - 1) / chunk_size);
        
        while remaining_bytes > 0 {
            let current_chunk = core::cmp::min(chunk_size, remaining_bytes);
            
            // Try to extend the vector by the current chunk size
            let old_len = self.data.len();
            self.data.resize(old_len + current_chunk, 0);
            
            // Check if the resize was successful
            if self.data.len() == old_len + current_chunk {
                // Explicitly zero out the newly allocated chunk and test access
                for i in old_len..self.data.len() {
                    self.data[i] = 0;
                }
                
                // Test that we can actually read from the newly allocated memory
                if self.data.len() > old_len {
                    let test_offset = old_len;
                    let test_value = self.data[test_offset];
                    if test_value != 0 {
                        debug_log!(config, "MemoryInstance::grow: warning: newly allocated byte at {} is not zero: 0x{:02x}", test_offset, test_value);
                    }
                }
                
                remaining_bytes -= current_chunk;
                debug_log!(config, "MemoryInstance::grow: extended by {} bytes, remaining: {}", current_chunk, remaining_bytes);
                debug_log!(config, "MemoryInstance::grow: chunk allocated successfully, remaining: {} bytes", remaining_bytes);
            } else {
                debug_log!(config, "MemoryInstance::grow: failed to allocate chunk of {} bytes", current_chunk);
                return Err(format!("Failed to allocate memory: could not extend by {} bytes", current_chunk));
            }
        }
        
        debug_log!(config, "MemoryInstance::grow: data extended successfully, new size: {}", self.data.len());
        debug_log!(config, "MemoryInstance::grow: memory growth completed successfully, new size: {} bytes", self.data.len());
        
        // Verify that the newly allocated memory is accessible by testing multiple points
        if self.data.len() > 0 {
            debug_log!(config, "MemoryInstance::grow: testing newly allocated memory access...");
            
            // Test the beginning of the newly allocated memory
            let new_start = current_size;
            if new_start < self.data.len() {
                let test_value = self.data[new_start];
                debug_log!(config, "MemoryInstance::grow: new memory start at {}: 0x{:02x}", new_start, test_value);
            }
            
            // Test the middle of the newly allocated memory
            let new_middle = new_start + (self.data.len() - new_start) / 2;
            if new_middle < self.data.len() {
                let test_value = self.data[new_middle];
                debug_log!(config, "MemoryInstance::grow: new memory middle at {}: 0x{:02x}", new_middle, test_value);
            }
            
            // Test the end of the newly allocated memory
            let new_end = self.data.len() - 1;
            if new_end >= new_start {
                let test_value = self.data[new_end];
                debug_log!(config, "MemoryInstance::grow: new memory end at {}: 0x{:02x}", new_end, test_value);
            }
            
            debug_log!(config, "MemoryInstance::grow: memory access test completed");
        }
        
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

        debug_log!(config, "MemoryInstance::fill: filling range {}..{} with value 0x{:02x}", offset, end, value);
        
        // Test memory access before filling to ensure the memory is properly mapped
        if count > 0 {
            // Test the first byte
            match self.read_byte(offset) {
                Ok(_) => debug_log!(config, "MemoryInstance::fill: first byte access test successful"),
                Err(e) => {
                    debug_log!(config, "MemoryInstance::fill: first byte access test failed: {}", e);
                    return Err(format!("Memory access test failed at offset {}: {}", offset, e));
                }
            }
            
            // Test the last byte if different from first
            if end > offset + 1 {
                match self.read_byte(end - 1) {
                    Ok(_) => debug_log!(config, "MemoryInstance::fill: last byte access test successful"),
                    Err(e) => {
                        debug_log!(config, "MemoryInstance::fill: last byte access test failed: {}", e);
                        return Err(format!("Memory access test failed at offset {}: {}", end - 1, e));
                    }
                }
            }
            
            // Test a few bytes in the middle if the range is large enough
            if end > offset + 100 {
                let mid = offset + (end - offset) / 2;
                match self.read_byte(mid) {
                    Ok(_) => debug_log!(config, "MemoryInstance::fill: middle byte access test successful"),
                    Err(e) => {
                        debug_log!(config, "MemoryInstance::fill: middle byte access test failed: {}", e);
                        return Err(format!("Memory access test failed at offset {}: {}", mid, e));
                    }
                }
            }
        }
        
        // Fill memory in very small chunks to avoid potential issues
        let chunk_size = 64; // Further reduced to 64 bytes for maximum safety
        let mut current_offset = offset;
        
        while current_offset < end {
            let current_chunk_end = core::cmp::min(current_offset + chunk_size, end);
            
            // Test access to the current chunk before filling
            if current_chunk_end > current_offset {
                match self.read_byte(current_offset) {
                    Ok(_) => debug_log!(config, "MemoryInstance::fill: chunk access test successful at offset {}", current_offset),
                    Err(e) => {
                        debug_log!(config, "MemoryInstance::fill: chunk access test failed at offset {}: {}", current_offset, e);
                        return Err(format!("Memory access test failed at offset {}: {}", current_offset, e));
                    }
                }
                
                // Also test the end of the chunk
                if current_chunk_end > current_offset + 1 {
                    match self.read_byte(current_chunk_end - 1) {
                        Ok(_) => debug_log!(config, "MemoryInstance::fill: chunk end access test successful at offset {}", current_chunk_end - 1),
                        Err(e) => {
                            debug_log!(config, "MemoryInstance::fill: chunk end access test failed at offset {}: {}", current_chunk_end - 1, e);
                            return Err(format!("Memory access test failed at offset {}: {}", current_chunk_end - 1, e));
                        }
                    }
                }
            }
            
            // Fill the current chunk with extra bounds checking
            for i in current_offset..current_chunk_end {
                // Double-check bounds before each write
                if i >= self.data.len() {
                    return Err(format!("Memory fill: index {} out of bounds (size: {})", i, self.data.len()));
                }
                
                // Test read access before write
                let _ = self.data[i];
                
                // Perform the write
                self.data[i] = value;
                
                // Verify the write was successful
                if self.data[i] != value {
                    return Err(format!("Memory fill: write verification failed at offset {}: expected 0x{:02x}, got 0x{:02x}", i, value, self.data[i]));
                }
            }
            
            current_offset = current_chunk_end;
        }
        
        debug_log!(config, "MemoryInstance::fill: fill completed successfully");
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

    /// Initializes a range of memory with data from a data segment
    /// 
    /// # Arguments
    /// 
    /// * `offset` - The starting byte offset in memory
    /// * `bytes` - The bytes to initialize with
    /// 
    /// # Returns
    /// 
    /// An error if the range is out of bounds.
    pub fn init(&mut self, offset: usize, bytes: &[u8]) -> Result<(), String> {
        let end = offset.checked_add(bytes.len()).ok_or_else(|| {
            "Memory init range overflow".to_string()
        })?;

        if end > self.data.len() {
            return Err(format!("Memory init range {}..{} out of bounds (size: {})", offset, end, self.data.len()));
        }

        // Initialize memory in smaller chunks to avoid potential issues
        let chunk_size = 64; // Use small chunks for safety
        let mut current_offset = offset;
        let mut bytes_index = 0;
        
        while bytes_index < bytes.len() {
            let current_chunk_end = core::cmp::min(current_offset + chunk_size, end);
            let current_chunk_size = current_chunk_end - current_offset;
            
            // Test memory access before writing
            if current_chunk_end > current_offset {
                // Test read access to ensure memory is properly mapped
                let _ = self.data[current_offset];
            }
            
            // Copy the current chunk
            for i in 0..current_chunk_size {
                let mem_index = current_offset + i;
                let bytes_index = bytes_index + i;
                
                // Double-check bounds before each write
                if mem_index >= self.data.len() || bytes_index >= bytes.len() {
                    return Err(format!("Memory init: index out of bounds (mem: {}, bytes: {})", mem_index, bytes_index));
                }
                
                // Test read access before write
                let _ = self.data[mem_index];
                
                // Perform the write
                self.data[mem_index] = bytes[bytes_index];
                
                // Verify the write was successful
                if self.data[mem_index] != bytes[bytes_index] {
                    return Err(format!("Memory init: write verification failed at offset {}: expected 0x{:02x}, got 0x{:02x}", mem_index, bytes[bytes_index], self.data[mem_index]));
                }
            }
            
            current_offset = current_chunk_end;
            bytes_index += current_chunk_size;
        }
        
        Ok(())
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

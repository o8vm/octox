//! Memory Instructions implementation for WebAssembly runtime.
//!
//! Implements instructions like i32.load, i64.load, f32.load, f64.load, i32.store, i64.store, f32.store, f64.store,
//! memory.size, memory.grow, memory.fill, memory.copy, memory.init.

use alloc::format;
use alloc::string::String;
use alloc::string::ToString;

use crate::wasm::runtime::{
    value::{Value, ValueType},
    DataInstance,
    RuntimeResult,
    RuntimeError,
    Store,
    Thread,
    numeric::{BitWidth, NumericResult, UnsignedOps, SignedOps, FloatOps},
};
use crate::wasm::ast::{Instruction, MemoryInstruction, ValType, WASM_PAGE_SIZE};
use crate::debug_log;

/// Memory instruction implementation.
pub struct Memory;

impl Memory {
    /// Executes a load instruction.
    /// 
    /// Pops an i32 address from the stack, loads a value of the specified type from memory,
    /// and pushes it to the stack.
    /// 
    /// # Specification
    /// 
    /// 1. Let 𝐹 be the current frame.
    /// 2. Assert: due to validation, 𝐹.module.memaddrs[0] exists.
    /// 3. Let 𝑎 be the memory address 𝐹.module.memaddrs[0].
    /// 4. Assert: due to validation, 𝑆.mems[𝑎] exists.
    /// 5. Let mem be the memory instance 𝑆.mems[𝑎].
    /// 6. Assert: due to validation, a value of value type i32 is on the top of the stack.
    /// 7. Pop the value i32.const 𝑖 from the stack.
    /// 8. Let ea be the integer 𝑖 + memarg.offset.
    /// 9. If 𝑁 is not part of the instruction, then:
    ///    a. Let 𝑁 be the bit width |𝑡| of number type 𝑡.
    /// 10. If ea + 𝑁/8 is larger than the length of mem.data, then:
    ///     a. Trap.
    /// 11. Let 𝑏* be the byte sequence mem.data[ea : 𝑁/8].
    /// 12. If 𝑁 and sx are part of the instruction, then:
    ///     a. Let 𝑛 be the integer for which bytesi𝑁(𝑛) = 𝑏*.
    ///     b. Let 𝑐 be the result of computing extendsx𝑁,|𝑡|(𝑛).
    /// 13. Else:
    ///     a. Let 𝑐 be the constant for which bytes𝑡(𝑐) = 𝑏*.
    /// 14. Push the value 𝑡.const 𝑐 to the stack.
    pub fn load(
        store: &Store,
        thread: &mut Thread,
        val_type: ValType,
        offset: u32,
        align: u32,
        width: Option<u32>,
        signed: Option<bool>,
    ) -> RuntimeResult<()> {
        // Get the current frame
        let frame = thread.frame_state();
        
        // Get the memory address from the module
        let mem_addr = frame.module().mem_addrs.get(0).ok_or_else(|| {
            RuntimeError::Execution(format!(
                "memory.load: Memory index 0 does not exist in current module"
            ))
        })?;

        // Get the memory instance from the store
        let mem = store.mems.get(mem_addr.as_usize()).ok_or_else(|| {
            RuntimeError::Execution(format!(
                "memory.load: Memory address {} does not exist in store",
                mem_addr
            ))
        })?;

        // Pop the i32 address from the stack
        let addr = match thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Stack("No value on stack for memory.load instruction".to_string())
        })? {
            Value::I32(i) => i as usize,
            _ => return Err(RuntimeError::TypeError("Expected i32 address for memory.load".to_string())),
        };

        // Calculate the effective address
        let ea = addr.checked_add(offset as usize).ok_or_else(|| {
            RuntimeError::Execution(format!(
                "memory.load: Address overflow: {} + {}",
                addr, offset
            ))
        })?;

        // Determine the number of bytes to read
        let width = width.unwrap_or_else(|| val_type.bit_width() as u32);
        let bytes = (width / 8) as usize;

        // Check if the read would be out of bounds
        if ea + bytes > mem.size_bytes() {
            return Err(RuntimeError::Execution(format!(
                "memory.load: Address out of bounds: {} + {} > {}",
                ea, bytes, mem.size_bytes()
            )));
        }

        // Read the bytes from memory
        let bytes = mem.read_bytes(ea, bytes).map_err(|e| {
            RuntimeError::Memory(format!("memory.load: {}", e))
        })?;

        // Convert the bytes to a value
        let value = match (val_type, width, signed) {
            (ValType::I32, 32, _) => {
                let n = i32::from_le_bytes(bytes.try_into().unwrap());
                Value::I32(n)
            }
            (ValType::I32, 16, Some(true)) => {
                let n = i16::from_le_bytes(bytes.try_into().unwrap());
                Value::I32(n as i32)
            }
            (ValType::I32, 16, Some(false)) => {
                let n = u16::from_le_bytes(bytes.try_into().unwrap());
                Value::I32(n as i32)
            }
            (ValType::I32, 8, Some(true)) => {
                let n = i8::from_le_bytes(bytes.try_into().unwrap());
                Value::I32(n as i32)
            }
            (ValType::I32, 8, Some(false)) => {
                let n = u8::from_le_bytes(bytes.try_into().unwrap());
                Value::I32(n as i32)
            }
            (ValType::I64, 64, _) => {
                let n = i64::from_le_bytes(bytes.try_into().unwrap());
                Value::I64(n)
            }
            (ValType::I64, 32, Some(true)) => {
                let n = i32::from_le_bytes(bytes.try_into().unwrap());
                Value::I64(n as i64)
            }
            (ValType::I64, 32, Some(false)) => {
                let n = u32::from_le_bytes(bytes.try_into().unwrap());
                Value::I64(n as i64)
            }
            (ValType::F32, 32, _) => {
                let n = f32::from_le_bytes(bytes.try_into().unwrap());
                Value::F32(n)
            }
            (ValType::F64, 64, _) => {
                let n = f64::from_le_bytes(bytes.try_into().unwrap());
                Value::F64(n)
            }
            _ => return Err(RuntimeError::TypeError(format!(
                "memory.load: Invalid type/width/signed combination: {:?}/{:?}/{:?}",
                val_type, width, signed
            ))),
        };

        // Push the value to the stack
        thread.stack_mut().push_value(value);
        Ok(())
    }

    /// Executes a store instruction.
    /// 
    /// Pops a value of the specified type and an i32 address from the stack,
    /// and stores the value to memory.
    /// 
    /// # Specification
    /// 
    /// 1. Let 𝐹 be the current frame.
    /// 2. Assert: due to validation, 𝐹.module.memaddrs[0] exists.
    /// 3. Let 𝑎 be the memory address 𝐹.module.memaddrs[0].
    /// 4. Assert: due to validation, 𝑆.mems[𝑎] exists.
    /// 5. Let mem be the memory instance 𝑆.mems[𝑎].
    /// 6. Assert: due to validation, a value of value type 𝑡 is on the top of the stack.
    /// 7. Pop the value 𝑡.const 𝑐 from the stack.
    /// 8. Assert: due to validation, a value of value type i32 is on the top of the stack.
    /// 9. Pop the value i32.const 𝑖 from the stack.
    /// 10. Let ea be the integer 𝑖 + memarg.offset.
    /// 11. If 𝑁 is not part of the instruction, then:
    ///     a. Let 𝑁 be the bit width |𝑡| of number type 𝑡.
    /// 12. If ea + 𝑁/8 is larger than the length of mem.data, then:
    ///     a. Trap.
    /// 13. If 𝑁 is part of the instruction, then:
    ///     a. Let 𝑛 be the result of computing wrap|𝑡|,𝑁 (𝑐).
    ///     b. Let 𝑏* be the byte sequence bytesi𝑁(𝑛).
    /// 14. Else:
    ///     a. Let 𝑏* be the byte sequence bytes𝑡(𝑐).
    /// 15. Replace the bytes mem.data[ea : 𝑁/8] with 𝑏*.
    pub fn store(
        store: &mut Store,
        thread: &mut Thread,
        val_type: ValType,
        offset: u32,
        align: u32,
        width: Option<u32>,
    ) -> RuntimeResult<()> {
        // Get the current frame
        let frame = thread.frame_state();
        
        // Get the memory address from the module
        let mem_addr = frame.module().mem_addrs.get(0).ok_or_else(|| {
            RuntimeError::Execution(format!(
                "memory.store: Memory index 0 does not exist in current module"
            ))
        })?;

        // Get the memory instance from the store
        let mem = store.mems.get_mut(mem_addr.as_usize()).ok_or_else(|| {
            RuntimeError::Execution(format!(
                "memory.store: Memory address {} does not exist in store",
                mem_addr
            ))
        })?;

        // Pop the value to store from the stack
        let value = thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Stack("No value on stack for memory.store instruction".to_string())
        })?;

        // Pop the i32 address from the stack
        let addr = match thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Stack("No address on stack for memory.store instruction".to_string())
        })? {
            Value::I32(i) => i as usize,
            _ => return Err(RuntimeError::TypeError("Expected i32 address for memory.store".to_string())),
        };

        // Calculate the effective address
        let ea = addr.checked_add(offset as usize).ok_or_else(|| {
            RuntimeError::Execution(format!(
                "memory.store: Address overflow: {} + {}",
                addr, offset
            ))
        })?;

        // Determine the number of bytes to write
        let width = width.unwrap_or_else(|| val_type.bit_width() as u32);
        let bytes = (width / 8) as usize;

        // Check if the write would be out of bounds
        if ea + bytes > mem.size_bytes() {
            return Err(RuntimeError::Execution(format!(
                "memory.store: Address out of bounds: {} + {} > {}",
                ea, bytes, mem.size_bytes()
            )));
        }

        // Convert the value to bytes
        let bytes_to_write = match (val_type, width, &value) {
            (ValType::I32, 32, Value::I32(n)) => {
                n.to_le_bytes().to_vec()
            }
            (ValType::I32, 16, Value::I32(n)) => {
                let wrapped = (*n as u16).wrapping_add(0) as i16; // wrap|𝑡|,𝑁 (𝑐)
                wrapped.to_le_bytes().to_vec()
            }
            (ValType::I32, 8, Value::I32(n)) => {
                let wrapped = (*n as u8).wrapping_add(0) as i8; // wrap|𝑡|,𝑁 (𝑐)
                wrapped.to_le_bytes().to_vec()
            }
            (ValType::I64, 64, Value::I64(n)) => {
                n.to_le_bytes().to_vec()
            }
            (ValType::I64, 32, Value::I64(n)) => {
                let wrapped = (*n as u32).wrapping_add(0) as i32; // wrap|𝑡|,𝑁 (𝑐)
                wrapped.to_le_bytes().to_vec()
            }
            (ValType::I64, 16, Value::I64(n)) => {
                let wrapped = (*n as u16).wrapping_add(0) as i16; // wrap|𝑡|,𝑁 (𝑐)
                wrapped.to_le_bytes().to_vec()
            }
            (ValType::I64, 8, Value::I64(n)) => {
                let wrapped = (*n as u8).wrapping_add(0) as i8; // wrap|𝑡|,𝑁 (𝑐)
                wrapped.to_le_bytes().to_vec()
            }
            (ValType::F32, 32, Value::F32(n)) => {
                n.to_le_bytes().to_vec()
            }
            (ValType::F64, 64, Value::F64(n)) => {
                n.to_le_bytes().to_vec()
            }
            _ => return Err(RuntimeError::TypeError(format!(
                "memory.store: Invalid type/width combination or value type mismatch: {:?}/{:?}/{:?}",
                val_type, width, value
            ))),
        };

        // Write the bytes to memory
        mem.write_bytes(ea, &bytes_to_write).map_err(|e| {
            RuntimeError::Memory(format!("memory.store: {}", e))
        })?;

        Ok(())
    }

    /// Executes a memory.size instruction.
    /// 
    /// Returns the current size of the memory in pages and pushes it to the stack.
    /// 
    /// # Specification
    /// 
    /// 1. Let 𝐹 be the current frame.
    /// 2. Assert: due to validation, 𝐹.module.memaddrs[0] exists.
    /// 3. Let 𝑎 be the memory address 𝐹.module.memaddrs[0].
    /// 4. Assert: due to validation, 𝑆.mems[𝑎] exists.
    /// 5. Let mem be the memory instance 𝑆.mems[𝑎].
    /// 6. Let sz be the length of mem.data divided by the page size.
    /// 7. Push the value i32.const sz to the stack.
    pub fn memory_size(
        store: &Store,
        thread: &mut Thread,
    ) -> RuntimeResult<()> {
        // Get the current frame
        let frame = thread.frame_state();
        
        // Get the memory address from the module
        let mem_addr = frame.module().mem_addrs.get(0).ok_or_else(|| {
            RuntimeError::Execution(format!(
                "memory.size: Memory index 0 does not exist in current module"
            ))
        })?;

        // Get the memory instance from the store
        let mem = store.mems.get(mem_addr.as_usize()).ok_or_else(|| {
            RuntimeError::Execution(format!(
                "memory.size: Memory address {} does not exist in store",
                mem_addr
            ))
        })?;

        // Get the current size in pages (sz = length of mem.data / page size)
        let size_in_pages = mem.size();

        // Push the size as i32 to the stack
        thread.stack_mut().push_value(Value::I32(size_in_pages as i32));
        crate::wasm::runtime::debug_log(store.config(), &format!("memory_size: pushed {}, stack now: {}", size_in_pages, thread.stack()));
        Ok(())
    }

    /// Executes a memory.grow instruction.
    /// 
    /// Attempts to grow the memory by the given number of pages.
    /// Returns the old size on success, or -1 on failure.
    /// 
    /// # Specification
    /// 
    /// 1. Let 𝐹 be the current frame.
    /// 2. Assert: due to validation, 𝐹.module.memaddrs[0] exists.
    /// 3. Let 𝑎 be the memory address 𝐹.module.memaddrs[0].
    /// 4. Assert: due to validation, 𝑆.mems[𝑎] exists.
    /// 5. Let mem be the memory instance 𝑆.mems[𝑎].
    /// 6. Let sz be the length of 𝑆.mems[𝑎] divided by the page size.
    /// 7. Assert: due to validation, a value of value type i32 is on the top of the stack.
    /// 8. Pop the value i32.const 𝑛 from the stack.
    /// 9. Let err be the i32 value 2^32 − 1, for which signed32(err) is −1.
    /// 10. Either:
    ///     a. If growing mem by 𝑛 pages succeeds, then:
    ///        i. Push the value i32.const sz to the stack.
    ///     b. Else:
    ///        i. Push the value i32.const err to the stack.
    /// 11. Or:
    ///     a. Push the value i32.const err to the stack.
    pub fn memory_grow(
        store: &mut Store,
        thread: &mut Thread,
    ) -> RuntimeResult<()> {
        // Get the current frame
        let frame = thread.frame_state();
        
        // Get the memory address from the module
        let mem_addr = frame.module().mem_addrs.get(0).ok_or_else(|| {
            RuntimeError::Execution(format!(
                "memory.grow: Memory index 0 does not exist in current module"
            ))
        })?;

        // Get the config before any mutable borrows and clone it
        let config = store.config().clone();

        // Get a mutable reference to the memory instance from the store
        let mem = store.mems.get_mut(mem_addr.as_usize()).ok_or_else(|| {
            RuntimeError::Execution(format!(
                "memory.grow: Memory address {} does not exist in store",
                mem_addr
            ))
        })?;

        // Get the current size before growing (sz = length of mem.data / page size)
        let old_size = mem.size();

        // Pop the i32 delta size from the stack
        let delta = match thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Stack("No value on stack for memory.grow instruction".to_string())
        })? {
            Value::I32(n) => n as u32,
            _ => return Err(RuntimeError::TypeError("Expected i32 delta for memory.grow".to_string())),
        };

        // Debug logging
        crate::wasm::runtime::debug_log(&config, &format!("memory.grow: old_size={}, delta={}, old_bytes={}", old_size, delta, mem.size_bytes()));

        // Attempt to grow the memory
        match mem.grow(delta, &config) {
            Ok(_) => {
                // Success: push the old size (sz)
                crate::wasm::runtime::debug_log(&config, &format!("memory.grow: success, new_size={}, new_bytes={}", mem.size(), mem.size_bytes()));
                thread.stack_mut().push_value(Value::I32(old_size as i32));
            }
            Err(e) => {
                // Failure: push -1 (err = 2^32 - 1, which is -1 when interpreted as signed i32)
                crate::wasm::runtime::debug_log(&config, &format!("memory.grow: failed: {}", e));
                thread.stack_mut().push_value(Value::I32(-1));
            }
        }

        Ok(())
    }

    /// Executes a memory.fill instruction.
    /// 
    /// Fills a range of memory with a byte value.
    /// The range is specified by a start offset d and a count n.
    /// 
    /// # Specification
    /// 
    /// 1. Let 𝐹 be the current frame.
    /// 2. Assert: due to validation, 𝐹.module.memaddrs[0] exists.
    /// 3. Let ma be the memory address 𝐹.module.memaddrs[0].
    /// 4. Assert: due to validation, 𝑆.mems[ma] exists.
    /// 5. Let mem be the memory instance 𝑆.mems[ma].
    /// 6. Assert: due to validation, a value of value type i32 is on the top of the stack.
    /// 7. Pop the value i32.const 𝑛 from the stack.
    /// 8. Assert: due to validation, a value of value type i32 is on the top of the stack.
    /// 9. Pop the value val from the stack.
    /// 10. Assert: due to validation, a value of value type i32 is on the top of the stack.
    /// 11. Pop the value i32.const 𝑑 from the stack.
    /// 12. If 𝑑 + 𝑛 is larger than the length of mem.data, then:
    ///     a. Trap.
    /// 13. If 𝑛 = 0, then:
    ///     a. Return.
    /// 14. Push the value i32.const 𝑑 to the stack.
    /// 15. Push the value val to the stack.
    /// 16. Execute the instruction i32.store8 {offset 0, align 0}.
    /// 17. Assert: due to the earlier check against the memory size, 𝑑 + 1 < 2^32.
    /// 18. Push the value i32.const (𝑑 + 1) to the stack.
    /// 19. Push the value val to the stack.
    /// 20. Push the value i32.const (𝑛 − 1) to the stack.
    /// 21. Execute the instruction memory.fill.
    pub fn memory_fill(
        store: &mut Store,
        thread: &mut Thread,
    ) -> RuntimeResult<()> {
        // Get the current frame
        let frame = thread.frame_state();
        
        // Get the memory address from the module
        let mem_addr = frame.module().mem_addrs.get(0).ok_or_else(|| {
            RuntimeError::Execution(format!(
                "memory.fill: Memory index 0 does not exist in current module"
            ))
        })?;

        // Get the config before any mutable borrows and clone it
        let config = store.config().clone();

        // Get a mutable reference to the memory instance from the store
        let mem = store.mems.get_mut(mem_addr.as_usize()).ok_or_else(|| {
            RuntimeError::Execution(format!(
                "memory.fill: Memory address {} does not exist in store",
                mem_addr
            ))
        })?;

        // Pop the count n from the stack
        let n = match thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Stack("No value on stack for memory.fill instruction".to_string())
        })? {
            Value::I32(n) => n as usize,
            _ => return Err(RuntimeError::TypeError("Expected i32 count for memory.fill".to_string())),
        };

        // Pop the value to fill with from the stack
        let val = match thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Stack("No value on stack for memory.fill instruction".to_string())
        })? {
            Value::I32(val) => val as u8,
            _ => return Err(RuntimeError::TypeError("Expected i32 value for memory.fill".to_string())),
        };

        // Pop the start offset d from the stack
        let d = match thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Stack("No offset on stack for memory.fill instruction".to_string())
        })? {
            Value::I32(d) => d as usize,
            _ => return Err(RuntimeError::TypeError("Expected i32 offset for memory.fill".to_string())),
        };

        // Debug logging
        crate::wasm::runtime::debug_log(&config, &format!("memory.fill: offset={}, value={}, count={}, memory_size={}", d, val, n, mem.size_bytes()));

        // Additional bounds checking
        if d >= mem.size_bytes() {
            return Err(RuntimeError::Memory(format!(
                "memory.fill: offset {} >= memory size {}",
                d, mem.size_bytes()
            )));
        }

        let end = d.checked_add(n).ok_or_else(|| {
            RuntimeError::Memory(format!(
                "memory.fill: offset overflow: {} + {}",
                d, n
            ))
        })?;

        if end > mem.size_bytes() {
            return Err(RuntimeError::Memory(format!(
                "memory.fill: range {}..{} out of bounds (memory size: {})",
                d, end, mem.size_bytes()
            )));
        }

        crate::wasm::runtime::debug_log(&config, &format!("memory.fill: filling range {}..{} ({} bytes)", d, end, n));

        // Test memory access before filling - only test a few points to avoid performance issues
        if n > 0 {
            // Test start of range
            crate::wasm::runtime::debug_log(&config, &format!("memory.fill: testing memory access at offset {}", d));
            match mem.read_byte(d) {
                Ok(_) => crate::wasm::runtime::debug_log(&config, "memory.fill: memory access test successful"),
                Err(e) => {
                    crate::wasm::runtime::debug_log(&config, &format!("memory.fill: memory access test failed: {}", e));
                    return Err(RuntimeError::Memory(format!("memory.fill: memory access test failed: {}", e)));
                }
            }

            // Test end of range (if different from start)
            if end > d + 1 {
                crate::wasm::runtime::debug_log(&config, &format!("memory.fill: testing memory access at offset {} (end-1)", end - 1));
                match mem.read_byte(end - 1) {
                    Ok(_) => crate::wasm::runtime::debug_log(&config, "memory.fill: end memory access test successful"),
                    Err(e) => {
                        crate::wasm::runtime::debug_log(&config, &format!("memory.fill: end memory access test failed: {}", e));
                        return Err(RuntimeError::Memory(format!("memory.fill: end memory access test failed: {}", e)));
                    }
                }
            }
        }

        // Fill the memory range efficiently using the memory instance's fill method
        mem.fill(d, n, val, &config).map_err(|e| {
            RuntimeError::Memory(format!("memory.fill: {}", e))
        })?;

        crate::wasm::runtime::debug_log(&config, "memory.fill: completed successfully");

        Ok(())
    }

    /// Executes a memory.copy instruction.
    /// 
    /// Copies a range of bytes from one location in memory to another.
    /// The range is specified by a destination offset d, source offset s, and count n.
    /// 
    /// # Specification
    /// 
    /// 1. Let 𝐹 be the current frame.
    /// 2. Assert: due to validation, 𝐹.module.memaddrs[0] exists.
    /// 3. Let ma be the memory address 𝐹.module.memaddrs[0].
    /// 4. Assert: due to validation, 𝑆.mems[ma] exists.
    /// 5. Let mem be the memory instance 𝑆.mems[ma].
    /// 6. Assert: due to validation, a value of value type i32 is on the top of the stack.
    /// 7. Pop the value i32.const 𝑛 from the stack.
    /// 8. Assert: due to validation, a value of value type i32 is on the top of the stack.
    /// 9. Pop the value i32.const 𝑠 from the stack.
    /// 10. Assert: due to validation, a value of value type i32 is on the top of the stack.
    /// 11. Pop the value i32.const 𝑑 from the stack.
    /// 12. If 𝑠 + 𝑛 is larger than the length of mem.data or 𝑑 + 𝑛 is larger than the length of mem.data, then:
    ///     a. Trap.
    /// 13. If 𝑛 = 0, then:
    ///     a. Return.
    /// 14. If 𝑑 ≤ 𝑠, then:
    ///     a. Push the value i32.const 𝑑 to the stack.
    ///     b. Push the value i32.const 𝑠 to the stack.
    ///     c. Execute the instruction i32.load8_u {offset 0, align 0}.
    ///     d. Execute the instruction i32.store8 {offset 0, align 0}.
    ///     e. Assert: due to the earlier check against the memory size, 𝑑 + 1 < 2^32.
    ///     f. Push the value i32.const (𝑑 + 1) to the stack.
    ///     g. Assert: due to the earlier check against the memory size, 𝑠 + 1 < 2^32.
    ///     h. Push the value i32.const (𝑠 + 1) to the stack.
    /// 15. Else:
    ///     a. Assert: due to the earlier check against the memory size, 𝑑 + 𝑛 − 1 < 2^32.
    ///     b. Push the value i32.const (𝑑 + 𝑛 − 1) to the stack.
    ///     c. Assert: due to the earlier check against the memory size, 𝑠 + 𝑛 − 1 < 2^32.
    ///     d. Push the value i32.const (𝑠 + 𝑛 − 1) to the stack.
    ///     e. Execute the instruction i32.load8_u {offset 0, align 0}.
    ///     f. Execute the instruction i32.store8 {offset 0, align 0}.
    ///     g. Push the value i32.const 𝑑 to the stack.
    ///     h. Push the value i32.const 𝑠 to the stack.
    /// 16. Push the value i32.const (𝑛 − 1) to the stack.
    /// 17. Execute the instruction memory.copy.
    pub fn memory_copy(
        store: &mut Store,
        thread: &mut Thread,
    ) -> RuntimeResult<()> {
        // Get the current frame
        let frame = thread.frame_state();
        
        // Get the memory address from the module
        let mem_addr = frame.module().mem_addrs.get(0).ok_or_else(|| {
            RuntimeError::Execution(format!(
                "memory.copy: Memory index 0 does not exist in current module"
            ))
        })?;

        // Get a mutable reference to the memory instance from the store
        let mem = store.mems.get_mut(mem_addr.as_usize()).ok_or_else(|| {
            RuntimeError::Execution(format!(
                "memory.copy: Memory address {} does not exist in store",
                mem_addr
            ))
        })?;

        // Pop the count n from the stack
        let n = match thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Stack("No value on stack for memory.copy instruction".to_string())
        })? {
            Value::I32(n) => n as usize,
            _ => return Err(RuntimeError::TypeError("Expected i32 count for memory.copy".to_string())),
        };

        // Pop the source offset s from the stack
        let s = match thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Stack("No source offset on stack for memory.copy instruction".to_string())
        })? {
            Value::I32(s) => s as usize,
            _ => return Err(RuntimeError::TypeError("Expected i32 source offset for memory.copy".to_string())),
        };

        // Pop the destination offset d from the stack
        let d = match thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Stack("No destination offset on stack for memory.copy instruction".to_string())
        })? {
            Value::I32(d) => d as usize,
            _ => return Err(RuntimeError::TypeError("Expected i32 destination offset for memory.copy".to_string())),
        };

        // Copy the memory range efficiently using the memory instance's copy method
        mem.copy(d, s, n).map_err(|e| {
            RuntimeError::Memory(format!("memory.copy: {}", e))
        })?;

        Ok(())
    }

    /// Executes a memory.init instruction.
    /// 
    /// Initializes a range of memory with data from a data segment.
    /// The range is specified by a destination offset d, source offset s, and count n.
    /// 
    /// # Specification
    /// 
    /// 1. Let 𝐹 be the current frame.
    /// 2. Assert: due to validation, 𝐹.module.memaddrs[0] exists.
    /// 3. Let ma be the memory address 𝐹.module.memaddrs[0].
    /// 4. Assert: due to validation, 𝑆.mems[ma] exists.
    /// 5. Let mem be the memory instance 𝑆.mems[ma].
    /// 6. Assert: due to validation, 𝐹.module.dataaddrs[𝑥] exists.
    /// 7. Let da be the data address 𝐹.module.dataaddrs[𝑥].
    /// 8. Assert: due to validation, 𝑆.datas[da] exists.
    /// 9. Let data be the data instance 𝑆.datas[da].
    /// 10. Assert: due to validation, a value of value type i32 is on the top of the stack.
    /// 11. Pop the value i32.const 𝑛 from the stack.
    /// 12. Assert: due to validation, a value of value type i32 is on the top of the stack.
    /// 13. Pop the value i32.const 𝑠 from the stack.
    /// 14. Assert: due to validation, a value of value type i32 is on the top of the stack.
    /// 15. Pop the value i32.const 𝑑 from the stack.
    /// 16. If 𝑠 + 𝑛 is larger than the length of data.data or 𝑑 + 𝑛 is larger than the length of mem.data, then:
    ///     a. Trap.
    /// 17. If 𝑛 = 0, then:
    ///     a. Return.
    /// 18. Let 𝑏 be the byte data.data[𝑠].
    /// 19. Push the value i32.const 𝑑 to the stack.
    /// 20. Push the value i32.const 𝑏 to the stack.
    /// 21. Execute the instruction i32.store8 {offset 0, align 0}.
    /// 22. Assert: due to the earlier check against the memory size, 𝑑 + 1 < 2^32.
    /// 23. Push the value i32.const (𝑑 + 1) to the stack.
    /// 24. Assert: due to the earlier check against the memory size, 𝑠 + 1 < 2^32.
    /// 25. Push the value i32.const (𝑠 + 1) to the stack.
    /// 26. Push the value i32.const (𝑛 − 1) to the stack.
    /// 27. Execute the instruction memory.init 𝑥.
    pub fn memory_init(
        store: &mut Store,
        thread: &mut Thread,
        data_index: u32,
    ) -> RuntimeResult<()> {
        // Get the current frame
        let frame = thread.frame_state();
        
        // Get the memory address from the module
        let mem_addr = frame.module().mem_addrs.get(0).ok_or_else(|| {
            RuntimeError::Execution(format!(
                "memory.init: Memory index 0 does not exist in current module"
            ))
        })?;

        // Get a mutable reference to the memory instance from the store
        let mem = store.mems.get_mut(mem_addr.as_usize()).ok_or_else(|| {
            RuntimeError::Execution(format!(
                "memory.init: Memory address {} does not exist in store",
                mem_addr
            ))
        })?;

        // Get the data address from the module
        let data_addr = frame.module().data_addrs.get(data_index as usize).ok_or_else(|| {
            RuntimeError::Execution(format!(
                "memory.init: Data index {} does not exist in current module",
                data_index
            ))
        })?;

        // Get the data instance from the store
        let data = store.datas.get(data_addr.as_usize()).ok_or_else(|| {
            RuntimeError::Execution(format!(
                "memory.init: Data address {} does not exist in store",
                data_addr
            ))
        })?;

        // Pop the count n from the stack
        let n = match thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Stack("No value on stack for memory.init instruction".to_string())
        })? {
            Value::I32(n) => n as usize,
            _ => return Err(RuntimeError::TypeError("Expected i32 count for memory.init".to_string())),
        };

        // Pop the source offset s from the stack
        let s = match thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Stack("No source offset on stack for memory.init instruction".to_string())
        })? {
            Value::I32(s) => s as usize,
            _ => return Err(RuntimeError::TypeError("Expected i32 source offset for memory.init".to_string())),
        };

        // Pop the destination offset d from the stack
        let d = match thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Stack("No destination offset on stack for memory.init instruction".to_string())
        })? {
            Value::I32(d) => d as usize,
            _ => return Err(RuntimeError::TypeError("Expected i32 destination offset for memory.init".to_string())),
        };

        // Check if the ranges are within bounds
        if s + n > data.size() || d + n > mem.size_bytes() {
            return Err(RuntimeError::Execution(format!(
                "memory.init: Range out of bounds - source: {}..{} (data size: {}), destination: {}..{} (memory size: {})",
                s, s + n, data.size(), d, d + n, mem.size_bytes()
            )));
        }

        // If n is 0, we're done
        if n == 0 {
            return Ok(());
        }

        // Initialize the memory range efficiently by copying bytes from data segment
        // Read bytes from data segment
        let mut bytes = [0u8; 1024]; // Use a fixed-size buffer
        let mut total_copied = 0;
        
        while total_copied < n {
            let chunk_size = (n - total_copied).min(bytes.len());
            
            // Read chunk from data segment
            for i in 0..chunk_size {
                let b = data.get(s + total_copied + i).ok_or_else(|| {
                    RuntimeError::Execution(format!(
                        "memory.init: Data index {} out of bounds (data size: {})",
                        s + total_copied + i, data.size()
                    ))
                })?;
                bytes[i] = *b;
            }
            
            // Write chunk to memory
            mem.write_bytes(d + total_copied, &bytes[..chunk_size]).map_err(|e| {
                RuntimeError::Memory(format!("memory.init: {}", e))
            })?;
            
            total_copied += chunk_size;
        }

        Ok(())
    }

    /// Executes a data.drop instruction.
    /// 
    /// Drops a data segment by replacing it with an empty data instance.
    /// 
    /// # Specification
    /// 
    /// 1. Let 𝐹 be the current frame.
    /// 2. Assert: due to validation, 𝐹.module.dataaddrs[𝑥] exists.
    /// 3. Let 𝑎 be the data address 𝐹.module.dataaddrs[𝑥].
    /// 4. Assert: due to validation, 𝑆.datas[𝑎] exists.
    /// 5. Replace 𝑆.datas[𝑎] with the data instance {data 𝜖}.
    pub fn data_drop(
        store: &mut Store,
        thread: &mut Thread,
        data_index: u32,
    ) -> RuntimeResult<()> {
        // Get the current frame
        let frame = thread.frame_state();
        
        // Get the data address from the module
        let data_addr = frame.module().data_addrs.get(data_index as usize).ok_or_else(|| {
            RuntimeError::Execution(format!(
                "data.drop: Data index {} does not exist in current module",
                data_index
            ))
        })?;

        // Get a mutable reference to the data instance from the store
        let data = store.datas.get_mut(data_addr.as_usize()).ok_or_else(|| {
            RuntimeError::Execution(format!(
                "data.drop: Data address {} does not exist in store",
                data_addr
            ))
        })?;

        // Replace the data instance with an empty one
        *data = DataInstance::new();

        Ok(())
    }
}

/// Executes a memory instruction
pub fn execute_memory(
    store: &mut Store,
    thread: &mut Thread,
    instruction: &Instruction,
) -> RuntimeResult<()> {
    match instruction {
        Instruction::Memory(memory_inst) => match memory_inst {
            // Integer loads
            MemoryInstruction::I32Load { memarg } => {
                Memory::load(store, thread, ValType::I32, memarg.offset, memarg.align, None, None)
            }
            MemoryInstruction::I64Load { memarg } => {
                Memory::load(store, thread, ValType::I64, memarg.offset, memarg.align, None, None)
            }
            // Float loads
            MemoryInstruction::F32Load { memarg } => {
                Memory::load(store, thread, ValType::F32, memarg.offset, memarg.align, None, None)
            }
            MemoryInstruction::F64Load { memarg } => {
                Memory::load(store, thread, ValType::F64, memarg.offset, memarg.align, None, None)
            }
            // Integer loads with sign extension
            MemoryInstruction::I32Load8S { memarg } => {
                Memory::load(store, thread, ValType::I32, memarg.offset, memarg.align, Some(8), Some(true))
            }
            MemoryInstruction::I32Load8U { memarg } => {
                Memory::load(store, thread, ValType::I32, memarg.offset, memarg.align, Some(8), Some(false))
            }
            MemoryInstruction::I32Load16S { memarg } => {
                Memory::load(store, thread, ValType::I32, memarg.offset, memarg.align, Some(16), Some(true))
            }
            MemoryInstruction::I32Load16U { memarg } => {
                Memory::load(store, thread, ValType::I32, memarg.offset, memarg.align, Some(16), Some(false))
            }
            MemoryInstruction::I64Load8S { memarg } => {
                Memory::load(store, thread, ValType::I64, memarg.offset, memarg.align, Some(8), Some(true))
            }
            MemoryInstruction::I64Load8U { memarg } => {
                Memory::load(store, thread, ValType::I64, memarg.offset, memarg.align, Some(8), Some(false))
            }
            MemoryInstruction::I64Load16S { memarg } => {
                Memory::load(store, thread, ValType::I64, memarg.offset, memarg.align, Some(16), Some(true))
            }
            MemoryInstruction::I64Load16U { memarg } => {
                Memory::load(store, thread, ValType::I64, memarg.offset, memarg.align, Some(16), Some(false))
            }
            MemoryInstruction::I64Load32S { memarg } => {
                Memory::load(store, thread, ValType::I64, memarg.offset, memarg.align, Some(32), Some(true))
            }
            MemoryInstruction::I64Load32U { memarg } => {
                Memory::load(store, thread, ValType::I64, memarg.offset, memarg.align, Some(32), Some(false))
            }
            // Integer stores
            MemoryInstruction::I32Store { memarg } => {
                Memory::store(store, thread, ValType::I32, memarg.offset, memarg.align, None)
            }
            MemoryInstruction::I64Store { memarg } => {
                Memory::store(store, thread, ValType::I64, memarg.offset, memarg.align, None)
            }
            // Float stores
            MemoryInstruction::F32Store { memarg } => {
                Memory::store(store, thread, ValType::F32, memarg.offset, memarg.align, None)
            }
            MemoryInstruction::F64Store { memarg } => {
                Memory::store(store, thread, ValType::F64, memarg.offset, memarg.align, None)
            }
            // Integer stores with reduced width
            MemoryInstruction::I32Store8 { memarg } => {
                Memory::store(store, thread, ValType::I32, memarg.offset, memarg.align, Some(8))
            }
            MemoryInstruction::I32Store16 { memarg } => {
                Memory::store(store, thread, ValType::I32, memarg.offset, memarg.align, Some(16))
            }
            MemoryInstruction::I64Store8 { memarg } => {
                Memory::store(store, thread, ValType::I64, memarg.offset, memarg.align, Some(8))
            }
            MemoryInstruction::I64Store16 { memarg } => {
                Memory::store(store, thread, ValType::I64, memarg.offset, memarg.align, Some(16))
            }
            MemoryInstruction::I64Store32 { memarg } => {
                Memory::store(store, thread, ValType::I64, memarg.offset, memarg.align, Some(32))
            }
            // Memory management
            MemoryInstruction::MemorySize => {
                Memory::memory_size(store, thread)
            }
            MemoryInstruction::MemoryGrow => {
                Memory::memory_grow(store, thread)
            }
            MemoryInstruction::MemoryFill => {
                Memory::memory_fill(store, thread)
            }
            MemoryInstruction::MemoryCopy => {
                Memory::memory_copy(store, thread)
            }
            MemoryInstruction::MemoryInit { data_index } => {
                Memory::memory_init(store, thread, *data_index)
            }
            MemoryInstruction::DataDrop { data_index } => {
                Memory::data_drop(store, thread, *data_index)
            }
        },
        _ => Err(RuntimeError::Execution(format!(
            "Expected memory instruction, got: {:?}",
            instruction
        ))),
    }
} 
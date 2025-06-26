//! Table Instructions implementation for WebAssembly runtime.
//!
//! Implements instructions like table.get, table.set, table.size, table.grow, table.fill, table.copy, table.init.

use alloc::format;
use alloc::string::String;
use alloc::string::ToString;

use crate::wasm::runtime::{
    value::{Value, ValueType},
    RuntimeResult,
    RuntimeError,
    Store,
    Thread,
    TableElement,
};
use crate::wasm::ast::{Instruction, TableInstruction, ValType};

impl From<TableElement> for Value {
    fn from(elem: TableElement) -> Self {
        match elem {
            TableElement::FuncRef(None) => Value::NullRef(ValueType::FuncRef),
            TableElement::FuncRef(Some(idx)) => Value::FuncRef(idx),
            TableElement::ExternRef(None) => Value::NullRef(ValueType::ExternRef),
            TableElement::ExternRef(Some(idx)) => Value::ExternRef(idx),
        }
    }
}

impl TryFrom<Value> for TableElement {
    type Error = String;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::NullRef(ValueType::FuncRef) => Ok(TableElement::FuncRef(None)),
            Value::FuncRef(idx) => Ok(TableElement::FuncRef(Some(idx))),
            Value::NullRef(ValueType::ExternRef) => Ok(TableElement::ExternRef(None)),
            Value::ExternRef(idx) => Ok(TableElement::ExternRef(Some(idx))),
            _ => Err(format!("Cannot convert value of type {} to table element", value.value_type())),
        }
    }
}

/// Table instruction implementation.
pub struct Table;

impl Table {
    /// Executes the table.get instruction.
    /// 
    /// Pops an i32 index from the stack, gets the value at that index from the table,
    /// and pushes it to the stack.
    /// 
    /// # Specification
    /// 
    /// 1. Let 𝐹 be the current frame.
    /// 2. Assert: due to validation, 𝐹.module.tableaddrs[𝑥] exists.
    /// 3. Let 𝑎 be the table address 𝐹.module.tableaddrs[𝑥].
    /// 4. Assert: due to validation, 𝑆.tables[𝑎] exists.
    /// 5. Let tab be the table instance 𝑆.tables[𝑎].
    /// 6. Assert: due to validation, a value of value type i32 is on the top of the stack.
    /// 7. Pop the value i32.const 𝑖 from the stack.
    /// 8. If 𝑖 is not smaller than the length of tab.elem, then:
    ///    a. Trap.
    /// 9. Let val be the value tab.elem[𝑖].
    /// 10. Push the value val to the stack.
    pub fn table_get(store: &Store, thread: &mut Thread, table_idx: u32) -> RuntimeResult<()> {
        // Get the current frame
        let frame = thread.frame_state();
        
        // Get the table address from the module
        let table_addr = frame.module().table_addrs.get(table_idx as usize).ok_or_else(|| {
            RuntimeError::Execution(format!(
                "table.get: Table index {} does not exist in current module",
                table_idx
            ))
        })?;

        // Get the table instance from the store
        let table = store.tables.get(table_addr.as_usize()).ok_or_else(|| {
            RuntimeError::Execution(format!(
                "table.get: Table address {} does not exist in store",
                table_addr
            ))
        })?;

        // Pop the i32 index from the stack
        let idx = match thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Stack("No value on stack for table.get instruction".to_string())
        })? {
            Value::I32(i) => i as usize,
            _ => return Err(RuntimeError::TypeError("Expected i32 index for table.get".to_string())),
        };

        // Check if the index is within bounds
        if idx >= table.size() as usize {
            return Err(RuntimeError::Execution(format!(
                "table.get: Table index {} out of bounds (table size: {})",
                idx,
                table.size()
            )));
        }

        // Get the value at the index and push it to the stack
        let elem = table.get(idx as u32).ok_or_else(|| {
            RuntimeError::Execution(format!(
                "table.get: Failed to get element at index {}",
                idx
            ))
        })?.clone();
        thread.stack_mut().push_value(elem.into());
        Ok(())
    }

    /// Executes the table.set instruction.
    /// 
    /// Pops an i32 index and a reference value from the stack, and sets the value
    /// at that index in the table.
    /// 
    /// # Specification
    /// 
    /// 1. Let 𝐹 be the current frame.
    /// 2. Assert: due to validation, 𝐹.module.tableaddrs[𝑥] exists.
    /// 3. Let 𝑎 be the table address 𝐹.module.tableaddrs[𝑥].
    /// 4. Assert: due to validation, 𝑆.tables[𝑎] exists.
    /// 5. Let tab be the table instance 𝑆.tables[𝑎].
    /// 6. Assert: due to validation, a reference value is on the top of the stack.
    /// 7. Pop the value val from the stack.
    /// 8. Assert: due to validation, a value of value type i32 is on the top of the stack.
    /// 9. Pop the value i32.const 𝑖 from the stack.
    /// 10. If 𝑖 is not smaller than the length of tab.elem, then:
    ///     a. Trap.
    /// 11. Replace the element tab.elem[𝑖] with val.
    pub fn table_set(store: &mut Store, thread: &mut Thread, table_idx: u32) -> RuntimeResult<()> {
        // Get the current frame
        let frame = thread.frame_state();
        
        // Get the table address from the module
        let table_addr = frame.module().table_addrs.get(table_idx as usize).ok_or_else(|| {
            RuntimeError::Execution(format!(
                "table.set: Table index {} does not exist in current module",
                table_idx
            ))
        })?;

        // Get a mutable reference to the table instance from the store
        let table = store.tables.get_mut(table_addr.as_usize()).ok_or_else(|| {
            RuntimeError::Execution(format!(
                "table.set: Table address {} does not exist in store",
                table_addr
            ))
        })?;

        // Pop the reference value from the stack
        let val = thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Stack("No value on stack for table.set instruction".to_string())
        })?;

        // Convert the value to a table element
        let elem = TableElement::try_from(val).map_err(|e| {
            RuntimeError::TypeError(format!("table.set: {}", e))
        })?;

        // Pop the i32 index from the stack
        let idx = match thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Stack("No value on stack for table.set instruction".to_string())
        })? {
            Value::I32(i) => i as usize,
            _ => return Err(RuntimeError::TypeError("Expected i32 index for table.set".to_string())),
        };

        // Check if the index is within bounds
        if idx >= table.size() as usize {
            return Err(RuntimeError::Execution(format!(
                "table.set: Table index {} out of bounds (table size: {})",
                idx,
                table.size()
            )));
        }

        // Set the element at the index
        table.set(idx as u32, elem).map_err(|e| {
            RuntimeError::Execution(format!("table.set: {}", e))
        })?;

        Ok(())
    }

    /// Executes the table.size instruction.
    /// 
    /// Gets the current size of the table at index x and pushes it to the stack as an i32 value.
    /// 
    /// # Specification
    /// 
    /// 1. Let 𝐹 be the current frame.
    /// 2. Assert: due to validation, 𝐹.module.tableaddrs[𝑥] exists.
    /// 3. Let 𝑎 be the table address 𝐹.module.tableaddrs[𝑥].
    /// 4. Assert: due to validation, 𝑆.tables[𝑎] exists.
    /// 5. Let tab be the table instance 𝑆.tables[𝑎].
    /// 6. Let sz be the length of tab.elem.
    /// 7. Push the value i32.const sz to the stack.
    pub fn table_size(store: &Store, thread: &mut Thread, table_idx: u32) -> RuntimeResult<()> {
        // Get the current frame
        let frame = thread.frame_state();
        
        // Get the table address from the module
        let table_addr = frame.module().table_addrs.get(table_idx as usize).ok_or_else(|| {
            RuntimeError::Execution(format!(
                "table.size: Table index {} does not exist in current module",
                table_idx
            ))
        })?;

        // Get the table instance from the store
        let table = store.tables.get(table_addr.as_usize()).ok_or_else(|| {
            RuntimeError::Execution(format!(
                "table.size: Table address {} does not exist in store",
                table_addr
            ))
        })?;

        // Get the size and push it to the stack as i32
        let size = table.size() as i32;
        thread.stack_mut().push_value(Value::I32(size));
        Ok(())
    }

    /// Executes the table.grow instruction.
    /// 
    /// Attempts to grow the table by n entries, initializing new entries with val.
    /// Returns the old size on success, or -1 on failure.
    /// 
    /// # Specification
    /// 
    /// 1. Let 𝐹 be the current frame.
    /// 2. Assert: due to validation, 𝐹.module.tableaddrs[𝑥] exists.
    /// 3. Let 𝑎 be the table address 𝐹.module.tableaddrs[𝑥].
    /// 4. Assert: due to validation, 𝑆.tables[𝑎] exists.
    /// 5. Let tab be the table instance 𝑆.tables[𝑎].
    /// 6. Let sz be the length of 𝑆.tables[𝑎].
    /// 7. Assert: due to validation, a value of value type i32 is on the top of the stack.
    /// 8. Pop the value i32.const 𝑛 from the stack.
    /// 9. Assert: due to validation, a reference value is on the top of the stack.
    /// 10. Pop the value val from the stack.
    /// 11. Let err be the i32 value 2^32 − 1, for which signed32(err) is −1.
    /// 12. Either:
    ///     a. If growing tab by 𝑛 entries with initialization value val succeeds, then:
    ///        i. Push the value i32.const sz to the stack.
    ///     b. Else:
    ///        i. Push the value i32.const err to the stack.
    pub fn table_grow(store: &mut Store, thread: &mut Thread, table_idx: u32) -> RuntimeResult<()> {
        // Get the current frame
        let frame = thread.frame_state();
        
        // Get the table address from the module
        let table_addr = frame.module().table_addrs.get(table_idx as usize).ok_or_else(|| {
            RuntimeError::Execution(format!(
                "table.grow: Table index {} does not exist in current module",
                table_idx
            ))
        })?;

        // Get a mutable reference to the table instance from the store
        let table = store.tables.get_mut(table_addr.as_usize()).ok_or_else(|| {
            RuntimeError::Execution(format!(
                "table.grow: Table address {} does not exist in store",
                table_addr
            ))
        })?;

        // Get the current size before growing
        let old_size = table.size();

        // Pop the i32 delta size from the stack
        let delta = match thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Stack("No value on stack for table.grow instruction".to_string())
        })? {
            Value::I32(n) => n as u32,
            _ => return Err(RuntimeError::TypeError("Expected i32 delta for table.grow".to_string())),
        };

        // Pop the reference value from the stack
        let val = thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Stack("No value on stack for table.grow instruction".to_string())
        })?;

        // Convert the value to a table element
        let elem = TableElement::try_from(val).map_err(|e| {
            RuntimeError::TypeError(format!("table.grow: {}", e))
        })?;

        // Attempt to grow the table
        match table.grow(delta, elem) {
            Ok(_) => {
                // Success: push the old size
                thread.stack_mut().push_value(Value::I32(old_size as i32));
            }
            Err(_) => {
                // Failure: push -1
                thread.stack_mut().push_value(Value::I32(-1));
            }
        }

        Ok(())
    }

    /// Executes the table.fill instruction.
    /// 
    /// Fills a range of table entries with a given value.
    /// The range is specified by a start index i and a count n.
    /// 
    /// # Specification
    /// 
    /// 1. Let 𝐹 be the current frame.
    /// 2. Assert: due to validation, 𝐹.module.tableaddrs[𝑥] exists.
    /// 3. Let ta be the table address 𝐹.module.tableaddrs[𝑥].
    /// 4. Assert: due to validation, 𝑆.tables[ta] exists.
    /// 5. Let tab be the table instance 𝑆.tables[ta].
    /// 6. Assert: due to validation, a value of value type i32 is on the top of the stack.
    /// 7. Pop the value i32.const 𝑛 from the stack.
    /// 8. Assert: due to validation, a reference value is on the top of the stack.
    /// 9. Pop the value val from the stack.
    /// 10. Assert: due to validation, a value of value type i32 is on the top of the stack.
    /// 11. Pop the value i32.const 𝑖 from the stack.
    /// 12. If 𝑖 + 𝑛 is larger than the length of tab.elem, then:
    ///     a. Trap.
    /// 13. If 𝑛 is 0, then:
    ///     a. Return.
    /// 14. Push the value i32.const 𝑖 to the stack.
    /// 15. Push the value val to the stack.
    /// 16. Execute the instruction table.set 𝑥.
    /// 17. Push the value i32.const (𝑖 + 1) to the stack.
    /// 18. Push the value val to the stack.
    /// 19. Push the value i32.const (𝑛 − 1) to the stack.
    /// 20. Execute the instruction table.fill 𝑥.
    pub fn table_fill(store: &mut Store, thread: &mut Thread, table_idx: u32) -> RuntimeResult<()> {
        // Get the current frame
        let frame = thread.frame_state();
        
        // Get the table address from the module
        let table_addr = frame.module().table_addrs.get(table_idx as usize).ok_or_else(|| {
            RuntimeError::Execution(format!(
                "table.fill: Table index {} does not exist in current module",
                table_idx
            ))
        })?;

        // Get a reference to the table instance from the store
        let table = store.tables.get(table_addr.as_usize()).ok_or_else(|| {
            RuntimeError::Execution(format!(
                "table.fill: Table address {} does not exist in store",
                table_addr
            ))
        })?;

        // Get the table size for bounds checking
        let table_size = table.size() as usize;

        // Pop the count n from the stack
        let n = match thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Stack("No value on stack for table.fill instruction".to_string())
        })? {
            Value::I32(n) => n as usize,
            _ => return Err(RuntimeError::TypeError("Expected i32 count for table.fill".to_string())),
        };

        // Pop the value to fill with from the stack
        let val = thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Stack("No value on stack for table.fill instruction".to_string())
        })?;

        // Convert the value to a table element
        let elem = TableElement::try_from(val.clone()).map_err(|e| {
            RuntimeError::TypeError(format!("table.fill: {}", e))
        })?;

        // Pop the start index i from the stack
        let i = match thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Stack("No value on stack for table.fill instruction".to_string())
        })? {
            Value::I32(i) => i as usize,
            _ => return Err(RuntimeError::TypeError("Expected i32 index for table.fill".to_string())),
        };

        // Check if the range is within bounds
        if i + n > table_size {
            return Err(RuntimeError::Execution(format!(
                "table.fill: Range {}..{} out of bounds (table size: {})",
                i, i + n, table_size
            )));
        }

        // If n is 0, we're done
        if n == 0 {
            return Ok(());
        }

        // Set the current element
        thread.stack_mut().push_value(Value::I32(i as i32));
        thread.stack_mut().push_value(val.clone());
        Self::table_set(store, thread, table_idx)?;

        // Recursively fill the rest of the range
        thread.stack_mut().push_value(Value::I32((i + 1) as i32));
        thread.stack_mut().push_value(val);
        thread.stack_mut().push_value(Value::I32((n - 1) as i32));
        Self::table_fill(store, thread, table_idx)
    }

    /// Executes the table.copy instruction.
    /// 
    /// Copies elements from one table to another.
    /// The copy operation is specified by:
    /// - destination table index x
    /// - source table index y
    /// - destination start index d
    /// - source start index s
    /// - number of elements to copy n
    /// 
    /// # Specification
    /// 
    /// 1. Let 𝐹 be the current frame.
    /// 2. Assert: due to validation, 𝐹.module.tableaddrs[𝑥] exists.
    /// 3. Let ta𝑥 be the table address 𝐹.module.tableaddrs[𝑥].
    /// 4. Assert: due to validation, 𝑆.tables[ta𝑥] exists.
    /// 5. Let tab𝑥 be the table instance 𝑆.tables[ta𝑥].
    /// 6. Assert: due to validation, 𝐹.module.tableaddrs[𝑦] exists.
    /// 7. Let ta𝑦 be the table address 𝐹.module.tableaddrs[𝑦].
    /// 8. Assert: due to validation, 𝑆.tables[ta𝑦] exists.
    /// 9. Let tab𝑦 be the table instance 𝑆.tables[ta𝑦].
    /// 10. Assert: due to validation, a value of value type i32 is on the top of the stack.
    /// 11. Pop the value i32.const 𝑛 from the stack.
    /// 12. Assert: due to validation, a value of value type i32 is on the top of the stack.
    /// 13. Pop the value i32.const 𝑠 from the stack.
    /// 14. Assert: due to validation, a value of value type i32 is on the top of the stack.
    /// 15. Pop the value i32.const 𝑑 from the stack.
    /// 16. If 𝑠 + 𝑛 is larger than the length of tab𝑦.elem or 𝑑 + 𝑛 is larger than the length of tab𝑥.elem, then:
    ///     a. Trap.
    /// 17. If 𝑛 = 0, then:
    ///     a. Return.
    /// 18. If 𝑑 ≤ 𝑠, then:
    ///     a. Push the value i32.const 𝑑 to the stack.
    ///     b. Push the value i32.const 𝑠 to the stack.
    ///     c. Execute the instruction table.get 𝑦.
    ///     d. Execute the instruction table.set 𝑥.
    ///     e. Push the value i32.const (𝑑 + 1) to the stack.
    ///     f. Push the value i32.const (𝑠 + 1) to the stack.
    /// 19. Else:
    ///     a. Push the value i32.const (𝑑 + 𝑛 − 1) to the stack.
    ///     b. Push the value i32.const (𝑠 + 𝑛 − 1) to the stack.
    ///     c. Execute the instruction table.get 𝑦.
    ///     d. Execute the instruction table.set 𝑥.
    ///     e. Push the value i32.const 𝑑 to the stack.
    ///     f. Push the value i32.const 𝑠 to the stack.
    /// 20. Push the value i32.const (𝑛 − 1) to the stack.
    /// 21. Execute the instruction table.copy 𝑥 𝑦.
    pub fn table_copy(store: &mut Store, thread: &mut Thread, dst_idx: u32, src_idx: u32) -> RuntimeResult<()> {
        // Get the current frame
        let frame = thread.frame_state();
        
        // Get the destination table address from the module
        let dst_addr = frame.module().table_addrs.get(dst_idx as usize).ok_or_else(|| {
            RuntimeError::Execution(format!(
                "table.copy: Destination table index {} does not exist in current module",
                dst_idx
            ))
        })?;

        // Get the source table address from the module
        let src_addr = frame.module().table_addrs.get(src_idx as usize).ok_or_else(|| {
            RuntimeError::Execution(format!(
                "table.copy: Source table index {} does not exist in current module",
                src_idx
            ))
        })?;

        // Get references to both table instances from the store
        let dst_table = store.tables.get(dst_addr.as_usize()).ok_or_else(|| {
            RuntimeError::Execution(format!(
                "table.copy: Destination table address {} does not exist in store",
                dst_addr
            ))
        })?;

        let src_table = store.tables.get(src_addr.as_usize()).ok_or_else(|| {
            RuntimeError::Execution(format!(
                "table.copy: Source table address {} does not exist in store",
                src_addr
            ))
        })?;

        // Get the table sizes for bounds checking
        let dst_size = dst_table.size() as usize;
        let src_size = src_table.size() as usize;

        // Pop the count n from the stack
        let n = match thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Stack("No value on stack for table.copy instruction".to_string())
        })? {
            Value::I32(n) => n as usize,
            _ => return Err(RuntimeError::TypeError("Expected i32 count for table.copy".to_string())),
        };

        // Pop the source start index s from the stack
        let s = match thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Stack("No value on stack for table.copy instruction".to_string())
        })? {
            Value::I32(s) => s as usize,
            _ => return Err(RuntimeError::TypeError("Expected i32 source index for table.copy".to_string())),
        };

        // Pop the destination start index d from the stack
        let d = match thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Stack("No value on stack for table.copy instruction".to_string())
        })? {
            Value::I32(d) => d as usize,
            _ => return Err(RuntimeError::TypeError("Expected i32 destination index for table.copy".to_string())),
        };

        // Check if the ranges are within bounds
        if s + n > src_size || d + n > dst_size {
            return Err(RuntimeError::Execution(format!(
                "table.copy: Range {}..{} or {}..{} out of bounds (table sizes: {}, {})",
                s, s + n, d, d + n, src_size, dst_size
            )));
        }

        // If n is 0, we're done
        if n == 0 {
            return Ok(());
        }

        if d <= s {
            // Forward copy (d ≤ s)
            // Get and set the current element
            thread.stack_mut().push_value(Value::I32(s as i32));
            Self::table_get(store, thread, src_idx)?;
            thread.stack_mut().push_value(Value::I32(d as i32));
            Self::table_set(store, thread, dst_idx)?;

            // Recursively copy the rest
            thread.stack_mut().push_value(Value::I32((d + 1) as i32));
            thread.stack_mut().push_value(Value::I32((s + 1) as i32));
            thread.stack_mut().push_value(Value::I32((n - 1) as i32));
            Self::table_copy(store, thread, dst_idx, src_idx)
        } else {
            // Backward copy (d > s)
            // Get and set the last element
            thread.stack_mut().push_value(Value::I32((s + n - 1) as i32));
            Self::table_get(store, thread, src_idx)?;
            thread.stack_mut().push_value(Value::I32((d + n - 1) as i32));
            Self::table_set(store, thread, dst_idx)?;

            // Recursively copy the rest
            thread.stack_mut().push_value(Value::I32(d as i32));
            thread.stack_mut().push_value(Value::I32(s as i32));
            thread.stack_mut().push_value(Value::I32((n - 1) as i32));
            Self::table_copy(store, thread, dst_idx, src_idx)
        }
    }

    /// Executes the table.init instruction.
    /// 
    /// Initializes a range of table entries from an element segment.
    /// The operation is specified by:
    /// - destination table index x
    /// - source element segment index y
    /// - destination start index d
    /// - source start index s
    /// - number of elements to copy n
    /// 
    /// # Specification
    /// 
    /// 1. Let 𝐹 be the current frame.
    /// 2. Assert: due to validation, 𝐹.module.tableaddrs[𝑥] exists.
    /// 3. Let ta be the table address 𝐹.module.tableaddrs[𝑥].
    /// 4. Assert: due to validation, 𝑆.tables[ta] exists.
    /// 5. Let tab be the table instance 𝑆.tables[ta].
    /// 6. Assert: due to validation, 𝐹.module.elemaddrs[𝑦] exists.
    /// 7. Let ea be the element address 𝐹.module.elemaddrs[𝑦].
    /// 8. Assert: due to validation, 𝑆.elems[ea] exists.
    /// 9. Let elem be the element instance 𝑆.elems[ea].
    /// 10. Assert: due to validation, a value of value type i32 is on the top of the stack.
    /// 11. Pop the value i32.const 𝑛 from the stack.
    /// 12. Assert: due to validation, a value of value type i32 is on the top of the stack.
    /// 13. Pop the value i32.const 𝑠 from the stack.
    /// 14. Assert: due to validation, a value of value type i32 is on the top of the stack.
    /// 15. Pop the value i32.const 𝑑 from the stack.
    /// 16. If 𝑠 + 𝑛 is larger than the length of elem.elem or 𝑑 + 𝑛 is larger than the length of tab.elem, then:
    ///     a. Trap.
    /// 17. If 𝑛 = 0, then:
    ///     a. Return.
    /// 18. Let val be the reference value elem.elem[𝑠].
    /// 19. Push the value i32.const 𝑑 to the stack.
    /// 20. Push the value val to the stack.
    /// 21. Execute the instruction table.set 𝑥.
    /// 22. Assert: due to the earlier check against the table size, 𝑑 + 1 < 232.
    /// 23. Push the value i32.const (𝑑 + 1) to the stack.
    /// 24. Assert: due to the earlier check against the segment size, 𝑠 + 1 < 232.
    /// 25. Push the value i32.const (𝑠 + 1) to the stack.
    /// 26. Push the value i32.const (𝑛 − 1) to the stack.
    /// 27. Execute the instruction table.init 𝑥 𝑦.
    pub fn table_init(store: &mut Store, thread: &mut Thread, table_idx: u32, elem_idx: u32) -> RuntimeResult<()> {
        // Get the current frame
        let frame = thread.frame_state();
        
        // Get the table address from the module
        let table_addr = frame.module().table_addrs.get(table_idx as usize).ok_or_else(|| {
            RuntimeError::Execution(format!(
                "table.init: Table index {} does not exist in current module",
                table_idx
            ))
        })?;

        // Get the element segment address from the module
        let elem_addr = frame.module().elem_addrs.get(elem_idx as usize).ok_or_else(|| {
            RuntimeError::Execution(format!(
                "table.init: Element segment index {} does not exist in current module",
                elem_idx
            ))
        })?;

        // Get references to both the table and element segment instances from the store
        let table = store.tables.get(table_addr.as_usize()).ok_or_else(|| {
            RuntimeError::Execution(format!(
                "table.init: Table address {} does not exist in store",
                table_addr
            ))
        })?;

        let elem = store.elems.get(elem_addr.as_usize()).ok_or_else(|| {
            RuntimeError::Execution(format!(
                "table.init: Element segment address {} does not exist in store",
                elem_addr
            ))
        })?;

        // Get the sizes for bounds checking
        let table_size = table.size() as usize;
        let elem_size = elem.size();

        // Pop the count n from the stack
        let n = match thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Stack("No value on stack for table.init instruction".to_string())
        })? {
            Value::I32(n) => n as usize,
            _ => return Err(RuntimeError::TypeError("Expected i32 count for table.init".to_string())),
        };

        // Pop the source start index s from the stack
        let s = match thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Stack("No value on stack for table.init instruction".to_string())
        })? {
            Value::I32(s) => s as usize,
            _ => return Err(RuntimeError::TypeError("Expected i32 source index for table.init".to_string())),
        };

        // Pop the destination start index d from the stack
        let d = match thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Stack("No value on stack for table.init instruction".to_string())
        })? {
            Value::I32(d) => d as usize,
            _ => return Err(RuntimeError::TypeError("Expected i32 destination index for table.init".to_string())),
        };

        // Check if the ranges are within bounds
        if s + n > elem_size || d + n > table_size {
            return Err(RuntimeError::Execution(format!(
                "table.init: Range {}..{} or {}..{} out of bounds (table size: {}, element size: {})",
                s, s + n, d, d + n, table_size, elem_size
            )));
        }

        // If n is 0, we're done
        if n == 0 {
            return Ok(());
        }

        // Get the value from the element segment
        let val = elem.get(s).ok_or_else(|| {
            RuntimeError::Execution(format!(
                "table.init: Failed to get element at index {}",
                s
            ))
        })?.clone();

        // Set the current element
        thread.stack_mut().push_value(Value::I32(d as i32));
        thread.stack_mut().push_value(val.into());
        Self::table_set(store, thread, table_idx)?;

        // Recursively initialize the rest of the range
        thread.stack_mut().push_value(Value::I32((d + 1) as i32));
        thread.stack_mut().push_value(Value::I32((s + 1) as i32));
        thread.stack_mut().push_value(Value::I32((n - 1) as i32));
        Self::table_init(store, thread, table_idx, elem_idx)
    }

    /// Executes the table.elem.drop instruction.
    /// 
    /// Clears the contents of the specified element segment.
    /// 
    /// # Specification
    /// 
    /// 1. Let 𝐹 be the current frame.
    /// 2. Assert: due to validation, 𝐹.module.elemaddrs[𝑥] exists.
    /// 3. Let 𝑎 be the element address 𝐹.module.elemaddrs[𝑥].
    /// 4. Assert: due to validation, 𝑆.elems[𝑎] exists.
    /// 5. Replace 𝑆.elems[𝑎].elem with 𝜖.
    pub fn table_elem_drop(store: &mut Store, thread: &mut Thread, elem_idx: u32) -> RuntimeResult<()> {
        // Get the current frame
        let frame = thread.frame_state();
        
        // Get the element segment address from the module
        let elem_addr = frame.module().elem_addrs.get(elem_idx as usize).ok_or_else(|| {
            RuntimeError::Execution(format!(
                "table.elem.drop: Element segment index {} does not exist in current module",
                elem_idx
            ))
        })?;

        // Get a mutable reference to the element segment instance from the store
        let elem = store.elems.get_mut(elem_addr.as_usize()).ok_or_else(|| {
            RuntimeError::Execution(format!(
                "table.elem.drop: Element segment address {} does not exist in store",
                elem_addr
            ))
        })?;

        // Clear the element segment
        elem.clear();
        Ok(())
    }
}

/// Executes a table instruction
pub fn execute_table(
    store: &mut Store,
    thread: &mut Thread,
    instruction: &Instruction,
) -> RuntimeResult<()> {
    match instruction {
        Instruction::Table(table_inst) => match table_inst {
            TableInstruction::Get(idx) => {
                Table::table_get(store, thread, *idx)
            }
            TableInstruction::Set(idx) => {
                Table::table_set(store, thread, *idx)
            }
            TableInstruction::Size(idx) => {
                Table::table_size(store, thread, *idx)
            }
            TableInstruction::Grow(idx) => {
                Table::table_grow(store, thread, *idx)
            }
            TableInstruction::Fill(idx) => {
                Table::table_fill(store, thread, *idx)
            }
            TableInstruction::Copy { dst_table, src_table } => {
                Table::table_copy(store, thread, *dst_table, *src_table)
            }
            TableInstruction::Init { table_index, elem_index } => {
                Table::table_init(store, thread, *table_index, *elem_index)
            }
            TableInstruction::ElemDrop(idx) => {
                Table::table_elem_drop(store, thread, *idx)
            }
        },
        _ => Err(RuntimeError::Execution(format!(
            "Expected table instruction, got: {:?}",
            instruction
        ))),
    }
} 
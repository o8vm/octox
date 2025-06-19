//! Control Instructions implementation for WebAssembly runtime.
//!
//! Implements instructions like nop, unreachable, block, loop, if, br, br_if, br_table, return, call, call_indirect.

use alloc::format;
use alloc::vec::Vec;
use alloc::string::ToString;

use crate::wasm::runtime::{
    value::Value,
    RuntimeResult,
    RuntimeError,
    Store,
    Thread,
    stack::{Stack, Label},
};
use crate::wasm::ast::{Instruction, ControlInstruction, BlockType};
use crate::wasm::runtime::instruction::InstructionExecutor;
use crate::debug_log;

/// Control instruction implementation.
pub struct Control;

impl Control {
    /// Executes the nop instruction.
    /// 
    /// Do nothing.
    /// 
    /// # Specification
    /// 
    /// nop → 𝜖
    /// 
    /// The nop instruction does nothing. It is used as a placeholder or for alignment.
    /// 
    /// # Examples
    /// 
    /// ```
    /// // Do nothing
    /// nop
    /// ```
    pub fn nop(_thread: &mut Thread) -> RuntimeResult<()> {
        // Do nothing - this is the entire implementation
        Ok(())
    }

    /// Executes the unreachable instruction.
    /// 
    /// Trap.
    /// 
    /// # Specification
    /// 
    /// unreachable → trap
    /// 
    /// The unreachable instruction causes an unconditional trap.
    /// This instruction is used to indicate that the current execution
    /// should not be reachable under normal circumstances.
    /// 
    /// # Examples
    /// 
    /// ```
    /// // Cause an unconditional trap
    /// unreachable
    /// ```
    pub fn unreachable(_thread: &mut Thread) -> RuntimeResult<()> {
        // Cause an unconditional trap
        Err(RuntimeError::Trap("unreachable instruction executed".to_string()))
    }

    /// Executes the block instruction.
    /// 
    /// Enter a block of instructions with a block type.
    /// 
    /// # Specification
    /// 
    /// 1. Let 𝐹 be the current frame.
    /// 2. Assert: due to validation, expand𝐹 (blocktype) is defined.
    /// 3. Let [𝑡𝑚1 ] → [𝑡𝑛2 ] be the function type expand𝐹 (blocktype).
    /// 4. Let 𝐿 be the label whose arity is 𝑛 and whose continuation is the end of the block.
    /// 5. Assert: due to validation, there are at least 𝑚 values on the top of the stack.
    /// 6. Pop the values val𝑚 from the stack.
    /// 7. Enter the block val𝑚 instr * with label 𝐿.
    /// 
    /// 𝐹; val𝑚 block bt instr * end ˓→ 𝐹; label𝑛{𝜖} val𝑚 instr * end
    /// (if expand𝐹 (bt) = [𝑡𝑚1 ] → [𝑡𝑛2 ])
    /// 
    /// # Examples
    /// 
    /// ```
    /// // Block with no parameters and no results
    /// block
    ///   i32.const 1
    ///   i32.const 2
    ///   i32.add
    /// end
    /// 
    /// // Block with parameters and results
    /// i32.const 1
    /// i32.const 2
    /// block (i32 i32) -> (i32)
    ///   i32.add
    /// end
    /// ```
    pub fn block(
        store: &mut Store,
        thread: &mut Thread,
        block_type: &BlockType,
        instructions: &[Instruction],
    ) -> RuntimeResult<()> {
        // Get the current frame
        let frame = thread.frame_state();
        
        // Expand the block type to get the function type
        let func_type = frame.expand_block_type(block_type);
        
        // Get the number of parameters (m) and results (n)
        let param_count = func_type.params.len();
        let result_count = func_type.results.len();
        
        // Validate that there are at least m values on the stack
        let stack = thread.stack();
        if stack.value_count() < param_count {
            return Err(RuntimeError::Execution(format!(
                "block: Expected {} values on stack, but only {} available",
                param_count,
                stack.value_count()
            )));
        }
        
        // Pop the parameter values from the stack
        let mut param_values = Vec::new();
        for _ in 0..param_count {
            let value = thread.stack_mut().pop_value().ok_or_else(|| {
                RuntimeError::Stack("Failed to pop parameter value for block".to_string())
            })?;
            param_values.push(value);
        }
        
        // Create a label with arity n and empty continuation (end of block)
        // The continuation represents the end of the block, which means no further instructions
        let end_instruction = Instruction::Control(ControlInstruction::End);
        let mut continuation = Vec::new();
        continuation.push(end_instruction);
        let label = Label::new(result_count, continuation);
        
        // Push the label onto the stack
        thread.stack_mut().push_label(label);
        
        // Push the parameter values back onto the stack
        for value in param_values.into_iter().rev() {
            thread.stack_mut().push_value(value);
        }
        
        // Execute the block instructions
        let executor = crate::wasm::runtime::instruction::DefaultInstructionExecutor;
        for instruction in instructions {
            executor.execute(store, thread, instruction)?;
        }
        
        Ok(())
    }

    /// Executes the loop instruction.
    /// 
    /// Enter a loop with a block type.
    /// 
    /// # Specification
    /// 
    /// 1. Let 𝐹 be the current frame.
    /// 2. Assert: due to validation, expand𝐹 (blocktype) is defined.
    /// 3. Let [𝑡𝑚1 ] → [𝑡𝑛2 ] be the function type expand𝐹 (blocktype).
    /// 4. Let 𝐿 be the label whose arity is 𝑚 and whose continuation is the start of the loop.
    /// 5. Assert: due to validation, there are at least 𝑚 values on the top of the stack.
    /// 6. Pop the values val𝑚 from the stack.
    /// 7. Enter the block val𝑚 instr * with label 𝐿.
    /// 
    /// 𝐹; val𝑚 loop bt instr * end ˓→ 𝐹; label𝑚{loop bt instr * end} val𝑚 instr * end
    /// (if expand𝐹 (bt) = [𝑡𝑚1 ] → [𝑡𝑛2 ])
    /// 
    /// # Examples
    /// 
    /// ```
    /// // Loop with no parameters and no results
    /// loop
    ///   i32.const 1
    ///   i32.const 2
    ///   i32.add
    ///   br 0  // Branch back to the start of the loop
    /// end
    /// 
    /// // Loop with parameters and results
    /// i32.const 1
    /// i32.const 2
    /// loop (i32 i32) -> (i32)
    ///   i32.add
    ///   br 0  // Branch back to the start of the loop
    /// end
    /// ```
    pub fn loop_(
        thread: &mut Thread,
        block_type: &BlockType,
        instructions: &[Instruction],
    ) -> RuntimeResult<()> {
        // Get the current frame
        let frame = thread.frame_state();
        
        // Expand the block type to get the function type
        let func_type = frame.expand_block_type(block_type);
        
        // Get the number of parameters (m) and results (n)
        let param_count = func_type.params.len();
        let result_count = func_type.results.len();
        
        // Validate that there are at least m values on the stack
        let stack = thread.stack();
        if stack.value_count() < param_count {
            return Err(RuntimeError::Execution(format!(
                "loop: Expected {} values on stack, but only {} available",
                param_count,
                stack.value_count()
            )));
        }
        
        // Pop the parameter values from the stack
        let mut param_values = Vec::new();
        for _ in 0..param_count {
            let value = thread.stack_mut().pop_value().ok_or_else(|| {
                RuntimeError::Stack("Failed to pop parameter value for loop".to_string())
            })?;
            param_values.push(value);
        }
        
        // Create a label with arity m (parameter count) and continuation pointing to the start of the loop
        // The continuation is the loop instruction itself, which will be executed when branching to this label
        // This matches the specification: "Let 𝐿 be the label whose arity is 𝑚 and whose continuation is the start of the loop"
        let loop_instruction = Instruction::Control(ControlInstruction::Loop {
            block_type: block_type.clone(),
            instructions: instructions.to_vec(),
        });
        let mut continuation = Vec::new();
        continuation.push(loop_instruction);
        let label = Label::new(param_count, continuation);
        
        // Push the label onto the stack
        // This creates the state: 𝐹; label𝑚{loop bt instr * end} val𝑚 instr * end
        thread.stack_mut().push_label(label);
        
        // Push the parameter values back onto the stack
        for value in param_values.into_iter().rev() {
            thread.stack_mut().push_value(value);
        }
        
        // Execute the loop instructions
        for instruction in instructions {
            // TODO: Execute the instruction
            // This will be implemented when we have a proper instruction executor
            // For now, we'll just return an error
            return Err(RuntimeError::Execution(format!(
                "loop: Instruction execution not yet implemented: {:?}",
                instruction
            )));
        }
        
        Ok(())
    }

    /// Executes the if instruction.
    /// 
    /// Conditional execution based on a value of type i32.
    /// 
    /// # Specification
    /// 
    /// 1. Assert: due to validation, a value of value type i32 is on the top of the stack.
    /// 2. Pop the value i32.const 𝑐 from the stack.
    /// 3. If 𝑐 is non-zero, then:
    ///    a. Execute the block instruction block blocktype instr*1 end.
    /// 4. Else:
    ///    a. Execute the block instruction block blocktype instr*2 end.
    /// 
    /// (i32.const 𝑐) if bt instr*1 else instr*2 end ˓→ block bt instr*1 end
    /// (if 𝑐 ≠ 0)
    /// (i32.const 𝑐) if bt instr*1 else instr*2 end ˓→ block bt instr*2 end
    /// (if 𝑐 = 0)
    /// 
    /// # Examples
    /// 
    /// ```
    /// // Simple conditional execution
    /// i32.const 1
    /// if
    ///   i32.const 42  // This will be executed
    /// else
    ///   i32.const 0   // This will not be executed
    /// end
    /// 
    /// // Conditional with parameters and results
    /// i32.const 1
    /// i32.const 2
    /// i32.const 1  // condition
    /// if (i32 i32) -> (i32)
    ///   i32.add     // true branch
    /// else
    ///   i32.sub     // false branch
    /// end
    /// ```
    pub fn if_(
        store: &mut Store,
        thread: &mut Thread,
        block_type: &BlockType,
        true_instructions: &[Instruction],
        false_instructions: &[Instruction],
    ) -> RuntimeResult<()> {
        debug_log!(store.config(), "=== IF instruction ===");
        debug_log!(store.config(), "Block type: {:?}", block_type);
        debug_log!(store.config(), "True instructions: {:?}", true_instructions);
        debug_log!(store.config(), "False instructions: {:?}", false_instructions);
        
        // Step 1: Assert: due to validation, a value of value type i32 is on the top of the stack
        // Step 2: Pop the value i32.const 𝑐 from the stack
        let condition_value = thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Stack("No value on stack for if instruction".to_string())
        })?;
        
        // Validate that the condition is an i32 value
        let condition = match condition_value {
            Value::I32(val) => val,
            _ => return Err(RuntimeError::Execution(format!(
                "if: Expected i32 condition value, got {:?}",
                condition_value
            ))),
        };
        
        debug_log!(store.config(), "Condition value: {}", condition);
        
        // Step 3-4: Choose which instructions to execute based on the condition
        let instructions_to_execute = if condition != 0 {
            debug_log!(store.config(), "Executing true branch");
            true_instructions
        } else {
            debug_log!(store.config(), "Executing false branch");
            false_instructions
        };
        
        // Execute the chosen block using the block instruction logic
        // This matches: (i32.const 𝑐) if bt instr*1 else instr*2 end ˓→ block bt instr*1 end (if 𝑐 ≠ 0)
        // or: (i32.const 𝑐) if bt instr*1 else instr*2 end ˓→ block bt instr*2 end (if 𝑐 = 0)
        Self::block(store, thread, block_type, instructions_to_execute)
    }

    /// Executes the br instruction.
    /// 
    /// Unconditional branch to a label.
    /// 
    /// # Specification
    /// 
    /// 1. Assert: due to validation, the stack contains at least 𝑙 + 1 labels.
    /// 2. Let 𝐿 be the 𝑙-th label appearing on the stack, starting from the top and counting from zero.
    /// 3. Let 𝑛 be the arity of 𝐿.
    /// 4. Assert: due to validation, there are at least 𝑛 values on the top of the stack.
    /// 5. Pop the values val𝑛 from the stack.
    /// 6. Repeat 𝑙 + 1 times:
    ///    a. While the top of the stack is a value, do:
    ///       i. Pop the value from the stack.
    ///    b. Assert: due to validation, the top of the stack now is a label.
    ///    c. Pop the label from the stack.
    /// 7. Push the values val𝑛 to the stack.
    /// 8. Jump to the continuation of 𝐿.
    /// 
    /// label𝑛{instr *} 𝐵𝑙[val𝑛 (br 𝑙)] end ˓→ val𝑛 instr *
    /// 
    /// # Examples
    /// 
    /// ```
    /// // Branch to the innermost label (br 0)
    /// block
    ///   i32.const 42
    ///   br 0  // Branch to the end of this block
    /// end
    /// 
    /// // Branch to an outer label (br 1)
    /// block
    ///   block
    ///     i32.const 42
    ///     br 1  // Branch to the outer block
    ///   end
    /// end
    /// ```
    pub fn br(store: &mut Store, thread: &mut Thread, label_index: u32) -> RuntimeResult<()> {
        // Step 1: Validate that there are at least l + 1 labels on the stack
        if thread.stack().label_count() < (label_index + 1) as usize {
            return Err(RuntimeError::Execution(format!(
                "br: Expected at least {} labels on stack, but only {} available",
                label_index + 1,
                thread.stack().label_count()
            )));
        }
        // Step 2-3: Get the l-th label and its arity
        let (arity, continuation) = {
            let stack = thread.stack();
            let target_label = stack.get_label(label_index as usize).ok_or_else(|| {
                RuntimeError::Execution(format!(
                    "br: Label at index {} not found",
                    label_index
                ))
            })?;
            (target_label.arity(), target_label.continuation().to_vec())
        };
        // Step 4-5: Validate and pop the values for the label
        if thread.stack().value_count() < arity {
            return Err(RuntimeError::Execution(format!(
                "br: Expected {} values on stack for label arity, but only {} available",
                arity,
                thread.stack().value_count()
            )));
        }
        let mut branch_values = Vec::new();
        for _ in 0..arity {
            let value = thread.stack_mut().pop_value().ok_or_else(|| {
                RuntimeError::Stack("Failed to pop value for br instruction".to_string())
            })?;
            branch_values.push(value);
        }
        // Step 6: Repeat l + 1 times: clear values and pop labels
        for _ in 0..=label_index {
            while thread.stack().is_top_value() {
                thread.stack_mut().pop_value().ok_or_else(|| {
                    RuntimeError::Stack("Failed to pop value during br cleanup".to_string())
                })?;
            }
            thread.stack_mut().pop_label().ok_or_else(|| {
                RuntimeError::Stack("Expected label on stack during br cleanup".to_string())
            })?;
        }
        // Step 7: Push the values val_n to the stack
        for value in branch_values.into_iter().rev() {
            thread.stack_mut().push_value(value);
        }
        // Step 8: Jump to the continuation of L
        let executor = crate::wasm::runtime::instruction::DefaultInstructionExecutor;
        for instr in &continuation {
            executor.execute(store, thread, instr)?;
        }
        Ok(())
    }

    /// Executes the br_if instruction.
    ///
    /// Conditional branch to a label if the top stack value is non-zero.
    ///
    /// # Specification
    ///
    /// 1. Assert: due to validation, a value of value type i32 is on the top of the stack.
    /// 2. Pop the value i32.const 𝑐 from the stack.
    /// 3. If 𝑐 is non-zero, then:
    ///    a. Execute the instruction br 𝑙.
    /// 4. Else:
    ///    a. Do nothing.
    pub fn br_if(store: &mut Store, thread: &mut Thread, label_index: u32) -> RuntimeResult<()> {
        // Step 1-2: Pop the value i32.const 𝑐 from the stack
        let condition_value = thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Stack("No value on stack for br_if instruction".to_string())
        })?;
        let condition = match condition_value {
            Value::I32(val) => val,
            _ => return Err(RuntimeError::Execution(format!(
                "br_if: Expected i32 condition value, got {:?}",
                condition_value
            ))),
        };
        // Step 3: If 𝑐 is non-zero, execute br 𝑙
        if condition != 0 {
            Self::br(store, thread, label_index)?;
        }
        // Step 4: Else, do nothing
        Ok(())
    }

    /// Executes the br_table instruction.
    ///
    /// Branches to a label based on an index from the stack.
    ///
    /// # Specification
    ///
    /// 1. Assert: due to validation, a value of value type i32 is on the top of the stack.
    /// 2. Pop the value i32.const 𝑖 from the stack.
    /// 3. If 𝑖 is smaller than the length of 𝑙*, then:
    ///    a. Let 𝑙𝑖 be the label 𝑙*[𝑖].
    ///    b. Execute the instruction br 𝑙𝑖.
    /// 4. Else:
    ///    a. Execute the instruction br 𝑙𝑁.
    pub fn br_table(store: &mut Store, thread: &mut Thread, label_indices: &[u32], default_index: u32) -> RuntimeResult<()> {
        // Step 1-2: Pop the value i32.const 𝑖 from the stack
        let index_value = thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Stack("No value on stack for br_table instruction".to_string())
        })?;
        let index = match index_value {
            Value::I32(val) => val,
            _ => return Err(RuntimeError::Execution(format!(
                "br_table: Expected i32 index value, got {:?}",
                index_value
            ))),
        };
        // Step 3-4: Select the label and branch
        let label_index = if (index as usize) < label_indices.len() && index >= 0 {
            label_indices[index as usize]
        } else {
            default_index
        };
        Self::br(store, thread, label_index)
    }

    /// Executes the return instruction.
    ///
    /// Returns from the current function frame, leaving the results on the stack.
    ///
    /// # Specification
    ///
    /// 1. Let 𝐹 be the current frame.
    /// 2. Let 𝑛 be the arity of 𝐹.
    /// 3. Assert: due to validation, there are at least 𝑛 values on the top of the stack.
    /// 4. Pop the results val𝑛 from the stack.
    /// 5. Assert: due to validation, the stack contains at least one frame.
    /// 6. While the top of the stack is not a frame, do:
    ///    a. Pop the top element from the stack.
    /// 7. Assert: the top of the stack is the frame 𝐹.
    /// 8. Pop the frame from the stack.
    /// 9. Push val𝑛 to the stack.
    /// 10. Jump to the instruction after the original call that pushed the frame.
    pub fn return_(thread: &mut Thread) -> RuntimeResult<()> {
        // 1. Let 𝐹 be the current frame.
        let frame = thread.stack().top_frame().ok_or_else(|| {
            RuntimeError::Stack("No frame on stack for return instruction".to_string())
        })?;
        // 2. Let 𝑛 be the arity of 𝐹.
        let arity = frame.arity();
        // 3. Assert: there are at least 𝑛 values on the top of the stack.
        if thread.stack().value_count() < arity {
            return Err(RuntimeError::Execution(format!(
                "return: Expected {} values on stack for frame arity, but only {} available",
                arity,
                thread.stack().value_count()
            )));
        }
        // 4. Pop the results val𝑛 from the stack.
        let mut results = Vec::new();
        for _ in 0..arity {
            let value = thread.stack_mut().pop_value().ok_or_else(|| {
                RuntimeError::Stack("Failed to pop value for return instruction".to_string())
            })?;
            results.push(value);
        }
        // 5. Assert: the stack contains at least one frame.
        if thread.stack().frame_count() == 0 {
            return Err(RuntimeError::Stack("No frame on stack for return instruction".to_string()));
        }
        // 6. While the top of the stack is not a frame, pop the top element.
        while thread.stack().top_frame().is_none() {
            thread.stack_mut().pop_value(); // or pop_label/pop_block_context, but pop_value is safe for non-frame
        }
        // 7. Assert: the top of the stack is the frame 𝐹.
        if thread.stack().top_frame().is_none() {
            return Err(RuntimeError::Stack("Top of stack is not a frame for return instruction".to_string()));
        }
        // 8. Pop the frame from the stack.
        thread.stack_mut().pop_frame();
        // 9. Push val𝑛 to the stack (in reverse order to preserve original order)
        for value in results.into_iter().rev() {
            thread.stack_mut().push_value(value);
        }
        // 10. Jump to the instruction after the original call.
        // (In this interpreter, control will return to the caller after this function returns)
        Ok(())
    }

    /// Executes the call instruction.
    ///
    /// Calls a function by index in the current module.
    ///
    /// # Specification
    ///
    /// 1. Let 𝐹 be the current frame.
    /// 2. Assert: due to validation, 𝐹.module.funcaddrs[𝑥] exists.
    /// 3. Let 𝑎 be the function address 𝐹.module.funcaddrs[𝑥].
    /// 4. Invoke the function instance at address 𝑎.
    pub fn call(store: &mut Store, thread: &mut Thread, function_index: u32) -> RuntimeResult<()> {
        debug_log!(store.config(), "=== CALL instruction ===");
        debug_log!(store.config(), "Function index: {}", function_index);
        debug_log!(store.config(), "Stack depth before call: {}", thread.stack().frame_count());
        debug_log!(store.config(), "Stack values before call: {}", thread.stack().value_count());
        
        // Get the current frame state
        let frame_state = thread.frame_state();
        debug_log!(store.config(), "Current frame locals: {:?}", frame_state.locals());
        
        // Get the function address from the module
        let func_addr = frame_state.module().func_addrs.get(function_index as usize).ok_or_else(|| {
            RuntimeError::Execution(format!(
                "call: Function address at index {} does not exist in current module",
                function_index
            ))
        })?;
        
        debug_log!(store.config(), "Function address: {}", func_addr.as_usize());
        
        // Get the function instance from the store
        let func_instance = store.funcs.get(func_addr.as_usize()).ok_or_else(|| {
            RuntimeError::Execution(format!(
                "call: Function instance at address {} does not exist in store",
                func_addr.as_usize()
            ))
        })?;
        
        debug_log!(store.config(), "Function instance: is_host={}, is_wasm={}", func_instance.is_host(), func_instance.is_wasm());
        
        // Create the invoke instruction
        let invoke_instr = crate::wasm::ast::Instruction::Administrative(
            crate::wasm::ast::AdministrativeInstruction::Invoke(func_addr.clone())
        );
        
        debug_log!(store.config(), "About to execute invoke instruction...");
        
        // Execute the invoke instruction
        let result = crate::wasm::runtime::instruction::DefaultInstructionExecutor.execute(store, thread, &invoke_instr);
        
        debug_log!(store.config(), "After invoke execution:");
        debug_log!(store.config(), "Stack depth: {}", thread.stack().frame_count());
        debug_log!(store.config(), "Stack values: {}", thread.stack().value_count());
        if let Some(frame) = thread.stack().top_frame() {
            debug_log!(store.config(), "Top frame locals: {:?}", frame.state().locals());
        }
        
        result
    }

    /// Executes the call_indirect instruction.
    ///
    /// Calls a function indirectly through a table.
    ///
    /// # Specification
    ///
    /// 1. Let 𝐹 be the current frame.
    /// 2. Assert: due to validation, 𝐹.module.tableaddrs[𝑥] exists.
    /// 3. Let ta be the table address 𝐹.module.tableaddrs[𝑥].
    /// 4. Assert: due to validation, 𝑆.tables[ta] exists.
    /// 5. Let tab be the table instance 𝑆.tables[ta].
    /// 6. Assert: due to validation, 𝐹.module.types[𝑦] exists.
    /// 7. Let ftexpect be the function type 𝐹.module.types[𝑦].
    /// 8. Assert: due to validation, a value with value type i32 is on the top of the stack.
    /// 9. Pop the value i32.const 𝑖 from the stack.
    /// 10. If 𝑖 is not smaller than the length of tab.elem, then: a. Trap.
    /// 11. Let 𝑟 be the reference tab.elem[𝑖].
    /// 12. If 𝑟 is ref.null 𝑡, then: a. Trap.
    /// 13. Assert: due to validation of table mutation, 𝑟 is a function reference.
    /// 14. Let ref 𝑎 be the function reference 𝑟.
    /// 15. Assert: due to validation of table mutation, 𝑆.funcs[𝑎] exists.
    /// 16. Let f be the function instance 𝑆.funcs[𝑎].
    /// 17. Let ft actual be the function type f .type.
    /// 18. If ft actual and ftexpect differ, then: a. Trap.
    /// 19. Invoke the function instance at address 𝑎.
    pub fn call_indirect(store: &mut Store, thread: &mut Thread, table_index: u32, type_index: u32) -> RuntimeResult<()> {
        // 1. Let 𝐹 be the current frame.
        let frame_state = thread.frame_state();
        let module = frame_state.module().clone();
        let table_addrs = module.table_addrs.clone();
        let types = module.types.clone();
        // 2. Assert: 𝐹.module.tableaddrs[𝑥] exists.
        let table_addr = table_addrs.get(table_index as usize).ok_or_else(|| {
            RuntimeError::Execution(format!(
                "call_indirect: Table address at index {} does not exist in current module",
                table_index
            ))
        })?;
        // 4. Assert: 𝑆.tables[ta] exists。
        let table = store.tables.get(table_addr.as_usize()).ok_or_else(|| {
            RuntimeError::Execution(format!(
                "call_indirect: Table instance at address {} does not exist in store",
                table_addr.as_usize()
            ))
        })?;
        // 6. Assert: 𝐹.module.types[𝑦] exists。
        let ftexpect = types.get(type_index as usize).ok_or_else(|| {
            RuntimeError::Execution(format!(
                "call_indirect: Function type at index {} does not exist in current module",
                type_index
            ))
        })?;
        // 8-9. Pop the value i32.const 𝑖 from the stack.
        let index_value = thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Stack("No value on stack for call_indirect instruction".to_string())
        })?;
        let index = match index_value {
            Value::I32(val) => val,
            _ => return Err(RuntimeError::Execution(format!(
                "call_indirect: Expected i32 index value, got {:?}",
                index_value
            ))),
        };
        if index < 0 {
            return Err(RuntimeError::Trap("call_indirect: Table index is negative".to_string()));
        }
        let index = index as u32;
        // 10. If 𝑖 is not smaller than the length of tab.elem, then: a. Trap.
        if index >= table.size() {
            return Err(RuntimeError::Trap(format!(
                "call_indirect: Table index {} out of bounds (table size: {})",
                index, table.size()
            )));
        }
        // 11. Let 𝑟 be the reference tab.elem[𝑖].
        let elem = table.get(index).ok_or_else(|| {
            RuntimeError::Trap(format!(
                "call_indirect: Table element at index {} does not exist",
                index
            ))
        })?;
        // 12. If 𝑟 is ref.null 𝑡, then: a. Trap.
        if elem.is_null() {
            return Err(RuntimeError::Trap("call_indirect: Table element is null".to_string()));
        }
        // 13. Assert: 𝑟 is a function reference.
        let func_idx = match elem {
            crate::wasm::runtime::table::TableElement::FuncRef(Some(idx)) => *idx,
            _ => return Err(RuntimeError::Trap("call_indirect: Table element is not a function reference".to_string())),
        };
        // 15. Assert: 𝑆.funcs[𝑎] exists.
        let func_instance = store.funcs.get(func_idx as usize).ok_or_else(|| {
            RuntimeError::Trap(format!(
                "call_indirect: Function instance at index {} does not exist in store",
                func_idx
            ))
        })?;
        // 17. Let ft actual be the function type f .type.
        let ft_actual = func_instance.ty();
        // 18. If ft actual and ftexpect differ, then: a. Trap.
        if ft_actual != ftexpect {
            return Err(RuntimeError::Trap("call_indirect: Function type mismatch".to_string()));
        }
        // 19. Invoke the function instance at address 𝑎.
        let invoke_instr = crate::wasm::ast::Instruction::Administrative(
            crate::wasm::ast::AdministrativeInstruction::Invoke(crate::wasm::runtime::address::FuncAddr::new(func_idx))
        );
        crate::wasm::runtime::instruction::DefaultInstructionExecutor.execute(store, thread, &invoke_instr)
    }

    /// Executes the end instruction.
    ///
    /// When the end of a function is reached without a jump (i.e., return) or trap aborting it,
    /// then the following steps are performed:
    /// 1. Let F be the current frame.
    /// 2. Let n be the arity of the activation of F.
    /// 3. Assert: due to validation, there are n values on the top of the stack.
    /// 4. Pop the results val_n from the stack.
    /// 5. Assert: due to validation, the frame F is now on the top of the stack.
    /// 6. Pop the frame from the stack.
    /// 7. Push val_n back to the stack.
    /// 8. Jump to the instruction after the original call.
    ///
    /// # Specification
    /// frame_n{F} val_n end → val_n
    pub fn end(thread: &mut Thread, store: &Store) -> RuntimeResult<()> {
        debug_log!(store.config(), "=== END instruction ===");
        debug_log!(store.config(), "Stack has {} values", thread.stack().value_count());
        debug_log!(store.config(), "Stack depth: {}", thread.stack().frame_count());
        debug_log!(store.config(), "Thread instructions before end: {:?}", thread.instructions());
        
        // 1. Let F be the current frame.
        let frame = thread.stack().top_frame().ok_or_else(|| {
            RuntimeError::Stack("No frame on stack for end instruction".to_string())
        })?;
        
        debug_log!(store.config(), "Top frame arity: {}", frame.arity());
        debug_log!(store.config(), "Top frame locals: {:?}", frame.state().locals());
        
        // 2. Let n be the arity of the activation of F.
        let arity = frame.arity();
        debug_log!(store.config(), "End instruction: frame arity = {}", arity);
        
        // 3. Assert: due to validation, there are n values on the top of the stack.
        if thread.stack().value_count() < arity {
            return Err(RuntimeError::Execution(format!(
                "end: Expected {} values on stack for frame arity, but only {} available",
                arity,
                thread.stack().value_count()
            )));
        }
        
        // 4. Pop the results val_n from the stack.
        let mut results = Vec::new();
        for i in 0..arity {
            let value = thread.stack_mut().pop_value().ok_or_else(|| {
                RuntimeError::Stack(format!("Failed to pop value {} for end instruction", i))
            })?;
            debug_log!(store.config(), "End instruction: popped result {}: {:?}", i, value);
            results.push(value);
        }
        
        // 5. Assert: due to validation, the frame F is now on the top of the stack.
        if thread.stack().top_frame().is_none() {
            return Err(RuntimeError::Stack("Top of stack is not a frame for end instruction".to_string()));
        }
        
        // 6. Pop the frame from the stack.
        thread.stack_mut().pop_frame();
        debug_log!(store.config(), "End instruction: popped frame");
        debug_log!(store.config(), "Stack depth after popping frame: {}", thread.stack().frame_count());
        
        // 7. Push val_n back to the stack (in reverse order to preserve original order)
        for (i, value) in results.into_iter().rev().enumerate() {
            debug_log!(store.config(), "End instruction: pushing result {} back: {:?}", i, value);
            thread.stack_mut().push_value(value);
        }
        
        debug_log!(store.config(), "End instruction: final stack has {} values", thread.stack().value_count());
        debug_log!(store.config(), "Final stack depth: {}", thread.stack().frame_count());
        if let Some(frame) = thread.stack().top_frame() {
            debug_log!(store.config(), "Final top frame locals: {:?}", frame.state().locals());
        }
        debug_log!(store.config(), "Thread instructions after end: {:?}", thread.instructions());
        
        // 8. Jump to the instruction after the original call.
        // (In this interpreter, control will return to the caller after this function returns)
        Ok(())
    }
}

/// Executes a control instruction
pub fn execute_control(
    store: &mut Store,
    thread: &mut Thread,
    instruction: &Instruction,
) -> RuntimeResult<()> {
    match instruction {
        Instruction::Control(control_inst) => match control_inst {
            ControlInstruction::Nop => {
                Control::nop(thread)
            }
            ControlInstruction::Unreachable => {
                Control::unreachable(thread)
            }
            ControlInstruction::Block { block_type, instructions } => {
                Control::block(store, thread, block_type, instructions)
            }
            ControlInstruction::Loop { block_type, instructions } => {
                Control::loop_(thread, block_type, instructions)
            }
            ControlInstruction::If { block_type, true_instructions, false_instructions } => {
                Control::if_(store, thread, block_type, true_instructions, false_instructions)
            }
            ControlInstruction::Br { label_index } => {
                Control::br(store, thread, *label_index)
            }
            ControlInstruction::BrIf { label_index } => {
                Control::br_if(store, thread, *label_index)
            }
            ControlInstruction::BrTable { label_indices, default_index } => {
                Control::br_table(store, thread, label_indices, *default_index)
            }
            ControlInstruction::Return => {
                Control::return_(thread)
            }
            ControlInstruction::Call { function_index } => {
                Control::call(store, thread, *function_index)
            }
            ControlInstruction::CallIndirect { table_index, type_index } => {
                Control::call_indirect(store, thread, *table_index, *type_index)
            }
            ControlInstruction::End => {
                Control::end(thread, store)
            }
            ControlInstruction::Else => {
                // Else instruction should not be executed directly
                // It should only appear within if instructions
                Err(RuntimeError::Execution("Else instruction should not be executed directly".to_string()))
            }
            // TODO: Implement other control instructions
            _ => Err(RuntimeError::Execution(format!(
                "Unimplemented control instruction: {:?}",
                control_inst
            ))),
        },
        _ => Err(RuntimeError::Execution(format!(
            "Expected control instruction, got: {:?}",
            instruction
        ))),
    }
} 
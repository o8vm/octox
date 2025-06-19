//! Block Instructions implementation for WebAssembly runtime.
//!
//! Implements the semantics of entering and exiting a block as described in the WebAssembly specification (4.4.9 Blocks).

use alloc::vec::Vec;
use alloc::string::ToString;

use crate::wasm::runtime::{
    RuntimeResult,
    RuntimeError,
    Store,
    Thread,
    stack::{Label},
};
use crate::wasm::ast::{Instruction, BlockType};
use crate::wasm::runtime::instruction::InstructionExecutor;

/// Block instruction implementation.
pub struct Block;

impl Block {
    /// Enter a block of instructions with a label.
    ///
    /// # Semantics (Entering instr* with label L)
    /// 1. Push L to the stack.
    /// 2. Jump to the start of the instruction sequence instr*.
    pub fn enter(
        store: &mut Store,
        thread: &mut Thread,
        label: Label,
        instructions: &[Instruction],
    ) -> RuntimeResult<()> {
        // 1. Push L to the stack.
        thread.stack_mut().push_label(label);
        
        // 2. Jump to the start of the instruction sequence instr*.
        // Convert instructions to an expression and execute it
        let expression = crate::wasm::ast::Expression::general(instructions.to_vec());
        let _result = crate::wasm::runtime::instruction::execute_expression(
            store, 
            thread, 
            &expression
        )?;
        
        // Note: The result value is already on the stack from execute_expression
        Ok(())
    }

    /// Exit a block of instructions with a label.
    ///
    /// # Semantics (Exiting instr* with label L)
    /// 1. Pop all values val* from the top of the stack.
    /// 2. Assert: due to validation, the label L is now on the top of the stack.
    /// 3. Pop the label from the stack.
    /// 4. Push val* back to the stack.
    /// 5. Jump to the position after the end of the structured control instruction associated with the label L.
    pub fn exit(thread: &mut Thread) -> RuntimeResult<()> {
        // 1. Pop all values val* from the top of the stack (up to the label arity)
        let label = thread.stack().top_label().ok_or_else(|| {
            RuntimeError::Stack("No label on stack when exiting block".to_string())
        })?;
        let arity = label.arity();
        let mut values = Vec::new();
        for _ in 0..arity {
            let value = thread.stack_mut().pop_value().ok_or_else(|| {
                RuntimeError::Stack("Failed to pop value when exiting block".to_string())
            })?;
            values.push(value);
        }
        // 2. Assert: the label L is now on the top of the stack.
        if thread.stack().top_label().is_none() {
            return Err(RuntimeError::Stack("No label on stack when exiting block".to_string()));
        }
        // 3. Pop the label from the stack.
        thread.stack_mut().pop_label();
        // 4. Push val* back to the stack (in reverse order to preserve original order)
        for value in values.into_iter().rev() {
            thread.stack_mut().push_value(value);
        }
        // 5. Jump to the position after the end of the structured control instruction (handled by control flow)
        Ok(())
    }
} 
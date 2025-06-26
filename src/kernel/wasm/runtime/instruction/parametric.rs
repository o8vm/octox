//! Parametric Instructions implementation for WebAssembly runtime.
//!
//! Implements instructions like drop and select.

use alloc::format;
use alloc::string::ToString;

use crate::wasm::ast::{Instruction, ParametricInstruction};
use crate::wasm::runtime::{RuntimeResult, RuntimeError, Store, Thread};

/// Executes a parametric instruction
pub fn execute_parametric(
    _store: &mut Store,
    thread: &mut Thread,
    instruction: &Instruction,
) -> RuntimeResult<()> {
    match instruction {
        Instruction::Parametric(parametric_instr) => match parametric_instr {
            ParametricInstruction::Drop => {
                // Pop the value from the stack
                let popped = thread.stack_mut().pop_value();
                if popped.is_none() {
                    return Err(RuntimeError::Stack("No value on stack for drop instruction".to_string()));
                }
                Ok(())
            }
            ParametricInstruction::Select(_) => {
                // Pop c (i32), val2, val1 from the stack (in reverse order)
                let c = thread.stack_mut().pop_value().ok_or_else(|| {
                    RuntimeError::Stack("No condition value (i32) on stack for select instruction".to_string())
                })?;
                let val2 = thread.stack_mut().pop_value().ok_or_else(|| {
                    RuntimeError::Stack("No second value on stack for select instruction".to_string())
                })?;
                let val1 = thread.stack_mut().pop_value().ok_or_else(|| {
                    RuntimeError::Stack("No first value on stack for select instruction".to_string())
                })?;
                // Check c is i32
                let c_val = match c {
                    crate::wasm::runtime::Value::I32(v) => v,
                    _ => {
                        return Err(RuntimeError::TypeError(format!(
                            "Select condition must be i32, got {:?}", c
                        )))
                    }
                };
                // Check val1 and val2 are the same type
                if val1.value_type() != val2.value_type() {
                    return Err(RuntimeError::TypeError(format!(
                        "Select operands must have the same type, got {:?} and {:?}",
                        val1.value_type(), val2.value_type()
                    )));
                }
                // Push the selected value
                if c_val != 0 {
                    thread.stack_mut().push_value(val1);
                } else {
                    thread.stack_mut().push_value(val2);
                }
                Ok(())
            }
        },
        _ => Err(RuntimeError::Execution(format!(
            "Expected parametric instruction, got: {:?}",
            instruction
        ))),
    }
} 
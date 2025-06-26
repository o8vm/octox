//! Reference Instructions implementation for WebAssembly runtime.
//! 
//! This module implements the reference instructions as defined in the WebAssembly specification.
//! Reference instructions handle operations on reference types (ref.null, ref.is_null, ref.func, etc.).

use alloc::format;
use alloc::string::ToString;

use crate::wasm::runtime::{
    value::{Value, ValueType},
    RuntimeResult,
    RuntimeError,
    Store,
    Thread,
};
use crate::wasm::ast::{Instruction, ReferenceInstruction};

/// Reference instruction implementation.
/// 
/// This struct contains methods for executing reference instructions in the WebAssembly runtime.
pub struct Reference;

impl Reference {
    /// Executes the ref.null instruction.
    /// 
    /// Pushes a null reference of the specified type onto the stack.
    /// 
    /// # Arguments
    /// 
    /// * `thread` - The current thread state
    /// * `ref_type` - The type of the null reference (funcref or externref)
    /// 
    /// # Returns
    /// 
    /// * `Ok(())` if the instruction executed successfully
    /// * `Err(String)` if an error occurred
    pub fn ref_null(thread: &mut Thread, ref_type: ValueType) -> RuntimeResult<()> {
        // Create a null reference of the specified type
        let null_ref = Value::NullRef(ref_type);
        
        // Push the null reference onto the stack
        thread.stack_mut().push_value(null_ref);
        
        Ok(())
    }

    /// Executes the ref.is_null instruction.
    /// 
    /// Pops a reference value from the stack and pushes an i32 value indicating
    /// whether the reference was null (1) or not (0).
    /// 
    /// # Arguments
    /// 
    /// * `thread` - The current thread state
    /// 
    /// # Returns
    /// 
    /// * `Ok(())` if the instruction executed successfully
    /// * `Err(String)` if an error occurred
    pub fn ref_is_null(thread: &mut Thread) -> RuntimeResult<()> {
        // Pop the reference value from the stack
        let val = thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Execution("Expected reference value on stack for ref.is_null".to_string())
        })?;

        // Check if the value is a null reference
        let is_null = match val {
            Value::NullRef(_) => true,
            _ => false,
        };

        // Push the result (1 for null, 0 for non-null)
        thread.stack_mut().push_value(Value::I32(if is_null { 1 } else { 0 }));

        Ok(())
    }

    /// Executes the ref.func instruction.
    /// 
    /// Pushes a function reference to the stack based on the function index.
    /// 
    /// # Arguments
    /// 
    /// * `thread` - The current thread state
    /// * `func_idx` - The function index
    /// 
    /// # Returns
    /// 
    /// * `Ok(())` if the instruction executed successfully
    /// * `Err(String)` if an error occurred
    pub fn ref_func(thread: &mut Thread, func_idx: u32) -> RuntimeResult<()> {
        // Get the function address in a separate scope to limit the immutable borrow
        let func_addr = {
            let frame_state = thread.frame_state();
            let module = frame_state.module();
            // Clone the Address to avoid keeping the immutable borrow alive
            module.get_func_addr(func_idx).ok_or_else(|| {
                RuntimeError::Execution(format!(
                    "Function address at index {} does not exist",
                    func_idx
                ))
            })?.clone()
        };
        
        // Push the function reference to the stack
        thread.stack_mut().push_value(Value::FuncRef(func_addr.as_u32()));
        
        Ok(())
    }
}

/// Executes a reference instruction
/// 
/// # Arguments
/// 
/// * `store` - The current store state
/// * `thread` - The current thread state
/// * `instruction` - The reference instruction to execute
/// 
/// # Returns
/// 
/// * `RuntimeResult<()>` - The result of the execution
pub fn execute_reference(
    store: &mut Store,
    thread: &mut Thread,
    instruction: &Instruction,
) -> RuntimeResult<()> {
    match instruction {
        Instruction::Reference(ref_inst) => {
            match ref_inst {
                ReferenceInstruction::RefNull(ref_type) => {
                    Reference::ref_null(thread, ValueType::from_val_type(*ref_type))
                        .map_err(|e| RuntimeError::Execution(e.to_string()))
                }
                ReferenceInstruction::RefIsNull => {
                    Reference::ref_is_null(thread)
                        .map_err(|e| RuntimeError::Execution(e.to_string()))
                }
                ReferenceInstruction::RefFunc(func_idx) => {
                    Reference::ref_func(thread, *func_idx)
                        .map_err(|e| RuntimeError::Execution(e.to_string()))
                }
            }
        }
        _ => Err(RuntimeError::Execution(format!(
            "Expected reference instruction, got: {:?}",
            instruction
        ))),
    }
} 
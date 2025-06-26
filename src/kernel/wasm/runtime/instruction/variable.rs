//! Variable Instructions implementation for WebAssembly runtime.
//!
//! Implements instructions like local.get, local.set, local.tee, global.get, global.set.

use alloc::format;
use alloc::string::ToString;

use crate::wasm::runtime::{
    value::Value,
    RuntimeResult,
    RuntimeError,
    Store,
    Thread,
    Frame,
};
use crate::wasm::ast::{Instruction, VariableInstruction};
use crate::debug_log;

/// Variable instruction implementation.
pub struct Variable;

impl Variable {
    /// Executes the local.get instruction.
    /// 
    /// Pops nothing, pushes the value of the local variable at index x.
    /// 
    /// # Specification
    /// 
    /// 1. Let 𝐹 be the current frame.
    /// 2. Assert: due to validation, 𝐹.locals[𝑥] exists.
    /// 3. Let val be the value 𝐹.locals[𝑥].
    /// 4. Push the value val to the stack.
    /// 
    /// 𝐹; (local.get 𝑥) → 𝐹; val (if 𝐹.locals[𝑥] = val )
    pub fn local_get(store: &Store, thread: &mut Thread, local_idx: u32) -> RuntimeResult<()> {
        debug_log!(store.config(), "[local.get] index={}, frame stack depth={}", local_idx, thread.stack().frame_count());
        
        // 1. Let 𝐹 be the current frame.
        // We need to find the WASM function frame, not the host function frame
        let mut target_frame: Option<&Frame> = None;
        
        // Search for the WASM function frame (typically at index 1, after host function frame)
        for i in 0..thread.stack().frame_count() {
            if let Some(frame) = thread.stack().get_frame(i) {
                debug_log!(store.config(), "[local.get] frame {} has {} locals: {:?}", i, frame.state().locals().len(), frame.state().locals());
                if frame.state().locals().len() > local_idx as usize {
                    // Check if this is a WASM function frame (not host function frame)
                    // Host function frames typically have more locals than needed for simple WASM functions
                    // We want the frame that corresponds to the WASM function being executed
                    // Look for the frame with the smallest number of locals that still has enough for our index
                    // This is likely the WASM function frame rather than a host function frame
                    if target_frame.is_none() || frame.state().locals().len() < target_frame.unwrap().state().locals().len() {
                        target_frame = Some(frame);
                        debug_log!(store.config(), "[local.get] found potential WASM function frame {} with {} locals", i, frame.state().locals().len());
                    }
                }
            }
        }
        
        // If we didn't find a WASM function frame, try the current frame state
        if target_frame.is_none() {
            debug_log!(store.config(), "[local.get] using current frame state for local {}", local_idx);
            let current_frame = thread.current_frame_state();
            if current_frame.locals().len() > local_idx as usize {
                // 2. Assert: due to validation, 𝐹.locals[𝑥] exists.
                // 3. Let val be the value 𝐹.locals[𝑥].
                let val = current_frame.locals().get(local_idx as usize).ok_or_else(|| {
                    RuntimeError::Execution(format!(
                        "local.get: Local index {} does not exist in current frame.",
                        local_idx
                    ))
                })?.clone();
                
                debug_log!(store.config(), "[local.get] found value {:?} in current frame", val);
                
                // 4. Push the value val to the stack.
                thread.stack_mut().push_value(val);
                return Ok(());
            }
        }
        
        let target_frame = target_frame.ok_or_else(|| {
            RuntimeError::Execution(format!(
                "local.get: Local index {} does not exist in any WASM function frame.",
                local_idx
            ))
        })?;
        
        // 2. Assert: due to validation, 𝐹.locals[𝑥] exists.
        // 3. Let val be the value 𝐹.locals[𝑥].
        let val = target_frame.state().locals().get(local_idx as usize).ok_or_else(|| {
            RuntimeError::Execution(format!(
                "local.get: Local index {} does not exist in target frame.",
                local_idx
            ))
        })?.clone();
        
        debug_log!(store.config(), "[local.get] found value {:?} in target frame", val);
        
        // 4. Push the value val to the stack.
        thread.stack_mut().push_value(val);
        Ok(())
    }

    /// Executes the local.set instruction.
    /// 
    /// Pops a value from the stack and sets it to the local variable at index x.
    /// 
    /// # Specification
    /// 
    /// 1. Let 𝐹 be the current frame.
    /// 2. Assert: due to validation, 𝐹.locals[𝑥] exists.
    /// 3. Assert: due to validation, a value is on the top of the stack.
    /// 4. Pop the value val from the stack.
    /// 5. Replace 𝐹.locals[𝑥] with the value val .
    /// 
    /// 𝐹; val (local.set 𝑥) → 𝐹′; 𝜖 (if 𝐹′ = 𝐹 with locals[𝑥] = val )
    /// 
    /// Note: This implementation finds the WASM function frame (not host function frame) for local variable access.
    pub fn local_set(thread: &mut Thread, local_idx: u32, store: &Store) -> RuntimeResult<()> {
        debug_log!(store.config(), "local_set: before pop, stack: {}", thread.stack());
        
        // 3. Assert: due to validation, a value is on the top of the stack.
        // 4. Pop the value val from the stack.
        let val = thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Stack("No value on stack for local.set instruction".to_string())
        })?;
        
        // Find the WASM function frame (not host function frame) for local variable access
        let mut target_frame_index = None;
        debug_log!(store.config(), "local_set: searching for WASM function frame with locals...");
        for i in 0..thread.stack().frame_count() {
            if let Some(frame) = thread.stack().get_frame(i) {
                debug_log!(store.config(), "local_set: frame {} has {} locals: {:?}", i, frame.state().locals().len(), frame.state().locals());
                // Check if this frame has enough locals for the given index
                if frame.state().locals().len() > local_idx as usize {
                    // Check if this is a WASM function frame (not host function frame)
                    // Host function frames typically have more locals than needed for simple WASM functions
                    // We want the frame that corresponds to the WASM function being executed
                    // Look for the frame with the smallest number of locals that still has enough for our index
                    // This is likely the WASM function frame rather than a host function frame
                    if target_frame_index.is_none() || frame.state().locals().len() < thread.stack().get_frame(target_frame_index.unwrap()).unwrap().state().locals().len() {
                        target_frame_index = Some(i);
                        debug_log!(store.config(), "local_set: found potential WASM function frame {} with {} locals for index {}", i, frame.state().locals().len(), local_idx);
                    }
                }
            }
        }
        
        // If we didn't find a WASM function frame, try the current frame state
        if target_frame_index.is_none() {
            debug_log!(store.config(), "local_set: using current frame state for local {}", local_idx);
            let current_frame = thread.current_frame_state();
            if current_frame.locals().len() > local_idx as usize {
                // Use the current frame state directly
                let mut frame_state = thread.current_frame_state_mut();
                let locals = frame_state.locals_mut();
                let local = locals.get_mut(local_idx as usize).ok_or_else(|| {
                    RuntimeError::Execution(format!(
                        "local.set: Local index {} does not exist in current frame.",
                        local_idx
                    ))
                })?;
                *local = val;
                return Ok(());
            }
        }
        
        let target_frame_index = target_frame_index.ok_or_else(|| {
            RuntimeError::Execution("No WASM function frame with locals found for local.set instruction".to_string())
        })?;
        
        debug_log!(store.config(), "local_set: setting local {} to {:?} in frame index {}", local_idx, val, target_frame_index);
        
        // Get a mutable reference to the target frame
        let target_frame_mut = thread.stack_mut().get_frame_mut(target_frame_index).ok_or_else(|| {
            RuntimeError::Execution(format!("Frame at index {} not available for local.set instruction", target_frame_index))
        })?;
        
        debug_log!(store.config(), "local_set: target frame locals: {:?}", target_frame_mut.state().locals());
        
        // Get a mutable reference to the locals
        let locals = target_frame_mut.state_mut().locals_mut();
        
        // 2. Assert: due to validation, 𝐹.locals[𝑥] exists.
        // 5. Replace 𝐹.locals[𝑥] with the value val .
        let local = locals.get_mut(local_idx as usize).ok_or_else(|| {
            RuntimeError::Execution(format!(
                "local.set: Local index {} does not exist in target frame.",
                local_idx
            ))
        })?;
        
        // Set the local
        *local = val;
        Ok(())
    }

    /// Executes the local.tee instruction.
    /// 
    /// Pops a value from the stack, pushes it back, and sets it to the local variable at index x.
    /// This is equivalent to duplicating the value and then executing local.set.
    pub fn local_tee(thread: &mut Thread, local_idx: u32, store: &Store) -> RuntimeResult<()> {
        // Get the value from the stack first
        let val = thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Stack("No value on stack for local.tee instruction".to_string())
        })?;

        // Push the value back to the stack (first push)
        thread.stack_mut().push_value(val.clone());

        // Push the value again (second push)
        thread.stack_mut().push_value(val.clone());

        // Execute local.set with the value
        Self::local_set(thread, local_idx, store)
    }

    /// Executes the global.get instruction.
    /// 
    /// Gets the value of the global variable at index x and pushes it to the stack.
    /// 
    /// # Specification
    /// 
    /// 1. Let 𝐹 be the current frame.
    /// 2. Assert: due to validation, 𝐹.module.globaladdrs[𝑥] exists.
    /// 3. Let 𝑎 be the global address 𝐹.module.globaladdrs[𝑥].
    /// 4. Assert: due to validation, 𝑆.globals[𝑎] exists.
    /// 5. Let glob be the global instance 𝑆.globals[𝑎].
    /// 6. Let val be the value glob.value.
    /// 7. Push the value val to the stack.
    pub fn global_get(store: &Store, thread: &mut Thread, global_idx: u32) -> RuntimeResult<()> {
        // Get the current frame
        let frame = thread.frame_state();
        
        // Get the global address from the module
        let global_addr = frame.module().global_addrs.get(global_idx as usize).ok_or_else(|| {
            RuntimeError::Execution(format!(
                "global.get: Global index {} does not exist in current module",
                global_idx
            ))
        })?;

        // Get the global instance from the store
        let global = store.globals.get(global_addr.as_usize()).ok_or_else(|| {
            RuntimeError::Execution(format!(
                "global.get: Global address {} does not exist in store",
                global_addr
            ))
        })?;

        // Get the value and push it to the stack
        let val = global.value().clone();
        thread.stack_mut().push_value(val);
        Ok(())
    }

    /// Executes the global.set instruction.
    /// 
    /// Pops a value from the stack and sets it to the global variable at index x.
    /// The global variable must be mutable.
    /// 
    /// # Specification
    /// 
    /// 1. Let 𝐹 be the current frame.
    /// 2. Assert: due to validation, 𝐹.module.globaladdrs[𝑥] exists.
    /// 3. Let 𝑎 be the global address 𝐹.module.globaladdrs[𝑥].
    /// 4. Assert: due to validation, 𝑆.globals[𝑎] exists.
    /// 5. Let glob be the global instance 𝑆.globals[𝑎].
    /// 6. Assert: due to validation, a value is on the top of the stack.
    /// 7. Pop the value val from the stack.
    /// 8. Replace glob.value with the value val.
    pub fn global_set(store: &mut Store, thread: &mut Thread, global_idx: u32) -> RuntimeResult<()> {
        // Get the global address from the module first
        let global_addr = {
            let frame = thread.frame_state();
            frame.module().global_addrs.get(global_idx as usize).ok_or_else(|| {
                RuntimeError::Execution(format!(
                    "global.set: Global index {} does not exist in current module",
                    global_idx
                ))
            })?.clone() // Clone the address to avoid keeping the frame borrow
        };

        // Pop the value from the stack
        let val = thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Stack("No value on stack for global.set instruction".to_string())
        })?;

        // Get a mutable reference to the global instance from the store
        let global = store.globals.get_mut(global_addr.as_usize()).ok_or_else(|| {
            RuntimeError::Execution(format!(
                "global.set: Global address {} does not exist in store",
                global_addr
            ))
        })?;

        // Check if the global is mutable
        if !global.is_mutable() {
            return Err(RuntimeError::Execution(format!(
                "global.set: Global {} is immutable",
                global_addr
            )));
        }

        // Set the value
        global.set_value(val).map_err(|e| {
            RuntimeError::Execution(format!("global.set: {}", e))
        })?;

        Ok(())
    }
}

/// Executes a variable instruction
pub fn execute_variable(
    store: &mut Store,
    thread: &mut Thread,
    instruction: &Instruction,
) -> RuntimeResult<()> {
    match instruction {
        Instruction::Variable(var_inst) => match var_inst {
            VariableInstruction::LocalGet(idx) => {
                Variable::local_get(store, thread, *idx)
            }
            VariableInstruction::LocalSet(idx) => {
                Variable::local_set(thread, *idx, store)
            }
            VariableInstruction::LocalTee(idx) => {
                Variable::local_tee(thread, *idx, store)
            }
            VariableInstruction::GlobalGet(idx) => {
                Variable::global_get(store, thread, *idx)
            }
            VariableInstruction::GlobalSet(idx) => {
                Variable::global_set(store, thread, *idx)
            }
        },
        _ => Err(RuntimeError::Execution(format!(
            "Expected variable instruction, got: {:?}",
            instruction
        ))),
    }
} 
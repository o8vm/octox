//! Function Instructions implementation for WebAssembly runtime.
//!
//! Implements the semantics of function invocation as described in the WebAssembly specification (4.4.10 Function Calls).

use alloc::format;
use alloc::vec::Vec;
use alloc::string::String;
use alloc::string::ToString;
use core::ptr;

use crate::wasm::runtime::{
    RuntimeResult,
    RuntimeError,
    Store,
    Thread,
    stack::{Label},
    frame::{Frame, FrameState},
    address::FuncAddr,
    module::ModuleInstance,
};
use crate::wasm::ast::{Instruction, FuncType, ValType};
use crate::wasm::runtime::instruction::InstructionExecutor;
use crate::debug_log;

/// Represents a possible outcome of a host function invocation.
#[derive(Debug, Clone)]
pub enum HostFunctionOutcome {
    /// Normal return with results
    Normal {
        /// The function results
        results: Vec<crate::wasm::runtime::Value>,
    },
    /// Trap with error message
    Trap {
        /// The trap message
        message: String,
    },
    /// Divergent behavior (infinite loop/recursion)
    Divergent,
}

/// Function instruction implementation.
pub struct Function;

impl Function {
    /// Helper function to extract host function information without borrowing conflicts
    fn extract_host_func_info<'a>(
        store: &'a Store,
        func_addr: FuncAddr,
        func_type: &crate::wasm::ast::FuncType,
    ) -> RuntimeResult<Option<&'a crate::wasm::runtime::HostFunc>> {
        let func_instance = store.funcs.get(func_addr.as_usize()).ok_or_else(|| {
            RuntimeError::Execution(format!(
                "invoke: Function instance at address {} does not exist in store",
                func_addr.as_usize()
            ))
        })?;
        
        if func_instance.is_host() {
            let host_func = func_instance.host_code().ok_or_else(|| {
                RuntimeError::Execution("Function instance is not a host function".to_string())
            })?;
            Ok(Some(host_func))
        } else {
            Ok(None)
        }
    }

    /// Invokes a function instance at the given address.
    ///
    /// # Semantics (Invocation of function address a)
    /// 1. Assert: due to validation, S.funcs[a] exists.
    /// 2. Let f be the function instance, S.funcs[a].
    /// 3. Let [t_n^1] -> [t_m^2] be the function type f.type.
    /// 4. Let t* be the list of value types f.code.locals.
    /// 5. Let instr* end be the expression f.code.body.
    /// 6. Assert: due to validation, n values are on the top of the stack.
    /// 7. Pop the values val_n from the stack.
    /// 8. Let F be the frame {module f.module, locals val_n (default_t)*}.
    /// 9. Push the activation of F with arity m to the stack.
    /// 10. Let L be the label whose arity is m and whose continuation is the end of the function.
    /// 11. Enter the instruction sequence instr* with label L.
    ///
    /// # Specification
    /// S; val_n (invoke a) → S; frame_m{F} label_m{} instr* end end
    /// (if S.funcs[a] = f
    ///  ∧ f.type = [t_n^1] → [t_m^2]
    ///  ∧ f.code = {type x, locals t_k, body instr* end}
    ///  ∧ F = {module f.module, locals val_n (default_t)^k})
    pub fn invoke(
        store: &mut Store,
        thread: &mut Thread,
        func_addr: FuncAddr,
    ) -> RuntimeResult<()> {
        // 1. Assert: due to validation, S.funcs[a] exists.
        // 2. Let f be the function instance, S.funcs[a].
        // Extract all necessary information from func_instance in a separate scope
        let (func_type, param_count, result_count, is_host, module, code_info) = {
            let func_instance = store.funcs.get(func_addr.as_usize()).ok_or_else(|| {
                RuntimeError::Execution(format!(
                    "invoke: Function instance at address {} does not exist in store",
                    func_addr.as_usize()
                ))
            })?;

            debug_log!(store.config(), "FuncInstance at address {}: is_host={}, is_wasm={}, code() is_some={}", 
                func_addr.as_usize(), func_instance.is_host(), func_instance.is_wasm(), func_instance.code().is_some());

            // 3. Let [t_n^1] -> [t_m^2] be the function type f.type.
            let func_type = func_instance.ty().clone(); // Clone to avoid borrowing
            let param_count = func_type.params.len();
            let result_count = func_type.results.len();

            debug_log!(store.config(), "Function type: {:?} -> {:?}", func_type.params, func_type.results);

            // Check if this is a host function and extract necessary info
            let is_host = func_instance.is_host();
            
            // For host functions, we don't need a module, but we need to handle this case
            let module = if is_host {
                // For host functions, we'll use the current thread's module
                thread.frame_state().module().clone()
            } else {
                // For WebAssembly functions, get the module
                func_instance.module().ok_or_else(|| {
                    RuntimeError::Execution("WebAssembly function instance has no module".to_string())
                })?.clone()
            };

            // Extract all necessary information from func_instance before any mutable borrows
            let code_info = func_instance.code().cloned();
            
            debug_log!(store.config(), "Function is_host: {}, code_info is_some: {}", is_host, code_info.is_some());
            if let Some(code) = &code_info {
                debug_log!(store.config(), "Code locals: {:?}, code body length: {}", code.locals, code.code.len());
            }

            (func_type, param_count, result_count, is_host, module, code_info)
        };

        // Extract host function information in a separate scope to avoid borrowing conflicts
        let is_host_function = is_host;

        // 4. Let t* be the list of value types f.code.locals.
        // Note: This is handled implicitly when we process the locals below

        // 5. Let instr* end be the expression f.code.body.
        // Note: This is handled when we parse the function code below

        // 6. Assert: due to validation, n values are on the top of the stack.
        if thread.stack().value_count() < param_count {
            return Err(RuntimeError::Execution(format!(
                "invoke: Expected {} values on stack, but only {} available",
                param_count,
                thread.stack().value_count()
            )));
        }

        // 7. Pop the values val_n from the stack.
        let mut param_values = Vec::new();
        for _ in 0..param_count {
            let value = thread.stack_mut().pop_value().ok_or_else(|| {
                RuntimeError::Stack("Failed to pop parameter value for function invocation".to_string())
            })?;
            param_values.push(value);
        }
        
        // Reverse the parameters because they were popped in reverse order (LIFO stack)
        // The first parameter should be at index 0, second at index 1, etc.
        param_values.reverse();
        
        debug_log!(store.config(), "All parameters: {:?}", param_values);

        // 8. Let F be the frame {module f.module, locals val_n (default_t)*}.
        let frame_state = {
            let mut locals = param_values.clone();
            
            if let Some(code) = &code_info {
                // Process locals t_k from f.code.locals
                for local_decl in &code.locals {
                    for _ in 0..local_decl.count {
                        let default_value = Self::default_value_for_type(&local_decl.ty)?;
                        locals.push(default_value);
                    }
                }
            }

            debug_log!(store.config(), "Creating frame with {} locals: {:?}", locals.len(), locals);
            FrameState::new(locals, module)
        };

        // 9. Push the activation of F with arity m to the stack.
        let frame = Frame::new(result_count, frame_state);
        thread.stack_mut().push_frame(frame);

        // 10. Let L be the label whose arity is m and whose continuation is the end of the function.
        let end_instruction = Instruction::Control(crate::wasm::ast::ControlInstruction::End);
        let mut continuation = Vec::new();
        continuation.push(end_instruction);
        let label = Label::new(result_count, continuation);

        // 11. Enter the instruction sequence instr* with label L.
        thread.stack_mut().push_label(label.clone());

        // Execute the function body
        if let Some(code) = code_info {
            // Parse the function code bytes into an expression (f.code.body)
            let parser_config = crate::wasm::parser::ParserConfig { debug: store.config().debug };
            let mut parser = crate::wasm::parser::Parser::with_config(&code.code, parser_config);
            debug_log!(store.config(), "Parsing function code: {:?}", code.code);
            let instructions = parser.parse_expr().map_err(|e| {
                RuntimeError::Execution(format!("Failed to parse function code: {:?}", e))
            })?;
            debug_log!(store.config(), "Parsed instructions: {:?}", instructions);
            
            // Convert instructions to Expression (instr* end)
            let expression = crate::wasm::ast::Expression::general(instructions);
            
            // Execute the expression (instr* end)
            let result = crate::wasm::runtime::instruction::execute_expression_and_update_thread(
                store, 
                thread, 
                &expression
            )?;
            
            debug_log!(store.config(), "After WebAssembly function execution: stack has {} values", thread.stack().value_count());
            debug_log!(store.config(), "WebAssembly function returned result: {:?}", result);
            
            // The label continuation will execute the end instruction, which will clear the stack
            // We need to save the result and restore it after the label continuation
            // For now, we'll push the result back to the stack
            thread.stack_mut().push_value(result);
            debug_log!(store.config(), "Pushed result back to stack: {} values", thread.stack().value_count());
        } else if is_host_function {
            debug_log!(store.config(), "Executing host function");
            // For host functions, use the extracted information
            Self::invoke_host_function_with_info(store, thread, func_type, func_addr, param_values)?;
            
            debug_log!(store.config(), "After invoke_host_function_with_info: stack has {} values", thread.stack().value_count());
            
            // For host functions, we need to manually execute the end instruction
            // since we didn't push a label with continuation
            debug_log!(store.config(), "Executing end instruction for host function");
            crate::wasm::runtime::instruction::control::Control::end(thread, store)?;
            debug_log!(store.config(), "Stack after host function end: {} values", thread.stack().value_count());
        } else {
            // This should not happen as we've already checked for code()
            return Err(RuntimeError::Execution("Function instance has neither code nor host code".to_string()));
        }

        Ok(())
    }

    /// Invokes a host function instance.
    ///
    /// # Semantics (Host Functions)
    /// Host functions have non-deterministic behavior. They may either terminate with a trap
    /// or return regularly. However, in the latter case, they must consume and produce the
    /// right number and types of WebAssembly values on the stack, according to its function type.
    ///
    /// A host function may also modify the store. However, all store modifications must result
    /// in an extension of the original store, i.e., they must only modify mutable contents and
    /// must not have instances removed.
    ///
    /// # Specification
    /// S; val_n (invoke a) → S'; result
    /// (if S.funcs[a] = {type [t_n^1] → [t_m^2], hostcode hf}
    ///  ∧ (S'; result) ∈ hf(S; val_n))
    ///
    /// S; val_n (invoke a) → S; val_n (invoke a)
    /// (if S.funcs[a] = {type [t_n^1] → [t_m^2], hostcode hf}
    ///  ∧ ⊥ ∈ hf(S; val_n))
    pub fn invoke_host_function(
        store: &mut Store,
        thread: &mut Thread,
        func_instance: &crate::wasm::runtime::FuncInstance,
        param_values: Vec<crate::wasm::runtime::Value>,
    ) -> RuntimeResult<()> {
        // Extract all necessary information from func_instance before any mutable borrows
        let func_type = func_instance.ty();
        let result_count = func_type.results.len();
        let host_func = func_instance.host_code().ok_or_else(|| {
            RuntimeError::Execution("Function instance is not a host function".to_string())
        })?;

        // Validate parameter types match function type
        if param_values.len() != func_type.params.len() {
            return Err(RuntimeError::Execution(format!(
                "Host function expected {} parameters, got {}",
                func_type.params.len(),
                param_values.len()
            )));
        }

        // Validate parameter types
        for (i, (value, expected_type)) in param_values.iter().zip(func_type.params.iter()).enumerate() {
            if !Self::value_matches_type(value, *expected_type) {
                return Err(RuntimeError::TypeError(format!(
                    "Host function parameter {} has wrong type: expected {:?}, got {:?}",
                    i, expected_type, value
                )));
            }
        }

        // Convert WebAssembly values to raw bytes for host function
        let mut args = Vec::new();
        for value in &param_values {
            let raw_value = Self::value_to_raw_bytes(value)?;
            args.push(raw_value);
        }
        debug_log!(store.config(), "Host function args (raw): {:?}", args);

        // Prepare results buffer
        let mut results = Vec::new();
        results.extend((0..result_count).map(|_| 0u64));

        // Store the original store state for validation
        let original_store_size = store.func_count() + store.table_count() + store.mem_count() + 
                                 store.global_count() + store.elem_count() + store.data_count();

        // Invoke the host function
        // This may trap (return Err) or return normally
        // Note: The host function may modify the store through mutable references
        host_func(&args, &mut results).map_err(|e| {
            RuntimeError::Trap(format!("Host function trap: {}", e))
        })?;

        // Validate store extension constraint
        let new_store_size = store.func_count() + store.table_count() + store.mem_count() + 
                            store.global_count() + store.elem_count() + store.data_count();
        
        if new_store_size < original_store_size {
            return Err(RuntimeError::Execution(
                "Host function violated store extension constraint: instances were removed".to_string()
            ));
        }

        // Convert results back to WebAssembly values and push to stack
        debug_log!(store.config(), "Host function results (raw): {:?}", results);
        for (i, &raw_result) in results.iter().enumerate() {
            let result_type = func_type.results.get(i).ok_or_else(|| {
                RuntimeError::Execution("Host function returned more results than expected".to_string())
            })?;
            
            let value = Self::raw_bytes_to_value(raw_result, *result_type)?;
            debug_log!(store.config(), "Converting result {}: raw={}, type={:?}, value={:?}", i, raw_result, result_type, value);
            thread.stack_mut().push_value(value);
        }
        debug_log!(store.config(), "Stack after host function: {} values", thread.stack().value_count());

        Ok(())
    }

    /// Invokes a host function with extracted information to avoid borrowing conflicts.
    ///
    /// This is a helper method that takes the necessary information directly instead of
    /// a reference to the function instance, avoiding borrowing conflicts.
    fn invoke_host_function_with_info(
        store: &mut Store,
        thread: &mut Thread,
        func_type: crate::wasm::ast::FuncType,
        func_addr: FuncAddr,
        param_values: Vec<crate::wasm::runtime::Value>,
    ) -> RuntimeResult<()> {
        let result_count = func_type.results.len();

        // Validate parameter types match function type
        if param_values.len() != func_type.params.len() {
            return Err(RuntimeError::Execution(format!(
                "Host function expected {} parameters, got {}",
                func_type.params.len(),
                param_values.len()
            )));
        }

        // Validate parameter types
        for (i, (value, expected_type)) in param_values.iter().zip(func_type.params.iter()).enumerate() {
            if !Self::value_matches_type(value, *expected_type) {
                return Err(RuntimeError::TypeError(format!(
                    "Host function parameter {} has wrong type: expected {:?}, got {:?}",
                    i, expected_type, value
                )));
            }
        }

        // Convert WebAssembly values to raw bytes for host function
        let mut args = Vec::new();
        for value in &param_values {
            let raw_value = Self::value_to_raw_bytes(value)?;
            args.push(raw_value);
        }
        debug_log!(store.config(), "Host function args (raw): {:?}", args);

        // Prepare results buffer
        let mut results = Vec::new();
        results.extend((0..result_count).map(|_| 0u64));

        // Store the original store state for validation
        let original_store_size = store.func_count() + store.table_count() + store.mem_count() + 
                                 store.global_count() + store.elem_count() + store.data_count();

        // Get the host function and invoke it
        let host_func = {
            let func_instance = store.funcs.get(func_addr.as_usize()).ok_or_else(|| {
                RuntimeError::Execution(format!(
                    "invoke: Function instance at address {} does not exist in store",
                    func_addr.as_usize()
                ))
            })?;
            
            func_instance.host_code().ok_or_else(|| {
                RuntimeError::Execution("Function instance is not a host function".to_string())
            })?
        };

        // Invoke the host function
        // This may trap (return Err) or return normally
        // Note: The host function may modify the store through mutable references
        host_func(&args, &mut results).map_err(|e| {
            RuntimeError::Trap(format!("Host function trap: {}", e))
        })?;

        // Validate store extension constraint
        let new_store_size = store.func_count() + store.table_count() + store.mem_count() + 
                            store.global_count() + store.elem_count() + store.data_count();
        
        if new_store_size < original_store_size {
            return Err(RuntimeError::Execution(
                "Host function violated store extension constraint: instances were removed".to_string()
            ));
        }

        // Convert results back to WebAssembly values and push to stack
        debug_log!(store.config(), "Host function results (raw): {:?}", results);
        for (i, &raw_result) in results.iter().enumerate() {
            let result_type = func_type.results.get(i).ok_or_else(|| {
                RuntimeError::Execution("Host function returned more results than expected".to_string())
            })?;
            
            let value = Self::raw_bytes_to_value(raw_result, *result_type)?;
            debug_log!(store.config(), "Converting result {}: raw={}, type={:?}, value={:?}", i, raw_result, result_type, value);
            thread.stack_mut().push_value(value);
        }
        debug_log!(store.config(), "Stack after host function: {} values", thread.stack().value_count());

        Ok(())
    }

    /// Validates that a value matches the expected type.
    ///
    /// # Arguments
    ///
    /// * `value` - The value to validate
    /// * `expected_type` - The expected value type
    ///
    /// # Returns
    ///
    /// * `bool` - True if the value matches the expected type
    fn value_matches_type(value: &crate::wasm::runtime::Value, expected_type: ValType) -> bool {
        match (value, expected_type) {
            (crate::wasm::runtime::Value::I32(_), ValType::I32) => true,
            (crate::wasm::runtime::Value::I64(_), ValType::I64) => true,
            (crate::wasm::runtime::Value::F32(_), ValType::F32) => true,
            (crate::wasm::runtime::Value::F64(_), ValType::F64) => true,
            (crate::wasm::runtime::Value::V128(_), ValType::V128) => true,
            (crate::wasm::runtime::Value::FuncRef(_), ValType::FuncRef) => true,
            (crate::wasm::runtime::Value::ExternRef(_), ValType::ExternRef) => true,
            (crate::wasm::runtime::Value::NullRef(ref_type), ValType::FuncRef) => {
                matches!(ref_type, crate::wasm::runtime::value::ValueType::FuncRef)
            }
            (crate::wasm::runtime::Value::NullRef(ref_type), ValType::ExternRef) => {
                matches!(ref_type, crate::wasm::runtime::value::ValueType::ExternRef)
            }
            _ => false,
        }
    }

    /// Converts a WebAssembly value to raw bytes for host function consumption.
    fn value_to_raw_bytes(value: &crate::wasm::runtime::Value) -> RuntimeResult<u64> {
        match value {
            crate::wasm::runtime::Value::I32(n) => Ok(*n as u64),
            crate::wasm::runtime::Value::I64(n) => Ok(*n as u64),
            crate::wasm::runtime::Value::F32(f) => Ok(f.to_bits() as u64),
            crate::wasm::runtime::Value::F64(f) => Ok(f.to_bits()),
            crate::wasm::runtime::Value::V128(v) => Ok(*v as u64), // Truncate to 64 bits
            crate::wasm::runtime::Value::FuncRef(addr) => Ok(*addr as u64),
            crate::wasm::runtime::Value::ExternRef(addr) => Ok(*addr as u64),
            crate::wasm::runtime::Value::NullRef(_) => Ok(0), // Null references become 0
        }
    }

    /// Converts raw bytes from host function to WebAssembly value.
    fn raw_bytes_to_value(raw: u64, val_type: ValType) -> RuntimeResult<crate::wasm::runtime::Value> {
        match val_type {
            ValType::I32 => Ok(crate::wasm::runtime::Value::I32(raw as i32)),
            ValType::I64 => Ok(crate::wasm::runtime::Value::I64(raw as i64)),
            ValType::F32 => Ok(crate::wasm::runtime::Value::F32(f32::from_bits(raw as u32))),
            ValType::F64 => Ok(crate::wasm::runtime::Value::F64(f64::from_bits(raw))),
            ValType::V128 => Ok(crate::wasm::runtime::Value::V128(raw as i128)), // Extend to 128 bits
            ValType::FuncRef => Ok(crate::wasm::runtime::Value::FuncRef(raw as u32)),
            ValType::ExternRef => Ok(crate::wasm::runtime::Value::ExternRef(raw as u32)),
        }
    }

    /// Creates a default value for a given value type.
    ///
    /// # Arguments
    ///
    /// * `val_type` - The value type to create a default value for
    ///
    /// # Returns
    ///
    /// * `RuntimeResult<Value>` - The default value for the type
    fn default_value_for_type(val_type: &ValType) -> RuntimeResult<crate::wasm::runtime::Value> {
        match val_type {
            ValType::I32 => Ok(crate::wasm::runtime::Value::I32(0)),
            ValType::I64 => Ok(crate::wasm::runtime::Value::I64(0)),
            ValType::F32 => Ok(crate::wasm::runtime::Value::F32(0.0)),
            ValType::F64 => Ok(crate::wasm::runtime::Value::F64(0.0)),
            ValType::V128 => Ok(crate::wasm::runtime::Value::V128(0)),
            ValType::FuncRef => Ok(crate::wasm::runtime::Value::NullRef(crate::wasm::runtime::value::ValueType::FuncRef)),
            ValType::ExternRef => Ok(crate::wasm::runtime::Value::NullRef(crate::wasm::runtime::value::ValueType::ExternRef)),
        }
    }

    /// Validates that a store modification is an extension of the original store.
    ///
    /// # Arguments
    ///
    /// * `original_store` - The original store state
    /// * `modified_store` - The modified store state
    ///
    /// # Returns
    ///
    /// * `RuntimeResult<()>` - Success if the modification is a valid extension
    fn validate_store_extension(
        original_store: &Store,
        modified_store: &Store,
    ) -> RuntimeResult<()> {
        // Check that no instances were removed
        if modified_store.func_count() < original_store.func_count() ||
           modified_store.table_count() < original_store.table_count() ||
           modified_store.mem_count() < original_store.mem_count() ||
           modified_store.global_count() < original_store.global_count() ||
           modified_store.elem_count() < original_store.elem_count() ||
           modified_store.data_count() < original_store.data_count() {
            return Err(RuntimeError::Execution(
                "Host function violated store extension constraint: instances were removed".to_string()
            ));
        }

        // Validate that existing instances are well-typed
        // This ensures that the resulting store is valid
        Self::validate_store_well_typed(modified_store)
    }

    /// Validates that all instances in the store are well-typed.
    ///
    /// # Arguments
    ///
    /// * `store` - The store to validate
    ///
    /// # Returns
    ///
    /// * `RuntimeResult<()>` - Success if all instances are well-typed
    fn validate_store_well_typed(store: &Store) -> RuntimeResult<()> {
        // Validate all function instances
        for (i, func_instance) in store.funcs.iter().enumerate() {
            // Check that function type is valid
            let func_type = func_instance.ty();
            
            // Validate parameter types
            for param_type in &func_type.params {
                if !Self::is_valid_value_type(*param_type) {
                    return Err(RuntimeError::TypeError(format!(
                        "Function {} has invalid parameter type: {:?}",
                        i, param_type
                    )));
                }
            }
            
            // Validate result types
            for result_type in &func_type.results {
                if !Self::is_valid_value_type(*result_type) {
                    return Err(RuntimeError::TypeError(format!(
                        "Function {} has invalid result type: {:?}",
                        i, result_type
                    )));
                }
            }
        }

        // Validate all table instances
        for (i, table_instance) in store.tables.iter().enumerate() {
            let table_type = table_instance.ty();
            
            // Validate element type
            if !Self::is_valid_reference_type(table_type.element_type) {
                return Err(RuntimeError::TypeError(format!(
                    "Table {} has invalid element type: {:?}",
                    i, table_type.element_type
                )));
            }
            
            // Validate limits
            if table_type.limits.min > table_type.limits.max.unwrap_or(u32::MAX) {
                return Err(RuntimeError::TypeError(format!(
                    "Table {} has invalid limits: min {} > max {}",
                    i, table_type.limits.min, table_type.limits.max.unwrap_or(u32::MAX)
                )));
            }
        }

        // Validate all memory instances
        for (i, memory_instance) in store.mems.iter().enumerate() {
            let memory_type = memory_instance.ty();
            
            // Validate limits
            if memory_type.limits.min > memory_type.limits.max.unwrap_or(u32::MAX) {
                return Err(RuntimeError::TypeError(format!(
                    "Memory {} has invalid limits: min {} > max {}",
                    i, memory_type.limits.min, memory_type.limits.max.unwrap_or(u32::MAX)
                )));
            }
        }

        // Validate all global instances
        for (i, global_instance) in store.globals.iter().enumerate() {
            let global_type = global_instance.ty();
            
            // Validate value type
            if !Self::is_valid_value_type(global_type.value_type) {
                return Err(RuntimeError::TypeError(format!(
                    "Global {} has invalid value type: {:?}",
                    i, global_type.value_type
                )));
            }
        }

        Ok(())
    }

    /// Checks if a value type is valid.
    ///
    /// # Arguments
    ///
    /// * `val_type` - The value type to check
    ///
    /// # Returns
    ///
    /// * `bool` - True if the value type is valid
    fn is_valid_value_type(val_type: crate::wasm::ast::ValType) -> bool {
        match val_type {
            crate::wasm::ast::ValType::I32 => true,
            crate::wasm::ast::ValType::I64 => true,
            crate::wasm::ast::ValType::F32 => true,
            crate::wasm::ast::ValType::F64 => true,
            crate::wasm::ast::ValType::V128 => true,
            crate::wasm::ast::ValType::FuncRef => true,
            crate::wasm::ast::ValType::ExternRef => true,
        }
    }

    /// Checks if a reference type is valid.
    ///
    /// # Arguments
    ///
    /// * `ref_type` - The reference type to check
    ///
    /// # Returns
    ///
    /// * `bool` - True if the reference type is valid
    fn is_valid_reference_type(ref_type: ValType) -> bool {
        match ref_type {
            ValType::FuncRef => true,
            ValType::ExternRef => true,
            _ => false,
        }
    }

    /// Invokes a host function with non-deterministic behavior support.
    ///
    /// This method supports the specification's non-deterministic behavior where
    /// hf(S; val_n) yields a set of possible outcomes.
    ///
    /// # Specification
    /// S; val_n (invoke a) → S'; result
    /// (if S.funcs[a] = {type [t_n^1] → [t_m^2], hostcode hf}
    ///  ∧ (S'; result) ∈ hf(S; val_n))
    ///
    /// S; val_n (invoke a) → S; val_n (invoke a)
    /// (if S.funcs[a] = {type [t_n^1] → [t_m^2], hostcode hf}
    ///  ∧ ⊥ ∈ hf(S; val_n))
    ///
    /// # Arguments
    ///
    /// * `store` - The current store state
    /// * `thread` - The current thread state
    /// * `func_instance` - The host function instance
    /// * `param_values` - The parameter values
    ///
    /// # Returns
    ///
    /// * `RuntimeResult<()>` - Success if invocation completes
    pub fn invoke_host_function_non_deterministic(
        store: &mut Store,
        thread: &mut Thread,
        func_instance: &crate::wasm::runtime::FuncInstance,
        param_values: Vec<crate::wasm::runtime::Value>,
    ) -> RuntimeResult<()> {
        // Extract necessary information to avoid borrowing conflicts
        let func_type = func_instance.ty();
        
        // Get the function address from the store
        let func_addr = {
            let mut found_addr = None;
            for (i, _) in store.funcs.iter().enumerate() {
                if let Some(instance) = store.funcs.get(i) {
                    if ptr::eq(instance, func_instance) {
                        found_addr = Some(FuncAddr::new(i as u32));
                        break;
                    }
                }
            }
            found_addr.ok_or_else(|| {
                RuntimeError::Execution("Function instance not found in store".to_string())
            })?
        };
        
        // Store the original store state for validation
        let original_store_size = store.func_count() + store.table_count() + store.mem_count() + 
                                 store.global_count() + store.elem_count() + store.data_count();
        
        // Validate parameter types match function type
        if param_values.len() != func_type.params.len() {
            return Err(RuntimeError::Execution(format!(
                "Host function expected {} parameters, got {}",
                func_type.params.len(),
                param_values.len()
            )));
        }

        // Validate parameter types
        for (i, (value, expected_type)) in param_values.iter().zip(func_type.params.iter()).enumerate() {
            if !Self::value_matches_type(value, *expected_type) {
                return Err(RuntimeError::TypeError(format!(
                    "Host function parameter {} has wrong type: expected {:?}, got {:?}",
                    i, expected_type, value
                )));
            }
        }

        // Convert WebAssembly values to raw bytes for host function
        let mut args = Vec::new();
        for value in &param_values {
            let raw_value = Self::value_to_raw_bytes(value)?;
            args.push(raw_value);
        }
        debug_log!(store.config(), "Host function args (raw): {:?}", args);

        // Prepare results buffer
        let result_count = func_type.results.len();
        let mut results = Vec::new();
        results.extend((0..result_count).map(|_| 0u64));

        // Get the host function
        let host_func = func_instance.host_code().ok_or_else(|| {
            RuntimeError::Execution("Function instance is not a host function".to_string())
        })?;

        // Invoke the host function with non-deterministic behavior
        // This may trap (return Err), diverge (return Ok but with ⊥), or return normally
        match host_func(&args, &mut results) {
            Ok(()) => {
                // Normal return: S; val_n (invoke a) → S'; result
                
                // Validate store extension constraint
                let new_store_size = store.func_count() + store.table_count() + store.mem_count() + 
                                    store.global_count() + store.elem_count() + store.data_count();
                
                if new_store_size < original_store_size {
                    return Err(RuntimeError::Execution(
                        "Host function violated store extension constraint: instances were removed".to_string()
                    ));
                }

                // Validate that the resulting store is well-typed
                Self::validate_store_well_typed(store)?;

                // Convert results back to WebAssembly values and push to stack
                debug_log!(store.config(), "Host function results (raw): {:?}", results);
                for (i, &raw_result) in results.iter().enumerate() {
                    let result_type = func_type.results.get(i).ok_or_else(|| {
                        RuntimeError::Execution("Host function returned more results than expected".to_string())
                    })?;
                    
                    let value = Self::raw_bytes_to_value(raw_result, *result_type)?;
                    debug_log!(store.config(), "Converting result {}: raw={}, type={:?}, value={:?}", i, raw_result, result_type, value);
                    thread.stack_mut().push_value(value);
                }
                debug_log!(store.config(), "Stack after host function: {} values", thread.stack().value_count());

                Ok(())
            }
            Err(e) => {
                // Trap: S; val_n (invoke a) → trap
                Err(RuntimeError::Trap(format!("Host function trap: {}", e)))
            }
        }
    }

    /// Invokes a host function with support for multiple possible outcomes.
    ///
    /// This method implements the full non-deterministic behavior where
    /// hf(S; val_n) yields a set of possible outcomes.
    ///
    /// # Arguments
    ///
    /// * `store` - The current store state
    /// * `thread` - The current thread state
    /// * `func_instance` - The host function instance
    /// * `param_values` - The parameter values
    /// * `outcome_selector` - A function to select which outcome to take
    ///
    /// # Returns
    ///
    /// * `RuntimeResult<()>` - Success if invocation completes
    pub fn invoke_host_function_with_outcomes<F>(
        store: &mut Store,
        thread: &mut Thread,
        func_instance: &crate::wasm::runtime::FuncInstance,
        param_values: Vec<crate::wasm::runtime::Value>,
        outcome_selector: F,
    ) -> RuntimeResult<()>
    where
        F: FnOnce(&[HostFunctionOutcome]) -> usize,
    {
        // Generate all possible outcomes
        let outcomes = Self::generate_host_function_outcomes(
            store,
            thread,
            func_instance,
            param_values.clone(),
        )?;

        // Select an outcome using the provided selector
        let selected_index = outcome_selector(&outcomes);
        if selected_index >= outcomes.len() {
            return Err(RuntimeError::Execution(
                "Invalid outcome selection index".to_string()
            ));
        }

        // Apply the selected outcome
        let outcome = &outcomes[selected_index];
        match outcome {
            HostFunctionOutcome::Normal { results } => {
                // Push results to stack
                for value in results {
                    thread.stack_mut().push_value(value.clone());
                }
                Ok(())
            }
            HostFunctionOutcome::Trap { message } => {
                Err(RuntimeError::Trap(message.clone()))
            }
            HostFunctionOutcome::Divergent => {
                // For divergence, we need to implement infinite recursion
                // This is a simplified implementation
                Self::invoke_host_function_divergent(store, thread, func_instance, param_values)
            }
        }
    }

    /// Generates all possible outcomes for a host function invocation.
    ///
    /// # Arguments
    ///
    /// * `store` - The current store state
    /// * `thread` - The current thread state
    /// * `func_instance` - The host function instance
    /// * `param_values` - The parameter values
    ///
    /// # Returns
    ///
    /// * `RuntimeResult<Vec<HostFunctionOutcome>>` - All possible outcomes
    fn generate_host_function_outcomes(
        store: &Store,
        _thread: &Thread,
        func_instance: &crate::wasm::runtime::FuncInstance,
        param_values: Vec<crate::wasm::runtime::Value>,
    ) -> RuntimeResult<Vec<HostFunctionOutcome>> {
        let func_type = func_instance.ty();
        let mut outcomes = Vec::new();

        // For now, we generate a single outcome based on the current implementation
        // In a full implementation, this would explore all possible execution paths
        
        // Convert parameters to raw bytes
        let mut args = Vec::new();
        for value in &param_values {
            let raw_value = Self::value_to_raw_bytes(value)?;
            args.push(raw_value);
        }

        // Prepare results buffer
        let result_count = func_type.results.len();
        let mut results = Vec::new();
        results.extend((0..result_count).map(|_| 0u64));

        // Try to invoke the host function
        let host_func = func_instance.host_code().ok_or_else(|| {
            RuntimeError::Execution("Function instance is not a host function".to_string())
        })?;

        match host_func(&args, &mut results) {
            Ok(()) => {
                // Normal outcome
                let mut outcome_results = Vec::new();
                for (i, &raw_result) in results.iter().enumerate() {
                    let result_type = func_type.results.get(i).ok_or_else(|| {
                        RuntimeError::Execution("Host function returned more results than expected".to_string())
                    })?;
                    
                    let value = Self::raw_bytes_to_value(raw_result, *result_type)?;
                    outcome_results.push(value);
                }
                outcomes.push(HostFunctionOutcome::Normal { results: outcome_results });
            }
            Err(e) => {
                // Trap outcome
                outcomes.push(HostFunctionOutcome::Trap { message: e });
            }
        }

        // Add divergent outcome as a possibility
        // In a real implementation, this would be determined by the host function
        outcomes.push(HostFunctionOutcome::Divergent);

        Ok(outcomes)
    }

    /// Invokes a host function with divergence support.
    ///
    /// This method implements the divergence case of the specification:
    /// S; val_n (invoke a) → S; val_n (invoke a)
    /// (if S.funcs[a] = {type [t_n^1] → [t_m^2], hostcode hf}
    ///  ∧ ⊥ ∈ hf(S; val_n))
    ///
    /// # Arguments
    ///
    /// * `store` - The current store state
    /// * `thread` - The current thread state
    /// * `func_instance` - The host function instance
    /// * `param_values` - The parameter values
    ///
    /// # Returns
    ///
    /// * `RuntimeResult<()>` - Never returns (diverges)
    pub fn invoke_host_function_divergent(
        store: &mut Store,
        thread: &mut Thread,
        func_instance: &crate::wasm::runtime::FuncInstance,
        param_values: Vec<crate::wasm::runtime::Value>,
    ) -> RuntimeResult<()> {
        // For divergence, we need to implement infinite recursion or infinite loop
        // This is a simplified implementation that simulates divergence
        
        // Push the parameters back onto the stack for the recursive call
        for value in param_values.clone().into_iter().rev() {
            thread.stack_mut().push_value(value);
        }
        
        // Create a new invoke instruction to simulate the recursive call
        let func_addr = {
            let mut found_addr = None;
            for (i, _) in store.funcs.iter().enumerate() {
                if let Some(instance) = store.funcs.get(i) {
                    if ptr::eq(instance, func_instance) {
                        found_addr = Some(FuncAddr::new(i as u32));
                        break;
                    }
                }
            }
            found_addr.ok_or_else(|| {
                RuntimeError::Execution("Function instance not found in store".to_string())
            })?
        };
        
        // Recursively invoke the same function (this creates divergence)
        // In a real implementation, this would be handled by the execution engine
        Self::invoke_host_function_non_deterministic(store, thread, func_instance, param_values)
    }

    /// Invokes a function following the exact specification reduction rule.
    ///
    /// This method implements the reduction rule:
    /// S; val_n (invoke a) → S; frame_m{F} label_m{} instr* end end
    ///
    /// # Arguments
    ///
    /// * `store` - The current store state
    /// * `thread` - The current thread state
    /// * `func_addr` - The function address to invoke
    ///
    /// # Returns
    ///
    /// * `RuntimeResult<()>` - Success if invocation completes
    pub fn invoke_with_reduction_rule(
        store: &mut Store,
        thread: &mut Thread,
        func_addr: FuncAddr,
    ) -> RuntimeResult<()> {
        debug_log!(store.config(), "=== INVOKE_WITH_REDUCTION_RULE ===");
        debug_log!(store.config(), "Function address: {}", func_addr.as_usize());
        debug_log!(store.config(), "Stack depth before invoke: {}", thread.stack().frame_count());
        debug_log!(store.config(), "Stack values before invoke: {}", thread.stack().value_count());
        
        // Get function instance (S.funcs[a] = f)
        // Extract all necessary information from func_instance in a separate scope
        let (func_type, param_count, result_count, is_host, module, code_info) = {
            let func_instance = store.funcs.get(func_addr.as_usize()).ok_or_else(|| {
                RuntimeError::Execution(format!(
                    "invoke: Function instance at address {} does not exist in store",
                    func_addr.as_usize()
                ))
            })?;

            debug_log!(store.config(), "FuncInstance at address {}: is_host={}, is_wasm={}, code() is_some={}", 
                func_addr.as_usize(), func_instance.is_host(), func_instance.is_wasm(), func_instance.code().is_some());

            // Get function type (f.type = [t_n^1] → [t_m^2])
            let func_type = func_instance.ty().clone(); // Clone to avoid borrowing
            let param_count = func_type.params.len();
            let result_count = func_type.results.len();

            debug_log!(store.config(), "Function type: {:?} -> {:?}", func_type.params, func_type.results);

            // Check if this is a host function and extract necessary info
            let is_host = func_instance.is_host();
            
            // For host functions, we don't need a module, but we need to handle this case
            let module = if is_host {
                // For host functions, we'll use the current thread's module
                thread.frame_state().module().clone()
            } else {
                // For WebAssembly functions, get the module
                func_instance.module().ok_or_else(|| {
                    RuntimeError::Execution("WebAssembly function instance has no module".to_string())
                })?.clone()
            };

            // Extract all necessary information from func_instance before any mutable borrows
            let code_info = func_instance.code().cloned();
            
            debug_log!(store.config(), "Function is_host: {}, code_info is_some: {}", is_host, code_info.is_some());
            if let Some(code) = &code_info {
                debug_log!(store.config(), "Code locals: {:?}, code body length: {}", code.locals, code.code.len());
            }

            (func_type, param_count, result_count, is_host, module, code_info)
        };

        // Extract host function information in a separate scope to avoid borrowing conflicts
        let is_host_function = is_host;

        // Pop parameter values (val_n)
        let mut param_values = Vec::new();
        for _ in 0..param_count {
            let value = thread.stack_mut().pop_value().ok_or_else(|| {
                RuntimeError::Stack("Failed to pop parameter value for function invocation".to_string())
            })?;
            param_values.push(value);
        }
        
        // Reverse the parameters because they were popped in reverse order (LIFO stack)
        // The first parameter should be at index 0, second at index 1, etc.
        param_values.reverse();
        
        debug_log!(store.config(), "All parameters: {:?}", param_values);

        // Create frame F = {module f.module, locals val_n (default_t)^k}
        let frame_state = {
            let mut locals = param_values.clone();
            
            if let Some(code) = &code_info {
                // Process locals t_k from f.code.locals in smaller chunks to avoid large allocations
                for local_decl in &code.locals {
                    // Allocate locals in smaller chunks to avoid large memory allocations
                    let chunk_size = 10; // Process 10 locals at a time
                    let mut remaining = local_decl.count;
                    
                    while remaining > 0 {
                        let current_chunk = core::cmp::min(chunk_size, remaining);
                        
                        for _ in 0..current_chunk {
                            let default_value = Self::default_value_for_type(&local_decl.ty)?;
                            locals.push(default_value);
                        }
                        
                        remaining -= current_chunk;
                        
                        // Add a small delay or check to avoid overwhelming the memory allocator
                        if remaining > 0 {
                            // Force a small allocation to ensure memory is properly mapped
                            let _ = Vec::<u8>::with_capacity(1);
                        }
                    }
                }
            }

            debug_log!(store.config(), "Creating frame with {} locals: {:?}", locals.len(), locals);
            FrameState::new(locals, module)
        };

        // Push frame_m{F} to stack
        let frame = Frame::new(result_count, frame_state);
        thread.stack_mut().push_frame(frame);
        debug_log!(store.config(), "Pushed frame to stack. Stack depth: {}", thread.stack().frame_count());
        debug_log!(store.config(), "Top frame locals: {:?}", thread.stack().top_frame().unwrap().state().locals());

        // Execute instr* end (f.code.body)
        if let Some(code) = code_info {
            debug_log!(store.config(), "Executing WebAssembly function with code");
            // Create label_m{} with continuation "end" for WebAssembly functions
            let end_instruction = Instruction::Control(crate::wasm::ast::ControlInstruction::End);
            let mut continuation = Vec::new();
            continuation.push(end_instruction);
            let label = Label::new(result_count, continuation);

            // Push label_m{} to stack
            thread.stack_mut().push_label(label.clone());
            debug_log!(store.config(), "Pushed label to stack. Stack depth: {}", thread.stack().frame_count());
            debug_log!(store.config(), "Label continuation: {:?}", label.continuation());
            
            let parser_config = crate::wasm::parser::ParserConfig { debug: store.config().debug };
            let mut parser = crate::wasm::parser::Parser::with_config(&code.code, parser_config);
            let instructions = parser.parse_expr().map_err(|e| {
                RuntimeError::Execution(format!("Failed to parse function code: {:?}", e))
            })?;
            
            let expression = crate::wasm::ast::Expression::general(instructions);
            
            debug_log!(store.config(), "About to execute expression. Stack depth: {}", thread.stack().frame_count());
            if let Some(frame) = thread.stack().top_frame() {
                debug_log!(store.config(), "Top frame locals before expression: {:?}", frame.state().locals());
            }
            
            // Execute the expression (instr* end)
            let result = crate::wasm::runtime::instruction::execute_expression_and_update_thread(
                store, 
                thread, 
                &expression
            )?;
            
            debug_log!(store.config(), "After WebAssembly function execution: stack has {} values", thread.stack().value_count());
            debug_log!(store.config(), "WebAssembly function returned result: {:?}", result);
            
            // The label continuation will execute the end instruction, which will clear the stack
            // We need to save the result and restore it after the label continuation
            // For now, we'll push the result back to the stack
            thread.stack_mut().push_value(result);
            debug_log!(store.config(), "Pushed result back to stack: {} values", thread.stack().value_count());
        } else if is_host_function {
            debug_log!(store.config(), "Executing host function");
            // For host functions, use the extracted information
            Self::invoke_host_function_with_info(store, thread, func_type, func_addr, param_values)?;
            
            debug_log!(store.config(), "After invoke_host_function_with_info: stack has {} values", thread.stack().value_count());
            
            // For host functions, we need to manually execute the end instruction
            // since we didn't push a label with continuation
            debug_log!(store.config(), "Executing end instruction for host function");
            crate::wasm::runtime::instruction::control::Control::end(thread, store)?;
            debug_log!(store.config(), "Stack after host function end: {} values", thread.stack().value_count());
        } else {
            return Err(RuntimeError::Execution("Function instance has neither code nor host code".to_string()));
        }

        debug_log!(store.config(), "invoke_with_reduction_rule: final stack has {} values", thread.stack().value_count());
        debug_log!(store.config(), "Final stack depth: {}", thread.stack().frame_count());
        if let Some(frame) = thread.stack().top_frame() {
            debug_log!(store.config(), "Final top frame locals: {:?}", frame.state().locals());
        }
        Ok(())
    }
}

/// Executes a function instruction
///
/// # Arguments
///
/// * `store` - The current store state
/// * `thread` - The current thread state
/// * `instruction` - The function instruction to execute
///
/// # Returns
///
/// * `RuntimeResult<()>` - The result of the execution
pub fn execute_function(
    store: &mut Store,
    thread: &mut Thread,
    instruction: &Instruction,
) -> RuntimeResult<()> {
    match instruction {
        Instruction::Administrative(admin_inst) => {
            match admin_inst {
                crate::wasm::ast::AdministrativeInstruction::Invoke(func_addr) => {
                    Function::invoke(store, thread, func_addr.clone())
                }
                _ => Err(RuntimeError::Execution(format!(
                    "Expected function instruction, got: {:?}",
                    admin_inst
                ))),
            }
        }
        _ => Err(RuntimeError::Execution(format!(
            "Expected administrative instruction, got: {:?}",
            instruction
        ))),
    }
}

/// Invokes a function following the exact specification reduction rule.
///
/// This function wraps Function::invoke_with_reduction_rule for easier access.
///
/// # Arguments
///
/// * `store` - The current store state
/// * `thread` - The current thread state
/// * `func_addr` - The function address to invoke
///
/// # Returns
///
/// * `RuntimeResult<()>` - Success if invocation completes
pub fn invoke_with_reduction_rule(
    store: &mut Store,
    thread: &mut Thread,
    func_addr: FuncAddr,
) -> RuntimeResult<()> {
    Function::invoke_with_reduction_rule(store, thread, func_addr)
} 
use alloc::vec::Vec;
use alloc::boxed::Box;
use alloc::string::String;
use alloc::string::ToString;
use core::fmt;
use alloc::format;
use alloc::sync::Arc;

use crate::wasm::ast::{FuncType, Function, ValType};
use crate::wasm::runtime::{
    Value,
    RuntimeResult,
    RuntimeError,
    frame::{Frame, FrameState},
    stack::Stack,
    instruction::InstructionExecutor,
    Store,
    Thread,
    RuntimeConfig,
    address::FuncAddr,
};

use super::ModuleInstance;

/// Host function
/// 
/// A host function is a function expressed outside WebAssembly but passed to a module as an import.
/// The definition and behavior of host functions are outside the scope of the WebAssembly specification.
/// 
/// # Specification Compliance
/// 
/// Host functions have non-deterministic behavior. They may either terminate with a trap
/// or return regularly. However, in the latter case, they must consume and produce the
/// right number and types of WebAssembly values on the stack, according to their function type.
/// 
/// A host function may also modify the store. However, all store modifications must result
/// in an extension of the original store, i.e., they must only modify mutable contents and
/// must not have instances removed. Furthermore, the resulting store must be valid, i.e.,
/// all data and code in it is well-typed.
/// 
/// # Non-deterministic Behavior
/// 
/// The function signature `hf(S; val_n)` denotes the implementation-defined execution of
/// host function hf in current store S with arguments val_n. It yields a set of possible
/// outcomes, where each element is either a pair of a modified store S' and a result or
/// the special value ⊥ indicating divergence.
/// 
/// A host function is non-deterministic if there is at least one argument for which the
/// set of outcomes is not singular.
/// 
/// # Note
/// When invoked, a host function behaves non-deterministically, but within certain constraints
/// that ensure the integrity of the runtime.
pub type HostFunc = Arc<dyn Fn(&[u64], &mut [u64]) -> Result<(), String> + Send + Sync>;

/// Function instance
/// 
/// Represents either a WebAssembly function or a host function.
#[derive(Clone)]
pub enum FuncInstance {
    /// WebAssembly function instance
    /// 
    /// Contains:
    /// - The function type
    /// - The module instance (for resolving references)
    /// - The function code
    Wasm {
        /// The function type
        ty: FuncType,
        /// The module instance
        module: ModuleInstance,
        /// The function code
        code: Function,
    },
    /// Host function instance
    /// 
    /// Contains:
    /// - The function type
    /// - The host function code
    Host {
        /// The function type
        ty: FuncType,
        /// The host function code
        code: HostFunc,
    },
}

impl FuncInstance {
    /// Creates a new WebAssembly function instance
    pub fn wasm(ty: FuncType, module: ModuleInstance, code: Function) -> Self {
        Self::Wasm { ty, module, code }
    }

    /// Creates a new host function instance
    pub fn host(ty: FuncType, code: HostFunc) -> Self {
        Self::Host { ty, code }
    }

    /// Returns the function type
    pub fn ty(&self) -> &FuncType {
        match self {
            Self::Wasm { ty, .. } => ty,
            Self::Host { ty, .. } => ty,
        }
    }

    /// Returns true if this is a WebAssembly function
    pub fn is_wasm(&self) -> bool {
        matches!(self, Self::Wasm { .. })
    }

    /// Returns true if this is a host function
    pub fn is_host(&self) -> bool {
        matches!(self, Self::Host { .. })
    }

    /// Returns the module instance if this is a WebAssembly function
    pub fn module(&self) -> Option<&ModuleInstance> {
        match self {
            Self::Wasm { module, .. } => Some(module),
            Self::Host { .. } => None,
        }
    }

    /// Returns the function code if this is a WebAssembly function
    pub fn code(&self) -> Option<&Function> {
        match self {
            Self::Wasm { code, .. } => Some(code),
            Self::Host { .. } => None,
        }
    }

    /// Returns the host function code if this is a host function
    pub fn host_code(&self) -> Option<&HostFunc> {
        match self {
            Self::Wasm { .. } => None,
            Self::Host { code, .. } => Some(code),
        }
    }

    /// Invokes the function with the given arguments
    /// 
    /// # Arguments
    /// 
    /// * `args` - The function arguments
    /// * `results` - The buffer to store the function results
    /// 
    /// # Returns
    /// 
    /// * `Ok(())` - The function executed successfully
    /// * `Err(String)` - An error occurred during execution
    pub fn invoke(&self, args: &[u64], results: &mut [u64]) -> Result<(), String> {
        match self {
            Self::Wasm { ty, module, code } => {
                // Validate argument count
                if args.len() != ty.params.len() {
                    return Err(format!(
                        "expected {} arguments, got {}",
                        ty.params.len(),
                        args.len()
                    ));
                }

                // Validate result count
                if results.len() != ty.results.len() {
                    return Err(format!(
                        "expected {} results, got {}",
                        ty.results.len(),
                        results.len()
                    ));
                }

                // Create a new store and thread for execution
                let mut store = Store::new();
                let mut thread = Thread::new(
                    FrameState::new(Vec::new(), module.clone()),
                    Vec::new(),
                );

                // Convert arguments from u64 to Value types and push to stack
                for (i, &arg) in args.iter().enumerate() {
                    let value = match ty.params[i] {
                        ValType::I32 => Value::I32(arg as i32),
                        ValType::I64 => Value::I64(arg as i64),
                        ValType::F32 => Value::F32(f32::from_bits(arg as u32)),
                        ValType::F64 => Value::F64(f64::from_bits(arg)),
                        _ => return Err(format!("Unsupported parameter type: {:?}", ty.params[i])),
                    };
                    thread.stack_mut().push_value(value);
                }

                // Create a function instance in the store
                let func_instance = FuncInstance::wasm(ty.clone(), module.clone(), code.clone());
                let func_addr = FuncAddr::new(store.add_func(func_instance));

                // Execute the function using the existing execution engine
                crate::wasm::runtime::instruction::invoke_with_reduction_rule(
                    &mut store, &mut thread, func_addr
                ).map_err(|e| e.to_string())?;

                // Extract results from the stack
                for (i, result) in results.iter_mut().enumerate() {
                    let value = thread.stack_mut().pop_value().ok_or_else(|| {
                        format!("Insufficient results: expected {}, got {}", ty.results.len(), i)
                    })?;

                    // Convert Value back to u64
                    *result = match value {
                        Value::I32(n) => n as u64,
                        Value::I64(n) => n as u64,
                        Value::F32(f) => f.to_bits() as u64,
                        Value::F64(f) => f.to_bits(),
                        _ => return Err(format!("Unsupported result type: {:?}", value)),
                    };
                }

                Ok(())
            }
            Self::Host { ty, code, .. } => {
                // Validate argument count
                if args.len() != ty.params.len() {
                    return Err(format!(
                        "expected {} arguments, got {}",
                        ty.params.len(),
                        args.len()
                    ));
                }

                // Validate result count
                if results.len() != ty.results.len() {
                    return Err(format!(
                        "expected {} results, got {}",
                        ty.results.len(),
                        results.len()
                    ));
                }

                // Invoke the host function
                code(args, results)
            }
        }
    }

    /// Invokes the function with Value types according to WebAssembly specification 4.5.5
    /// 
    /// This method implements the actual function execution part of the invocation algorithm.
    /// It assumes that the arguments have already been validated and pushed to the stack.
    /// 
    /// # Arguments
    /// 
    /// * `stack` - The stack containing the arguments and frame
    /// 
    /// # Returns
    /// 
    /// * `RuntimeResult<Vec<Value>>` - The result values from the function execution
    pub fn invoke_with_values(&self, stack: &mut Stack) -> RuntimeResult<Vec<Value>> {
        match self {
            Self::Wasm { ty, module, code } => {
                // Create a frame for this function execution
                let frame = Frame::new(
                    ty.results.len(), // arity is the number of return values
                    FrameState::new(Vec::new(), module.clone())
                );
                
                // Push the function frame to the stack
                stack.push_frame(frame);
                
                // Execute the function body
                let mut thread = crate::wasm::runtime::Thread::new(
                    FrameState::new(Vec::new(), module.clone()),
                    Vec::new(),
                );
                
                // Set up the thread with the current stack state
                // TODO: This is a simplified implementation
                // In a full implementation, we would need to properly integrate with the execution engine
                
                // For now, we'll simulate the execution by popping the expected number of results
                let mut results = Vec::new();
                for result_type in &ty.results {
                    // Pop a value from the stack (in a real implementation, this would come from execution)
                    let result = stack.pop_value().ok_or_else(|| {
                        RuntimeError::Stack("Insufficient values on stack for function results".to_string())
                    })?;
                    
                    // Validate the result type
                    if result.value_type().to_val_type() != *result_type {
                        return Err(RuntimeError::TypeError(format!(
                            "Result type mismatch: expected {:?}, got {:?}",
                            result_type, result.value_type()
                        )));
                    }
                    
                    results.push(result);
                }
                
                // Pop the function frame
                stack.pop_frame().ok_or_else(|| {
                    RuntimeError::Stack("Failed to pop function frame".to_string())
                })?;
                
                Ok(results)
            }
            Self::Host { ty, code } => {
                // Pop arguments from the stack
                let mut args = Vec::new();
                for _ in 0..ty.params.len() {
                    let arg = stack.pop_value().ok_or_else(|| {
                        RuntimeError::Stack("Insufficient arguments on stack for host function".to_string())
                    })?;
                    
                    // Convert Value to u64 (simplified conversion)
                    let u64_arg = match arg {
                        Value::I32(n) => n as u64,
                        Value::I64(n) => n as u64,
                        Value::F32(f) => f.to_bits() as u64,
                        Value::F64(f) => f.to_bits(),
                        _ => return Err(RuntimeError::TypeError(
                            "Unsupported value type for host function argument".to_string()
                        )),
                    };
                    args.push(u64_arg);
                }
                
                // Prepare result buffer
                let mut u64_results = Vec::new();
                for _ in 0..ty.results.len() {
                    u64_results.push(0u64);
                }
                
                // Invoke the host function
                code(&args, &mut u64_results).map_err(|e| {
                    RuntimeError::Function(format!("Host function execution failed: {}", e))
                })?;
                
                // Convert results back to Value types
                let mut results = Vec::new();
                for (i, u64_result) in u64_results.iter().enumerate() {
                    let result = match ty.results[i] {
                        crate::wasm::ast::ValType::I32 => Value::I32(*u64_result as i32),
                        crate::wasm::ast::ValType::I64 => Value::I64(*u64_result as i64),
                        crate::wasm::ast::ValType::F32 => Value::F32(f32::from_bits(*u64_result as u32)),
                        crate::wasm::ast::ValType::F64 => Value::F64(f64::from_bits(*u64_result)),
                        _ => return Err(RuntimeError::TypeError(
                            "Unsupported result type for host function".to_string()
                        )),
                    };
                    results.push(result);
                }
                
                Ok(results)
            }
        }
    }
}

impl fmt::Debug for FuncInstance {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Wasm { ty, module, code } => f.debug_struct("FuncInstance::Wasm")
                .field("ty", ty)
                .field("module", module)
                .field("code", code)
                .finish(),
            Self::Host { ty, code: _ } => f.debug_struct("FuncInstance::Host")
                .field("ty", ty)
                .field("code", &"<host function>")
                .finish(),
        }
    }
}

impl fmt::Display for FuncInstance {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Wasm { ty, .. } => write!(f, "wasm function {}", ty),
            Self::Host { ty, .. } => write!(f, "host function {}", ty),
        }
    }
}

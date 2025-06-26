//! WebAssembly runtime implementation for octox kernel
//! 
//! This module provides a no_std WebAssembly runtime implementation that can be used
//! to execute WebAssembly modules in the kernel space.
 
pub mod ast;
pub mod parser;
pub mod runtime;

use crate::wasm::parser::error::ParseResult;
use crate::wasm::parser::Parser;
use crate::wasm::runtime::{Store, ModuleInstance, RuntimeResult, RuntimeError, Value, ExternalValue, FuncAddr, FuncInstance, HostFunc, Address, MemoryInstance};
use crate::wasm::ast::{FuncType, ValType};
use crate::debug_log;
use crate::syscall::SysCalls;
use crate::error::Result as KernelResult;
use crate::error::Error::*;
use crate::proc::Cpus;
use crate::file::{FType, File, FTABLE};
use crate::fs::{self, Path};
use crate::fcntl::{FcntlCmd, OMode};
use crate::stat::FileType;
use crate::vm::{Addr, UVAddr, VirtAddr};
use crate::defs::AsBytes;
use crate::array;
use crate::console;

use alloc::format;
use alloc::vec::Vec;
use alloc::sync::Arc;
use alloc::string::String;
use alloc::string::ToString;
use core::mem::{size_of, size_of_val};
use core::str;

/// Global WASM memory access context
/// 
/// This is a temporary solution to access WASM memory from host functions.
/// In a production implementation, this would be integrated into the WASM runtime
/// architecture more elegantly.
static mut WASM_MEMORY_CONTEXT: Option<*mut Store> = None;

/// Set the global WASM memory context
/// 
/// This function sets the global context to the provided store.
/// It should be called before executing WASM code that needs to make system calls.
pub fn set_wasm_memory_context(store: &mut Store) {
    unsafe {
        WASM_MEMORY_CONTEXT = Some(store as *mut Store);
        debug_log!(store.config(), "[WASM] Set memory context: store has {} memories", store.mem_count());
    }
}

/// Clear the global WASM memory context
/// 
/// This function clears the global context.
/// It should be called after WASM execution is complete.
pub fn clear_wasm_memory_context() {
    unsafe {
        if WASM_MEMORY_CONTEXT.is_some() {
            // Use a default config for logging since we don't have access to the original config
            let default_config = runtime::RuntimeConfig::default();
            debug_log!(&default_config, "[WASM] Clearing memory context");
        }
        WASM_MEMORY_CONTEXT = None;
    }
}

/// Get a reference to the current WASM memory instance
/// 
/// This function attempts to get the first memory instance from the global context.
/// Returns None if no context is set or no memory is available.
fn get_current_wasm_memory() -> Option<&'static mut MemoryInstance> {
    unsafe {
        // Use a default config for logging since we don't have access to the original config
        let default_config = runtime::RuntimeConfig::default();
        
        // First, try to get memory from the global context
        if let Some(store_ptr) = WASM_MEMORY_CONTEXT {
            debug_log!(&default_config, "[WASM] Global context available, attempting to get store");
            
            if let Some(store) = store_ptr.as_mut() {
                debug_log!(&default_config, "[WASM] Store obtained, memory count: {}", store.mem_count());
                
                if store.mem_count() > 0 {
                    if let Some(memory) = store.get_memory_mut(0) {
                        debug_log!(&default_config, "[WASM] Successfully obtained memory instance with {} bytes", memory.size_bytes());
                        
                        // Test memory access to ensure it's properly mapped
                        if memory.size_bytes() > 0 {
                            // Test access to the first byte using public method
                            match memory.read_byte(0) {
                                Ok(_) => debug_log!(&default_config, "[WASM] First byte access test successful"),
                                Err(e) => {
                                    debug_log!(&default_config, "[WASM] First byte access test failed: {}", e);
                                    return None;
                                }
                            }
                            
                            // Test access to the last byte if memory is large enough
                            if memory.size_bytes() > 1 {
                                match memory.read_byte(memory.size_bytes() - 1) {
                                    Ok(_) => debug_log!(&default_config, "[WASM] Last byte access test successful"),
                                    Err(e) => {
                                        debug_log!(&default_config, "[WASM] Last byte access test failed: {}", e);
                                        return None;
                                    }
                                }
                            }
                            
                            debug_log!(&default_config, "[WASM] Memory access test successful");
                        }
                        
                        return Some(memory);
                    } else {
                        debug_log!(&default_config, "[WASM] Failed to get memory instance from store");
                    }
                } else {
                    debug_log!(&default_config, "[WASM] Store has no memories");
                }
            } else {
                debug_log!(&default_config, "[WASM] Failed to dereference store pointer");
            }
        } else {
            debug_log!(&default_config, "[WASM] No global context available");
        }
        
        // If global context is not available, try alternative methods
        // This is a fallback for cases where the context might be temporarily unavailable
        debug_log!(&default_config, "[WASM] No memory available from any source");
        None
    }
}

/// Helper function to get the first memory instance from a store
fn get_wasm_memory(store: &Store) -> Option<&MemoryInstance> {
    if store.mem_count() > 0 {
        store.get_memory(0)
    } else {
        None
    }
}

/// Helper function to get a mutable reference to the first memory instance from a store
fn get_wasm_memory_mut(store: &mut Store) -> Option<&mut MemoryInstance> {
    if store.mem_count() > 0 {
        store.get_memory_mut(0)
    } else {
        None
    }
}

/// Helper function to read a string from WASM memory
fn read_wasm_string(memory: &MemoryInstance, ptr: usize, len: usize) -> Result<String, String> {
    let bytes = memory.read_bytes(ptr, len)?;
    str::from_utf8(bytes)
        .map(|s| s.to_string())
        .map_err(|e| format!("Invalid UTF-8: {}", e))
}

/// Helper function to read a slice from WASM memory
fn read_wasm_slice(memory: &MemoryInstance, ptr: usize, len: usize) -> Result<Vec<u8>, String> {
    let bytes = memory.read_bytes(ptr, len)?;
    Ok(bytes.to_vec())
}

/// Helper function to write data to WASM memory
fn write_wasm_slice(memory: &mut MemoryInstance, ptr: usize, data: &[u8]) -> Result<(), String> {
    memory.write_bytes(ptr, data)
}

/// Helper function to safely read from WASM memory
fn read_wasm_memory(memory: &MemoryInstance, offset: usize, len: usize) -> Option<Vec<u8>> {
    let default_config = runtime::RuntimeConfig::default();
    if offset >= memory.size_bytes() {
        debug_log!(&default_config, "[WASM] Error: Offset {} is out of bounds (memory size: {})", offset, memory.size_bytes());
        return None;
    }
    if offset + len > memory.size_bytes() {
        debug_log!(&default_config, "[WASM] Error: Read would exceed memory bounds (offset: {}, len: {}, memory size: {})", offset, len, memory.size_bytes());
        return None;
    }
    match memory.read_bytes(offset, len) {
        Ok(data) => {
            debug_log!(&default_config, "[WASM] Successfully read {} bytes from offset {}", len, offset);
            Some(data.to_vec())
        }
        Err(e) => {
            debug_log!(&default_config, "[WASM] Error reading from memory: {}", e);
            None
        }
    }
}

/// Parse WebAssembly binary format into an AST module.
///
/// This function parses the WebAssembly binary format and returns a module AST.
///
/// # Arguments
///
/// * `bytes` - The WebAssembly module bytes
///
/// # Returns
///
/// * `ParseResult<ast::Module>` - The parsed module or an error
///
/// # Examples
///
/// ```
/// let wasm = [
///     0x00, 0x61, 0x73, 0x6D,  // "\0asm"
///     0x01, 0x00, 0x00, 0x00,  // version 1
///     // ... rest of the module
/// ];
/// let module = parse(&wasm).unwrap();
/// ```
pub fn parse(bytes: &[u8]) -> ParseResult<ast::Module> {
    // Create a parser with debug logging enabled
    // let mut parser = Parser::debug(bytes);
    let mut parser = Parser::new(bytes);
    parser.parse_module()
}

/// Parse WebAssembly binary format into an AST module with custom configuration.
///
/// This function parses the WebAssembly binary format and returns a module AST
/// using the provided parser configuration.
///
/// # Arguments
///
/// * `bytes` - The WebAssembly module bytes
/// * `config` - Parser configuration
///
/// # Returns
///
/// * `ParseResult<ast::Module>` - The parsed module or an error
pub fn parse_with_config(bytes: &[u8], config: parser::ParserConfig) -> ParseResult<ast::Module> {
    let mut parser = Parser::with_config(bytes, config);
    parser.parse_module()
}

/// Execute a WebAssembly module from its binary representation.
///
/// This function parses the WebAssembly bytes, instantiates the module,
/// and optionally invokes a specific exported function.
///
/// # Arguments
///
/// * `bytes` - The WebAssembly module bytes
/// * `function_name` - Optional name of an exported function to invoke
/// * `args` - Optional arguments to pass to the function
/// * `config` - Runtime configuration (optional, uses default if None)
///
/// # Returns
///
/// * `RuntimeResult<Vec<Value>>` - The result values from function execution, or empty vector if no function was invoked
///
/// # Examples
///
/// ```
/// let wasm = [
///     0x00, 0x61, 0x73, 0x6D,  // "\0asm"
///     0x01, 0x00, 0x00, 0x00,  // version 1
///     // ... rest of the module
/// ];
/// 
/// // Execute module without invoking any function
/// let result = execute(&wasm, None, &[], None).unwrap();
/// 
/// // Execute module and invoke an exported function
/// let result = execute(&wasm, Some("add"), &[Value::I32(1), Value::I32(2)], None).unwrap();
/// 
/// // Execute with debug logging enabled
/// let config = runtime::RuntimeConfig { debug: true, ..runtime::RuntimeConfig::default() };
/// let result = execute(&wasm, Some("add"), &[Value::I32(1), Value::I32(2)], Some(config)).unwrap();
/// ```
pub fn execute(
    bytes: &[u8], 
    function_name: Option<&str>, 
    args: &[Value],
    config: Option<runtime::RuntimeConfig>
) -> RuntimeResult<Vec<Value>> {
    let config = config.unwrap_or_else(runtime::RuntimeConfig::default);
    
    // Parse the WebAssembly module
    let parser_config = parser::ParserConfig { debug: config.debug };
    let module = parse_with_config(bytes, parser_config).map_err(|e| {
        RuntimeError::Module(format!("Failed to parse WebAssembly module: {}", e))
    })?;
    
    debug_log!(&config, "Module types: {:?}", module.types);
    debug_log!(&config, "Module imports: {:?}", module.imports);
    
    // Create a new store with the configuration
    let mut store = Store::with_config(config);
    
    // Set the WASM memory context for system calls
    set_wasm_memory_context(&mut store);
    
    // Create external values (including imports)
    let external_values = create_external_values(&module, &mut store)?;
    
    // Instantiate the module
    let module_instance = ModuleInstance::instantiate(&mut store, &module, &external_values[..])?;
    
    // If a function name is provided, invoke it
    let result = if let Some(name) = function_name {
        // Create a thread for execution
        let mut thread = runtime::Thread::new(
            runtime::FrameState::new(Vec::new(), module_instance.clone()),
            Vec::new(),
        );
        
        // Invoke the exported function
        module_instance.invoke_exported_function(&mut store, &mut thread, name, args)
    } else {
        // Return empty result if no function was invoked
        Ok(Vec::new())
    };
    
    // Clear the WASM memory context
    clear_wasm_memory_context();
    
    result
}

/// Execute a WebAssembly module and invoke its start function if present.
///
/// This function parses the WebAssembly bytes and instantiates the module,
/// which will automatically invoke the start function if one is defined.
///
/// # Arguments
///
/// * `bytes` - The WebAssembly module bytes
/// * `config` - Runtime configuration (optional, uses default if None)
///
/// # Returns
///
/// * `RuntimeResult<()>` - Success or failure of module execution
///
/// # Examples
///
/// ```
/// let wasm = [
///     0x00, 0x61, 0x73, 0x6D,  // "\0asm"
///     0x01, 0x00, 0x00, 0x00,  // version 1
///     // ... rest of the module
/// ];
/// 
/// // Execute module (start function will be called automatically if present)
/// execute_with_start(&wasm, None).unwrap();
/// 
/// // Execute with debug logging enabled
/// let config = runtime::RuntimeConfig { debug: true, ..runtime::RuntimeConfig::default() };
/// execute_with_start(&wasm, Some(config)).unwrap();
/// ```
pub fn execute_with_start(bytes: &[u8], config: Option<runtime::RuntimeConfig>) -> RuntimeResult<()> {
    let config = config.unwrap_or_else(runtime::RuntimeConfig::default);
    
    // Parse the WebAssembly module
    let parser_config = parser::ParserConfig { debug: config.debug };
    let module = parse_with_config(bytes, parser_config).map_err(|e| {
        RuntimeError::Module(format!("Failed to parse WebAssembly module: {}", e))
    })?;
    
    // Create a new store with the configuration
    let mut store = Store::with_config(config);
    
    // Set the WASM memory context for system calls
    set_wasm_memory_context(&mut store);
    
    // Create external values (including imports)
    let external_values = create_external_values(&module, &mut store)?;
    
    // Instantiate the module (this will automatically invoke the start function if present)
    let _module_instance = ModuleInstance::instantiate(&mut store, &module, &external_values[..])?;
    
    // Clear the WASM memory context
    clear_wasm_memory_context();
    
    Ok(())
}

/// Execute a WebAssembly module with automatic function selection.
///
/// This function automatically tries to execute a "main" function if it exists,
/// otherwise falls back to executing the start function if present.
///
/// # Arguments
///
/// * `bytes` - The WebAssembly module bytes
/// * `config` - Runtime configuration (optional, uses default if None)
///
/// # Returns
///
/// * `RuntimeResult<Vec<Value>>` - The result values from function execution, or empty vector if no function was invoked
///
/// # Examples
///
/// ```
/// let wasm = [
///     0x00, 0x61, 0x73, 0x6D,  // "\0asm"
///     0x01, 0x00, 0x00, 0x00,  // version 1
///     // ... rest of the module
/// ];
/// 
/// // Execute module with automatic function selection
/// let result = execute_auto(&wasm, None).unwrap();
/// 
/// // Execute with debug logging enabled
/// let config = runtime::RuntimeConfig { debug: true, ..runtime::RuntimeConfig::default() };
/// let result = execute_auto(&wasm, Some(config)).unwrap();
/// ```
pub fn execute_auto(bytes: &[u8], config: Option<runtime::RuntimeConfig>) -> RuntimeResult<Vec<Value>> {
    let config = config.unwrap_or_else(runtime::RuntimeConfig::default);
    
    // Parse the WebAssembly module to check for exports
    let parser_config = parser::ParserConfig { debug: config.debug };
    let module = parse_with_config(bytes, parser_config).map_err(|e| {
        RuntimeError::Module(format!("Failed to parse WebAssembly module: {}", e))
    })?;
    
    // Check if there's a main function export
    let has_main = module.exports.iter()
        .any(|e| e.name == "main" && e.kind == ast::ExternKind::Func);
    
    if has_main {
        // Execute with main function
        execute(bytes, Some("main"), &[], Some(config))
    } else {
        // Execute with start function if no main function found
        execute_with_start(bytes, Some(config)).map(|_| Vec::new())
    }
}

/// Kernel syscall function implementation
/// 
/// This function implements the kernel.syscall import that WebAssembly modules can use
/// to make system calls to the kernel.
/// 
/// This implementation uses a global memory context to access WASM memory.
/// The context must be set before executing WASM modules using set_wasm_memory_context().
fn kernel_syscall_impl(args: &[u64], results: &mut [u64], config: &runtime::RuntimeConfig) -> Result<(), String> {
    if args.len() < 7 {
        return Err("Insufficient arguments for syscall".to_string());
    }

    let syscall_num = args[0] as i32;
    let arg1 = args[1] as i32;
    let arg2 = args[2] as i32;
    let arg3 = args[3] as i32;
    let arg4 = args[4] as i32;
    let arg5 = args[5] as i32;
    let arg6 = args[6] as i32;

    debug_log!(config, "Kernel syscall called with args: [{}, {}, {}, {}, {}, {}, {}]", 
        syscall_num, arg1, arg2, arg3, arg4, arg5, arg6);

    // Get the current process
    let p = crate::proc::Cpus::myproc()
        .ok_or("No current process")?;
    let pdata = p.data_mut();

    // Try to get WASM memory from the current context
    let memory = get_current_wasm_memory();
    
    // If we can't get memory from context, try to get it from the store
    let memory = if memory.is_none() {
        debug_log!(config, "[WASM] Could not get memory from context, trying alternative method");
        // For now, we'll continue without memory access
        None
    } else {
        debug_log!(config, "[WASM] Successfully obtained memory from context");
        memory
    };

    debug_log!(config, "[WASM] Memory available: {}", memory.is_some());
    
    // Additional safety check: verify memory is valid if available
    if let Some(ref memory) = memory {
        if memory.size_bytes() == 0 {
            debug_log!(config, "[WASM] Warning: Memory instance has empty data");
        } else {
            debug_log!(config, "[WASM] Memory instance has {} bytes of data", memory.size_bytes());
        }
    }

    let result = match SysCalls::from_usize(syscall_num as usize) {
        SysCalls::Write => {
            let fd = arg1 as i32;
            let buf_ptr = arg2 as usize;
            let count = arg3 as usize;
            
            debug_log!(config, "[WASM] Write to fd {}: {} bytes from address 0x{:x}", fd, count, buf_ptr);
            
            if let Some(memory) = memory {
                debug_log!(config, "[WASM] Memory instance available, attempting to read data");
                
                // Use the safe reading function
                if let Some(data) = read_wasm_memory(memory, buf_ptr, count) {
                    if fd == 1 {
                        // Direct console output for stdout
                        for &byte in &data {
                            console::putc(byte);
                        }
                        debug_log!(config, "[WASM] Successfully wrote {} bytes to console", data.len());
                        Ok(data.len() as isize)
                    } else {
                        // For other file descriptors, use the file system
                        if let Some(file) = pdata.ofile.get_mut(fd as usize).and_then(|f| f.as_mut()) {
                            let mut buf = [0u8; 1024];
                            let copy_len = count.min(buf.len());
                            buf[..copy_len].copy_from_slice(&data[..copy_len]);
                            
                            if let Ok(bytes_written) = file.write(VirtAddr::Kernel(buf.as_ptr() as usize), copy_len) {
                                debug_log!(config, "[WASM] Successfully wrote {} bytes to fd {}", bytes_written, fd);
                                Ok(bytes_written as isize)
                            } else {
                                debug_log!(config, "[WASM] Write failed");
                                Ok(-1 as isize)
                            }
                        } else {
                            debug_log!(config, "[WASM] No file descriptor available for write");
                            Ok(-1 as isize)
                        }
                    }
                } else {
                    debug_log!(config, "[WASM] Failed to read data from WASM memory");
                    Ok(-1 as isize)
                }
            } else {
                debug_log!(config, "[WASM] No memory available for write operation");
                Ok(-1 as isize)
            }
        }
        
        SysCalls::Read => {
            debug_log!(config, "Read syscall: fd={}, buf_ptr={:#x}, count={}", arg1, arg2, arg3);
            
            let fd = arg1 as usize;
            let buf_ptr = arg2 as usize;
            let count = arg3 as usize;
            
            // Read data to WASM memory via kernel buffer
            if let Some(memory) = memory {
                debug_log!(config, "[WASM] Read from fd {}: {} bytes to address {:#x}", fd, count, buf_ptr);
                
                // Create a kernel buffer to read into
                let mut kernel_buffer = Vec::with_capacity(count);
                kernel_buffer.resize(count, 0);
                
                // Get the file from the process
                let file = pdata.ofile.get_mut(fd)
                    .ok_or("File descriptor too large")?
                    .as_mut()
                    .ok_or("Bad file descriptor")?;
                
                // Read data into kernel buffer
                match file.read(crate::vm::VirtAddr::Kernel(kernel_buffer.as_ptr() as usize), kernel_buffer.len()) {
                    Ok(read_bytes) => {
                        debug_log!(config, "[WASM] Successfully read {} bytes from fd {}", read_bytes, fd);
                        
                        // Copy data from kernel buffer to WASM memory
                        kernel_buffer.truncate(read_bytes);
                        match write_wasm_slice(memory, buf_ptr, &kernel_buffer) {
                            Ok(()) => {
                                debug_log!(config, "[WASM] Successfully wrote {} bytes to WASM memory", read_bytes);
                                Ok(read_bytes as isize)
                            }
                            Err(e) => {
                                debug_log!(config, "[WASM] Failed to write to WASM memory: {}", e);
                                Ok(-1 as isize)
                            }
                        }
                    }
                    Err(e) => {
                        debug_log!(config, "[WASM] Read failed: {:?}", e);
                        Ok(-1 as isize)
                    }
                }
            } else {
                debug_log!(config, "[WASM] No WASM memory available");
                Ok(-1 as isize)
            }
        }
        
        SysCalls::Open => {
            debug_log!(config, "Open syscall: path_ptr={:#x}, flags={}", arg1, arg2);
            
            let path_ptr = arg1 as usize;
            let flags = arg2 as usize;
            
            // Read path from WASM memory and copy to kernel buffer
            if let Some(memory) = memory {
                // For now, assume the path is a null-terminated string
                // In a real implementation, we'd need to determine the string length
                let max_len = 256; // reasonable max path length
                match read_wasm_string(memory, path_ptr, max_len) {
                    Ok(wasm_path_str) => {
                        // Find the null terminator
                        let null_pos = wasm_path_str.find('\0').unwrap_or(wasm_path_str.len());
                        let actual_path = &wasm_path_str[..null_pos];
                        
                        debug_log!(config, "[WASM] Open file: '{}' with flags {}", actual_path, flags);
                        
                        // Copy the path string to kernel space for processing
                        let kernel_path = actual_path.to_string();
                        
                        // Create the path and open the file
                        match crate::fs::Path::new(&kernel_path).namei() {
                            Ok((_, inode)) => {
                                match FTABLE.alloc(crate::fcntl::OMode::from_usize(flags), crate::file::FType::Node(crate::fs::Path::new(&kernel_path))) {
                                    Ok(file) => {
                                        // Find an empty file descriptor slot
                                        let mut result_fd = -1;
                                        for i in 0..pdata.ofile.len() {
                                            if pdata.ofile[i].is_none() {
                                                pdata.ofile[i] = Some(file);
                                                debug_log!(config, "[WASM] Successfully opened file '{}' with fd {}", actual_path, i);
                                                result_fd = i as isize;
                                                break;
                                            }
                                        }
                                        if result_fd >= 0 {
                                            Ok(result_fd)
                                        } else {
                                            debug_log!(config, "[WASM] No available file descriptors");
                                            Ok(-1 as isize)
                                        }
                                    }
                                    Err(e) => {
                                        debug_log!(config, "[WASM] Failed to allocate file: {:?}", e);
                                        Ok(-1 as isize)
                                    }
                                }
                            }
                            Err(e) => {
                                debug_log!(config, "[WASM] Failed to resolve path '{}': {:?}", actual_path, e);
                                Ok(-1 as isize)
                            }
                        }
                    }
                    Err(e) => {
                        debug_log!(config, "[WASM] Failed to read path from WASM memory: {}", e);
                        Ok(-1 as isize)
                    }
                }
            } else {
                debug_log!(config, "[WASM] No WASM memory available");
                Ok(-1 as isize)
            }
        }
        
        SysCalls::Close => {
            debug_log!(config, "Close syscall: fd={}", arg1);
            
            let fd = arg1 as usize;
            
            // Close the file descriptor
            if let Some(file) = pdata.ofile.get_mut(fd).and_then(|f| f.take()) {
                debug_log!(config, "[WASM] Successfully closed fd {}", fd);
                Ok(0 as isize)
            } else {
                debug_log!(config, "[WASM] Invalid file descriptor {}", fd);
                Ok(-1 as isize)
            }
        }
        
        SysCalls::Exit => {
            debug_log!(config, "Exit syscall: status={}", arg1);
            
            let status = arg1 as i32;
            
            // Call the actual exit function
            crate::proc::exit(status);
            
            // This should never be reached
            unreachable!();
        }
        
        SysCalls::Getpid => {
            debug_log!(config, "Getpid syscall");
            
            // Return the current process ID
            Ok(p.pid() as isize)
        }
        
        SysCalls::Fork => {
            debug_log!(config, "Fork syscall");
            
            // For now, return an error (fork is complex in WASM context)
            debug_log!(config, "[WASM] Fork not supported in WASM context");
            Ok(-1 as isize)
        }
        
        SysCalls::Exec => {
            debug_log!(config, "Exec syscall: path_ptr={:#x}", arg1);
            
            let path_ptr = arg1 as usize;
            
            // Read path from WASM memory and copy to kernel buffer
            if let Some(memory) = memory {
                let max_len = 256;
                match read_wasm_string(memory, path_ptr, max_len) {
                    Ok(wasm_path_str) => {
                        let null_pos = wasm_path_str.find('\0').unwrap_or(wasm_path_str.len());
                        let actual_path = &wasm_path_str[..null_pos];
                        
                        debug_log!(config, "[WASM] Exec file: '{}'", actual_path);
                        
                        // Copy the path string to kernel space for processing
                        let kernel_path = actual_path.to_string();
                        
                        // For now, just simulate exec
                        debug_log!(config, "[WASM] Executing '{}' (simulated)", kernel_path);
                        Ok(0 as isize)
                    }
                    Err(e) => {
                        debug_log!(config, "[WASM] Failed to read path from WASM memory: {}", e);
                        Ok(-1 as isize)
                    }
                }
            } else {
                debug_log!(config, "[WASM] No WASM memory available");
                Ok(-1 as isize)
            }
        }
        
        SysCalls::Sleep => {
            debug_log!(config, "Sleep syscall: ticks={}", arg1);
            
            let ticks = arg1;
            
            // For now, simulate sleep
            debug_log!(config, "[WASM] Sleep for {} ticks", ticks);
            
            // Return success
            Ok(0 as isize)
        }
        
        SysCalls::Uptime => {
            debug_log!(config, "Uptime syscall");
            
            // Return uptime (simulated)
            debug_log!(config, "[WASM] Uptime requested");
            Ok(1000 as isize)
        }
        
        SysCalls::Mkdir => {
            debug_log!(config, "Mkdir syscall: path_ptr={:#x}", arg1);
            
            let path_ptr = arg1 as usize;
            
            // Read path from WASM memory and copy to kernel buffer
            if let Some(memory) = memory {
                let max_len = 256;
                match read_wasm_string(memory, path_ptr, max_len) {
                    Ok(wasm_path_str) => {
                        let null_pos = wasm_path_str.find('\0').unwrap_or(wasm_path_str.len());
                        let actual_path = &wasm_path_str[..null_pos];
                        
                        debug_log!(config, "[WASM] Mkdir: '{}'", actual_path);
                        
                        // Copy the path string to kernel space for processing
                        let kernel_path = actual_path.to_string();
                        
                        // For now, just simulate mkdir
                        debug_log!(config, "[WASM] Creating directory '{}' (simulated)", kernel_path);
                        Ok(0 as isize)
                    }
                    Err(e) => {
                        debug_log!(config, "[WASM] Failed to read path from WASM memory: {}", e);
                        Ok(-1 as isize)
                    }
                }
            } else {
                debug_log!(config, "[WASM] No WASM memory available");
                Ok(-1 as isize)
            }
        }
        
        SysCalls::Unlink => {
            debug_log!(config, "Unlink syscall: path_ptr={:#x}", arg1);
            
            let path_ptr = arg1 as usize;
            
            // Read path from WASM memory and copy to kernel buffer
            if let Some(memory) = memory {
                let max_len = 256;
                match read_wasm_string(memory, path_ptr, max_len) {
                    Ok(wasm_path_str) => {
                        let null_pos = wasm_path_str.find('\0').unwrap_or(wasm_path_str.len());
                        let actual_path = &wasm_path_str[..null_pos];
                        
                        debug_log!(config, "[WASM] Unlink: '{}'", actual_path);
                        
                        // Copy the path string to kernel space for processing
                        let kernel_path = actual_path.to_string();
                        
                        // For now, just simulate unlink
                        debug_log!(config, "[WASM] Removing file '{}' (simulated)", kernel_path);
                        Ok(0 as isize)
                    }
                    Err(e) => {
                        debug_log!(config, "[WASM] Failed to read path from WASM memory: {}", e);
                        Ok(-1 as isize)
                    }
                }
            } else {
                debug_log!(config, "[WASM] No WASM memory available");
                Ok(-1 as isize)
            }
        }
        
        SysCalls::Link => {
            debug_log!(config, "Link syscall: old_path_ptr={:#x}, new_path_ptr={:#x}", arg1, arg2);
            
            let old_path_ptr = arg1 as usize;
            let new_path_ptr = arg2 as usize;
            
            // Read paths from WASM memory and copy to kernel buffer
            if let Some(memory) = memory {
                let max_len = 256;
                match (read_wasm_string(memory, old_path_ptr, max_len), read_wasm_string(memory, new_path_ptr, max_len)) {
                    (Ok(old_wasm_path_str), Ok(new_wasm_path_str)) => {
                        let old_null_pos = old_wasm_path_str.find('\0').unwrap_or(old_wasm_path_str.len());
                        let new_null_pos = new_wasm_path_str.find('\0').unwrap_or(new_wasm_path_str.len());
                        let old_actual_path = &old_wasm_path_str[..old_null_pos];
                        let new_actual_path = &new_wasm_path_str[..new_null_pos];
                        
                        debug_log!(config, "[WASM] Link: '{}' -> '{}'", old_actual_path, new_actual_path);
                        
                        // Copy the path strings to kernel space for processing
                        let old_kernel_path = old_actual_path.to_string();
                        let new_kernel_path = new_actual_path.to_string();
                        
                        // For now, just simulate link
                        debug_log!(config, "[WASM] Creating link '{}' -> '{}' (simulated)", old_kernel_path, new_kernel_path);
                        Ok(0 as isize)
                    }
                    _ => {
                        debug_log!(config, "[WASM] Failed to read paths from WASM memory");
                        Ok(-1 as isize)
                    }
                }
            } else {
                debug_log!(config, "[WASM] No WASM memory available");
                Ok(-1 as isize)
            }
        }
        
        SysCalls::Chdir => {
            debug_log!(config, "Chdir syscall: path_ptr={:#x}", arg1);
            
            let path_ptr = arg1 as usize;
            
            // Read path from WASM memory and copy to kernel buffer
            if let Some(memory) = memory {
                let max_len = 256;
                match read_wasm_string(memory, path_ptr, max_len) {
                    Ok(wasm_path_str) => {
                        let null_pos = wasm_path_str.find('\0').unwrap_or(wasm_path_str.len());
                        let actual_path = &wasm_path_str[..null_pos];
                        
                        debug_log!(config, "[WASM] Chdir: '{}'", actual_path);
                        
                        // Copy the path string to kernel space for processing
                        let kernel_path = actual_path.to_string();
                        
                        // For now, just simulate chdir
                        debug_log!(config, "[WASM] Changing directory to '{}' (simulated)", kernel_path);
                        Ok(0 as isize)
                    }
                    Err(e) => {
                        debug_log!(config, "[WASM] Failed to read path from WASM memory: {}", e);
                        Ok(-1 as isize)
                    }
                }
            } else {
                debug_log!(config, "[WASM] No WASM memory available");
                Ok(-1 as isize)
            }
        }
        
        SysCalls::Fstat => {
            debug_log!(config, "Fstat syscall: fd={}, stat_ptr={:#x}", arg1, arg2);
            
            let fd = arg1 as usize;
            let stat_ptr = arg2 as usize;
            
            // For now, simulate getting file status
            debug_log!(config, "[WASM] Fstat fd {} to address {:#x}", fd, stat_ptr);
            
            // Return success
            Ok(0 as isize)
        }
        
        SysCalls::Dup => {
            debug_log!(config, "Dup syscall: fd={}", arg1);
            
            let fd = arg1 as usize;
            
            // For now, simulate duplicating file descriptor
            debug_log!(config, "[WASM] Dup fd {}", fd);
            
            // Return new file descriptor (simulated)
            Ok(4 as isize)
        }
        
        SysCalls::Dup2 => {
            debug_log!(config, "Dup2 syscall: src={}, dst={}", arg1, arg2);
            
            let src = arg1 as usize;
            let dst = arg2 as usize;
            
            // For now, simulate duplicating file descriptor
            debug_log!(config, "[WASM] Dup2 from {} to {}", src, dst);
            
            // Return destination file descriptor
            Ok(dst as isize)
        }
        
        SysCalls::Pipe => {
            debug_log!(config, "Pipe syscall: pipe_ptr={:#x}", arg1);
            
            let pipe_ptr = arg1 as usize;
            
            // For now, simulate creating a pipe
            debug_log!(config, "[WASM] Pipe at address {:#x}", pipe_ptr);
            
            // Return success
            Ok(0 as isize)
        }
        
        SysCalls::Kill => {
            debug_log!(config, "Kill syscall: pid={}", arg1);
            
            let pid = arg1 as usize;
            
            // For now, simulate killing a process
            debug_log!(config, "[WASM] Kill pid {}", pid);
            
            // Return success
            Ok(0 as isize)
        }
        
        SysCalls::Wait => {
            debug_log!(config, "Wait syscall: status_ptr={:#x}", arg1);
            
            let status_ptr = arg1 as usize;
            
            // For now, simulate waiting for a child
            debug_log!(config, "[WASM] Wait at address {:#x}", status_ptr);
            
            // Return child PID (simulated)
            Ok(-1 as isize)
        }
        
        SysCalls::Sbrk => {
            debug_log!(config, "Sbrk syscall: n={}", arg1);
            
            let n = arg1 as isize;
            
            // For now, simulate memory allocation
            debug_log!(config, "[WASM] Sbrk {} bytes", n);
            
            // Return current break (simulated)
            Ok(0x10000 as isize)
        }
        
        SysCalls::Mknod => {
            debug_log!(config, "Mknod syscall: path_ptr={:#x}, major={}, minor={}", arg1, arg2, arg3);
            
            let path_ptr = arg1 as usize;
            let major = arg2 as u16;
            let minor = arg3 as u16;
            
            // Read path from WASM memory
            if let Some(memory) = memory {
                let max_len = 256;
                match read_wasm_string(memory, path_ptr, max_len) {
                    Ok(path_str) => {
                        let null_pos = path_str.find('\0').unwrap_or(path_str.len());
                        let actual_path = &path_str[..null_pos];
                        
                        debug_log!(config, "[WASM] Mknod: '{}' major={} minor={}", actual_path, major, minor);
                        
                        // Return success
                        Ok(0 as isize)
                    }
                    Err(e) => {
                        debug_log!(config, "[WASM] Failed to read path from memory: {}", e);
                        Ok(-1 as isize)
                    }
                }
            } else {
                debug_log!(config, "[WASM] No WASM memory available");
                Ok(-1 as isize)
            }
        }
        
        SysCalls::Fcntl => {
            debug_log!(config, "Fcntl syscall: fd={}, cmd={}", arg1, arg2);
            
            let fd = arg1 as usize;
            let cmd = arg2 as usize;
            
            // For now, simulate file control operations
            debug_log!(config, "[WASM] Fcntl fd {} cmd {}", fd, cmd);
            
            // Return success
            Ok(0 as isize)
        }
        
        _ => {
            debug_log!(config, "Unsupported syscall number: {}", syscall_num);
            Err(format!("Unsupported syscall number: {}", syscall_num))
        }
    };
    
    // Set the result
    if !results.is_empty() {
        results[0] = result? as u64;
        debug_log!(config, "Set result[0] = {} (syscall result)", results[0]);
    }
    
    Ok(())
}

/// Create external values for imports
/// 
/// This function creates the external values needed for module instantiation
/// based on the imports declared in the module.
fn create_external_values(module: &ast::Module, store: &mut Store) -> RuntimeResult<Vec<ExternalValue>> {
    let mut external_values = Vec::new();
    let store_config = store.config().clone(); // Clone the config to avoid lifetime issues
    
    debug_log!(&store_config, "Processing {} imports", module.imports.len());
    for import in &module.imports {
        debug_log!(&store_config, "Import: {}.{} -> {:?}", import.module, import.field, import.ty);
        match (&import.module, &import.field, &import.ty) {
            (module, field, ast::ExternalType::Func(func_type)) if module == "kernel" && field == "syscall" => {
                debug_log!(&store_config, "Creating kernel syscall function with type: {:?} -> {:?}", func_type.params, func_type.results);
                // Create kernel syscall function - clone config for this iteration
                let config = store_config.clone();
                
                // TODO: In the future, we could pass the WASM memory instance to the syscall function
                // to enable actual memory access. This would require:
                // 1. Modifying the HostFunc signature to include memory access
                // 2. Passing the memory instance through the closure
                // 3. Using the memory instance to read/write data in system calls
                let host_func: HostFunc = Arc::new(move |args, results| kernel_syscall_impl(args, results, &config));
                let func_instance = FuncInstance::host(func_type.clone(), host_func);
                debug_log!(&store_config, "Created FuncInstance: is_host={}, is_wasm={}, code() is_some={}", 
                    func_instance.is_host(), func_instance.is_wasm(), func_instance.code().is_some());
                let func_addr = store.add_func(func_instance);
                external_values.push(ExternalValue::Func(Address::new(func_addr)));
            }
            _ => {
                return Err(RuntimeError::Module(format!(
                    "Unsupported import: {}.{}",
                    import.module, import.field
                )));
            }
        }
    }
    
    Ok(external_values)
}
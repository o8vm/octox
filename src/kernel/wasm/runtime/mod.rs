//! WebAssembly Runtime Module
//! 
//! This module provides a runtime environment for executing WebAssembly modules.
//! It includes components for memory management, stack operations, and execution.

mod address;
mod function;
mod module;
mod result;
mod store;
mod value;
mod table;
pub mod memory;
mod global;
mod element;
mod data;
mod export;
mod external;
mod stack;
mod frame;
mod numeric;
mod instruction;
mod typing;
mod allocation;
pub mod context;

use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;

use crate::wasm::ast::{Instruction};

pub use address::{Address, RuntimeAddr, FuncAddr, TableAddr, MemAddr, GlobalAddr, ElemAddr, DataAddr, ExternAddr};
pub use function::{FuncInstance, HostFunc};
pub use module::{ModuleInstance, ExportValue};
pub use result::ExecutionResult;
pub use store::Store;
pub use value::Value;
pub use table::{TableElement};
pub use memory::MemoryInstance;
pub use global::GlobalInstance;
pub use element::ElementInstance;
pub use data::DataInstance;
pub use export::ExportInstance;
pub use external::{external_values};
pub use stack::{Stack, StackEntry, Label, BlockContext};
pub use frame::{Frame, FrameState};
pub use context::{EvaluationContext, EvaluationState};
pub use numeric::{
    BitWidth,
    NumericResult,
    UnsignedOps,
    SignedOps,
    FloatOps,
    VectorOps,
};
pub use instruction::{InstructionExecutor, DefaultInstructionExecutor, evaluate_const_exprs};
pub use typing::{ExternalType, ValueTyping, ModuleTyping, ExternalValue};
pub use allocation::Allocation;

/// Result type for WASM runtime operations
pub type RuntimeResult<T> = core::result::Result<T, RuntimeError>;

/// Error type for WASM runtime operations
#[derive(Debug, Clone)]
pub enum RuntimeError {
    /// Memory-related errors
    Memory(String),
    /// Stack-related errors
    Stack(String),
    /// Execution-related errors
    Execution(String),
    /// Type-related errors
    TypeError(String),
    /// Trap errors
    Trap(String),
    /// Store error
    Store(String),
    /// Module error
    Module(String),
    /// Function error
    Function(String),
    /// Table error
    Table(String),
    /// Global error
    Global(String),
    /// Element error
    Element(String),
    /// Data error
    Data(String),
    /// Value error
    Value(String),
}

impl fmt::Display for RuntimeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Memory(msg) => write!(f, "Memory error: {}", msg),
            Self::Stack(msg) => write!(f, "Stack error: {}", msg),
            Self::Execution(msg) => write!(f, "Execution error: {}", msg),
            Self::TypeError(msg) => write!(f, "Type error: {}", msg),
            Self::Trap(msg) => write!(f, "Trap: {}", msg),
            Self::Store(msg) => write!(f, "store error: {}", msg),
            Self::Module(msg) => write!(f, "module error: {}", msg),
            Self::Function(msg) => write!(f, "function error: {}", msg),
            Self::Table(msg) => write!(f, "table error: {}", msg),
            Self::Global(msg) => write!(f, "global error: {}", msg),
            Self::Element(msg) => write!(f, "element error: {}", msg),
            Self::Data(msg) => write!(f, "data error: {}", msg),
            Self::Value(msg) => write!(f, "value error: {}", msg),
        }
    }
}

/// Configuration for the WASM runtime
#[derive(Debug, Clone)]
pub struct RuntimeConfig {
    /// Initial memory size in pages (64KB per page)
    pub initial_memory_pages: u32,
    /// Maximum memory size in pages
    pub max_memory_pages: u32,
    /// Whether to enable debug logging
    pub debug: bool,
}

impl Default for RuntimeConfig {
    fn default() -> Self {
        Self {
            initial_memory_pages: 1,
            max_memory_pages: 65536, // 4GB
            debug: false,
        }
    }
}

/// Debug logging helper function
/// 
/// Only prints debug messages when the debug flag is enabled in the runtime config
pub fn debug_log(config: &RuntimeConfig, message: &str) {
    if config.debug {
        println!("[DEBUG] {}", message);
    }
}

/// Debug logging helper function with format arguments
/// 
/// Only prints debug messages when the debug flag is enabled in the runtime config
#[macro_export]
macro_rules! debug_log {
    ($config:expr, $($arg:tt)*) => {
        if $config.debug {
            println!("[DEBUG] {}", format!($($arg)*));
        }
    };
}

/// WebAssembly thread
/// 
/// A thread represents a computation over instructions that operates relative
/// to the state of a current frame referring to the module instance in which
/// the computation runs.
#[derive(Debug, Clone)]
pub struct Thread {
    /// The current frame state
    frame_state: FrameState,
    /// The sequence of instructions to execute
    instructions: Vec<Instruction>,
    /// The execution stack
    stack: Stack,
}

impl Thread {
    /// Creates a new thread
    pub fn new(frame_state: FrameState, instructions: Vec<Instruction>) -> Self {
        Self { 
            frame_state, 
            instructions,
            stack: Stack::new(),
        }
    }

    /// Returns the current frame state
    pub fn frame_state(&self) -> &FrameState {
        &self.frame_state
    }

    /// Returns a mutable reference to the current frame state
    pub fn frame_state_mut(&mut self) -> &mut FrameState {
        &mut self.frame_state
    }

    /// Returns the current active frame state (from the top of the stack)
    /// If no frame is on the stack, returns the thread's frame state
    pub fn current_frame_state(&self) -> &FrameState {
        if let Some(frame) = self.stack.top_frame() {
            frame.state()
        } else {
            &self.frame_state
        }
    }

    /// Returns a mutable reference to the current active frame state (from the top of the stack)
    /// If no frame is on the stack, returns the thread's frame state
    pub fn current_frame_state_mut(&mut self) -> &mut FrameState {
        if let Some(frame) = self.stack.top_frame_mut() {
            frame.state_mut()
        } else {
            &mut self.frame_state
        }
    }

    /// Returns the execution stack
    pub fn stack(&self) -> &Stack {
        &self.stack
    }

    /// Returns a mutable reference to the execution stack
    pub fn stack_mut(&mut self) -> &mut Stack {
        &mut self.stack
    }

    /// Returns the instructions to execute
    pub fn instructions(&self) -> &[Instruction] {
        &self.instructions
    }

    /// Returns a mutable reference to the instructions to execute
    pub fn instructions_mut(&mut self) -> &mut Vec<Instruction> {
        &mut self.instructions
    }

    /// Returns the module instance in which the computation runs
    pub fn module(&self) -> &ModuleInstance {
        self.frame_state.module()
    }

    /// Returns a mutable reference to the module instance
    pub fn module_mut(&mut self) -> &mut ModuleInstance {
        self.frame_state.module_mut()
    }

    /// Returns true if there are no more instructions to execute
    pub fn is_empty(&self) -> bool {
        self.instructions.is_empty()
    }

    /// Returns the number of instructions remaining
    pub fn instruction_count(&self) -> usize {
        self.instructions.len()
    }

    /// Pops the next instruction to execute
    pub fn pop_instruction(&mut self) -> Option<Instruction> {
        if self.instructions.is_empty() {
            None
        } else {
            Some(self.instructions.remove(0))
        }
    }

    /// Peeks at the next instruction to execute
    pub fn peek_instruction(&self) -> Option<&Instruction> {
        self.instructions.first()
    }
}

impl fmt::Display for Thread {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}; ", self.frame_state)?;
        for (i, instr) in self.instructions.iter().enumerate() {
            if i > 0 {
                write!(f, " ")?;
            }
            write!(f, "{}", instr)?;
        }
        Ok(())
    }
}

/// WebAssembly configuration
/// 
/// A configuration consists of the current store and an executing thread.
/// The current version of WebAssembly is single-threaded, but configurations
/// with multiple threads may be supported in the future.
#[derive(Debug)]
pub struct Configuration {
    /// The current store
    store: Store,
    /// The executing thread
    thread: Thread,
}

impl Configuration {
    /// Creates a new configuration
    pub fn new(store: Store, thread: Thread) -> Self {
        Self { store, thread }
    }

    /// Returns the current store
    pub fn store(&self) -> &Store {
        &self.store
    }

    /// Returns a mutable reference to the current store
    pub fn store_mut(&mut self) -> &mut Store {
        &mut self.store
    }

    /// Returns the executing thread
    pub fn thread(&self) -> &Thread {
        &self.thread
    }

    /// Returns a mutable reference to the executing thread
    pub fn thread_mut(&mut self) -> &mut Thread {
        &mut self.thread
    }

    /// Returns true if the thread has no more instructions to execute
    pub fn is_empty(&self) -> bool {
        self.thread.is_empty()
    }

    /// Returns the number of instructions remaining in the thread
    pub fn instruction_count(&self) -> usize {
        self.thread.instruction_count()
    }

    /// Pops the next instruction to execute from the thread
    pub fn pop_instruction(&mut self) -> Option<Instruction> {
        self.thread.pop_instruction()
    }

    /// Peeks at the next instruction to execute in the thread
    pub fn peek_instruction(&self) -> Option<&Instruction> {
        self.thread.peek_instruction()
    }
}

impl fmt::Display for Configuration {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}; {}", self.store, self.thread)
    }
}

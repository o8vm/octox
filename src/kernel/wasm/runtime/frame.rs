use alloc::vec::Vec;
use core::fmt;

use crate::wasm::ast::{BlockType, FuncType, ValType };
use crate::wasm::runtime::{ModuleInstance, Value};

/// Frame state
/// 
/// A frame state represents the state of execution within a function,
/// including the values of locals and the module instance.
#[derive(Debug, Clone, PartialEq)]
pub struct FrameState {
    /// The values of locals (including arguments)
    locals: Vec<Value>,
    /// The module instance
    module: ModuleInstance,
}

impl FrameState {
    /// Creates a new frame state
    pub fn new(locals: Vec<Value>, module: ModuleInstance) -> Self {
        Self { locals, module }
    }

    /// Returns the values of locals
    pub fn locals(&self) -> &[Value] {
        &self.locals
    }

    /// Returns a mutable reference to the values of locals
    pub fn locals_mut(&mut self) -> &mut [Value] {
        &mut self.locals
    }

    /// Returns the module instance
    pub fn module(&self) -> &ModuleInstance {
        &self.module
    }

    /// Returns a mutable reference to the module instance
    pub fn module_mut(&mut self) -> &mut ModuleInstance {
        &mut self.module
    }

    /// Sets the module instance
    pub fn set_module(&mut self, module: ModuleInstance) {
        self.module = module;
    }

    /// Expands a block type into a function type
    /// 
    /// This is used to determine the types of values that can be
    /// branched to or returned from a block.
    pub fn expand_block_type(&self, block_type: &BlockType) -> FuncType {
        match block_type {
            BlockType::TypeIndex(index) => {
                // Get the function type from the module instance
                self.module.types[*index as usize].clone()
            }
            BlockType::ValueType(ty) => {
                // Create a function type with no parameters and optional result
                let mut results = Vec::new();
                if let Some(t) = ty {
                    results.push(t.clone());
                }
                FuncType::new(Vec::new(), results)
            }
        }
    }
}

impl fmt::Display for FrameState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{ locals: [")?;
        for (i, value) in self.locals.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", value)?;
        }
        write!(f, "], module: {} }}", self.module)
    }
}

/// Frame
/// 
/// A frame represents an activation of a function, including its
/// return arity and frame state.
#[derive(Debug, Clone, PartialEq)]
pub struct Frame {
    /// The return arity of the function
    arity: usize,
    /// The frame state
    state: FrameState,
}

impl Frame {
    /// Creates a new frame
    pub fn new(arity: usize, state: FrameState) -> Self {
        Self { arity, state }
    }

    /// Returns the return arity
    pub fn arity(&self) -> usize {
        self.arity
    }

    /// Returns the frame state
    pub fn state(&self) -> &FrameState {
        &self.state
    }

    /// Returns a mutable reference to the frame state
    pub fn state_mut(&mut self) -> &mut FrameState {
        &mut self.state
    }
}

impl fmt::Display for Frame {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{ arity: {}, state: {} }}", self.arity, self.state)
    }
} 
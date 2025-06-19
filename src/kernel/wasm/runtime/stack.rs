use alloc::vec::Vec;
use alloc::format;
use core::fmt;

use crate::wasm::ast::{BlockType, FuncType, Instruction, ValType };
use crate::wasm::runtime::{
    ModuleInstance,
    frame::{Frame, FrameState},
};
use crate::wasm::runtime::value::Value;

/// Stack entry
#[derive(Debug, Clone)]
pub enum StackEntry {
    /// Value on the stack
    Value(Value),
    /// Label on the stack
    Label(Label),
    /// Activation frame on the stack
    Frame(Frame),
    /// Block context on the stack
    BlockContext(BlockContext),
}

impl fmt::Display for StackEntry {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Value(value) => write!(f, "{}", value),
            Self::Label(label) => write!(f, "{}", label),
            Self::Frame(frame) => write!(f, "{}", frame),
            Self::BlockContext(context) => write!(f, "{}", context),
        }
    }
}

/// Label
/// 
/// A label represents a branch target, including its arity and
/// the instructions to execute when the branch is taken.
#[derive(Debug, Clone)]
pub struct Label {
    /// The argument arity of the label
    arity: usize,
    /// The continuation to execute when the branch is taken
    continuation: Vec<Instruction>,
}

impl Label {
    /// Creates a new label
    pub fn new(arity: usize, continuation: Vec<Instruction>) -> Self {
        Self { arity, continuation }
    }

    /// Returns the argument arity
    pub fn arity(&self) -> usize {
        self.arity
    }

    /// Returns the continuation
    pub fn continuation(&self) -> &[Instruction] {
        &self.continuation
    }
}

impl fmt::Display for Label {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "label{} {{ ", self.arity)?;
        for (i, instr) in self.continuation.iter().enumerate() {
            if i > 0 {
                write!(f, " ")?;
            }
            write!(f, "{}", instr)?;
        }
        write!(f, " }}")
    }
}

/// Block context
/// 
/// A block context represents the state of execution within a block,
/// including the surrounding labels and their continuations.
/// The context is indexed by the count k of labels surrounding a hole [_]
/// that marks the place where the next step of computation is taking place.
#[derive(Debug, Clone)]
pub struct BlockContext {
    /// The values on the stack before the hole
    values: Vec<Value>,
    /// The labels surrounding the hole, in order from innermost to outermost
    labels: Vec<Label>,
    /// The instructions after the hole
    instructions: Vec<Instruction>,
}

impl BlockContext {
    /// Creates a new block context
    pub fn new(values: Vec<Value>, labels: Vec<Label>, instructions: Vec<Instruction>) -> Self {
        Self { values, labels, instructions }
    }

    /// Creates a new empty block context (B₀)
    pub fn empty() -> Self {
        Self {
            values: Vec::new(),
            labels: Vec::new(),
            instructions: Vec::new(),
        }
    }

    /// Creates a new block context with a label (Bₖ₊₁)
    pub fn with_label(mut self, label: Label) -> Self {
        self.labels.push(label);
        self
    }

    /// Returns the number of surrounding labels
    pub fn label_count(&self) -> usize {
        self.labels.len()
    }

    /// Returns the values before the hole
    pub fn values(&self) -> &[Value] {
        &self.values
    }

    /// Returns the labels surrounding the hole
    pub fn labels(&self) -> &[Label] {
        &self.labels
    }

    /// Returns the instructions after the hole
    pub fn instructions(&self) -> &[Instruction] {
        &self.instructions
    }

    /// Returns the label at the given index
    /// 
    /// The index l corresponds to the number of surrounding label instructions
    /// that must be hopped over to reach the target label.
    pub fn get_label(&self, index: usize) -> Option<&Label> {
        if index >= self.labels.len() {
            None
        } else {
            // Labels are stored in order from innermost to outermost,
            // so we need to reverse the index
            Some(&self.labels[self.labels.len() - 1 - index])
        }
    }

    /// Removes the label at the given index and returns its continuation
    /// 
    /// This is used when a branch instruction is executed to replace
    /// the targeted label and associated instruction sequence with the
    /// label's continuation.
    pub fn remove_label(&mut self, index: usize) -> Option<Vec<Instruction>> {
        if index >= self.labels.len() {
            None
        } else {
            // Remove the label and return its continuation
            let label = self.labels.remove(self.labels.len() - 1 - index);
            Some(label.continuation().to_vec())
        }
    }
}

impl fmt::Display for BlockContext {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Display values
        for value in &self.values {
            write!(f, "{} ", value)?;
        }
        write!(f, "[_] ")?;

        // Display labels
        for label in self.labels.iter().rev() {
            write!(f, "label{} {{ {} }} ", label.arity(), label.continuation().iter().map(|i| format!("{}", i)).collect::<Vec<_>>().join(" "))?;
        }

        // Display instructions
        for instr in &self.instructions {
            write!(f, "{} ", instr)?;
        }
        Ok(())
    }
}

/// WebAssembly stack
/// 
/// The stack contains three kinds of entries:
/// - Values: the operands of instructions
/// - Labels: active structured control instructions that can be targeted by branches
/// - Activations: the call frames of active function calls
#[derive(Debug, Default, Clone)]
pub struct Stack {
    /// The stack entries
    entries: Vec<StackEntry>,
}

impl Stack {
    /// Creates a new empty stack
    pub fn new() -> Self {
        Self { entries: Vec::new() }
    }

    /// Returns the number of entries on the stack
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Returns true if the stack is empty
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Pushes a value onto the stack
    pub fn push_value(&mut self, value: Value) {
        self.entries.push(StackEntry::Value(value));
    }

    /// Pushes a label onto the stack
    pub fn push_label(&mut self, label: Label) {
        self.entries.push(StackEntry::Label(label));
    }

    /// Pushes a frame onto the stack
    pub fn push_frame(&mut self, frame: Frame) {
        self.entries.push(StackEntry::Frame(frame));
    }

    /// Pushes a block context onto the stack
    pub fn push_block_context(&mut self, context: BlockContext) {
        self.entries.push(StackEntry::BlockContext(context));
    }

    /// Pops a value from the stack
    pub fn pop_value(&mut self) -> Option<Value> {
        match self.entries.pop() {
            Some(StackEntry::Value(value)) => Some(value),
            Some(entry) => {
                self.entries.push(entry);
                None
            }
            None => None,
        }
    }

    /// Pops a label from the stack
    pub fn pop_label(&mut self) -> Option<Label> {
        match self.entries.pop() {
            Some(StackEntry::Label(label)) => Some(label),
            Some(entry) => {
                self.entries.push(entry);
                None
            }
            None => None,
        }
    }

    /// Pops a frame from the stack
    pub fn pop_frame(&mut self) -> Option<Frame> {
        match self.entries.pop() {
            Some(StackEntry::Frame(frame)) => Some(frame),
            Some(entry) => {
                self.entries.push(entry);
                None
            }
            None => None,
        }
    }

    /// Pops a block context from the stack
    pub fn pop_block_context(&mut self) -> Option<BlockContext> {
        match self.entries.pop() {
            Some(StackEntry::BlockContext(context)) => Some(context),
            Some(entry) => {
                // Put the entry back
                self.entries.push(entry);
                None
            }
            None => None,
        }
    }

    /// Returns a reference to the top value on the stack
    pub fn top_value(&self) -> Option<&Value> {
        self.entries.iter()
            .rev()
            .find_map(|entry| match entry {
                StackEntry::Value(value) => Some(value),
                _ => None,
            })
    }

    /// Returns a reference to the top label on the stack
    pub fn top_label(&self) -> Option<&Label> {
        self.entries.iter()
            .rev()
            .find_map(|entry| match entry {
                StackEntry::Label(label) => Some(label),
                _ => None,
            })
    }

    /// Returns a reference to the top frame on the stack
    pub fn top_frame(&self) -> Option<&Frame> {
        self.entries.iter()
            .rev()
            .find_map(|entry| match entry {
                StackEntry::Frame(frame) => Some(frame),
                _ => None,
            })
    }

    /// Returns a mutable reference to the top frame on the stack
    pub fn top_frame_mut(&mut self) -> Option<&mut Frame> {
        self.entries.iter_mut()
            .rev()
            .find_map(|entry| match entry {
                StackEntry::Frame(frame) => Some(frame),
                _ => None,
            })
    }

    /// Returns the number of values on the stack
    pub fn value_count(&self) -> usize {
        self.entries.iter()
            .filter(|entry| matches!(entry, StackEntry::Value(_)))
            .count()
    }

    /// Returns the number of labels on the stack
    pub fn label_count(&self) -> usize {
        self.entries.iter()
            .filter(|entry| matches!(entry, StackEntry::Label(_)))
            .count()
    }

    /// Returns the number of frames on the stack
    pub fn frame_count(&self) -> usize {
        self.entries.iter()
            .filter(|entry| matches!(entry, StackEntry::Frame(_)))
            .count()
    }

    /// Returns the number of block contexts on the stack
    pub fn block_context_count(&self) -> usize {
        self.entries.iter()
            .filter(|entry| matches!(entry, StackEntry::BlockContext(_)))
            .count()
    }

    /// Clears the stack
    pub fn clear(&mut self) {
        self.entries.clear();
    }

    /// Gets the top block context from the stack
    pub fn top_block_context(&self) -> Option<&BlockContext> {
        for entry in self.entries.iter().rev() {
            if let StackEntry::BlockContext(context) = entry {
                return Some(context);
            }
        }
        None
    }

    /// Gets a mutable reference to the top block context from the stack
    pub fn top_block_context_mut(&mut self) -> Option<&mut BlockContext> {
        for entry in self.entries.iter_mut().rev() {
            if let StackEntry::BlockContext(context) = entry {
                return Some(context);
            }
        }
        None
    }

    /// Gets a label at the specified index from the top of the stack
    /// 
    /// The index 0 refers to the topmost label, index 1 to the second topmost, etc.
    /// 
    /// # Arguments
    /// 
    /// * `index` - The index of the label to retrieve (0-based from top)
    /// 
    /// # Returns
    /// 
    /// * `Option<&Label>` - A reference to the label if found, None otherwise
    pub fn get_label(&self, index: usize) -> Option<&Label> {
        let mut label_count = 0;
        for entry in self.entries.iter().rev() {
            if let StackEntry::Label(label) = entry {
                if label_count == index {
                    return Some(label);
                }
                label_count += 1;
            }
        }
        None
    }

    /// Checks if the top of the stack is a value
    /// 
    /// # Returns
    /// 
    /// * `bool` - True if the top entry is a value, false otherwise
    pub fn is_top_value(&self) -> bool {
        self.entries.last().map_or(false, |entry| matches!(entry, StackEntry::Value(_)))
    }

    /// Gets a frame at the specified index from the top of the stack
    /// 
    /// The index 0 refers to the topmost frame, index 1 to the second topmost, etc.
    /// 
    /// # Arguments
    /// 
    /// * `index` - The index of the frame to retrieve (0-based from top)
    /// 
    /// # Returns
    /// 
    /// * `Option<&Frame>` - A reference to the frame if found, None otherwise
    pub fn get_frame(&self, index: usize) -> Option<&Frame> {
        let mut frame_count = 0;
        for entry in self.entries.iter().rev() {
            if let StackEntry::Frame(frame) = entry {
                if frame_count == index {
                    return Some(frame);
                }
                frame_count += 1;
            }
        }
        None
    }

    /// Gets a mutable reference to a frame at the specified index from the top of the stack
    /// 
    /// The index 0 refers to the topmost frame, index 1 to the second topmost, etc.
    /// 
    /// # Arguments
    /// 
    /// * `index` - The index of the frame to retrieve (0-based from top)
    /// 
    /// # Returns
    /// 
    /// * `Option<&mut Frame>` - A mutable reference to the frame if found, None otherwise
    pub fn get_frame_mut(&mut self, index: usize) -> Option<&mut Frame> {
        let mut frame_count = 0;
        for entry in self.entries.iter_mut().rev() {
            if let StackEntry::Frame(frame) = entry {
                if frame_count == index {
                    return Some(frame);
                }
                frame_count += 1;
            }
        }
        None
    }
}

impl fmt::Display for Stack {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        for (i, entry) in self.entries.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", entry)?;
        }
        write!(f, "]")
    }
}

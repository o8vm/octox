use alloc::vec::Vec;
use alloc::boxed::Box;
use core::fmt;

use crate::wasm::ast::Instruction;
use crate::wasm::runtime::{
    FrameState,
    value::Value,
    stack::Label,
    frame::Frame,
};

/// Evaluation context
/// 
/// An evaluation context represents a position in an instruction sequence
/// where reduction can occur. It is used to enable reduction inside instruction
/// sequences and administrative forms, as well as the propagation of traps.
/// 
/// E ::= [_] | val* E instr* | label_n{instr*} E end
#[derive(Debug, Clone)]
pub enum EvaluationContext {
    /// Empty context (hole)
    Hole,
    /// Values followed by a context and instructions
    ValuesContextInstructions {
        /// Values before the context
        values: Vec<Value>,
        /// The context
        context: Box<EvaluationContext>,
        /// Instructions after the context
        instructions: Vec<Instruction>,
    },
    /// Label with instructions, context, and end
    LabelContextEnd {
        /// The label
        label: Label,
        /// The context
        context: Box<EvaluationContext>,
    },
    /// Frame with instructions, context, and end
    FrameContextEnd {
        /// The frame
        frame: Frame,
        /// The context
        context: Box<EvaluationContext>,
    },
}

impl EvaluationContext {
    /// Creates a new empty context (hole)
    pub fn new() -> Self {
        Self::Hole
    }

    /// Creates a context with values, another context, and instructions
    pub fn with_values_context_instructions(
        values: Vec<Value>,
        context: EvaluationContext,
        instructions: Vec<Instruction>,
    ) -> Self {
        Self::ValuesContextInstructions {
            values,
            context: Box::new(context),
            instructions,
        }
    }

    /// Creates a context with a label, another context, and end
    pub fn with_label_context_end(label: Label, context: EvaluationContext) -> Self {
        Self::LabelContextEnd {
            label,
            context: Box::new(context),
        }
    }

    /// Creates a context with a frame, another context, and end
    pub fn with_frame_context_end(frame: Frame, context: EvaluationContext) -> Self {
        Self::FrameContextEnd {
            frame,
            context: Box::new(context),
        }
    }

    /// Fills the hole in the context with instructions
    pub fn fill(&self, instructions: Vec<Instruction>) -> Vec<Instruction> {
        match self {
            Self::Hole => instructions,
            Self::ValuesContextInstructions { values, context, instructions: after } => {
                let mut result = Vec::new();
                // Add values
                for value in values {
                    result.push(Instruction::Administrative(crate::wasm::ast::AdministrativeInstruction::Value(value.clone())));
                }
                // Add instructions from the context
                result.extend(context.fill(instructions));
                // Add instructions after the context
                result.extend(after.clone());
                result
            }
            Self::LabelContextEnd { label, context } => {
                let mut result = Vec::new();
                // Add label
                result.push(Instruction::Administrative(crate::wasm::ast::AdministrativeInstruction::Label {
                    arity: label.arity(),
                    instructions: label.continuation().to_vec(),
                }));
                // Add instructions from the context
                result.extend(context.fill(instructions));
                // Add end
                result.push(Instruction::Control(crate::wasm::ast::ControlInstruction::End));
                result
            }
            Self::FrameContextEnd { frame, context } => {
                let mut result = Vec::new();
                // Add frame
                result.push(Instruction::Administrative(crate::wasm::ast::AdministrativeInstruction::Frame {
                    arity: frame.arity(),
                    state: frame.state().clone(),
                    instructions: Vec::new(),
                }));
                // Add instructions from the context
                result.extend(context.fill(instructions));
                // Add end
                result.push(Instruction::Control(crate::wasm::ast::ControlInstruction::End));
                result
            }
        }
    }

    /// Returns true if this is a hole
    pub fn is_hole(&self) -> bool {
        matches!(self, Self::Hole)
    }

    /// Returns true if this context can propagate traps
    pub fn can_propagate_trap(&self) -> bool {
        !self.is_hole()
    }
}

impl fmt::Display for EvaluationContext {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Hole => write!(f, "[_]"),
            Self::ValuesContextInstructions { values, context, instructions } => {
                // Print values
                for (i, value) in values.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{}", value)?;
                }
                // Print context
                write!(f, " {} ", context)?;
                // Print instructions
                for (i, instr) in instructions.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{}", instr)?;
                }
                Ok(())
            }
            Self::LabelContextEnd { label, context } => {
                write!(f, "label{} {{ ", label.arity())?;
                for (i, instr) in label.continuation().iter().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{}", instr)?;
                }
                write!(f, " }} {} end", context)
            }
            Self::FrameContextEnd { frame, context } => {
                write!(f, "frame{} {{ ", frame.arity())?;
                write!(f, "{}", frame.state())?;
                write!(f, " }} {} end", context)
            }
        }
    }
}

/// Evaluation state
/// 
/// Represents the current state of evaluation, including the store,
/// frame state, and evaluation context.
#[derive(Debug)]
pub struct EvaluationState<'a> {
    /// The current store
    store: &'a mut crate::wasm::runtime::Store,
    /// The current frame state
    frame_state: FrameState,
    /// The current evaluation context
    context: EvaluationContext,
}

impl<'a> EvaluationState<'a> {
    /// Creates a new evaluation state
    pub fn new(
        store: &'a mut crate::wasm::runtime::Store,
        frame_state: FrameState,
        context: EvaluationContext,
    ) -> Self {
        Self {
            store,
            frame_state,
            context,
        }
    }

    /// Returns a reference to the store
    pub fn store(&self) -> &crate::wasm::runtime::Store {
        self.store
    }

    /// Returns a mutable reference to the store
    pub fn store_mut(&mut self) -> &mut crate::wasm::runtime::Store {
        self.store
    }

    /// Returns a reference to the frame state
    pub fn frame_state(&self) -> &FrameState {
        &self.frame_state
    }

    /// Returns a mutable reference to the frame state
    pub fn frame_state_mut(&mut self) -> &mut FrameState {
        &mut self.frame_state
    }

    /// Returns a reference to the evaluation context
    pub fn context(&self) -> &EvaluationContext {
        &self.context
    }

    /// Returns a mutable reference to the evaluation context
    pub fn context_mut(&mut self) -> &mut EvaluationContext {
        &mut self.context
    }

    /// Reduces the current instruction sequence in the context
    /// 
    /// This implements the reduction rules for evaluation contexts:
    /// 
    /// S; F; E[instr*] → S'; F'; E[instr'*]
    /// (if S; F; instr* → S'; F'; instr'*)
    /// 
    /// S; F; frame_n{F'} instr* end → S'; F; frame_n{F''} instr'* end
    /// (if S; F'; instr* → S'; F''; instr'*)
    /// 
    /// S; F; E[trap] → S; F; trap
    /// (if E ≠ [_])
    /// 
    /// S; F; frame_n{F'} trap end → S; F; trap
    pub fn reduce(&mut self, instructions: Vec<Instruction>) -> crate::wasm::runtime::RuntimeResult<Vec<Instruction>> {
        // TODO: Implement reduction rules
        // For now, just return the instructions unchanged
        Ok(instructions)
    }
}

impl<'a> fmt::Display for EvaluationState<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}; {}; {}", self.store, self.frame_state, self.context)
    }
} 
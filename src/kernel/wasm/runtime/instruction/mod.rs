//! WebAssembly Instruction Module
//! 
//! This module provides the implementation of WebAssembly instructions.
//! It includes the execution logic for all WASM instructions defined in the specification.

use alloc::string::ToString;
use alloc::format;

use crate::wasm::ast::Instruction;
use crate::wasm::runtime::{
    RuntimeResult,
    RuntimeError,
    Store,
    Thread,
    Value,
    Stack,
    Frame,
    ModuleInstance,
};
use crate::wasm::ast::{NumericInstruction, ControlInstruction, VectorInstruction};

mod numeric;
pub use numeric::execute_numeric;

mod reference;
pub use reference::{Reference, execute_reference};

mod vector;
pub use vector::{Vector, execute_vector};

mod parametric;
pub use parametric::execute_parametric;

mod variable;
pub use variable::{Variable, execute_variable};

mod table;
pub use table::{Table, execute_table};

mod memory;
pub use memory::{Memory, execute_memory};

mod control;
pub use control::{Control, execute_control};

mod block;
pub use block::Block;

mod function;
pub use function::{Function, execute_function, invoke_with_reduction_rule};

mod expression;
pub use expression::{
    ExpressionEval, 
    execute_expression, 
    execute_constant_expression,
    execute_expression_and_update_thread,
    evaluate_const_expr,
    evaluate_const_expr_with_type_validation,
    evaluate_const_exprs,
};

/// Trait for executing WebAssembly instructions
pub trait InstructionExecutor {
    /// Executes a single instruction
    /// 
    /// # Arguments
    /// 
    /// * `store` - The current store state
    /// * `thread` - The current thread state
    /// * `instruction` - The instruction to execute
    /// 
    /// # Returns
    /// 
    /// * `RuntimeResult<()>` - The result of the execution
    fn execute(
        &self,
        store: &mut Store,
        thread: &mut Thread,
        instruction: &Instruction,
    ) -> RuntimeResult<()>;
}

/// Default implementation of the instruction executor
#[derive(Debug, Clone)]
pub struct DefaultInstructionExecutor;

impl InstructionExecutor for DefaultInstructionExecutor {
    fn execute(
        &self,
        store: &mut Store,
        thread: &mut Thread,
        instruction: &Instruction,
    ) -> RuntimeResult<()> {
        match instruction {
            // Numeric instructions
            Instruction::Numeric(_) => {
                execute_numeric(store, thread, instruction)
            }
            // Reference instructions (as part of Control instructions)
            Instruction::Control(ControlInstruction::RefNull(_)) |
            Instruction::Control(ControlInstruction::RefIsNull) |
            Instruction::Control(ControlInstruction::RefFunc(_)) => {
                execute_reference(store, thread, instruction)
            }
            // Control instructions
            Instruction::Control(ControlInstruction::Nop) |
            Instruction::Control(ControlInstruction::Unreachable) |
            Instruction::Control(ControlInstruction::Block { .. }) |
            Instruction::Control(ControlInstruction::Loop { .. }) |
            Instruction::Control(ControlInstruction::If { .. }) |
            Instruction::Control(ControlInstruction::Br { .. }) |
            Instruction::Control(ControlInstruction::BrIf { .. }) |
            Instruction::Control(ControlInstruction::BrTable { .. }) |
            Instruction::Control(ControlInstruction::Return) |
            Instruction::Control(ControlInstruction::Call { .. }) |
            Instruction::Control(ControlInstruction::CallIndirect { .. }) |
            Instruction::Control(ControlInstruction::End) => {
                execute_control(store, thread, instruction)
            }
            // Vector instructions
            Instruction::Vector(_) => {
                execute_vector(store, thread, instruction)
            }
            // Parametric instructions
            Instruction::Parametric(_) => {
                execute_parametric(store, thread, instruction)
            }
            // Variable instructions
            Instruction::Variable(_) => {
                execute_variable(store, thread, instruction)
            }
            // Table instructions
            Instruction::Table(_) => {
                execute_table(store, thread, instruction)
            }
            // Memory instructions
            Instruction::Memory(mem_inst) => {
                crate::wasm::runtime::debug_log(store.config(), &format!("execute_memory: instruction = {:?}", mem_inst));
                execute_memory(store, thread, instruction)
            }
            // Function instructions (administrative)
            Instruction::Administrative(admin_inst) => {
                match admin_inst {
                    crate::wasm::ast::AdministrativeInstruction::Invoke(_) => {
                        execute_function(store, thread, instruction)
                    }
                    crate::wasm::ast::AdministrativeInstruction::Value(_) => {
                        // Handle value instructions (expressions)
                        // This would be used for evaluating expressions in various contexts
                        Err(RuntimeError::Execution(format!(
                            "Value instruction not yet implemented: {:?}",
                            admin_inst
                        )))
                    }
                    _ => Err(RuntimeError::Execution(format!(
                        "Unimplemented administrative instruction: {:?}",
                        admin_inst
                    ))),
                }
            }
            // TODO: Implement other instruction categories
            _ => Err(RuntimeError::Execution(format!(
                "Unimplemented instruction: {:?}",
                instruction
            ))),
        }
    }
}

/// Helper functions for instruction execution
pub(crate) mod helpers {
    use super::*;

    /// Validates the stack state for an instruction
    pub(crate) fn validate_stack(
        stack: &Stack,
        expected_types: &[Value],
    ) -> RuntimeResult<()> {
        // TODO: Implement stack validation
        Ok(())
    }

    /// Validates the frame state for an instruction
    pub(crate) fn validate_frame(
        frame: &Frame,
        expected_locals: &[Value],
    ) -> RuntimeResult<()> {
        // TODO: Implement frame validation
        Ok(())
    }

    /// Validates the module state for an instruction
    pub(crate) fn validate_module(
        module: &ModuleInstance,
        expected_imports: &[Value],
    ) -> RuntimeResult<()> {
        // TODO: Implement module validation
        Ok(())
    }
} 
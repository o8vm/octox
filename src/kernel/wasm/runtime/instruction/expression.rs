//! Expression Instructions implementation for WebAssembly runtime.
//!
//! Implements the semantics of expression evaluation as described in the WebAssembly specification (4.4.11 Expressions).
//!
//! # Usage Examples
//!
//! This module provides unified expression evaluation that can be used to refactor other parts of the codebase:
//!
//! ## Function Body Execution
//! ```rust
//! // Before: Manual instruction execution
//! let executor = DefaultInstructionExecutor;
//! for instruction in &instructions {
//!     executor.execute(store, thread, instruction)?;
//! }
//!
//! // After: Using execute_expression
//! let expression = Expression::general(instructions);
//! let _result = execute_expression(store, thread, &expression)?;
//! ```
//!
//! ## Block Execution
//! ```rust
//! // Before: Manual instruction execution
//! let executor = DefaultInstructionExecutor;
//! for instruction in instructions {
//!     executor.execute(store, thread, instruction)?;
//! }
//!
//! // After: Using execute_expression
//! let expression = Expression::general(instructions.to_vec());
//! let _result = execute_expression(store, thread, &expression)?;
//! ```
//!
//! ## Global Initialization
//! ```rust
//! // Before: Manual ConstExpr evaluation
//! // (implementation would be complex and duplicated)
//!
//! // After: Using evaluate_const_expr
//! let value = evaluate_const_expr(store, thread, &global.init)?;
//! let global_instance = GlobalInstance::new(global.ty.clone(), value);
//! ```
//!
//! ## Element Segment Initialization
//! ```rust
//! // Before: Manual evaluation of multiple ConstExpr
//! let mut elements = Vec::new();
//! for const_expr in &element_segment.elements {
//!     // Complex manual evaluation
//! }
//!
//! // After: Using evaluate_const_exprs
//! let elements = evaluate_const_exprs(store, thread, &element_segment.elements)?;
//! ```
//!
//! ## Data Segment Offset Evaluation
//! ```rust
//! // Before: Manual offset evaluation
//! // (implementation would be complex)
//!
//! // After: Using evaluate_const_expr
//! let offset = evaluate_const_expr(store, thread, &data_segment.offset)?;
//! ```

use alloc::format;
use alloc::vec::Vec;
use alloc::string::ToString;

use crate::wasm::runtime::{
    RuntimeResult,
    RuntimeError,
    Store,
    Thread,
    Value,
    stack::{Label},
    frame::{Frame, FrameState},
};
use crate::wasm::ast::{Expression, Instruction, ValType};
use crate::wasm::runtime::instruction::InstructionExecutor;

/// Expression instruction implementation.
pub struct ExpressionEval;

impl ExpressionEval {
    /// Evaluates an expression relative to a current frame pointing to its containing module instance.
    ///
    /// # Semantics (4.4.11 Expressions)
    /// An expression is evaluated relative to a current frame pointing to its containing module instance.
    /// 1. Jump to the start of the instruction sequence instr* of the expression.
    /// 2. Execute the instruction sequence.
    /// 3. Assert: due to validation, the top of the stack contains a value.
    /// 4. Pop the value val from the stack.
    /// The value val is the result of the evaluation.
    ///
    /// # Specification
    /// S; F; instr* → S'; F'; instr'* (if S; F; instr* end → S'; F'; instr'* end)
    /// Note: Evaluation iterates this reduction rule until reaching a value.
    /// Expressions constituting function bodies are executed during function invocation.
    ///
    /// # Arguments
    ///
    /// * `store` - The current store state
    /// * `thread` - The current thread state
    /// * `expression` - The expression to evaluate
    ///
    /// # Returns
    ///
    /// * `RuntimeResult<Value>` - The result value of the expression evaluation
    pub fn evaluate(
        store: &mut Store,
        thread: &mut Thread,
        expression: &Expression,
    ) -> RuntimeResult<Value> {
        // 1. Jump to the start of the instruction sequence instr* of the expression.
        let instructions = Self::get_expression_instructions(expression)?;
        
        // Create a new thread context for expression evaluation
        // This preserves the current frame state while allowing isolated execution
        let mut expr_thread = Thread::new(
            thread.frame_state().clone(),
            instructions,
        );

        // 2. Execute the instruction sequence.
        // Note: Evaluation iterates this reduction rule until reaching a value.
        // This handles control flow instructions that may require multiple iterations.
        let executor = crate::wasm::runtime::instruction::DefaultInstructionExecutor;
        
        // Execute instructions until we reach a value (no more instructions to execute)
        while !expr_thread.is_empty() {
            let instruction = expr_thread.pop_instruction().ok_or_else(|| {
                RuntimeError::Execution("Failed to get next instruction during expression evaluation".to_string())
            })?;
            
            executor.execute(store, &mut expr_thread, &instruction)?;
        }

        // 3. Assert: due to validation, the top of the stack contains a value.
        if expr_thread.stack().value_count() == 0 {
            return Err(RuntimeError::Execution(
                "Expression evaluation failed: no value on stack after execution".to_string()
            ));
        }

        // 4. Pop the value val from the stack.
        let result_value = expr_thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Stack("Failed to pop result value from expression evaluation".to_string())
        })?;

        Ok(result_value)
    }

    /// Evaluates a constant expression.
    ///
    /// Constant expressions are used for initialization values for globals,
    /// elements and offsets of element segments, and offsets of data segments.
    ///
    /// # Arguments
    ///
    /// * `store` - The current store state
    /// * `thread` - The current thread state
    /// * `expression` - The constant expression to evaluate
    ///
    /// # Returns
    ///
    /// * `RuntimeResult<Value>` - The constant value
    pub fn evaluate_constant(
        store: &mut Store,
        thread: &mut Thread,
        expression: &Expression,
    ) -> RuntimeResult<Value> {
        if !expression.is_constant() {
            return Err(RuntimeError::Execution(
                "Expected constant expression".to_string()
            ));
        }

        Self::evaluate(store, thread, expression)
    }

    /// Gets the instructions from an expression.
    ///
    /// # Arguments
    ///
    /// * `expression` - The expression to extract instructions from
    ///
    /// # Returns
    ///
    /// * `RuntimeResult<Vec<Instruction>>` - The sequence of instructions
    fn get_expression_instructions(expression: &Expression) -> RuntimeResult<Vec<Instruction>> {
        match expression {
            Expression::Constant { instruction, .. } => {
                // For constant expressions, we have a single instruction
                let mut instructions = Vec::new();
                instructions.push(instruction.clone());
                Ok(instructions)
            }
            Expression::General { instructions } => {
                // For general expressions, we have a sequence of instructions
                Ok(instructions.clone())
            }
        }
    }

    /// Validates that an expression produces a value of the expected type.
    ///
    /// # Arguments
    ///
    /// * `expression` - The expression to validate
    /// * `expected_type` - The expected result type
    ///
    /// # Returns
    ///
    /// * `RuntimeResult<()>` - Success if validation passes
    pub fn validate_result_type(
        expression: &Expression,
        expected_type: ValType,
    ) -> RuntimeResult<()> {
        let actual_type = expression.result_type().ok_or_else(|| {
            RuntimeError::TypeError("Expression has no result type".to_string())
        })?;

        if actual_type != expected_type {
            return Err(RuntimeError::TypeError(format!(
                "Expression result type mismatch: expected {:?}, got {:?}",
                expected_type, actual_type
            )));
        }

        Ok(())
    }

    /// Evaluates an expression and validates the result type.
    ///
    /// # Arguments
    ///
    /// * `store` - The current store state
    /// * `thread` - The current thread state
    /// * `expression` - The expression to evaluate
    /// * `expected_type` - The expected result type
    ///
    /// # Returns
    ///
    /// * `RuntimeResult<Value>` - The result value if type matches
    pub fn evaluate_with_type_validation(
        store: &mut Store,
        thread: &mut Thread,
        expression: &Expression,
        expected_type: ValType,
    ) -> RuntimeResult<Value> {
        // Validate the expression result type first
        Self::validate_result_type(expression, expected_type)?;
        
        // Evaluate the expression
        Self::evaluate(store, thread, expression)
    }

    /// Evaluates multiple expressions in sequence.
    ///
    /// # Arguments
    ///
    /// * `store` - The current store state
    /// * `thread` - The current thread state
    /// * `expressions` - The expressions to evaluate
    ///
    /// # Returns
    ///
    /// * `RuntimeResult<Vec<Value>>` - The results of all expressions
    pub fn evaluate_multiple(
        store: &mut Store,
        thread: &mut Thread,
        expressions: &[Expression],
    ) -> RuntimeResult<Vec<Value>> {
        let mut results = Vec::new();
        
        for expression in expressions {
            let result = Self::evaluate(store, thread, expression)?;
            results.push(result);
        }
        
        Ok(results)
    }

    /// Evaluates an expression and pushes the result onto the stack.
    ///
    /// # Arguments
    ///
    /// * `store` - The current store state
    /// * `thread` - The current thread state
    /// * `expression` - The expression to evaluate
    ///
    /// # Returns
    ///
    /// * `RuntimeResult<()>` - Success if evaluation and push succeed
    pub fn evaluate_and_push(
        store: &mut Store,
        thread: &mut Thread,
        expression: &Expression,
    ) -> RuntimeResult<()> {
        let result = Self::evaluate(store, thread, expression)?;
        thread.stack_mut().push_value(result);
        Ok(())
    }

    /// Checks if an expression is empty (has no instructions).
    ///
    /// # Arguments
    ///
    /// * `expression` - The expression to check
    ///
    /// # Returns
    ///
    /// * `bool` - True if the expression is empty
    pub fn is_empty(expression: &Expression) -> bool {
        expression.is_empty()
    }

    /// Gets the number of instructions in an expression.
    ///
    /// # Arguments
    ///
    /// * `expression` - The expression to count instructions for
    ///
    /// # Returns
    ///
    /// * `usize` - The number of instructions
    pub fn instruction_count(expression: &Expression) -> usize {
        expression.instruction_count()
    }

    /// Evaluates an expression and updates the thread with the result.
    /// 
    /// # Arguments
    /// 
    /// * `store` - The current store (will be updated)
    /// * `thread` - The current thread state (will be updated)
    /// * `expression` - The expression to evaluate
    ///
    /// # Returns
    ///
    /// * `RuntimeResult<Value>` - The result value of the expression evaluation
    pub fn evaluate_and_update_thread(
        store: &mut Store,
        thread: &mut Thread,
        expression: &Expression,
    ) -> RuntimeResult<Value> {
        crate::wasm::runtime::debug_log(store.config(), "=== EVALUATE_AND_UPDATE_THREAD ===");
        crate::wasm::runtime::debug_log(store.config(), &format!("Expression instruction count: {}", expression.instruction_count()));
        crate::wasm::runtime::debug_log(store.config(), &format!("Initial stack depth: {}", thread.stack().frame_count()));
        crate::wasm::runtime::debug_log(store.config(), &format!("Initial stack values: {}", thread.stack().value_count()));
        if let Some(frame) = thread.stack().top_frame() {
            crate::wasm::runtime::debug_log(store.config(), &format!("Initial top frame locals: {:?}", frame.state().locals()));
        }
        crate::wasm::runtime::debug_log(store.config(), &format!("Initial thread instructions: {:?}", thread.instructions()));
        
        // 1. Jump to the start of the instruction sequence instr* of the expression.
        let instructions = Self::get_expression_instructions(expression)?;
        
        crate::wasm::runtime::debug_log(store.config(), &format!("Adding {} instructions to thread", instructions.len()));
        
        // Add the expression instructions to the current thread
        let mut new_instructions = instructions.clone();
        new_instructions.extend(thread.instructions().to_vec());
        thread.instructions_mut().clear();
        thread.instructions_mut().extend(new_instructions);
        crate::wasm::runtime::debug_log(store.config(), &format!("Added instructions to thread: {:?}", thread.instructions()));

        // 2. Execute the instruction sequence.
        // Note: Evaluation iterates this reduction rule until reaching a value.
        let executor = crate::wasm::runtime::instruction::DefaultInstructionExecutor;
        
        let mut instruction_count = 0;
        // Execute instructions until we reach a value (no more instructions to execute)
        while !thread.is_empty() {
            let instruction = thread.pop_instruction().ok_or_else(|| {
                RuntimeError::Execution("Failed to get next instruction during expression evaluation".to_string())
            })?;
            
            instruction_count += 1;
            crate::wasm::runtime::debug_log(store.config(), &format!("execute_expression: instruction {} = {:?}", instruction_count, instruction));
            crate::wasm::runtime::debug_log(store.config(), &format!("Stack depth before instruction: {}", thread.stack().frame_count()));
            if let Some(frame) = thread.stack().top_frame() {
                crate::wasm::runtime::debug_log(store.config(), &format!("Top frame locals before instruction: {:?}", frame.state().locals()));
            }
            
            // Check if this is an end instruction and log it specially
            if let Instruction::Control(crate::wasm::ast::ControlInstruction::End) = instruction {
                crate::wasm::runtime::debug_log(store.config(), "*** EXECUTING END INSTRUCTION ***");
                crate::wasm::runtime::debug_log(store.config(), &format!("End instruction: stack has {} values", thread.stack().value_count()));
                crate::wasm::runtime::debug_log(store.config(), &format!("End instruction: stack depth: {}", thread.stack().frame_count()));
            }
            
            // Check if this is a label continuation instruction
            if let Instruction::Control(crate::wasm::ast::ControlInstruction::End) = instruction {
                crate::wasm::runtime::debug_log(store.config(), "*** LABEL CONTINUATION EXECUTION ***");
                crate::wasm::runtime::debug_log(store.config(), "Label continuation: executing end instruction");
            }
            
            executor.execute(store, thread, &instruction)?;
            
            // Check if this was an end instruction and log the result
            if let Instruction::Control(crate::wasm::ast::ControlInstruction::End) = instruction {
                crate::wasm::runtime::debug_log(store.config(), "*** END INSTRUCTION COMPLETED ***");
                crate::wasm::runtime::debug_log(store.config(), &format!("End instruction: stack has {} values", thread.stack().value_count()));
                crate::wasm::runtime::debug_log(store.config(), &format!("End instruction: stack depth: {}", thread.stack().frame_count()));
                if let Some(frame) = thread.stack().top_frame() {
                    crate::wasm::runtime::debug_log(store.config(), &format!("End instruction: top frame locals: {:?}", frame.state().locals()));
                }
            }
            
            crate::wasm::runtime::debug_log(store.config(), &format!("Stack depth after instruction: {}", thread.stack().frame_count()));
            if let Some(frame) = thread.stack().top_frame() {
                crate::wasm::runtime::debug_log(store.config(), &format!("Top frame locals after instruction: {:?}", frame.state().locals()));
            }
        }

        crate::wasm::runtime::debug_log(store.config(), &format!("Expression execution completed. Stack values: {}", thread.stack().value_count()));

        // 3. Assert: due to validation, the top of the stack contains a value.
        if thread.stack().value_count() == 0 {
            return Err(RuntimeError::Execution(
                "Expression evaluation failed: no value on stack after execution".to_string()
            ));
        }

        // 4. Pop the value val from the stack.
        let result_value = thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Stack("Failed to pop result value from expression evaluation".to_string())
        })?;

        crate::wasm::runtime::debug_log(store.config(), &format!("Expression result: {:?}", result_value));
        crate::wasm::runtime::debug_log(store.config(), &format!("Final stack depth: {}", thread.stack().frame_count()));
        if let Some(frame) = thread.stack().top_frame() {
            crate::wasm::runtime::debug_log(store.config(), &format!("Final top frame locals: {:?}", frame.state().locals()));
        }
        
        Ok(result_value)
    }
}

/// Executes an expression instruction
///
/// # Arguments
///
/// * `store` - The current store state
/// * `thread` - The current thread state
/// * `expression` - The expression to execute
///
/// # Returns
///
/// * `RuntimeResult<Value>` - The result of the expression execution
pub fn execute_expression(
    store: &mut Store,
    thread: &mut Thread,
    expression: &Expression,
) -> RuntimeResult<Value> {
    ExpressionEval::evaluate(store, thread, expression)
}

/// Executes a constant expression instruction
///
/// # Arguments
///
/// * `store` - The current store state
/// * `thread` - The current thread state
/// * `expression` - The constant expression to execute
///
/// # Returns
///
/// * `RuntimeResult<Value>` - The constant value
pub fn execute_constant_expression(
    store: &mut Store,
    thread: &mut Thread,
    expression: &Expression,
) -> RuntimeResult<Value> {
    ExpressionEval::evaluate_constant(store, thread, expression)
}

/// Evaluates a ConstExpr directly for global initialization and other constant expressions.
///
/// This function converts a ConstExpr to an Expression and then evaluates it.
/// It's useful for global initialization, element segment offsets, and data segment offsets.
///
/// # Arguments
///
/// * `store` - The current store state
/// * `thread` - The current thread state
/// * `const_expr` - The constant expression to evaluate
///
/// # Returns
///
/// * `RuntimeResult<Value>` - The constant value
pub fn evaluate_const_expr(
    store: &mut Store,
    thread: &mut Thread,
    const_expr: &crate::wasm::ast::ConstExpr,
) -> RuntimeResult<Value> {
    // Convert ConstExpr to Expression
    let expression = Expression::constant(const_expr.clone());
    
    // Evaluate the constant expression
    execute_constant_expression(store, thread, &expression)
}

/// Evaluates a ConstExpr with type validation.
///
/// This function is useful for global initialization where the result type
/// must match the global's value type.
///
/// # Arguments
///
/// * `store` - The current store state
/// * `thread` - The current thread state
/// * `const_expr` - The constant expression to evaluate
/// * `expected_type` - The expected result type
///
/// # Returns
///
/// * `RuntimeResult<Value>` - The constant value if type matches
pub fn evaluate_const_expr_with_type_validation(
    store: &mut Store,
    thread: &mut Thread,
    const_expr: &crate::wasm::ast::ConstExpr,
    expected_type: ValType,
) -> RuntimeResult<Value> {
    // Convert ConstExpr to Expression
    let expression = Expression::constant(const_expr.clone());
    
    // Evaluate with type validation
    ExpressionEval::evaluate_with_type_validation(store, thread, &expression, expected_type)
}

/// Evaluates multiple ConstExpr values in sequence.
///
/// This function is useful for element segment initialization where multiple
/// constant expressions need to be evaluated.
///
/// # Arguments
///
/// * `store` - The current store state
/// * `thread` - The current thread state
/// * `const_exprs` - The constant expressions to evaluate
///
/// # Returns
///
/// * `RuntimeResult<Vec<Value>>` - The results of all constant expressions
pub fn evaluate_const_exprs(
    store: &mut Store,
    thread: &mut Thread,
    const_exprs: &[crate::wasm::ast::ConstExpr],
) -> RuntimeResult<Vec<Value>> {
    let mut results = Vec::new();
    
    for const_expr in const_exprs {
        let result = evaluate_const_expr(store, thread, const_expr)?;
        results.push(result);
    }
    
    Ok(results)
}

/// Executes an expression and updates the original thread state.
///
/// This function is more faithful to the specification's reduction rule.
///
/// # Arguments
///
/// * `store` - The current store state
/// * `thread` - The current thread state (will be updated)
/// * `expression` - The expression to execute
///
/// # Returns
///
/// * `RuntimeResult<Value>` - The result of the expression execution
pub fn execute_expression_and_update_thread(
    store: &mut Store,
    thread: &mut Thread,
    expression: &Expression,
) -> RuntimeResult<Value> {
    ExpressionEval::evaluate_and_update_thread(store, thread, expression)
}
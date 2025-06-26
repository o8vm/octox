//! Numeric Instructions Module
//! 
//! This module implements the numeric instructions of WebAssembly.
//! It includes operations for integer and floating-point arithmetic,
//! comparisons, and conversions.

use crate::wasm::ast::Instruction;
use crate::wasm::runtime::{
    RuntimeResult,
    RuntimeError,
    Store,
    Thread,
    Value,
    Stack,
};

use alloc::format;
use alloc::string::ToString;

use crate::wasm::ast::{
    NumericInstruction,
    IntUnOp,
    FloatUnOp,
    IntBinOp,
    FloatBinOp,
    IntRelOp,
    FloatRelOp,
    ConversionOp,
};
use crate::wasm::runtime::{
    numeric::{
        BitWidth,
        NumericResult,
        UnsignedOps,
        SignedOps,
        FloatOps,
        IntOps,
    },
};

// Import debug_log macro
use crate::debug_log;

/// Executes a numeric constant instruction
/// 
/// # Arguments
/// 
/// * `thread` - The current thread state
/// * `value` - The constant value to push onto the stack
/// 
/// # Returns
/// 
/// * `RuntimeResult<()>` - The result of the execution
pub fn execute_const(thread: &mut Thread, value: Value) -> RuntimeResult<()> {
    // Push the constant value onto the stack
    thread.stack_mut().push_value(value);
    
    Ok(())
}

/// Executes an integer unary operation
/// 
/// # Arguments
/// 
/// * `thread` - The current thread state
/// * `op` - The unary operation to execute
/// * `width` - The bit width of the operation
/// 
/// # Returns
/// 
/// * `RuntimeResult<()>` - The result of the execution
fn execute_int_unop(
    thread: &mut Thread,
    op: &IntUnOp,
    width: BitWidth,
) -> RuntimeResult<()> {
    let stack = thread.stack_mut();
    
    // Pop the operand from the stack
    let operand = stack.pop_value().ok_or_else(|| {
        RuntimeError::Stack("Expected operand for integer unary operation".to_string())
    })?;
    
    // Execute the operation based on the bit width
    match width {
        BitWidth::W32 => {
            match operand {
                Value::I32(value) => {
                    let result = match op {
                        IntUnOp::Clz => IntOps::clz(value),
                        IntUnOp::Ctz => IntOps::ctz(value),
                        IntUnOp::Popcnt => IntOps::popcnt(value),
                    };
                    stack.push_value(Value::I32(result));
                }
                _ => return Err(RuntimeError::TypeError(format!(
                    "Expected i32 operand for i32 unary operation, got {:?}",
                    operand
                ))),
            }
        }
        BitWidth::W64 => {
            match operand {
                Value::I64(value) => {
                    let result = match op {
                        IntUnOp::Clz => IntOps::clz(value),
                        IntUnOp::Ctz => IntOps::ctz(value),
                        IntUnOp::Popcnt => IntOps::popcnt(value),
                    };
                    stack.push_value(Value::I64(result));
                }
                _ => return Err(RuntimeError::TypeError(format!(
                    "Expected i64 operand for i64 unary operation, got {:?}",
                    operand
                ))),
            }
        }
    }
    
    Ok(())
}

/// Executes a float unary operation
/// 
/// # Arguments
/// 
/// * `thread` - The current thread state
/// * `op` - The unary operation to execute
/// * `width` - The bit width of the operation
/// 
/// # Returns
/// 
/// * `RuntimeResult<()>` - The result of the execution
fn execute_float_unop(
    thread: &mut Thread,
    op: &FloatUnOp,
    width: BitWidth,
) -> RuntimeResult<()> {
    let stack = thread.stack_mut();
    
    // Pop the operand from the stack
    let operand = stack.pop_value().ok_or_else(|| {
        RuntimeError::Stack("Expected operand for float unary operation".to_string())
    })?;
    
    // Execute the operation based on the bit width
    match width {
        BitWidth::W32 => {
            match operand {
                Value::F32(value) => {
                    let result = match op {
                        FloatUnOp::Abs => value.abs(),
                        FloatUnOp::Neg => -value,
                        FloatUnOp::Sqrt => value.sqrt(),
                        FloatUnOp::Ceil => value.ceil(),
                        FloatUnOp::Floor => value.floor(),
                        FloatUnOp::Trunc => value.trunc(),
                        FloatUnOp::Nearest => value.nearest(),
                    };
                    stack.push_value(Value::F32(result));
                }
                _ => return Err(RuntimeError::TypeError(format!(
                    "Expected f32 operand for f32 unary operation, got {:?}",
                    operand
                ))),
            }
        }
        BitWidth::W64 => {
            match operand {
                Value::F64(value) => {
                    let result = match op {
                        FloatUnOp::Abs => value.abs(),
                        FloatUnOp::Neg => -value,
                        FloatUnOp::Sqrt => value.sqrt(),
                        FloatUnOp::Ceil => value.ceil(),
                        FloatUnOp::Floor => value.floor(),
                        FloatUnOp::Trunc => value.trunc(),
                        FloatUnOp::Nearest => value.nearest(),
                    };
                    stack.push_value(Value::F64(result));
                }
                _ => return Err(RuntimeError::TypeError(format!(
                    "Expected f64 operand for f64 unary operation, got {:?}",
                    operand
                ))),
            }
        }
    }
    
    Ok(())
}

/// Executes an integer binary operation
/// 
/// # Arguments
/// 
/// * `thread` - The current thread state
/// * `op` - The binary operation to execute
/// * `width` - The bit width of the operation
/// 
/// # Returns
/// 
/// * `RuntimeResult<()>` - The result of the execution
fn execute_int_binop(
    thread: &mut Thread,
    op: &IntBinOp,
    width: BitWidth,
) -> RuntimeResult<()> {
    let stack = thread.stack_mut();
    
    // Pop the second operand from the stack
    let operand2 = stack.pop_value().ok_or_else(|| {
        RuntimeError::Stack(format!(
            "Expected second operand for {} binary operation",
            width.type_name()
        ))
    })?;
    
    // Pop the first operand from the stack
    let operand1 = stack.pop_value().ok_or_else(|| {
        RuntimeError::Stack(format!(
            "Expected first operand for {} binary operation",
            width.type_name()
        ))
    })?;
    
    // Execute the operation based on the bit width
    let result = match width {
        BitWidth::W32 => {
            match (operand1.clone(), operand2.clone()) {
                (Value::I32(value1), Value::I32(value2)) => {
                    match op {
                        IntBinOp::Add => value1.checked_add(value2).map(Value::I32),
                        IntBinOp::Sub => value1.checked_sub(value2).map(Value::I32),
                        IntBinOp::Mul => value1.checked_mul(value2).map(Value::I32),
                        IntBinOp::Div { signed } => {
                            if value2 == 0 {
                                None
                            } else if *signed {
                                value1.checked_div(value2).map(Value::I32)
                            } else {
                                (value1 as u32).checked_div(value2 as u32).map(|v| Value::I32(v as i32))
                            }
                        }
                        IntBinOp::Rem { signed } => {
                            if value2 == 0 {
                                None
                            } else if *signed {
                                value1.checked_rem(value2).map(Value::I32)
                            } else {
                                (value1 as u32).checked_rem(value2 as u32).map(|v| Value::I32(v as i32))
                            }
                        }
                        IntBinOp::And => Some(Value::I32(value1 & value2)),
                        IntBinOp::Or => Some(Value::I32(value1 | value2)),
                        IntBinOp::Xor => Some(Value::I32(value1 ^ value2)),
                        IntBinOp::Shl => value1.checked_shl(value2 as u32).map(Value::I32),
                        IntBinOp::Shr { signed } => {
                            if *signed {
                                value1.checked_shr(value2 as u32).map(Value::I32)
                            } else {
                                (value1 as u32).checked_shr(value2 as u32).map(|v| Value::I32(v as i32))
                            }
                        }
                        IntBinOp::Rotl => {
                            let shift = value2 as u32 & 31;
                            Some(Value::I32(value1.rotate_left(shift)))
                        }
                        IntBinOp::Rotr => {
                            let shift = value2 as u32 & 31;
                            Some(Value::I32(value1.rotate_right(shift)))
                        }
                    }
                }
                _ => return Err(RuntimeError::TypeError(format!(
                    "Expected {} operands for {} binary operation, got {:?} and {:?}",
                    width.type_name(),
                    width.type_name(),
                    operand1,
                    operand2
                ))),
            }
        }
        BitWidth::W64 => {
            match (operand1.clone(), operand2.clone()) {
                (Value::I64(value1), Value::I64(value2)) => {
                    match op {
                        IntBinOp::Add => value1.checked_add(value2).map(Value::I64),
                        IntBinOp::Sub => value1.checked_sub(value2).map(Value::I64),
                        IntBinOp::Mul => value1.checked_mul(value2).map(Value::I64),
                        IntBinOp::Div { signed } => {
                            if value2 == 0 {
                                None
                            } else if *signed {
                                value1.checked_div(value2).map(Value::I64)
                            } else {
                                (value1 as u64).checked_div(value2 as u64).map(|v| Value::I64(v as i64))
                            }
                        }
                        IntBinOp::Rem { signed } => {
                            if value2 == 0 {
                                None
                            } else if *signed {
                                value1.checked_rem(value2).map(Value::I64)
                            } else {
                                (value1 as u64).checked_rem(value2 as u64).map(|v| Value::I64(v as i64))
                            }
                        }
                        IntBinOp::And => Some(Value::I64(value1 & value2)),
                        IntBinOp::Or => Some(Value::I64(value1 | value2)),
                        IntBinOp::Xor => Some(Value::I64(value1 ^ value2)),
                        IntBinOp::Shl => value1.checked_shl(value2 as u32).map(Value::I64),
                        IntBinOp::Shr { signed } => {
                            if *signed {
                                value1.checked_shr(value2 as u32).map(Value::I64)
                            } else {
                                (value1 as u64).checked_shr(value2 as u32).map(|v| Value::I64(v as i64))
                            }
                        }
                        IntBinOp::Rotl => {
                            let shift = value2 as u32 & 63;
                            Some(Value::I64(value1.rotate_left(shift)))
                        }
                        IntBinOp::Rotr => {
                            let shift = value2 as u32 & 63;
                            Some(Value::I64(value1.rotate_right(shift)))
                        }
                    }
                }
                _ => return Err(RuntimeError::TypeError(format!(
                    "Expected {} operands for {} binary operation, got {:?} and {:?}",
                    width.type_name(),
                    width.type_name(),
                    operand1,
                    operand2
                ))),
            }
        }
    }.ok_or_else(|| {
        RuntimeError::Execution(format!(
            "Integer overflow or division by zero in {} binary operation",
            width.type_name()
        ))
    })?;
    
    // Push the result onto the stack
    stack.push_value(result);
    
    Ok(())
}

/// Executes a float binary operation
/// 
/// # Arguments
/// 
/// * `thread` - The current thread state
/// * `op` - The binary operation to execute
/// * `width` - The bit width of the operation
/// 
/// # Returns
/// 
/// * `RuntimeResult<()>` - The result of the execution
fn execute_float_binop(
    thread: &mut Thread,
    op: &FloatBinOp,
    width: BitWidth,
) -> RuntimeResult<()> {
    let stack = thread.stack_mut();
    
    // Pop the second operand from the stack
    let operand2 = stack.pop_value().ok_or_else(|| {
        RuntimeError::Stack(format!(
            "Expected second operand for {} binary operation",
            width.type_name()
        ))
    })?;
    
    // Pop the first operand from the stack
    let operand1 = stack.pop_value().ok_or_else(|| {
        RuntimeError::Stack(format!(
            "Expected first operand for {} binary operation",
            width.type_name()
        ))
    })?;
    
    // Execute the operation based on the bit width
    match width {
        BitWidth::W32 => {
            match (operand1.clone(), operand2.clone()) {
                (Value::F32(value1), Value::F32(value2)) => {
                    let result = match op {
                        FloatBinOp::Add => value1 + value2,
                        FloatBinOp::Sub => value1 - value2,
                        FloatBinOp::Mul => value1 * value2,
                        FloatBinOp::Div => {
                            if value2 == 0.0 {
                                if value1 == 0.0 {
                                    f32::NAN
                                } else if value1 > 0.0 {
                                    f32::INFINITY
                                } else {
                                    f32::NEG_INFINITY
                                }
                            } else {
                                value1 / value2
                            }
                        }
                        FloatBinOp::Min => value1.min(value2),
                        FloatBinOp::Max => value1.max(value2),
                        FloatBinOp::Copysign => value1.copysign(value2),
                    };
                    stack.push_value(Value::F32(result));
                }
                _ => return Err(RuntimeError::TypeError(format!(
                    "Expected {} operands for {} binary operation, got {:?} and {:?}",
                    width.type_name(),
                    width.type_name(),
                    operand1,
                    operand2
                ))),
            }
        }
        BitWidth::W64 => {
            match (operand1.clone(), operand2.clone()) {
                (Value::F64(value1), Value::F64(value2)) => {
                    let result = match op {
                        FloatBinOp::Add => value1 + value2,
                        FloatBinOp::Sub => value1 - value2,
                        FloatBinOp::Mul => value1 * value2,
                        FloatBinOp::Div => {
                            if value2 == 0.0 {
                                if value1 == 0.0 {
                                    f64::NAN
                                } else if value1 > 0.0 {
                                    f64::INFINITY
                                } else {
                                    f64::NEG_INFINITY
                                }
                            } else {
                                value1 / value2
                            }
                        }
                        FloatBinOp::Min => value1.min(value2),
                        FloatBinOp::Max => value1.max(value2),
                        FloatBinOp::Copysign => value1.copysign(value2),
                    };
                    stack.push_value(Value::F64(result));
                }
                _ => return Err(RuntimeError::TypeError(format!(
                    "Expected {} operands for {} binary operation, got {:?} and {:?}",
                    width.type_name(),
                    width.type_name(),
                    operand1,
                    operand2
                ))),
            }
        }
    }
    
    Ok(())
}

/// Executes a test operation (eqz)
/// 
/// # Arguments
/// 
/// * `thread` - The current thread state
/// * `width` - The bit width of the operation
/// 
/// # Returns
/// 
/// * `RuntimeResult<()>` - The result of the execution
fn execute_testop(
    thread: &mut Thread,
    width: BitWidth,
) -> RuntimeResult<()> {
    let stack = thread.stack_mut();
    
    // Pop the operand from the stack
    let operand = stack.pop_value().ok_or_else(|| {
        RuntimeError::Stack("Expected operand for test operation".to_string())
    })?;
    
    // Execute the operation based on the bit width
    match width {
        BitWidth::W32 => {
            match operand {
                Value::I32(value) => {
                    let result = IntOps::eqz(value);
                    stack.push_value(Value::I32(result));
                }
                _ => return Err(RuntimeError::TypeError(format!(
                    "Expected i32 operand for i32 test operation, got {:?}",
                    operand
                ))),
            }
        }
        BitWidth::W64 => {
            match operand {
                Value::I64(value) => {
                    let result = IntOps::eqz(value);
                    stack.push_value(Value::I32(result as i32));
                }
                _ => return Err(RuntimeError::TypeError(format!(
                    "Expected i64 operand for i64 test operation, got {:?}",
                    operand
                ))),
            }
        }
    }
    
    Ok(())
}

/// Executes an integer relational operation
/// 
/// # Arguments
/// 
/// * `store` - The current store state
/// * `thread` - The current thread state
/// * `op` - The relational operation to execute
/// * `width` - The bit width of the operation
/// 
/// # Returns
/// 
/// * `RuntimeResult<()>` - The result of the execution
fn execute_relop(
    store: &mut Store,
    thread: &mut Thread,
    op: &IntRelOp,
    width: BitWidth,
) -> RuntimeResult<()> {
    let stack = thread.stack_mut();
    
    // Pop the second operand from the stack
    let operand2 = stack.pop_value().ok_or_else(|| {
        RuntimeError::Stack(format!(
            "Expected second operand for {} relational operation",
            width.type_name()
        ))
    })?;
    
    // Pop the first operand from the stack
    let operand1 = stack.pop_value().ok_or_else(|| {
        RuntimeError::Stack(format!(
            "Expected first operand for {} relational operation",
            width.type_name()
        ))
    })?;
    
    debug_log!(store.config(), "=== RELATIONAL OPERATION ===");
    debug_log!(store.config(), "Operation: {:?}", op);
    debug_log!(store.config(), "Operand1: {:?}", operand1);
    debug_log!(store.config(), "Operand2: {:?}", operand2);
    
    // Execute the operation based on the bit width
    match width {
        BitWidth::W32 => {
            match (operand1.clone(), operand2.clone()) {
                (Value::I32(value1), Value::I32(value2)) => {
                    let result = match op {
                        IntRelOp::Eq { signed: _ } => {
                            let res = value1 == value2;
                            debug_log!(store.config(), "Eq: {} == {} = {}", value1, value2, res);
                            res
                        },
                        IntRelOp::Ne { signed: _ } => {
                            let res = value1 != value2;
                            debug_log!(store.config(), "Ne: {} != {} = {}", value1, value2, res);
                            res
                        },
                        IntRelOp::Lt { signed } => {
                            let res = if *signed {
                                value1 < value2
                            } else {
                                (value1 as u32) < (value2 as u32)
                            };
                            debug_log!(store.config(), "Lt (signed={}): {} < {} = {}", signed, value1, value2, res);
                            res
                        },
                        IntRelOp::Gt { signed } => {
                            let res = if *signed {
                                value1 > value2
                            } else {
                                (value1 as u32) > (value2 as u32)
                            };
                            debug_log!(store.config(), "Gt (signed={}): {} > {} = {}", signed, value1, value2, res);
                            res
                        },
                        IntRelOp::Le { signed } => {
                            let res = if *signed {
                                value1 <= value2
                            } else {
                                (value1 as u32) <= (value2 as u32)
                            };
                            debug_log!(store.config(), "Le (signed={}): {} <= {} = {}", signed, value1, value2, res);
                            res
                        },
                        IntRelOp::Ge { signed } => {
                            let res = if *signed {
                                value1 >= value2
                            } else {
                                (value1 as u32) >= (value2 as u32)
                            };
                            debug_log!(store.config(), "Ge (signed={}): {} >= {} = {}", signed, value1, value2, res);
                            res
                        },
                    };
                    debug_log!(store.config(), "Result: {} (as i32: {})", result, result as i32);
                    stack.push_value(Value::I32(result as i32));
                }
                _ => return Err(RuntimeError::TypeError(format!(
                    "Expected {} operands for {} relational operation, got {:?} and {:?}",
                    width.type_name(),
                    width.type_name(),
                    operand1,
                    operand2
                ))),
            }
        }
        BitWidth::W64 => {
            match (operand1.clone(), operand2.clone()) {
                (Value::I64(value1), Value::I64(value2)) => {
                    let result = match op {
                        IntRelOp::Eq { signed: _ } => {
                            let res = value1 == value2;
                            debug_log!(store.config(), "Eq: {} == {} = {}", value1, value2, res);
                            res
                        },
                        IntRelOp::Ne { signed: _ } => {
                            let res = value1 != value2;
                            debug_log!(store.config(), "Ne: {} != {} = {}", value1, value2, res);
                            res
                        },
                        IntRelOp::Lt { signed } => {
                            let res = if *signed {
                                value1 < value2
                            } else {
                                (value1 as u64) < (value2 as u64)
                            };
                            debug_log!(store.config(), "Lt (signed={}): {} < {} = {}", signed, value1, value2, res);
                            res
                        },
                        IntRelOp::Gt { signed } => {
                            let res = if *signed {
                                value1 > value2
                            } else {
                                (value1 as u64) > (value2 as u64)
                            };
                            debug_log!(store.config(), "Gt (signed={}): {} > {} = {}", signed, value1, value2, res);
                            res
                        },
                        IntRelOp::Le { signed } => {
                            let res = if *signed {
                                value1 <= value2
                            } else {
                                (value1 as u64) <= (value2 as u64)
                            };
                            debug_log!(store.config(), "Le (signed={}): {} <= {} = {}", signed, value1, value2, res);
                            res
                        },
                        IntRelOp::Ge { signed } => {
                            let res = if *signed {
                                value1 >= value2
                            } else {
                                (value1 as u64) >= (value2 as u64)
                            };
                            debug_log!(store.config(), "Ge (signed={}): {} >= {} = {}", signed, value1, value2, res);
                            res
                        },
                    };
                    debug_log!(store.config(), "Result: {} (as i32: {})", result, result as i32);
                    stack.push_value(Value::I32(result as i32));
                }
                _ => return Err(RuntimeError::TypeError(format!(
                    "Expected {} operands for {} relational operation, got {:?} and {:?}",
                    width.type_name(),
                    width.type_name(),
                    operand1,
                    operand2
                ))),
            }
        }
    }
    
    Ok(())
}

/// Executes a float relational operation
/// 
/// # Arguments
/// 
/// * `thread` - The current thread state
/// * `op` - The relational operation to execute
/// * `width` - The bit width of the operation
/// 
/// # Returns
/// 
/// * `RuntimeResult<()>` - The result of the execution
fn execute_float_relop(
    thread: &mut Thread,
    op: &FloatRelOp,
    width: BitWidth,
) -> RuntimeResult<()> {
    let stack = thread.stack_mut();
    
    // Pop the second operand from the stack
    let operand2 = stack.pop_value().ok_or_else(|| {
        RuntimeError::Stack(format!(
            "Expected second operand for {} relational operation",
            width.type_name()
        ))
    })?;
    
    // Pop the first operand from the stack
    let operand1 = stack.pop_value().ok_or_else(|| {
        RuntimeError::Stack(format!(
            "Expected first operand for {} relational operation",
            width.type_name()
        ))
    })?;
    
    // Execute the operation based on the bit width
    match width {
        BitWidth::W32 => {
            match (operand1.clone(), operand2.clone()) {
                (Value::F32(value1), Value::F32(value2)) => {
                    let result = match op {
                        FloatRelOp::Eq => value1 == value2,
                        FloatRelOp::Ne => value1 != value2,
                        FloatRelOp::Lt => value1 < value2,
                        FloatRelOp::Gt => value1 > value2,
                        FloatRelOp::Le => value1 <= value2,
                        FloatRelOp::Ge => value1 >= value2,
                    };
                    stack.push_value(Value::I32(result as i32));
                }
                _ => return Err(RuntimeError::TypeError(format!(
                    "Expected {} operands for {} relational operation, got {:?} and {:?}",
                    width.type_name(),
                    width.type_name(),
                    operand1,
                    operand2
                ))),
            }
        }
        BitWidth::W64 => {
            match (operand1.clone(), operand2.clone()) {
                (Value::F64(value1), Value::F64(value2)) => {
                    let result = match op {
                        FloatRelOp::Eq => value1 == value2,
                        FloatRelOp::Ne => value1 != value2,
                        FloatRelOp::Lt => value1 < value2,
                        FloatRelOp::Gt => value1 > value2,
                        FloatRelOp::Le => value1 <= value2,
                        FloatRelOp::Ge => value1 >= value2,
                    };
                    stack.push_value(Value::I32(result as i32));
                }
                _ => return Err(RuntimeError::TypeError(format!(
                    "Expected {} operands for {} relational operation, got {:?} and {:?}",
                    width.type_name(),
                    width.type_name(),
                    operand1,
                    operand2
                ))),
            }
        }
    }
    
    Ok(())
}

/// Executes a conversion operation
/// 
/// # Arguments
/// 
/// * `thread` - The current thread state
/// * `op` - The conversion operation to execute
/// * `width` - The bit width of the operation
/// 
/// # Returns
/// 
/// * `RuntimeResult<()>` - The result of the execution
fn execute_conversion(
    thread: &mut Thread,
    op: &ConversionOp,
    width: BitWidth,
) -> RuntimeResult<()> {
    let stack = thread.stack_mut();
    
    // Pop the operand from the stack
    let operand = stack.pop_value().ok_or_else(|| {
        RuntimeError::Stack("Expected operand for conversion operation".to_string())
    })?;
    
    // Execute the operation based on the bit width and conversion type
    match op {
        // i32 <-> i64 conversions
        ConversionOp::Wrap => {
            match operand {
                Value::I64(value) => {
                    // i64 to i32: wrap
                    stack.push_value(Value::I32(value as i32));
                }
                _ => return Err(RuntimeError::TypeError(format!(
                    "Expected i64 operand for i32.wrap_i64, got {:?}",
                    operand
                ))),
            }
        }
        ConversionOp::Extend { signed } => {
            match operand {
                Value::I32(value) => {
                    // i32 to i64: extend
                    if *signed {
                        stack.push_value(Value::I64(value as i64));
                    } else {
                        stack.push_value(Value::I64((value as u32) as i64));
                    }
                }
                _ => return Err(RuntimeError::TypeError(format!(
                    "Expected i32 operand for i64.extend_i32{}, got {:?}",
                    if *signed { "_s" } else { "_u" },
                    operand
                ))),
            }
        }
        // i32/i64 <-> f32/f64 conversions
        ConversionOp::Trunc { signed } => {
            match (width, operand.clone()) {
                (BitWidth::W32, Value::F32(value)) => {
                    // f32 to i32: truncate
                    if value.is_nan() || value.is_infinite() {
                        return Err(RuntimeError::Execution("Invalid conversion: NaN or infinity".to_string()));
                    }
                    let result = if *signed {
                        if value >= i32::MAX as f32 || value <= i32::MIN as f32 {
                            return Err(RuntimeError::Execution("Invalid conversion: out of range".to_string()));
                        }
                        value as i32
                    } else {
                        if value >= u32::MAX as f32 || value < 0.0 {
                            return Err(RuntimeError::Execution("Invalid conversion: out of range".to_string()));
                        }
                        value as u32 as i32
                    };
                    stack.push_value(Value::I32(result));
                }
                (BitWidth::W64, Value::F32(value)) => {
                    // f32 to i64: truncate
                    if value.is_nan() || value.is_infinite() {
                        return Err(RuntimeError::Execution("Invalid conversion: NaN or infinity".to_string()));
                    }
                    let result = if *signed {
                        if value >= i64::MAX as f32 || value <= i64::MIN as f32 {
                            return Err(RuntimeError::Execution("Invalid conversion: out of range".to_string()));
                        }
                        value as i64
                    } else {
                        if value >= u64::MAX as f32 || value < 0.0 {
                            return Err(RuntimeError::Execution("Invalid conversion: out of range".to_string()));
                        }
                        value as u64 as i64
                    };
                    stack.push_value(Value::I64(result));
                }
                (BitWidth::W32, Value::F64(value)) => {
                    // f64 to i32: truncate
                    if value.is_nan() || value.is_infinite() {
                        return Err(RuntimeError::Execution("Invalid conversion: NaN or infinity".to_string()));
                    }
                    let result = if *signed {
                        if value >= i32::MAX as f64 || value <= i32::MIN as f64 {
                            return Err(RuntimeError::Execution("Invalid conversion: out of range".to_string()));
                        }
                        value as i32
                    } else {
                        if value >= u32::MAX as f64 || value < 0.0 {
                            return Err(RuntimeError::Execution("Invalid conversion: out of range".to_string()));
                        }
                        value as u32 as i32
                    };
                    stack.push_value(Value::I32(result));
                }
                (BitWidth::W64, Value::F64(value)) => {
                    // f64 to i64: truncate
                    if value.is_nan() || value.is_infinite() {
                        return Err(RuntimeError::Execution("Invalid conversion: NaN or infinity".to_string()));
                    }
                    let result = if *signed {
                        if value >= i64::MAX as f64 || value <= i64::MIN as f64 {
                            return Err(RuntimeError::Execution("Invalid conversion: out of range".to_string()));
                        }
                        value as i64
                    } else {
                        if value >= u64::MAX as f64 || value < 0.0 {
                            return Err(RuntimeError::Execution("Invalid conversion: out of range".to_string()));
                        }
                        value as u64 as i64
                    };
                    stack.push_value(Value::I64(result));
                }
                _ => return Err(RuntimeError::TypeError(format!(
                    "Invalid operand type for truncate operation: {:?}",
                    operand
                ))),
            }
        }
        ConversionOp::TruncSat { signed } => {
            match (width, operand.clone()) {
                (BitWidth::W32, Value::F32(value)) => {
                    // f32 to i32: truncate with saturation
                    let result = if *signed {
                        if value.is_nan() {
                            0
                        } else if value >= i32::MAX as f32 {
                            i32::MAX
                        } else if value <= i32::MIN as f32 {
                            i32::MIN
                        } else {
                            value as i32
                        }
                    } else {
                        if value.is_nan() {
                            0
                        } else if value >= u32::MAX as f32 {
                            u32::MAX as i32
                        } else if value < 0.0 {
                            0
                        } else {
                            value as u32 as i32
                        }
                    };
                    stack.push_value(Value::I32(result));
                }
                (BitWidth::W64, Value::F32(value)) => {
                    // f32 to i64: truncate with saturation
                    let result = if *signed {
                        if value.is_nan() {
                            0
                        } else if value >= i64::MAX as f32 {
                            i64::MAX
                        } else if value <= i64::MIN as f32 {
                            i64::MIN
                        } else {
                            value as i64
                        }
                    } else {
                        if value.is_nan() {
                            0
                        } else if value >= u64::MAX as f32 {
                            u64::MAX as i64
                        } else if value < 0.0 {
                            0
                        } else {
                            value as u64 as i64
                        }
                    };
                    stack.push_value(Value::I64(result));
                }
                (BitWidth::W32, Value::F64(value)) => {
                    // f64 to i32: truncate with saturation
                    let result = if *signed {
                        if value.is_nan() {
                            0
                        } else if value >= i32::MAX as f64 {
                            i32::MAX
                        } else if value <= i32::MIN as f64 {
                            i32::MIN
                        } else {
                            value as i32
                        }
                    } else {
                        if value.is_nan() {
                            0
                        } else if value >= u32::MAX as f64 {
                            u32::MAX as i32
                        } else if value < 0.0 {
                            0
                        } else {
                            value as u32 as i32
                        }
                    };
                    stack.push_value(Value::I32(result));
                }
                (BitWidth::W64, Value::F64(value)) => {
                    // f64 to i64: truncate with saturation
                    let result = if *signed {
                        if value.is_nan() {
                            0
                        } else if value >= i64::MAX as f64 {
                            i64::MAX
                        } else if value <= i64::MIN as f64 {
                            i64::MIN
                        } else {
                            value as i64
                        }
                    } else {
                        if value.is_nan() {
                            0
                        } else if value >= u64::MAX as f64 {
                            u64::MAX as i64
                        } else if value < 0.0 {
                            0
                        } else {
                            value as u64 as i64
                        }
                    };
                    stack.push_value(Value::I64(result));
                }
                _ => return Err(RuntimeError::TypeError(format!(
                    "Invalid operand type for truncate_sat operation: {:?}",
                    operand
                ))),
            }
        }
        ConversionOp::Demote => {
            match operand {
                Value::F64(value) => {
                    // f64 to f32: demote
                    stack.push_value(Value::F32(value as f32));
                }
                _ => return Err(RuntimeError::TypeError(format!(
                    "Expected f64 operand for f32.demote_f64, got {:?}",
                    operand
                ))),
            }
        }
        ConversionOp::Promote => {
            match operand {
                Value::F32(value) => {
                    // f32 to f64: promote
                    stack.push_value(Value::F64(value as f64));
                }
                _ => return Err(RuntimeError::TypeError(format!(
                    "Expected f32 operand for f64.promote_f32, got {:?}",
                    operand
                ))),
            }
        }
        ConversionOp::Convert { signed } => {
            match (width, operand.clone()) {
                (BitWidth::W32, Value::I32(value)) => {
                    // i32 to f32: convert
                    if *signed {
                        stack.push_value(Value::F32(value as f32));
                    } else {
                        stack.push_value(Value::F32((value as u32) as f32));
                    }
                }
                (BitWidth::W32, Value::I64(value)) => {
                    // i64 to f32: convert
                    if *signed {
                        stack.push_value(Value::F32(value as f32));
                    } else {
                        stack.push_value(Value::F32((value as u64) as f32));
                    }
                }
                (BitWidth::W64, Value::I32(value)) => {
                    // i32 to f64: convert
                    if *signed {
                        stack.push_value(Value::F64(value as f64));
                    } else {
                        stack.push_value(Value::F64((value as u32) as f64));
                    }
                }
                (BitWidth::W64, Value::I64(value)) => {
                    // i64 to f64: convert
                    if *signed {
                        stack.push_value(Value::F64(value as f64));
                    } else {
                        stack.push_value(Value::F64((value as u64) as f64));
                    }
                }
                _ => return Err(RuntimeError::TypeError(format!(
                    "Invalid operand type for convert operation: {:?}",
                    operand
                ))),
            }
        }
        ConversionOp::Reinterpret => {
            match (width, operand.clone()) {
                (BitWidth::W32, Value::I32(value)) => {
                    // i32 to f32: reinterpret
                    stack.push_value(Value::F32(f32::from_bits(value as u32)));
                }
                (BitWidth::W32, Value::F32(value)) => {
                    // f32 to i32: reinterpret
                    stack.push_value(Value::I32(value.to_bits() as i32));
                }
                (BitWidth::W64, Value::I64(value)) => {
                    // i64 to f64: reinterpret
                    stack.push_value(Value::F64(f64::from_bits(value as u64)));
                }
                (BitWidth::W64, Value::F64(value)) => {
                    // f64 to i64: reinterpret
                    stack.push_value(Value::I64(value.to_bits() as i64));
                }
                _ => return Err(RuntimeError::TypeError(format!(
                    "Invalid operand type for reinterpret operation: {:?}",
                    operand
                ))),
            }
        }
        // Extended conversions
        ConversionOp::Extend8S => {
            match operand {
                Value::I32(value) => {
                    // i32.extend8_s
                    stack.push_value(Value::I32(((value as i8) as i32)));
                }
                Value::I64(value) => {
                    // i64.extend8_s
                    stack.push_value(Value::I64(((value as i8) as i64)));
                }
                _ => return Err(RuntimeError::TypeError(format!(
                    "Expected integer operand for extend8_s operation, got {:?}",
                    operand
                ))),
            }
        }
        ConversionOp::Extend16S => {
            match operand {
                Value::I32(value) => {
                    // i32.extend16_s
                    stack.push_value(Value::I32(((value as i16) as i32)));
                }
                Value::I64(value) => {
                    // i64.extend16_s
                    stack.push_value(Value::I64(((value as i16) as i64)));
                }
                _ => return Err(RuntimeError::TypeError(format!(
                    "Expected integer operand for extend16_s operation, got {:?}",
                    operand
                ))),
            }
        }
        ConversionOp::Extend32S => {
            match operand {
                Value::I64(value) => {
                    // i64.extend32_s
                    stack.push_value(Value::I64(((value as i32) as i64)));
                }
                _ => return Err(RuntimeError::TypeError(format!(
                    "Expected i64 operand for extend32_s operation, got {:?}",
                    operand
                ))),
            }
        }
    }
    
    Ok(())
}

/// Executes a numeric instruction
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
pub fn execute_numeric(
    store: &mut Store,
    thread: &mut Thread,
    instruction: &Instruction,
) -> RuntimeResult<()> {
    match instruction {
        Instruction::Numeric(numeric_instr) => {
            match numeric_instr {
                // Constant instructions
                NumericInstruction::I32Const(value) => {
                    execute_const(thread, Value::I32(*value))
                }
                NumericInstruction::I64Const(value) => {
                    execute_const(thread, Value::I64(*value))
                }
                NumericInstruction::F32Const(value) => {
                    execute_const(thread, Value::F32(*value))
                }
                NumericInstruction::F64Const(value) => {
                    execute_const(thread, Value::F64(*value))
                }
                // Integer unary operations
                NumericInstruction::I32UnOp(op) => {
                    execute_int_unop(thread, op, BitWidth::W32)
                }
                NumericInstruction::I64UnOp(op) => {
                    execute_int_unop(thread, op, BitWidth::W64)
                }
                // Float unary operations
                NumericInstruction::F32UnOp(op) => {
                    execute_float_unop(thread, op, BitWidth::W32)
                }
                NumericInstruction::F64UnOp(op) => {
                    execute_float_unop(thread, op, BitWidth::W64)
                }
                // Integer binary operations
                NumericInstruction::I32BinOp(op) => {
                    execute_int_binop(thread, op, BitWidth::W32)
                }
                NumericInstruction::I64BinOp(op) => {
                    execute_int_binop(thread, op, BitWidth::W64)
                }
                // Float binary operations
                NumericInstruction::F32BinOp(op) => {
                    execute_float_binop(thread, op, BitWidth::W32)
                }
                NumericInstruction::F64BinOp(op) => {
                    execute_float_binop(thread, op, BitWidth::W64)
                }
                // Test operations
                NumericInstruction::I32TestOp => {
                    execute_testop(thread, BitWidth::W32)
                }
                NumericInstruction::I64TestOp => {
                    execute_testop(thread, BitWidth::W64)
                }
                // Relational operations
                NumericInstruction::I32RelOp(op) => {
                    execute_relop(store, thread, op, BitWidth::W32)
                }
                NumericInstruction::I64RelOp(op) => {
                    execute_relop(store, thread, op, BitWidth::W64)
                }
                NumericInstruction::F32RelOp(op) => {
                    execute_float_relop(thread, op, BitWidth::W32)
                }
                NumericInstruction::F64RelOp(op) => {
                    execute_float_relop(thread, op, BitWidth::W64)
                }
                // Conversion operations
                NumericInstruction::I32ConversionOp(op) => {
                    execute_conversion(thread, op, BitWidth::W32)
                }
                NumericInstruction::I64ConversionOp(op) => {
                    execute_conversion(thread, op, BitWidth::W64)
                }
                NumericInstruction::F32ConversionOp(op) => {
                    execute_conversion(thread, op, BitWidth::W32)
                }
                NumericInstruction::F64ConversionOp(op) => {
                    execute_conversion(thread, op, BitWidth::W64)
                }
            }
        }
        _ => Err(RuntimeError::Execution(format!(
            "Expected numeric instruction, got: {:?}",
            instruction
        ))),
    }
}

//! Vector Instructions implementation for WebAssembly runtime.
//! 
//! This module implements the vector (SIMD) instructions as defined in the WebAssembly specification.
//! Vector instructions handle operations on 128-bit vector values, including:
//! - Vector construction and extraction
//! - Vector arithmetic operations
//! - Vector comparison operations
//! - Vector bitwise operations
//! - Vector shuffle and swizzle operations

use alloc::format;
use alloc::string::ToString;

use crate::wasm::runtime::{
    value::{Value, ValueType},
    numeric::FloatOps,
    RuntimeResult,
    RuntimeError,
    Store,
    Thread,
};
use crate::wasm::ast::{Instruction, VectorInstruction, VectorVUnOp, VectorVBinOp, VectorIntUnOp, VectorFloatUnOp, VectorShape, IntVectorShape, FloatVectorShape, VectorHalf, VectorIntShiftOp, VectorIntBinOp, VectorFloatBinOp, VectorIntRelOp, VectorFloatRelOp};

/// Vector instruction implementation.
/// 
/// This struct contains methods for executing vector instructions in the WebAssembly runtime.
pub struct Vector;

impl Vector {
    /// Executes the v128.const instruction.
    /// 
    /// Pushes a 128-bit vector constant onto the stack.
    /// 
    /// # Arguments
    /// 
    /// * `thread` - The current thread state
    /// * `value` - The 128-bit vector constant value
    /// 
    /// # Returns
    /// 
    /// * `Ok(())` if the instruction executed successfully
    /// * `Err(String)` if an error occurred
    pub fn v128_const(thread: &mut Thread, value: i128) -> RuntimeResult<()> {
        // Push the vector constant onto the stack
        thread.stack_mut().push_value(Value::V128(value));
        
        Ok(())
    }

    /// Executes the v128.vvunop instruction.
    /// 
    /// Performs a bitwise NOT operation on a 128-bit vector value.
    /// 
    /// # Arguments
    /// 
    /// * `thread` - The current thread state
    /// * `op` - The unary operation to execute
    /// 
    /// # Returns
    /// 
    /// * `RuntimeResult<()>` - The result of the execution
    pub fn vvunop(thread: &mut Thread, op: VectorVUnOp) -> RuntimeResult<()> {
        // Pop the vector value from the stack
        let val = thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Execution("Expected v128 value on stack for v128.vvunop".to_string())
        })?;

        // Execute the operation
        let result = match (val.clone(), op) {
            (Value::V128(value), VectorVUnOp::Not) => {
                // Perform bitwise NOT on the 128-bit value
                Value::V128(!value)
            }
            _ => return Err(RuntimeError::TypeError(format!(
                "Expected v128 operand for v128.vvunop, got {:?}",
                val
            ))),
        };

        // Push the result onto the stack
        thread.stack_mut().push_value(result);

        Ok(())
    }

    /// Executes the v128.vvbinop instruction.
    /// 
    /// Performs a bitwise operation (AND, AND-NOT, OR, XOR) on two 128-bit vector values.
    /// 
    /// # Arguments
    /// 
    /// * `thread` - The current thread state
    /// * `op` - The binary operation to execute
    /// 
    /// # Returns
    /// 
    /// * `RuntimeResult<()>` - The result of the execution
    pub fn vvbinop(thread: &mut Thread, op: VectorVBinOp) -> RuntimeResult<()> {
        // Pop the second vector value from the stack
        let val2 = thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Execution("Expected second v128 value on stack for v128.vvbinop".to_string())
        })?;

        // Pop the first vector value from the stack
        let val1 = thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Execution("Expected first v128 value on stack for v128.vvbinop".to_string())
        })?;

        // Execute the operation
        let result = match (val1.clone(), val2.clone(), op) {
            (Value::V128(v1), Value::V128(v2), VectorVBinOp::And) => {
                // Perform bitwise AND
                Value::V128(v1 & v2)
            }
            (Value::V128(v1), Value::V128(v2), VectorVBinOp::AndNot) => {
                // Perform bitwise AND-NOT (v1 & !v2)
                Value::V128(v1 & !v2)
            }
            (Value::V128(v1), Value::V128(v2), VectorVBinOp::Or) => {
                // Perform bitwise OR
                Value::V128(v1 | v2)
            }
            (Value::V128(v1), Value::V128(v2), VectorVBinOp::Xor) => {
                // Perform bitwise XOR
                Value::V128(v1 ^ v2)
            }
            _ => return Err(RuntimeError::TypeError(format!(
                "Expected v128 operands for v128.vvbinop, got {:?} and {:?}",
                val1, val2
            ))),
        };

        // Push the result onto the stack
        thread.stack_mut().push_value(result);

        Ok(())
    }

    /// Executes the v128.any_true instruction.
    /// 
    /// Pops a v128 value from the stack and pushes i32(1) if any bit is set, else i32(0).
    pub fn any_true(thread: &mut Thread) -> RuntimeResult<()> {
        let val = thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Execution("Expected v128 value on stack for v128.any_true".to_string())
        })?;
        let result = match val {
            Value::V128(bits) => Value::I32(if bits != 0 { 1 } else { 0 }),
            _ => return Err(RuntimeError::TypeError(format!(
                "Expected v128 operand for v128.any_true, got {:?}", val
            ))),
        };
        thread.stack_mut().push_value(result);
        Ok(())
    }

    /// Executes the i8x16.swizzle instruction.
    /// 
    /// Pops two v128 values from the stack, uses the second as indices to swizzle the first, and pushes the result as v128.
    pub fn i8x16_swizzle(thread: &mut Thread) -> RuntimeResult<()> {
        // Pop c2 (indices) from the stack
        let val2 = thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Execution("Expected second v128 value on stack for i8x16.swizzle".to_string())
        })?;
        // Pop c1 (data) from the stack
        let val1 = thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Execution("Expected first v128 value on stack for i8x16.swizzle".to_string())
        })?;
        let (c1, c2) = match (val1, val2) {
            (Value::V128(v1), Value::V128(v2)) => (v1, v2),
            (a, b) => return Err(RuntimeError::TypeError(format!(
                "Expected v128 operands for i8x16.swizzle, got {:?} and {:?}", a, b
            ))),
        };
        let mut c1_bytes = c1.to_le_bytes(); // [u8; 16]
        let c2_bytes = c2.to_le_bytes(); // [u8; 16]
        // c* = c1_bytes + [0,1,...,15]
        let mut c_star = [0u8; 32];
        c_star[..16].copy_from_slice(&c1_bytes);
        for i in 0..16 {
            c_star[16 + i] = i as u8;
        }
        // c'[i] = if c2_bytes[i] < 32 { c_star[c2_bytes[i] as usize] } else { 0 }
        let mut result_bytes = [0u8; 16];
        for i in 0..16 {
            let idx = c2_bytes[i] as usize;
            result_bytes[i] = if idx < 32 { c_star[idx] } else { 0 };
        }
        let result = Value::V128(i128::from_le_bytes(result_bytes));
        thread.stack_mut().push_value(result);
        Ok(())
    }

    /// Executes the i8x16.shuffle instruction.
    /// 
    /// Pops two v128 values from the stack, uses the provided 16 indices to shuffle the concatenated bytes of both, and pushes the result as v128.
    pub fn i8x16_shuffle(thread: &mut Thread, lanes: [u8; 16]) -> RuntimeResult<()> {
        // Pop c2 from the stack
        let val2 = thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Execution("Expected second v128 value on stack for i8x16.shuffle".to_string())
        })?;
        // Pop c1 from the stack
        let val1 = thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Execution("Expected first v128 value on stack for i8x16.shuffle".to_string())
        })?;
        let (c1, c2) = match (val1, val2) {
            (Value::V128(v1), Value::V128(v2)) => (v1, v2),
            (a, b) => return Err(RuntimeError::TypeError(format!(
                "Expected v128 operands for i8x16.shuffle, got {:?} and {:?}", a, b
            ))),
        };
        let c1_bytes = c1.to_le_bytes();
        let c2_bytes = c2.to_le_bytes();
        // Concatenate c1_bytes and c2_bytes to form 32 bytes
        let mut concat = [0u8; 32];
        concat[..16].copy_from_slice(&c1_bytes);
        concat[16..].copy_from_slice(&c2_bytes);
        // For each lane index, select the corresponding byte
        let mut result_bytes = [0u8; 16];
        for i in 0..16 {
            let idx = lanes[i] as usize;
            if idx >= 32 {
                return Err(RuntimeError::TypeError(format!(
                    "i8x16.shuffle: lane index {} out of range (must be < 32)", idx
                )));
            }
            result_bytes[i] = concat[idx];
        }
        let result = Value::V128(i128::from_le_bytes(result_bytes));
        thread.stack_mut().push_value(result);
        Ok(())
    }

    /// Executes the shape.splat instruction (e.g., i8x16.splat, i16x8.splat, ...).
    /// Pops a scalar value, splats it to all lanes of the given shape, and pushes the result as v128.
    pub fn splat(thread: &mut Thread, shape: crate::wasm::ast::VectorShape) -> RuntimeResult<()> {
        let mut stack = thread.stack_mut();
        let value = stack.pop_value().ok_or_else(|| {
            RuntimeError::Execution("Expected scalar value on stack for shape.splat".to_string())
        })?;
        let result_bytes = match shape {
            VectorShape::Int(IntVectorShape::I8X16) => {
                let v = match value {
                    Value::I32(x) => x as u8,
                    _ => return Err(RuntimeError::TypeError(format!("Expected i32 for i8x16.splat, got {:?}", value))),
                };
                [v; 16]
            }
            VectorShape::Int(IntVectorShape::I16X8) => {
                let v = match value {
                    Value::I32(x) => x as u16,
                    _ => return Err(RuntimeError::TypeError(format!("Expected i32 for i16x8.splat, got {:?}", value))),
                };
                let mut arr = [0u8; 16];
                for i in 0..8 {
                    arr[i*2..i*2+2].copy_from_slice(&v.to_le_bytes());
                }
                arr
            }
            VectorShape::Int(IntVectorShape::I32X4) => {
                let v = match value {
                    Value::I32(x) => x,
                    _ => return Err(RuntimeError::TypeError(format!("Expected i32 for i32x4.splat, got {:?}", value))),
                };
                let mut arr = [0u8; 16];
                for i in 0..4 {
                    arr[i*4..i*4+4].copy_from_slice(&v.to_le_bytes());
                }
                arr
            }
            VectorShape::Int(IntVectorShape::I64X2) => {
                let v = match value {
                    Value::I64(x) => x,
                    _ => return Err(RuntimeError::TypeError(format!("Expected i64 for i64x2.splat, got {:?}", value))),
                };
                let mut arr = [0u8; 16];
                for i in 0..2 {
                    arr[i*8..i*8+8].copy_from_slice(&v.to_le_bytes());
                }
                arr
            }
            VectorShape::Float(FloatVectorShape::F32X4) => {
                let v = match value {
                    Value::F32(x) => x,
                    _ => return Err(RuntimeError::TypeError(format!("Expected f32 for f32x4.splat, got {:?}", value))),
                };
                let mut arr = [0u8; 16];
                for i in 0..4 {
                    arr[i*4..i*4+4].copy_from_slice(&v.to_le_bytes());
                }
                arr
            }
            VectorShape::Float(FloatVectorShape::F64X2) => {
                let v = match value {
                    Value::F64(x) => x,
                    _ => return Err(RuntimeError::TypeError(format!("Expected f64 for f64x2.splat, got {:?}", value))),
                };
                let mut arr = [0u8; 16];
                for i in 0..2 {
                    arr[i*8..i*8+8].copy_from_slice(&v.to_le_bytes());
                }
                arr
            }
        };
        let result = Value::V128(i128::from_le_bytes(result_bytes));
        stack.push_value(result);
        Ok(())
    }

    /// Executes the extract_lane instruction (e.g., i8x16.extract_lane_s, i8x16.extract_lane_u, ...).
    /// Pops a v128 value, extracts the specified lane, sign-extends if needed, and pushes the scalar result.
    pub fn extract_lane(thread: &mut Thread, shape: crate::wasm::ast::VectorShape, lane: u8, signed: bool) -> RuntimeResult<()> {
        let value = thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Execution("Expected v128 value on stack for extract_lane".to_string())
        })?;
        let v128 = match value {
            Value::V128(v) => v,
            _ => return Err(RuntimeError::TypeError(format!("Expected v128 for extract_lane, got {:?}", value))),
        };
        let bytes = v128.to_le_bytes();
        let scalar = match shape {
            VectorShape::Int(IntVectorShape::I8X16) => {
                if lane >= 16 { return Err(RuntimeError::TypeError(format!("i8x16.extract_lane: lane {} out of range", lane))); }
                let b = bytes[lane as usize];
                if signed {
                    Value::I32((b as i8) as i32)
                } else {
                    Value::I32(b as u8 as i32)
                }
            }
            VectorShape::Int(IntVectorShape::I16X8) => {
                if lane >= 8 { return Err(RuntimeError::TypeError(format!("i16x8.extract_lane: lane {} out of range", lane))); }
                let mut arr = [0u8; 2];
                arr.copy_from_slice(&bytes[(lane as usize)*2..(lane as usize)*2+2]);
                let b = u16::from_le_bytes(arr);
                if signed {
                    Value::I32((b as i16) as i32)
                } else {
                    Value::I32(b as u16 as i32)
                }
            }
            VectorShape::Int(IntVectorShape::I32X4) => {
                if lane >= 4 { return Err(RuntimeError::TypeError(format!("i32x4.extract_lane: lane {} out of range", lane))); }
                let mut arr = [0u8; 4];
                arr.copy_from_slice(&bytes[(lane as usize)*4..(lane as usize)*4+4]);
                let b = i32::from_le_bytes(arr);
                Value::I32(b)
            }
            VectorShape::Int(IntVectorShape::I64X2) => {
                if lane >= 2 { return Err(RuntimeError::TypeError(format!("i64x2.extract_lane: lane {} out of range", lane))); }
                let mut arr = [0u8; 8];
                arr.copy_from_slice(&bytes[(lane as usize)*8..(lane as usize)*8+8]);
                let b = i64::from_le_bytes(arr);
                Value::I64(b)
            }
            VectorShape::Float(FloatVectorShape::F32X4) => {
                if lane >= 4 { return Err(RuntimeError::TypeError(format!("f32x4.extract_lane: lane {} out of range", lane))); }
                let mut arr = [0u8; 4];
                arr.copy_from_slice(&bytes[(lane as usize)*4..(lane as usize)*4+4]);
                let b = f32::from_le_bytes(arr);
                Value::F32(b)
            }
            VectorShape::Float(FloatVectorShape::F64X2) => {
                if lane >= 2 { return Err(RuntimeError::TypeError(format!("f64x2.extract_lane: lane {} out of range", lane))); }
                let mut arr = [0u8; 8];
                arr.copy_from_slice(&bytes[(lane as usize)*8..(lane as usize)*8+8]);
                let b = f64::from_le_bytes(arr);
                Value::F64(b)
            }
        };
        thread.stack_mut().push_value(scalar);
        Ok(())
    }

    /// Executes the shape.vunop instruction (e.g., i8x16.abs, i16x8.abs, i32x4.abs, f32x4.abs, f64x2.abs, f32x4.neg, f64x2.neg, f32x4.sqrt, f64x2.sqrt).
    /// Pops a v128 value, applies the unary operation (abs, neg, sqrt) per lane, and pushes the result as v128.
    pub fn vunop(thread: &mut Thread, shape: VectorShape, op: impl Into<VectorVUnOp>) -> RuntimeResult<()> {
        let value = thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Execution("Expected v128 value on stack for shape.vunop".to_string())
        })?;
        let v128 = match value {
            Value::V128(v) => v,
            _ => return Err(RuntimeError::TypeError(format!("Expected v128 for shape.vunop, got {:?}", value))),
        };
        let bytes = v128.to_le_bytes();
        let result_bytes = match (shape, op.into()) {
            (VectorShape::Int(IntVectorShape::I8X16), VectorVUnOp::Not) => {
                let mut arr = [0u8; 16];
                for i in 0..16 {
                    arr[i] = !bytes[i];
                }
                arr
            }
            (VectorShape::Int(IntVectorShape::I16X8), VectorVUnOp::Not) => {
                let mut arr = [0u8; 16];
                for i in 0..8 {
                    let mut lane_bytes = [0u8; 2];
                    lane_bytes.copy_from_slice(&bytes[i*2..i*2+2]);
                    let lane = u16::from_le_bytes(lane_bytes);
                    let not_lane = !lane;
                    arr[i*2..i*2+2].copy_from_slice(&not_lane.to_le_bytes());
                }
                arr
            }
            (VectorShape::Int(IntVectorShape::I32X4), VectorVUnOp::Not) => {
                let mut arr = [0u8; 16];
                for i in 0..4 {
                    let mut lane_bytes = [0u8; 4];
                    lane_bytes.copy_from_slice(&bytes[i*4..i*4+4]);
                    let lane = u32::from_le_bytes(lane_bytes);
                    let not_lane = !lane;
                    arr[i*4..i*4+4].copy_from_slice(&not_lane.to_le_bytes());
                }
                arr
            }
            (VectorShape::Int(IntVectorShape::I64X2), VectorVUnOp::Not) => {
                let mut arr = [0u8; 16];
                for i in 0..2 {
                    let mut lane_bytes = [0u8; 8];
                    lane_bytes.copy_from_slice(&bytes[i*8..i*8+8]);
                    let lane = u64::from_le_bytes(lane_bytes);
                    let not_lane = !lane;
                    arr[i*8..i*8+8].copy_from_slice(&not_lane.to_le_bytes());
                }
                arr
            }
            (VectorShape::Float(FloatVectorShape::F32X4), VectorVUnOp::Not) => {
                let mut arr = [0u8; 16];
                for i in 0..4 {
                    let mut lane_bytes = [0u8; 4];
                    lane_bytes.copy_from_slice(&bytes[i*4..i*4+4]);
                    let lane = f32::from_le_bytes(lane_bytes);
                    let not_lane = !lane.to_bits();
                    arr[i*4..i*4+4].copy_from_slice(&not_lane.to_le_bytes());
                }
                arr
            }
            (VectorShape::Float(FloatVectorShape::F64X2), VectorVUnOp::Not) => {
                let mut arr = [0u8; 16];
                for i in 0..2 {
                    let mut lane_bytes = [0u8; 8];
                    lane_bytes.copy_from_slice(&bytes[i*8..i*8+8]);
                    let lane = f64::from_le_bytes(lane_bytes);
                    let not_lane = !lane.to_bits();
                    arr[i*8..i*8+8].copy_from_slice(&not_lane.to_le_bytes());
                }
                arr
            }
            (s, o) => return Err(RuntimeError::Execution(format!("Unsupported shape.vunop: shape {:?}, op {:?}", s, o))),
        };
        let result = Value::V128(i128::from_le_bytes(result_bytes));
        thread.stack_mut().push_value(result);
        Ok(())
    }

    /// Executes the shape.vbinop instruction (e.g., i8x16.add, i16x8.add, i32x4.add, f32x4.add, f64x2.add, ...).
    /// Pops two v128 values, applies the binary operation per lane, and pushes the result as v128.
    pub fn vbinop(thread: &mut Thread, shape: VectorShape, op: &crate::wasm::ast::VectorInstruction) -> RuntimeResult<()> {
        let val2 = thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Execution("Expected second v128 value on stack for shape.vbinop".to_string())
        })?;
        let val1 = thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Execution("Expected first v128 value on stack for shape.vbinop".to_string())
        })?;
        let v1 = match val1 {
            Value::V128(v) => v,
            _ => return Err(RuntimeError::TypeError(format!("Expected v128 for shape.vbinop, got {:?}", val1))),
        };
        let v2 = match val2 {
            Value::V128(v) => v,
            _ => return Err(RuntimeError::TypeError(format!("Expected v128 for shape.vbinop, got {:?}", val2))),
        };
        let b1 = v1.to_le_bytes();
        let b2 = v2.to_le_bytes();
        let result_bytes = match op {
            VectorInstruction::IntBinOp { shape: int_shape, op: int_op } => {
                match (int_shape, int_op) {
                    (IntVectorShape::I8X16, VectorIntBinOp::Add) => {
                        let mut arr = [0u8; 16];
                        for i in 0..16 {
                            let a = b1[i] as i8;
                            let b = b2[i] as i8;
                            arr[i] = a.wrapping_add(b) as u8;
                        }
                        arr
                    }
                    (IntVectorShape::I8X16, VectorIntBinOp::Sub) => {
                        let mut arr = [0u8; 16];
                        for i in 0..16 {
                            let a = b1[i] as i8;
                            let b = b2[i] as i8;
                            arr[i] = a.wrapping_sub(b) as u8;
                        }
                        arr
                    }
                    (IntVectorShape::I16X8, VectorIntBinOp::Add) => {
                        let mut arr = [0u8; 16];
                        for i in 0..8 {
                            let mut a_bytes = [0u8; 2];
                            let mut b_bytes = [0u8; 2];
                            a_bytes.copy_from_slice(&b1[i*2..i*2+2]);
                            b_bytes.copy_from_slice(&b2[i*2..i*2+2]);
                            let a = i16::from_le_bytes(a_bytes);
                            let b = i16::from_le_bytes(b_bytes);
                            let r = a.wrapping_add(b);
                            arr[i*2..i*2+2].copy_from_slice(&r.to_le_bytes());
                        }
                        arr
                    }
                    (IntVectorShape::I16X8, VectorIntBinOp::Sub) => {
                        let mut arr = [0u8; 16];
                        for i in 0..8 {
                            let mut a_bytes = [0u8; 2];
                            let mut b_bytes = [0u8; 2];
                            a_bytes.copy_from_slice(&b1[i*2..i*2+2]);
                            b_bytes.copy_from_slice(&b2[i*2..i*2+2]);
                            let a = i16::from_le_bytes(a_bytes);
                            let b = i16::from_le_bytes(b_bytes);
                            let r = a.wrapping_sub(b);
                            arr[i*2..i*2+2].copy_from_slice(&r.to_le_bytes());
                        }
                        arr
                    }
                    (IntVectorShape::I32X4, VectorIntBinOp::Add) => {
                        let mut arr = [0u8; 16];
                        for i in 0..4 {
                            let mut a_bytes = [0u8; 4];
                            let mut b_bytes = [0u8; 4];
                            a_bytes.copy_from_slice(&b1[i*4..i*4+4]);
                            b_bytes.copy_from_slice(&b2[i*4..i*4+4]);
                            let a = i32::from_le_bytes(a_bytes);
                            let b = i32::from_le_bytes(b_bytes);
                            let r = a.wrapping_add(b);
                            arr[i*4..i*4+4].copy_from_slice(&r.to_le_bytes());
                        }
                        arr
                    }
                    (IntVectorShape::I32X4, VectorIntBinOp::Sub) => {
                        let mut arr = [0u8; 16];
                        for i in 0..4 {
                            let mut a_bytes = [0u8; 4];
                            let mut b_bytes = [0u8; 4];
                            a_bytes.copy_from_slice(&b1[i*4..i*4+4]);
                            b_bytes.copy_from_slice(&b2[i*4..i*4+4]);
                            let a = i32::from_le_bytes(a_bytes);
                            let b = i32::from_le_bytes(b_bytes);
                            let r = a.wrapping_sub(b);
                            arr[i*4..i*4+4].copy_from_slice(&r.to_le_bytes());
                        }
                        arr
                    }
                    // TODO: I64X2, 他の演算
                    _ => return Err(RuntimeError::Execution(format!("Unsupported int vbinop: {:?} {:?}", int_shape, int_op))),
                }
            }
            VectorInstruction::FloatBinOp { shape: float_shape, op: float_op } => {
                match (float_shape, float_op) {
                    (FloatVectorShape::F32X4, VectorFloatBinOp::Add) => {
                        let mut arr = [0u8; 16];
                        for i in 0..4 {
                            let mut a_bytes = [0u8; 4];
                            let mut b_bytes = [0u8; 4];
                            a_bytes.copy_from_slice(&b1[i*4..i*4+4]);
                            b_bytes.copy_from_slice(&b2[i*4..i*4+4]);
                            let a = f32::from_le_bytes(a_bytes);
                            let b = f32::from_le_bytes(b_bytes);
                            let r = a + b;
                            arr[i*4..i*4+4].copy_from_slice(&r.to_le_bytes());
                        }
                        arr
                    }
                    (FloatVectorShape::F32X4, VectorFloatBinOp::Sub) => {
                        let mut arr = [0u8; 16];
                        for i in 0..4 {
                            let mut a_bytes = [0u8; 4];
                            let mut b_bytes = [0u8; 4];
                            a_bytes.copy_from_slice(&b1[i*4..i*4+4]);
                            b_bytes.copy_from_slice(&b2[i*4..i*4+4]);
                            let a = f32::from_le_bytes(a_bytes);
                            let b = f32::from_le_bytes(b_bytes);
                            let r = a - b;
                            arr[i*4..i*4+4].copy_from_slice(&r.to_le_bytes());
                        }
                        arr
                    }
                    (FloatVectorShape::F64X2, VectorFloatBinOp::Add) => {
                        let mut arr = [0u8; 16];
                        for i in 0..2 {
                            let mut a_bytes = [0u8; 8];
                            let mut b_bytes = [0u8; 8];
                            a_bytes.copy_from_slice(&b1[i*8..i*8+8]);
                            b_bytes.copy_from_slice(&b2[i*8..i*8+8]);
                            let a = f64::from_le_bytes(a_bytes);
                            let b = f64::from_le_bytes(b_bytes);
                            let r = a + b;
                            arr[i*8..i*8+8].copy_from_slice(&r.to_le_bytes());
                        }
                        arr
                    }
                    (FloatVectorShape::F64X2, VectorFloatBinOp::Sub) => {
                        let mut arr = [0u8; 16];
                        for i in 0..2 {
                            let mut a_bytes = [0u8; 8];
                            let mut b_bytes = [0u8; 8];
                            a_bytes.copy_from_slice(&b1[i*8..i*8+8]);
                            b_bytes.copy_from_slice(&b2[i*8..i*8+8]);
                            let a = f64::from_le_bytes(a_bytes);
                            let b = f64::from_le_bytes(b_bytes);
                            let r = a - b;
                            arr[i*8..i*8+8].copy_from_slice(&r.to_le_bytes());
                        }
                        arr
                    }
                    _ => return Err(RuntimeError::Execution(format!("Unsupported float vbinop: {:?} {:?}", float_shape, float_op))),
                }
            }
            _ => return Err(RuntimeError::Execution("Unsupported vbinop instruction variant".to_string())),
        };
        let result = Value::V128(i128::from_le_bytes(result_bytes));
        thread.stack_mut().push_value(result);
        Ok(())
    }

    /// Executes the t x N.vrelop instruction (e.g., i8x16.eq, i16x8.lt_s, f32x4.gt, ...).
    /// Pops two v128 values, applies the relational operation per lane, and pushes the result as v128.
    pub fn vrelop(thread: &mut Thread, op: &crate::wasm::ast::VectorInstruction) -> RuntimeResult<()> {
        let val2 = thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Execution("Expected second v128 value on stack for vrelop".to_string())
        })?;
        let val1 = thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Execution("Expected first v128 value on stack for vrelop".to_string())
        })?;
        let v1 = match val1 {
            Value::V128(v) => v,
            _ => return Err(RuntimeError::TypeError(format!("Expected v128 for vrelop, got {:?}", val1))),
        };
        let v2 = match val2 {
            Value::V128(v) => v,
            _ => return Err(RuntimeError::TypeError(format!("Expected v128 for vrelop, got {:?}", val2))),
        };
        let b1 = v1.to_le_bytes();
        let b2 = v2.to_le_bytes();
        let result_bytes = match op {
            VectorInstruction::IntRelOp { shape: int_shape, op: int_op } => {
                match (int_shape, int_op) {
                    (IntVectorShape::I8X16, VectorIntRelOp::Eq) => {
                        let mut arr = [0u8; 16];
                        for i in 0..16 {
                            let a = b1[i] as i8;
                            let b = b2[i] as i8;
                            arr[i] = if a == b { 0xFF } else { 0x00 };
                        }
                        arr
                    }
                    (IntVectorShape::I8X16, VectorIntRelOp::Ne) => {
                        let mut arr = [0u8; 16];
                        for i in 0..16 {
                            let a = b1[i] as i8;
                            let b = b2[i] as i8;
                            arr[i] = if a != b { 0xFF } else { 0x00 };
                        }
                        arr
                    }
                    (IntVectorShape::I8X16, VectorIntRelOp::Lt { signed }) => {
                        let mut arr = [0u8; 16];
                        for i in 0..16 {
                            let a = if *signed { b1[i] as i8 as i32 } else { b1[i] as u8 as i32 };
                            let b = if *signed { b2[i] as i8 as i32 } else { b2[i] as u8 as i32 };
                            arr[i] = if a < b { 0xFF } else { 0x00 };
                        }
                        arr
                    }
                    (IntVectorShape::I8X16, VectorIntRelOp::Gt { signed }) => {
                        let mut arr = [0u8; 16];
                        for i in 0..16 {
                            let a = if *signed { b1[i] as i8 as i32 } else { b1[i] as u8 as i32 };
                            let b = if *signed { b2[i] as i8 as i32 } else { b2[i] as u8 as i32 };
                            arr[i] = if a > b { 0xFF } else { 0x00 };
                        }
                        arr
                    }
                    (IntVectorShape::I8X16, VectorIntRelOp::Le { signed }) => {
                        let mut arr = [0u8; 16];
                        for i in 0..16 {
                            let a = if *signed { b1[i] as i8 as i32 } else { b1[i] as u8 as i32 };
                            let b = if *signed { b2[i] as i8 as i32 } else { b2[i] as u8 as i32 };
                            arr[i] = if a <= b { 0xFF } else { 0x00 };
                        }
                        arr
                    }
                    (IntVectorShape::I8X16, VectorIntRelOp::Ge { signed }) => {
                        let mut arr = [0u8; 16];
                        for i in 0..16 {
                            let a = if *signed { b1[i] as i8 as i32 } else { b1[i] as u8 as i32 };
                            let b = if *signed { b2[i] as i8 as i32 } else { b2[i] as u8 as i32 };
                            arr[i] = if a >= b { 0xFF } else { 0x00 };
                        }
                        arr
                    }
                    // TODO: I16X8, I32X4, I64X2
                    _ => return Err(RuntimeError::Execution(format!("Unsupported int vrelop: {:?} {:?}", int_shape, int_op))),
                }
            }
            VectorInstruction::FloatRelOp { shape: float_shape, op: float_op } => {
                match (float_shape, float_op) {
                    (FloatVectorShape::F32X4, VectorFloatRelOp::Eq) => {
                        let mut arr = [0u8; 16];
                        for i in 0..4 {
                            let mut a_bytes = [0u8; 4];
                            let mut b_bytes = [0u8; 4];
                            a_bytes.copy_from_slice(&b1[i*4..i*4+4]);
                            b_bytes.copy_from_slice(&b2[i*4..i*4+4]);
                            let a = f32::from_le_bytes(a_bytes);
                            let b = f32::from_le_bytes(b_bytes);
                            let r = if a == b { 0xFFFFFFFFu32 } else { 0x00000000u32 };
                            arr[i*4..i*4+4].copy_from_slice(&r.to_le_bytes());
                        }
                        arr
                    }
                    (FloatVectorShape::F32X4, VectorFloatRelOp::Ne) => {
                        let mut arr = [0u8; 16];
                        for i in 0..4 {
                            let mut a_bytes = [0u8; 4];
                            let mut b_bytes = [0u8; 4];
                            a_bytes.copy_from_slice(&b1[i*4..i*4+4]);
                            b_bytes.copy_from_slice(&b2[i*4..i*4+4]);
                            let a = f32::from_le_bytes(a_bytes);
                            let b = f32::from_le_bytes(b_bytes);
                            let r = if a != b { 0xFFFFFFFFu32 } else { 0x00000000u32 };
                            arr[i*4..i*4+4].copy_from_slice(&r.to_le_bytes());
                        }
                        arr
                    }
                    (FloatVectorShape::F32X4, VectorFloatRelOp::Lt) => {
                        let mut arr = [0u8; 16];
                        for i in 0..4 {
                            let mut a_bytes = [0u8; 4];
                            let mut b_bytes = [0u8; 4];
                            a_bytes.copy_from_slice(&b1[i*4..i*4+4]);
                            b_bytes.copy_from_slice(&b2[i*4..i*4+4]);
                            let a = f32::from_le_bytes(a_bytes);
                            let b = f32::from_le_bytes(b_bytes);
                            let r = if a < b { 0xFFFFFFFFu32 } else { 0x00000000u32 };
                            arr[i*4..i*4+4].copy_from_slice(&r.to_le_bytes());
                        }
                        arr
                    }
                    (FloatVectorShape::F32X4, VectorFloatRelOp::Gt) => {
                        let mut arr = [0u8; 16];
                        for i in 0..4 {
                            let mut a_bytes = [0u8; 4];
                            let mut b_bytes = [0u8; 4];
                            a_bytes.copy_from_slice(&b1[i*4..i*4+4]);
                            b_bytes.copy_from_slice(&b2[i*4..i*4+4]);
                            let a = f32::from_le_bytes(a_bytes);
                            let b = f32::from_le_bytes(b_bytes);
                            let r = if a > b { 0xFFFFFFFFu32 } else { 0x00000000u32 };
                            arr[i*4..i*4+4].copy_from_slice(&r.to_le_bytes());
                        }
                        arr
                    }
                    (FloatVectorShape::F32X4, VectorFloatRelOp::Le) => {
                        let mut arr = [0u8; 16];
                        for i in 0..4 {
                            let mut a_bytes = [0u8; 4];
                            let mut b_bytes = [0u8; 4];
                            a_bytes.copy_from_slice(&b1[i*4..i*4+4]);
                            b_bytes.copy_from_slice(&b2[i*4..i*4+4]);
                            let a = f32::from_le_bytes(a_bytes);
                            let b = f32::from_le_bytes(b_bytes);
                            let r = if a <= b { 0xFFFFFFFFu32 } else { 0x00000000u32 };
                            arr[i*4..i*4+4].copy_from_slice(&r.to_le_bytes());
                        }
                        arr
                    }
                    (FloatVectorShape::F32X4, VectorFloatRelOp::Ge) => {
                        let mut arr = [0u8; 16];
                        for i in 0..4 {
                            let mut a_bytes = [0u8; 4];
                            let mut b_bytes = [0u8; 4];
                            a_bytes.copy_from_slice(&b1[i*4..i*4+4]);
                            b_bytes.copy_from_slice(&b2[i*4..i*4+4]);
                            let a = f32::from_le_bytes(a_bytes);
                            let b = f32::from_le_bytes(b_bytes);
                            let r = if a >= b { 0xFFFFFFFFu32 } else { 0x00000000u32 };
                            arr[i*4..i*4+4].copy_from_slice(&r.to_le_bytes());
                        }
                        arr
                    }
                    // TODO: F64X2
                    _ => return Err(RuntimeError::Execution(format!("Unsupported float vrelop: {:?} {:?}", float_shape, float_op))),
                }
            }
            _ => return Err(RuntimeError::Execution("Unsupported vrelop instruction variant".to_string())),
        };
        let result = Value::V128(i128::from_le_bytes(result_bytes));
        thread.stack_mut().push_value(result);
        Ok(())
    }

    /// Executes the t x N.vishiftop instruction (e.g., i8x16.shl, i16x8.shr_s, i32x4.shr_u, ...).
    /// Pops an i32 value (shift amount) and a v128 value, applies the shift operation per lane, and pushes the result as v128.
    pub fn vishiftop(thread: &mut Thread, op: &crate::wasm::ast::VectorInstruction) -> RuntimeResult<()> {
        let shift_val = thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Execution("Expected i32 value on stack for vishiftop".to_string())
        })?;
        let shift = match shift_val {
            Value::I32(s) => s as u32,
            _ => return Err(RuntimeError::TypeError(format!("Expected i32 for vishiftop, got {:?}", shift_val))),
        };
        let val = thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Execution("Expected v128 value on stack for vishiftop".to_string())
        })?;
        let v = match val {
            Value::V128(v) => v,
            _ => return Err(RuntimeError::TypeError(format!("Expected v128 for vishiftop, got {:?}", val))),
        };
        let b = v.to_le_bytes();
        let result_bytes = match op {
            VectorInstruction::IntShiftOp { shape: int_shape, op: shift_op } => {
                match (int_shape, shift_op) {
                    (IntVectorShape::I8X16, VectorIntShiftOp::Shl) => {
                        let mut arr = [0u8; 16];
                        let s = (shift & 0x7) as u8; // 3 bits for i8
                        for i in 0..16 {
                            let a = b[i] as u8;
                            arr[i] = a.wrapping_shl(s as u32);
                        }
                        arr
                    }
                    (IntVectorShape::I8X16, VectorIntShiftOp::Shr { signed }) => {
                        let mut arr = [0u8; 16];
                        let s = (shift & 0x7) as u8; // 3 bits for i8
                        for i in 0..16 {
                            if *signed {
                                let a = b[i] as i8;
                                arr[i] = (a.wrapping_shr(s as u32) as i8) as u8;
                            } else {
                                let a = b[i] as u8;
                                arr[i] = a.wrapping_shr(s as u32);
                            }
                        }
                        arr
                    }
                    (IntVectorShape::I16X8, VectorIntShiftOp::Shl) => {
                        let mut arr = [0u8; 16];
                        let s = (shift & 0xF) as u16; // 4 bits for i16
                        for i in 0..8 {
                            let mut lane_bytes = [0u8; 2];
                            lane_bytes.copy_from_slice(&b[i*2..i*2+2]);
                            let a = u16::from_le_bytes(lane_bytes);
                            let r = a.wrapping_shl(s as u32);
                            arr[i*2..i*2+2].copy_from_slice(&r.to_le_bytes());
                        }
                        arr
                    }
                    (IntVectorShape::I16X8, VectorIntShiftOp::Shr { signed }) => {
                        let mut arr = [0u8; 16];
                        let s = (shift & 0xF) as u16; // 4 bits for i16
                        for i in 0..8 {
                            let mut lane_bytes = [0u8; 2];
                            lane_bytes.copy_from_slice(&b[i*2..i*2+2]);
                            if *signed {
                                let a = i16::from_le_bytes(lane_bytes);
                                let r = a.wrapping_shr(s as u32);
                                arr[i*2..i*2+2].copy_from_slice(&(r as u16).to_le_bytes());
                            } else {
                                let a = u16::from_le_bytes(lane_bytes);
                                let r = a.wrapping_shr(s as u32);
                                arr[i*2..i*2+2].copy_from_slice(&r.to_le_bytes());
                            }
                        }
                        arr
                    }
                    (IntVectorShape::I32X4, VectorIntShiftOp::Shl) => {
                        let mut arr = [0u8; 16];
                        let s = (shift & 0x1F) as u32; // 5 bits for i32
                        for i in 0..4 {
                            let mut lane_bytes = [0u8; 4];
                            lane_bytes.copy_from_slice(&b[i*4..i*4+4]);
                            let a = u32::from_le_bytes(lane_bytes);
                            let r = a.wrapping_shl(s);
                            arr[i*4..i*4+4].copy_from_slice(&r.to_le_bytes());
                        }
                        arr
                    }
                    (IntVectorShape::I32X4, VectorIntShiftOp::Shr { signed }) => {
                        let mut arr = [0u8; 16];
                        let s = (shift & 0x1F) as u32; // 5 bits for i32
                        for i in 0..4 {
                            let mut lane_bytes = [0u8; 4];
                            lane_bytes.copy_from_slice(&b[i*4..i*4+4]);
                            if *signed {
                                let a = i32::from_le_bytes(lane_bytes);
                                let r = a.wrapping_shr(s);
                                arr[i*4..i*4+4].copy_from_slice(&(r as u32).to_le_bytes());
                            } else {
                                let a = u32::from_le_bytes(lane_bytes);
                                let r = a.wrapping_shr(s);
                                arr[i*4..i*4+4].copy_from_slice(&r.to_le_bytes());
                            }
                        }
                        arr
                    }
                    // TODO: I64X2
                    _ => return Err(RuntimeError::Execution(format!("Unsupported int vishiftop: {:?} {:?}", int_shape, shift_op))),
                }
            }
            _ => return Err(RuntimeError::Execution("Unsupported vishiftop instruction variant".to_string())),
        };
        let result = Value::V128(i128::from_le_bytes(result_bytes));
        thread.stack_mut().push_value(result);
        Ok(())
    }

    /// Executes the shape.all_true instruction (e.g., i8x16.all_true, i16x8.all_true, ...).
    /// Pops a v128 value, checks if all lanes are nonzero, and pushes i32(1) if true, else i32(0).
    pub fn all_true(thread: &mut Thread, shape: crate::wasm::ast::IntVectorShape) -> RuntimeResult<()> {
        let value = thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Execution("Expected v128 value on stack for shape.all_true".to_string())
        })?;
        let v128 = match value {
            Value::V128(v) => v,
            _ => return Err(RuntimeError::TypeError(format!("Expected v128 for shape.all_true, got {:?}", value))),
        };
        let bytes = v128.to_le_bytes();
        let all_true = match shape {
            crate::wasm::ast::IntVectorShape::I8X16 => {
                (0..16).all(|i| bytes[i] != 0)
            }
            crate::wasm::ast::IntVectorShape::I16X8 => {
                (0..8).all(|i| {
                    let mut arr = [0u8; 2];
                    arr.copy_from_slice(&bytes[i*2..i*2+2]);
                    i16::from_le_bytes(arr) != 0
                })
            }
            crate::wasm::ast::IntVectorShape::I32X4 => {
                (0..4).all(|i| {
                    let mut arr = [0u8; 4];
                    arr.copy_from_slice(&bytes[i*4..i*4+4]);
                    i32::from_le_bytes(arr) != 0
                })
            }
            crate::wasm::ast::IntVectorShape::I64X2 => {
                (0..2).all(|i| {
                    let mut arr = [0u8; 8];
                    arr.copy_from_slice(&bytes[i*8..i*8+8]);
                    i64::from_le_bytes(arr) != 0
                })
            }
        };
        thread.stack_mut().push_value(Value::I32(if all_true { 1 } else { 0 }));
        Ok(())
    }

    /// Executes the t x N.bitmask instruction (e.g., i8x16.bitmask, i16x8.bitmask, ...).
    /// Pops a v128 value, computes the sign bit of each lane, and pushes the concatenated bits as i32.
    pub fn bitmask(thread: &mut Thread, shape: crate::wasm::ast::IntVectorShape) -> RuntimeResult<()> {
        let value = thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Execution("Expected v128 value on stack for bitmask".to_string())
        })?;
        let v128 = match value {
            Value::V128(v) => v,
            _ => return Err(RuntimeError::TypeError(format!("Expected v128 for bitmask, got {:?}", value))),
        };
        let bytes = v128.to_le_bytes();
        let mask = match shape {
            crate::wasm::ast::IntVectorShape::I8X16 => {
                let mut m = 0u32;
                for i in 0..16 {
                    let lane = bytes[i] as i8;
                    if lane < 0 { m |= 1 << i; }
                }
                m
            }
            crate::wasm::ast::IntVectorShape::I16X8 => {
                let mut m = 0u32;
                for i in 0..8 {
                    let mut arr = [0u8; 2];
                    arr.copy_from_slice(&bytes[i*2..i*2+2]);
                    let lane = i16::from_le_bytes(arr);
                    if lane < 0 { m |= 1 << i; }
                }
                m
            }
            crate::wasm::ast::IntVectorShape::I32X4 => {
                let mut m = 0u32;
                for i in 0..4 {
                    let mut arr = [0u8; 4];
                    arr.copy_from_slice(&bytes[i*4..i*4+4]);
                    let lane = i32::from_le_bytes(arr);
                    if lane < 0 { m |= 1 << i; }
                }
                m
            }
            crate::wasm::ast::IntVectorShape::I64X2 => {
                let mut m = 0u32;
                for i in 0..2 {
                    let mut arr = [0u8; 8];
                    arr.copy_from_slice(&bytes[i*8..i*8+8]);
                    let lane = i64::from_le_bytes(arr);
                    if lane < 0 { m |= 1 << i; }
                }
                m
            }
        };
        thread.stack_mut().push_value(Value::I32(mask as i32));
        Ok(())
    }

    /// Executes the t2xN.narrow_t1xM_sx instruction (e.g., i8x16.narrow_i16x8_s, i8x16.narrow_i16x8_u, i16x8.narrow_i32x4_s, ...).
    /// Pops two v128 values, narrows each lane from t1 to t2 (signed/unsigned), concatenates, and pushes as v128.
    pub fn narrow(thread: &mut Thread, shape: crate::wasm::ast::IntVectorShape, signed: bool) -> RuntimeResult<()> {
        // Pop c2
        let val2 = thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Execution("Expected second v128 value on stack for narrow".to_string())
        })?;
        let v2 = match val2 {
            Value::V128(v) => v,
            _ => return Err(RuntimeError::TypeError(format!("Expected v128 for narrow, got {:?}", val2))),
        };
        // Pop c1
        let val1 = thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Execution("Expected first v128 value on stack for narrow".to_string())
        })?;
        let v1 = match val1 {
            Value::V128(v) => v,
            _ => return Err(RuntimeError::TypeError(format!("Expected v128 for narrow, got {:?}", val1))),
        };
        let b1 = v1.to_le_bytes();
        let b2 = v2.to_le_bytes();
        let result_bytes = match shape {
            IntVectorShape::I8X16 => {
                // i8x16.narrow_i16x8_s/u
                let mut arr = [0u8; 16];
                for i in 0..8 {
                    let mut lane_bytes = [0u8; 2];
                    lane_bytes.copy_from_slice(&b1[i*2..i*2+2]);
                    let v = if signed {
                        let x = i16::from_le_bytes(lane_bytes);
                        x.clamp(i8::MIN as i16, i8::MAX as i16) as i8 as u8
                    } else {
                        let x = u16::from_le_bytes(lane_bytes);
                        x.min(u8::MAX as u16) as u8
                    };
                    arr[i] = v;
                }
                for i in 0..8 {
                    let mut lane_bytes = [0u8; 2];
                    lane_bytes.copy_from_slice(&b2[i*2..i*2+2]);
                    let v = if signed {
                        let x = i16::from_le_bytes(lane_bytes);
                        x.clamp(i8::MIN as i16, i8::MAX as i16) as i8 as u8
                    } else {
                        let x = u16::from_le_bytes(lane_bytes);
                        x.min(u8::MAX as u16) as u8
                    };
                    arr[8 + i] = v;
                }
                arr
            }
            IntVectorShape::I16X8 => {
                // i16x8.narrow_i32x4_s/u
                let mut arr = [0u8; 16];
                for i in 0..4 {
                    let mut lane_bytes = [0u8; 4];
                    lane_bytes.copy_from_slice(&b1[i*4..i*4+4]);
                    let v = if signed {
                        let x = i32::from_le_bytes(lane_bytes);
                        x.clamp(i16::MIN as i32, i16::MAX as i32) as i16 as u16
                    } else {
                        let x = u32::from_le_bytes(lane_bytes);
                        x.min(u16::MAX as u32) as u16
                    };
                    arr[i*2..i*2+2].copy_from_slice(&v.to_le_bytes());
                }
                for i in 0..4 {
                    let mut lane_bytes = [0u8; 4];
                    lane_bytes.copy_from_slice(&b2[i*4..i*4+4]);
                    let v = if signed {
                        let x = i32::from_le_bytes(lane_bytes);
                        x.clamp(i16::MIN as i32, i16::MAX as i32) as i16 as u16
                    } else {
                        let x = u32::from_le_bytes(lane_bytes);
                        x.min(u16::MAX as u32) as u16
                    };
                    arr[8 + i*2..8 + i*2+2].copy_from_slice(&v.to_le_bytes());
                }
                arr
            }
            _ => return Err(RuntimeError::Execution("Unsupported shape for narrow".to_string())),
        };
        let result = Value::V128(i128::from_le_bytes(result_bytes));
        thread.stack_mut().push_value(result);
        Ok(())
    }

    /// Executes the t2xN.vcvtop_t1xM_sx instruction (e.g., i32x4.trunc_sat_f32x4_s, i32x4.trunc_sat_f32x4_u, f32x4.convert_i32x4_s, ...).
    /// Pops a v128 value, converts each lane from t1 to t2 (signed/unsigned, saturating if needed), and pushes as v128.
    pub fn vcvtop(thread: &mut Thread, op: &crate::wasm::ast::VectorInstruction) -> RuntimeResult<()> {
        let value = thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Execution("Expected v128 value on stack for vcvtop".to_string())
        })?;
        let v128 = match value {
            Value::V128(v) => v,
            _ => return Err(RuntimeError::TypeError(format!("Expected v128 for vcvtop, got {:?}", value))),
        };
        let bytes = v128.to_le_bytes();
        let result_bytes = match op {
            VectorInstruction::TruncSat { shape, signed } => {
                // i32x4.trunc_sat_f32x4_s/u
                match (shape, signed) {
                    (IntVectorShape::I32X4, true) => {
                        let mut arr = [0u8; 16];
                        for i in 0..4 {
                            let mut lane_bytes = [0u8; 4];
                            lane_bytes.copy_from_slice(&bytes[i*4..i*4+4]);
                            let f = f32::from_le_bytes(lane_bytes);
                            let v = if f.is_nan() {
                                0
                            } else if f > i32::MAX as f32 {
                                i32::MAX
                            } else if f < i32::MIN as f32 {
                                i32::MIN
                            } else {
                                f as i32
                            };
                            arr[i*4..i*4+4].copy_from_slice(&v.to_le_bytes());
                        }
                        arr
                    }
                    (IntVectorShape::I32X4, false) => {
                        let mut arr = [0u8; 16];
                        for i in 0..4 {
                            let mut lane_bytes = [0u8; 4];
                            lane_bytes.copy_from_slice(&bytes[i*4..i*4+4]);
                            let f = f32::from_le_bytes(lane_bytes);
                            let v = if f.is_nan() {
                                0
                            } else if f > u32::MAX as f32 {
                                u32::MAX as i32
                            } else if f < 0.0 {
                                0
                            } else {
                                f as u32 as i32
                            };
                            arr[i*4..i*4+4].copy_from_slice(&v.to_le_bytes());
                        }
                        arr
                    }
                    _ => return Err(RuntimeError::Execution("Unsupported TruncSat shape".to_string())),
                }
            }
            VectorInstruction::Convert { shape, signed } => {
                // f32x4.convert_i32x4_s/u
                match (shape, signed) {
                    (FloatVectorShape::F32X4, true) => {
                        let mut arr = [0u8; 16];
                        for i in 0..4 {
                            let mut lane_bytes = [0u8; 4];
                            lane_bytes.copy_from_slice(&bytes[i*4..i*4+4]);
                            let v = i32::from_le_bytes(lane_bytes) as f32;
                            arr[i*4..i*4+4].copy_from_slice(&v.to_le_bytes());
                        }
                        arr
                    }
                    (FloatVectorShape::F32X4, false) => {
                        let mut arr = [0u8; 16];
                        for i in 0..4 {
                            let mut lane_bytes = [0u8; 4];
                            lane_bytes.copy_from_slice(&bytes[i*4..i*4+4]);
                            let v = u32::from_le_bytes(lane_bytes) as f32;
                            arr[i*4..i*4+4].copy_from_slice(&v.to_le_bytes());
                        }
                        arr
                    }
                    _ => return Err(RuntimeError::Execution("Unsupported Convert shape".to_string())),
                }
            }
            _ => return Err(RuntimeError::Execution("Unsupported vcvtop instruction variant".to_string())),
        };
        let result = Value::V128(i128::from_le_bytes(result_bytes));
        thread.stack_mut().push_value(result);
        Ok(())
    }

    /// Executes the t2xN.vcvtop_half_t1xM_sx instruction (e.g., i16x8.trunc_sat_f32x4x2_s low/high, f32x4.convert_i16x8x2_s low/high).
    /// Pops a v128 value, selects half the lanes, converts each lane from t1 to t2 (signed/unsigned, saturating if needed), and pushes as v128.
    pub fn vcvtop_half(thread: &mut Thread, shape: crate::wasm::ast::IntVectorShape, half: crate::wasm::ast::VectorHalf, signed: bool) -> RuntimeResult<()> {
        let value = thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Execution("Expected v128 value on stack for vcvtop_half".to_string())
        })?;
        let v128 = match value {
            Value::V128(v) => v,
            _ => return Err(RuntimeError::TypeError(format!("Expected v128 for vcvtop_half, got {:?}", value))),
        };
        let bytes = v128.to_le_bytes();
        let result_bytes = match shape {
            IntVectorShape::I16X8 => {
                // i16x8.trunc_sat_f32x4x2_s/u low/high
                // 8 lanes (i16), 4 lanes (f32) per half
                let mut arr = [0u8; 16];
                let offset = match half {
                    VectorHalf::Low => 0,
                    VectorHalf::High => 4,
                };
                for i in 0..4 {
                    let mut lane_bytes = [0u8; 4];
                    lane_bytes.copy_from_slice(&bytes[(offset + i)*4..(offset + i)*4+4]);
                    let f = f32::from_le_bytes(lane_bytes);
                    let v = if signed {
                        if f.is_nan() {
                            0
                        } else if f > i16::MAX as f32 {
                            i16::MAX
                        } else if f < i16::MIN as f32 {
                            i16::MIN
                        } else {
                            f as i16
                        }
                    } else {
                        if f.is_nan() {
                            0
                        } else if f > u16::MAX as f32 {
                            u16::MAX as i16
                        } else if f < 0.0 {
                            0
                        } else {
                            f as u16 as i16
                        }
                    };
                    arr[i*2..i*2+2].copy_from_slice(&v.to_le_bytes());
                }
                // 残りの4レーンは0埋め
                for i in 4..8 {
                    arr[i*2..i*2+2].copy_from_slice(&0i16.to_le_bytes());
                }
                arr
            }
            IntVectorShape::I32X4 => {
                // i32x4.trunc_sat_f64x2x2_s/u low/high
                // 4 lanes (i32), 2 lanes (f64) per half
                let mut arr = [0u8; 16];
                let offset = match half {
                    VectorHalf::Low => 0,
                    VectorHalf::High => 2,
                };
                for i in 0..2 {
                    let mut lane_bytes = [0u8; 8];
                    lane_bytes.copy_from_slice(&bytes[(offset + i)*8..(offset + i)*8+8]);
                    let f = f64::from_le_bytes(lane_bytes);
                    let v = if signed {
                        if f.is_nan() {
                            0
                        } else if f > i32::MAX as f64 {
                            i32::MAX
                        } else if f < i32::MIN as f64 {
                            i32::MIN
                        } else {
                            f as i32
                        }
                    } else {
                        if f.is_nan() {
                            0
                        } else if f > u32::MAX as f64 {
                            u32::MAX as i32
                        } else if f < 0.0 {
                            0
                        } else {
                            f as u32 as i32
                        }
                    };
                    arr[i*4..i*4+4].copy_from_slice(&v.to_le_bytes());
                }
                // 残りの2レーンは0埋め
                for i in 2..4 {
                    arr[i*4..i*4+4].copy_from_slice(&0i32.to_le_bytes());
                }
                arr
            }
            _ => return Err(RuntimeError::Execution("Unsupported shape for vcvtop_half".to_string())),
        };
        let result = Value::V128(i128::from_le_bytes(result_bytes));
        thread.stack_mut().push_value(result);
        Ok(())
    }

    /// Executes the t2xN.vcvtop_t1xM_sx?_zero instruction (e.g., i16x8.extend_low_i8x16_s, i32x4.extend_high_i16x8_u, ...).
    /// Pops a v128 value, converts each lane from t1 to t2 (signed/unsigned), concatenates with zeros, and pushes as v128.
    pub fn vcvtop_zero(thread: &mut Thread, shape: crate::wasm::ast::IntVectorShape, half: crate::wasm::ast::VectorHalf, signed: bool) -> RuntimeResult<()> {
        let value = thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Execution("Expected v128 value on stack for vcvtop_zero".to_string())
        })?;
        let v128 = match value {
            Value::V128(v) => v,
            _ => return Err(RuntimeError::TypeError(format!("Expected v128 for vcvtop_zero, got {:?}", value))),
        };
        let bytes = v128.to_le_bytes();
        let result_bytes = match shape {
            IntVectorShape::I16X8 => {
                // i16x8.extend_low_i8x16_s/u, i16x8.extend_high_i8x16_s/u
                let mut arr = [0u8; 16];
                let offset = match half {
                    VectorHalf::Low => 0,
                    VectorHalf::High => 8,
                };
                for i in 0..8 {
                    let lane = bytes[offset + i] as u8;
                    let v = if signed {
                        (lane as i8) as i16
                    } else {
                        lane as i16
                    };
                    arr[i*2..i*2+2].copy_from_slice(&v.to_le_bytes());
                }
                arr
            }
            IntVectorShape::I32X4 => {
                // i32x4.extend_low_i16x8_s/u, i32x4.extend_high_i16x8_s/u
                let mut arr = [0u8; 16];
                let offset = match half {
                    VectorHalf::Low => 0,
                    VectorHalf::High => 4,
                };
                for i in 0..4 {
                    let mut lane_bytes = [0u8; 2];
                    lane_bytes.copy_from_slice(&bytes[(offset + i)*2..(offset + i)*2+2]);
                    let v = if signed {
                        i16::from_le_bytes(lane_bytes) as i32
                    } else {
                        u16::from_le_bytes(lane_bytes) as i32
                    };
                    arr[i*4..i*4+4].copy_from_slice(&v.to_le_bytes());
                }
                arr
            }
            IntVectorShape::I64X2 => {
                // i64x2.extend_low_i32x4_s/u, i64x2.extend_high_i32x4_s/u
                let mut arr = [0u8; 16];
                let offset = match half {
                    VectorHalf::Low => 0,
                    VectorHalf::High => 2,
                };
                for i in 0..2 {
                    let mut lane_bytes = [0u8; 4];
                    lane_bytes.copy_from_slice(&bytes[(offset + i)*4..(offset + i)*4+4]);
                    let v = if signed {
                        i32::from_le_bytes(lane_bytes) as i64
                    } else {
                        u32::from_le_bytes(lane_bytes) as i64
                    };
                    arr[i*8..i*8+8].copy_from_slice(&v.to_le_bytes());
                }
                arr
            }
            _ => return Err(RuntimeError::Execution("Unsupported shape for vcvtop_zero".to_string())),
        };
        let result = Value::V128(i128::from_le_bytes(result_bytes));
        thread.stack_mut().push_value(result);
        Ok(())
    }

    /// Executes the i32x4.dot_i16x8_s instruction.
    /// Pops two v128 values, interprets as i16x8, computes dot product pairs, and pushes as v128 (i32x4).
    pub fn dot_i16x8_s(thread: &mut Thread) -> RuntimeResult<()> {
        let val2 = thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Execution("Expected second v128 value on stack for i32x4.dot_i16x8_s".to_string())
        })?;
        let val1 = thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Execution("Expected first v128 value on stack for i32x4.dot_i16x8_s".to_string())
        })?;
        let v1 = match val1 {
            Value::V128(v) => v,
            _ => return Err(RuntimeError::TypeError(format!("Expected v128 for i32x4.dot_i16x8_s, got {:?}", val1))),
        };
        let v2 = match val2 {
            Value::V128(v) => v,
            _ => return Err(RuntimeError::TypeError(format!("Expected v128 for i32x4.dot_i16x8_s, got {:?}", val2))),
        };
        let b1 = v1.to_le_bytes();
        let b2 = v2.to_le_bytes();
        let mut i1 = [0i16; 8];
        let mut i2 = [0i16; 8];
        for i in 0..8 {
            let mut arr1 = [0u8; 2];
            let mut arr2 = [0u8; 2];
            arr1.copy_from_slice(&b1[i*2..i*2+2]);
            arr2.copy_from_slice(&b2[i*2..i*2+2]);
            i1[i] = i16::from_le_bytes(arr1);
            i2[i] = i16::from_le_bytes(arr2);
        }
        let mut k = [0i32; 8];
        for i in 0..8 {
            k[i] = i1[i] as i32 * i2[i] as i32;
        }
        let mut result = [0u8; 16];
        for j in 0..4 {
            let sum = k[j*2] + k[j*2+1];
            result[j*4..j*4+4].copy_from_slice(&sum.to_le_bytes());
        }
        let v = Value::V128(i128::from_le_bytes(result));
        thread.stack_mut().push_value(v);
        Ok(())
    }

    /// Executes the t2xN.extmul_half_t1xM_sx instruction (e.g., i16x8.extmul_low_i8x16_s, i32x4.extmul_high_i16x8_u, ...).
    /// Pops two v128 values, extracts half lanes, sign/zero extends, multiplies, and pushes as v128.
    pub fn extmul_half(thread: &mut Thread, shape: crate::wasm::ast::IntVectorShape, half: crate::wasm::ast::VectorHalf, signed: bool) -> RuntimeResult<()> {
        // Pop c2
        let val2 = thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Execution("Expected second v128 value on stack for extmul_half".to_string())
        })?;
        let v2 = match val2 {
            Value::V128(v) => v,
            _ => return Err(RuntimeError::TypeError(format!("Expected v128 for extmul_half, got {:?}", val2))),
        };
        // Pop c1
        let val1 = thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Execution("Expected first v128 value on stack for extmul_half".to_string())
        })?;
        let v1 = match val1 {
            Value::V128(v) => v,
            _ => return Err(RuntimeError::TypeError(format!("Expected v128 for extmul_half, got {:?}", val1))),
        };
        let b1 = v1.to_le_bytes();
        let b2 = v2.to_le_bytes();
        let result_bytes = match shape {
            IntVectorShape::I16X8 => {
                // i16x8.extmul_low/high_i8x16_s/u
                let mut arr = [0u8; 16];
                let offset = match half {
                    VectorHalf::Low => 0,
                    VectorHalf::High => 8,
                };
                for i in 0..8 {
                    let lane1 = b1[offset + i] as u8;
                    let lane2 = b2[offset + i] as u8;
                    let k1 = if signed { (lane1 as i8) as i16 } else { lane1 as i16 };
                    let k2 = if signed { (lane2 as i8) as i16 } else { lane2 as i16 };
                    let prod = k1.wrapping_mul(k2);
                    arr[i*2..i*2+2].copy_from_slice(&prod.to_le_bytes());
                }
                arr
            }
            IntVectorShape::I32X4 => {
                // i32x4.extmul_low/high_i16x8_s/u
                let mut arr = [0u8; 16];
                let offset = match half {
                    VectorHalf::Low => 0,
                    VectorHalf::High => 4,
                };
                for i in 0..4 {
                    let mut lane1_bytes = [0u8; 2];
                    let mut lane2_bytes = [0u8; 2];
                    lane1_bytes.copy_from_slice(&b1[(offset + i)*2..(offset + i)*2+2]);
                    lane2_bytes.copy_from_slice(&b2[(offset + i)*2..(offset + i)*2+2]);
                    let k1 = if signed { i16::from_le_bytes(lane1_bytes) as i32 } else { u16::from_le_bytes(lane1_bytes) as i32 };
                    let k2 = if signed { i16::from_le_bytes(lane2_bytes) as i32 } else { u16::from_le_bytes(lane2_bytes) as i32 };
                    let prod = k1.wrapping_mul(k2);
                    arr[i*4..i*4+4].copy_from_slice(&prod.to_le_bytes());
                }
                arr
            }
            IntVectorShape::I64X2 => {
                // i64x2.extmul_low/high_i32x4_s/u
                let mut arr = [0u8; 16];
                let offset = match half {
                    VectorHalf::Low => 0,
                    VectorHalf::High => 2,
                };
                for i in 0..2 {
                    let mut lane1_bytes = [0u8; 4];
                    let mut lane2_bytes = [0u8; 4];
                    lane1_bytes.copy_from_slice(&b1[(offset + i)*4..(offset + i)*4+4]);
                    lane2_bytes.copy_from_slice(&b2[(offset + i)*4..(offset + i)*4+4]);
                    let k1 = if signed { i32::from_le_bytes(lane1_bytes) as i64 } else { u32::from_le_bytes(lane1_bytes) as i64 };
                    let k2 = if signed { i32::from_le_bytes(lane2_bytes) as i64 } else { u32::from_le_bytes(lane2_bytes) as i64 };
                    let prod = k1.wrapping_mul(k2);
                    arr[i*8..i*8+8].copy_from_slice(&prod.to_le_bytes());
                }
                arr
            }
            _ => return Err(RuntimeError::Execution("Unsupported shape for extmul_half".to_string())),
        };
        let result = Value::V128(i128::from_le_bytes(result_bytes));
        thread.stack_mut().push_value(result);
        Ok(())
    }

    /// Executes the t2xN.extadd_pairwise_t1xM_sx instruction (e.g., i16x8.extadd_pairwise_i8x16_s, i32x4.extadd_pairwise_i16x8_u, ...).
    /// Pops a v128 value, sign/zero extends pairs, adds, and pushes as v128.
    pub fn extadd_pairwise(thread: &mut Thread, shape: crate::wasm::ast::IntVectorShape, signed: bool) -> RuntimeResult<()> {
        let value = thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Execution("Expected v128 value on stack for extadd_pairwise".to_string())
        })?;
        let v128 = match value {
            Value::V128(v) => v,
            _ => return Err(RuntimeError::TypeError(format!("Expected v128 for extadd_pairwise, got {:?}", value))),
        };
        let bytes = v128.to_le_bytes();
        let result_bytes = match shape {
            IntVectorShape::I16X8 => {
                // i16x8.extadd_pairwise_i8x16_s/u
                let mut arr = [0u8; 16];
                for i in 0..8 {
                    let lane1 = bytes[i*2] as u8;
                    let lane2 = bytes[i*2+1] as u8;
                    let k1 = if signed { (lane1 as i8) as i16 } else { lane1 as i16 };
                    let k2 = if signed { (lane2 as i8) as i16 } else { lane2 as i16 };
                    let sum = k1.wrapping_add(k2);
                    arr[i*2..i*2+2].copy_from_slice(&sum.to_le_bytes());
                }
                arr
            }
            IntVectorShape::I32X4 => {
                // i32x4.extadd_pairwise_i16x8_s/u
                let mut arr = [0u8; 16];
                for i in 0..4 {
                    let mut lane1_bytes = [0u8; 2];
                    let mut lane2_bytes = [0u8; 2];
                    lane1_bytes.copy_from_slice(&bytes[i*4..i*4+2]);
                    lane2_bytes.copy_from_slice(&bytes[i*4+2..i*4+4]);
                    let k1 = if signed { i16::from_le_bytes(lane1_bytes) as i32 } else { u16::from_le_bytes(lane1_bytes) as i32 };
                    let k2 = if signed { i16::from_le_bytes(lane2_bytes) as i32 } else { u16::from_le_bytes(lane2_bytes) as i32 };
                    let sum = k1.wrapping_add(k2);
                    arr[i*4..i*4+4].copy_from_slice(&sum.to_le_bytes());
                }
                arr
            }
            IntVectorShape::I64X2 => {
                // i64x2.extadd_pairwise_i32x4_s/u
                let mut arr = [0u8; 16];
                for i in 0..2 {
                    let mut lane1_bytes = [0u8; 4];
                    let mut lane2_bytes = [0u8; 4];
                    lane1_bytes.copy_from_slice(&bytes[i*8..i*8+4]);
                    lane2_bytes.copy_from_slice(&bytes[i*8+4..i*8+8]);
                    let k1 = if signed { i32::from_le_bytes(lane1_bytes) as i64 } else { u32::from_le_bytes(lane1_bytes) as i64 };
                    let k2 = if signed { i32::from_le_bytes(lane2_bytes) as i64 } else { u32::from_le_bytes(lane2_bytes) as i64 };
                    let sum = k1.wrapping_add(k2);
                    arr[i*8..i*8+8].copy_from_slice(&sum.to_le_bytes());
                }
                arr
            }
            _ => return Err(RuntimeError::Execution("Unsupported shape for extadd_pairwise".to_string())),
        };
        let result = Value::V128(i128::from_le_bytes(result_bytes));
        thread.stack_mut().push_value(result);
        Ok(())
    }

    /// Executes the v128.load𝑀x𝑁_sx instruction.
    /// 
    /// Loads M-bit integers from memory, extends them to W-bit integers (W = M * 2),
    /// and packs them into a 128-bit vector.
    /// 
    /// # Arguments
    /// 
    /// * `store` - The current store state
    /// * `thread` - The current thread state
    /// * `memarg` - The memory argument containing offset and alignment
    /// * `m` - The bit width of each integer to load (8, 16, or 32)
    /// * `n` - The number of integers to load (8, 4, or 2)
    /// * `signed` - Whether to sign-extend the loaded integers
    /// 
    /// # Returns
    /// 
    /// * `RuntimeResult<()>` - The result of the execution
    pub fn v128_load_mxn_sx(
        store: &Store,
        thread: &mut Thread,
        memarg: &crate::wasm::ast::MemArg,
        m: u8,
        n: u8,
        signed: bool,
    ) -> RuntimeResult<()> {
        // Get the current frame
        let frame = thread.frame_state();
        
        // Get the memory address from the module
        let mem_addr = frame.module().mem_addrs.get(0).ok_or_else(|| {
            RuntimeError::Execution("v128.load: Memory index 0 does not exist in current module".to_string())
        })?;

        // Get the memory instance from the store
        let mem = store.mems.get(mem_addr.as_usize()).ok_or_else(|| {
            RuntimeError::Execution("v128.load: Memory address does not exist in store".to_string())
        })?;

        // Pop the i32 address from the stack
        let addr = match thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Stack("No value on stack for v128.load".to_string())
        })? {
            Value::I32(i) => i as usize,
            _ => return Err(RuntimeError::TypeError("Expected i32 address for v128.load".to_string())),
        };

        // Calculate the effective address
        let ea = addr.checked_add(memarg.offset as usize).ok_or_else(|| {
            RuntimeError::Execution("v128.load: Address overflow".to_string())
        })?;

        // Calculate the total number of bytes to read
        let total_bytes = (m as usize * n as usize) / 8;
        if ea + total_bytes > mem.size() as usize {
            return Err(RuntimeError::Execution(format!(
                "v128.load: Memory access out of bounds (address: {}, size: {})",
                ea, mem.size()
            )));
        }

        // Read the bytes from memory
        let mut result_bytes = [0u8; 16];
        for i in 0..n as usize {
            let start = ea + (i * m as usize / 8);
            let end = start + m as usize / 8;
            let bytes = mem.read_bytes(start, m as usize / 8).map_err(|e| {
                RuntimeError::Memory(format!("v128.load: {}", e))
            })?;
            
            // Convert the bytes to a wider integer type and store in a fixed-size array
            let mut extended_bytes = [0u8; 8]; // Use a fixed-size array for all cases
            match (m, signed) {
                (8, true) => {
                    let v = i8::from_le_bytes([bytes[0]]) as i16;
                    extended_bytes[0..2].copy_from_slice(&v.to_le_bytes());
                }
                (8, false) => {
                    let v = bytes[0] as u16;
                    extended_bytes[0..2].copy_from_slice(&v.to_le_bytes());
                }
                (16, true) => {
                    let v = i16::from_le_bytes([bytes[0], bytes[1]]) as i32;
                    extended_bytes[0..4].copy_from_slice(&v.to_le_bytes());
                }
                (16, false) => {
                    let v = u16::from_le_bytes([bytes[0], bytes[1]]) as u32;
                    extended_bytes[0..4].copy_from_slice(&v.to_le_bytes());
                }
                (32, true) => {
                    let v = i32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]) as i64;
                    extended_bytes[0..8].copy_from_slice(&v.to_le_bytes());
                }
                (32, false) => {
                    let v = u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]) as u64;
                    extended_bytes[0..8].copy_from_slice(&v.to_le_bytes());
                }
                _ => return Err(RuntimeError::Execution(format!(
                    "v128.load: Unsupported bit width {}",
                    m
                ))),
            }

            // Copy the extended value to the result
            let w = m * 2; // W = M * 2
            let start = i * w as usize / 8;
            let end = start + w as usize / 8;
            result_bytes[start..end].copy_from_slice(&extended_bytes[..w as usize / 8]);
        }

        // Push the result onto the stack
        let result = Value::V128(i128::from_le_bytes(result_bytes));
        thread.stack_mut().push_value(result);

        Ok(())
    }

    /// Executes the v128.load𝑁_splat instruction.
    /// 
    /// Loads an N-bit integer from memory and splats it to all lanes of a 128-bit vector.
    /// 
    /// # Arguments
    /// 
    /// * `store` - The current store state
    /// * `thread` - The current thread state
    /// * `memarg` - The memory argument containing offset and alignment
    /// * `n` - The bit width of the integer to load (8, 16, 32, or 64)
    /// 
    /// # Returns
    /// 
    /// * `RuntimeResult<()>` - The result of the execution
    pub fn v128_load_n_splat(
        store: &Store,
        thread: &mut Thread,
        memarg: &crate::wasm::ast::MemArg,
        n: u8,
    ) -> RuntimeResult<()> {
        // Get the current frame
        let frame = thread.frame_state();
        
        // Get the memory address from the module
        let mem_addr = frame.module().mem_addrs.get(0).ok_or_else(|| {
            RuntimeError::Execution("v128.load: Memory index 0 does not exist in current module".to_string())
        })?;

        // Get the memory instance from the store
        let mem = store.mems.get(mem_addr.as_usize()).ok_or_else(|| {
            RuntimeError::Execution("v128.load: Memory address does not exist in store".to_string())
        })?;

        // Pop the i32 address from the stack
        let addr = match thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Stack("No value on stack for v128.load".to_string())
        })? {
            Value::I32(i) => i as usize,
            _ => return Err(RuntimeError::TypeError("Expected i32 address for v128.load".to_string())),
        };

        // Calculate the effective address
        let ea = addr.checked_add(memarg.offset as usize).ok_or_else(|| {
            RuntimeError::Execution("v128.load: Address overflow".to_string())
        })?;

        // Calculate the number of bytes to read
        let bytes_to_read = n as usize / 8;
        if ea + bytes_to_read > mem.size() as usize {
            return Err(RuntimeError::Execution(format!(
                "v128.load: Memory access out of bounds (address: {}, size: {})",
                ea, mem.size()
            )));
        }

        // Read the bytes from memory
        let bytes = mem.read_bytes(ea, bytes_to_read).map_err(|e| {
            RuntimeError::Memory(format!("v128.load: {}", e))
        })?;

        // Convert the bytes to an integer and create the splat vector
        let mut result_bytes = [0u8; 16];
        match n {
            8 => {
                let value = bytes[0] as u8;
                // Splat to all 16 lanes
                for i in 0..16 {
                    result_bytes[i] = value;
                }
            }
            16 => {
                let value = u16::from_le_bytes([bytes[0], bytes[1]]);
                // Splat to all 8 lanes
                for i in 0..8 {
                    result_bytes[i*2..i*2+2].copy_from_slice(&value.to_le_bytes());
                }
            }
            32 => {
                let value = u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
                // Splat to all 4 lanes
                for i in 0..4 {
                    result_bytes[i*4..i*4+4].copy_from_slice(&value.to_le_bytes());
                }
            }
            64 => {
                let value = u64::from_le_bytes([
                    bytes[0], bytes[1], bytes[2], bytes[3],
                    bytes[4], bytes[5], bytes[6], bytes[7]
                ]);
                // Splat to all 2 lanes
                for i in 0..2 {
                    result_bytes[i*8..i*8+8].copy_from_slice(&value.to_le_bytes());
                }
            }
            _ => return Err(RuntimeError::Execution(format!(
                "v128.load: Unsupported bit width {}",
                n
            ))),
        }

        // Push the result onto the stack
        let result = Value::V128(i128::from_le_bytes(result_bytes));
        thread.stack_mut().push_value(result);

        Ok(())
    }

    /// Executes the v128.load𝑁_zero instruction.
    /// 
    /// Loads an N-bit integer from memory and zero-extends it to a 128-bit vector.
    /// 
    /// # Arguments
    /// 
    /// * `store` - The current store state
    /// * `thread` - The current thread state
    /// * `memarg` - The memory argument containing offset and alignment
    /// * `n` - The bit width of the integer to load (32 or 64)
    /// 
    /// # Returns
    /// 
    /// * `RuntimeResult<()>` - The result of the execution
    pub fn v128_load_n_zero(
        store: &Store,
        thread: &mut Thread,
        memarg: &crate::wasm::ast::MemArg,
        n: u8,
    ) -> RuntimeResult<()> {
        // Get the current frame
        let frame = thread.frame_state();
        
        // Get the memory address from the module
        let mem_addr = frame.module().mem_addrs.get(0).ok_or_else(|| {
            RuntimeError::Execution("v128.load: Memory index 0 does not exist in current module".to_string())
        })?;

        // Get the memory instance from the store
        let mem = store.mems.get(mem_addr.as_usize()).ok_or_else(|| {
            RuntimeError::Execution("v128.load: Memory address does not exist in store".to_string())
        })?;

        // Pop the i32 address from the stack
        let addr = match thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Stack("No value on stack for v128.load".to_string())
        })? {
            Value::I32(i) => i as usize,
            _ => return Err(RuntimeError::TypeError("Expected i32 address for v128.load".to_string())),
        };

        // Calculate the effective address
        let ea = addr.checked_add(memarg.offset as usize).ok_or_else(|| {
            RuntimeError::Execution("v128.load: Address overflow".to_string())
        })?;

        // Calculate the number of bytes to read
        let bytes_to_read = n as usize / 8;
        if ea + bytes_to_read > mem.size() as usize {
            return Err(RuntimeError::Execution(format!(
                "v128.load: Memory access out of bounds (address: {}, size: {})",
                ea, mem.size()
            )));
        }

        // Read the bytes from memory
        let bytes = mem.read_bytes(ea, bytes_to_read).map_err(|e| {
            RuntimeError::Memory(format!("v128.load: {}", e))
        })?;

        // Convert the bytes to an integer and zero-extend to 128 bits
        let mut result_bytes = [0u8; 16];
        match n {
            32 => {
                let value = u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
                // Zero-extend to 128 bits (place in the lower 32 bits)
                result_bytes[0..4].copy_from_slice(&value.to_le_bytes());
                // Upper 96 bits remain zero
            }
            64 => {
                let value = u64::from_le_bytes([
                    bytes[0], bytes[1], bytes[2], bytes[3],
                    bytes[4], bytes[5], bytes[6], bytes[7]
                ]);
                // Zero-extend to 128 bits (place in the lower 64 bits)
                result_bytes[0..8].copy_from_slice(&value.to_le_bytes());
                // Upper 64 bits remain zero
            }
            _ => return Err(RuntimeError::Execution(format!(
                "v128.load: Unsupported bit width {} for zero extension",
                n
            ))),
        }

        // Push the result onto the stack
        let result = Value::V128(i128::from_le_bytes(result_bytes));
        thread.stack_mut().push_value(result);

        Ok(())
    }

    /// Executes the v128.load𝑁_lane instruction.
    /// 
    /// Loads an N-bit integer from memory and replaces a specific lane in a 128-bit vector.
    /// 
    /// # Arguments
    /// 
    /// * `store` - The current store state
    /// * `thread` - The current thread state
    /// * `memarg` - The memory argument containing offset and alignment
    /// * `n` - The bit width of the integer to load (8, 16, 32, or 64)
    /// * `lane` - The lane index to replace
    /// 
    /// # Returns
    /// 
    /// * `RuntimeResult<()>` - The result of the execution
    pub fn v128_load_n_lane(
        store: &Store,
        thread: &mut Thread,
        memarg: &crate::wasm::ast::MemArg,
        n: u8,
        lane: u8,
    ) -> RuntimeResult<()> {
        // Get the current frame
        let frame = thread.frame_state();
        
        // Get the memory address from the module
        let mem_addr = frame.module().mem_addrs.get(0).ok_or_else(|| {
            RuntimeError::Execution("v128.load: Memory index 0 does not exist in current module".to_string())
        })?;

        // Get the memory instance from the store
        let mem = store.mems.get(mem_addr.as_usize()).ok_or_else(|| {
            RuntimeError::Execution("v128.load: Memory address does not exist in store".to_string())
        })?;

        // Pop the v128 vector from the stack
        let vector = match thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Stack("No value on stack for v128.load".to_string())
        })? {
            Value::V128(v) => v,
            _ => return Err(RuntimeError::TypeError("Expected v128 vector for v128.load".to_string())),
        };

        // Pop the i32 address from the stack
        let addr = match thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Stack("No value on stack for v128.load".to_string())
        })? {
            Value::I32(i) => i as usize,
            _ => return Err(RuntimeError::TypeError("Expected i32 address for v128.load".to_string())),
        };

        // Calculate the effective address
        let ea = addr.checked_add(memarg.offset as usize).ok_or_else(|| {
            RuntimeError::Execution("v128.load: Address overflow".to_string())
        })?;

        // Calculate the number of bytes to read
        let bytes_to_read = n as usize / 8;
        if ea + bytes_to_read > mem.size() as usize {
            return Err(RuntimeError::Execution(format!(
                "v128.load: Memory access out of bounds (address: {}, size: {})",
                ea, mem.size()
            )));
        }

        // Read the bytes from memory
        let bytes = mem.read_bytes(ea, bytes_to_read).map_err(|e| {
            RuntimeError::Memory(format!("v128.load: {}", e))
        })?;

        // Convert the bytes to an integer
        let value = match n {
            8 => bytes[0] as u64,
            16 => u16::from_le_bytes([bytes[0], bytes[1]]) as u64,
            32 => u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]) as u64,
            64 => u64::from_le_bytes([
                bytes[0], bytes[1], bytes[2], bytes[3],
                bytes[4], bytes[5], bytes[6], bytes[7]
            ]),
            _ => return Err(RuntimeError::Execution(format!(
                "v128.load: Unsupported bit width {}",
                n
            ))),
        };

        // Calculate the number of lanes
        let num_lanes = 128 / n as usize;
        if lane as usize >= num_lanes {
            return Err(RuntimeError::Execution(format!(
                "v128.load: Lane index {} out of range (max: {})",
                lane, num_lanes - 1
            )));
        }

        // Convert the vector to bytes and replace the specified lane
        let mut result_bytes = vector.to_le_bytes();
        match n {
            8 => {
                result_bytes[lane as usize] = value as u8;
            }
            16 => {
                let start = lane as usize * 2;
                result_bytes[start..start + 2].copy_from_slice(&(value as u16).to_le_bytes());
            }
            32 => {
                let start = lane as usize * 4;
                result_bytes[start..start + 4].copy_from_slice(&(value as u32).to_le_bytes());
            }
            64 => {
                let start = lane as usize * 8;
                result_bytes[start..start + 8].copy_from_slice(&(value as u64).to_le_bytes());
            }
            _ => unreachable!(), // Already checked above
        }

        // Push the result onto the stack
        let result = Value::V128(i128::from_le_bytes(result_bytes));
        thread.stack_mut().push_value(result);

        Ok(())
    }

    /// Executes the v128.store𝑁_lane instruction.
    /// 
    /// Stores an N-bit integer from a specific lane of a 128-bit vector to memory.
    /// 
    /// # Arguments
    /// 
    /// * `store` - The current store state
    /// * `thread` - The current thread state
    /// * `memarg` - The memory argument containing offset and alignment
    /// * `n` - The bit width of the integer to store (8, 16, 32, or 64)
    /// * `lane` - The lane index to extract
    /// 
    /// # Returns
    /// 
    /// * `RuntimeResult<()>` - The result of the execution
    /// 
    /// # Specification
    /// 
    /// 1. Let 𝐹 be the current frame.
    /// 2. Assert: due to validation, 𝐹.module.memaddrs[0] exists.
    /// 3. Let 𝑎 be the memory address 𝐹.module.memaddrs[0].
    /// 4. Assert: due to validation, 𝑆.mems[𝑎] exists.
    /// 5. Let mem be the memory instance 𝑆.mems[𝑎].
    /// 6. Assert: due to validation, a value of value type v128 is on the top of the stack.
    /// 7. Pop the value v128.const 𝑐 from the stack.
    /// 8. Assert: due to validation, a value of value type i32 is on the top of the stack.
    /// 9. Pop the value i32.const 𝑖 from the stack.
    /// 10. Let ea be the integer 𝑖 + memarg.offset.
    /// 11. If ea + 𝑁/8 is larger than the length of mem.data, then:
    ///     a. Trap.
    /// 12. Let 𝐿 be 128/𝑁.
    /// 13. Let 𝑗* be the result of computing lanesi𝑁x𝐿(𝑐).
    /// 14. Let 𝑏* be the result of computing bytesi𝑁(𝑗*[𝑥]).
    /// 15. Replace the bytes mem.data[ea : 𝑁/8] with 𝑏*.
    pub fn v128_store_n_lane(
        store: &mut Store,
        thread: &mut Thread,
        memarg: &crate::wasm::ast::MemArg,
        n: u8,
        lane: u8,
    ) -> RuntimeResult<()> {
        // Get the current frame
        let frame = thread.frame_state();
        
        // Get the memory address from the module
        let mem_addr = frame.module().mem_addrs.get(0).ok_or_else(|| {
            RuntimeError::Execution("v128.store: Memory index 0 does not exist in current module".to_string())
        })?;

        // Get the memory instance from the store
        let mem = store.mems.get_mut(mem_addr.as_usize()).ok_or_else(|| {
            RuntimeError::Execution("v128.store: Memory address does not exist in store".to_string())
        })?;

        // Pop the v128 vector from the stack
        let vector = match thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Stack("No value on stack for v128.store".to_string())
        })? {
            Value::V128(v) => v,
            _ => return Err(RuntimeError::TypeError("Expected v128 vector for v128.store".to_string())),
        };

        // Pop the i32 address from the stack
        let addr = match thread.stack_mut().pop_value().ok_or_else(|| {
            RuntimeError::Stack("No address on stack for v128.store".to_string())
        })? {
            Value::I32(i) => i as usize,
            _ => return Err(RuntimeError::TypeError("Expected i32 address for v128.store".to_string())),
        };

        // Calculate the effective address
        let ea = addr.checked_add(memarg.offset as usize).ok_or_else(|| {
            RuntimeError::Execution("v128.store: Address overflow".to_string())
        })?;

        // Calculate the number of bytes to write
        let bytes_to_write = n as usize / 8;
        if ea + bytes_to_write > mem.size_bytes() {
            return Err(RuntimeError::Execution(format!(
                "v128.store: Memory access out of bounds (address: {}, size: {})",
                ea, mem.size_bytes()
            )));
        }

        // Calculate the number of lanes (L = 128/N)
        let num_lanes = 128 / n as usize;
        if lane as usize >= num_lanes {
            return Err(RuntimeError::Execution(format!(
                "v128.store: Lane index {} out of range (max: {})",
                lane, num_lanes - 1
            )));
        }

        // Extract the specified lane from the vector (lanesi𝑁x𝐿(𝑐)[𝑥])
        let vector_bytes = vector.to_le_bytes();
        let lane_value = match n {
            8 => {
                // Extract 8-bit lane
                vector_bytes[lane as usize] as u64
            }
            16 => {
                // Extract 16-bit lane
                let start = lane as usize * 2;
                u16::from_le_bytes([vector_bytes[start], vector_bytes[start + 1]]) as u64
            }
            32 => {
                // Extract 32-bit lane
                let start = lane as usize * 4;
                u32::from_le_bytes([
                    vector_bytes[start],
                    vector_bytes[start + 1],
                    vector_bytes[start + 2],
                    vector_bytes[start + 3]
                ]) as u64
            }
            64 => {
                // Extract 64-bit lane
                let start = lane as usize * 8;
                u64::from_le_bytes([
                    vector_bytes[start],
                    vector_bytes[start + 1],
                    vector_bytes[start + 2],
                    vector_bytes[start + 3],
                    vector_bytes[start + 4],
                    vector_bytes[start + 5],
                    vector_bytes[start + 6],
                    vector_bytes[start + 7]
                ])
            }
            _ => return Err(RuntimeError::Execution(format!(
                "v128.store: Unsupported bit width {}",
                n
            ))),
        };

        // Convert the lane value to bytes (bytesi𝑁(𝑗*[𝑥]))
        let bytes_to_store = match n {
            8 => {
                let mut bytes = [0u8; 1];
                bytes[0] = lane_value as u8;
                bytes.to_vec()
            }
            16 => {
                let bytes = (lane_value as u16).to_le_bytes();
                bytes.to_vec()
            }
            32 => {
                let bytes = (lane_value as u32).to_le_bytes();
                bytes.to_vec()
            }
            64 => {
                let bytes = lane_value.to_le_bytes();
                bytes.to_vec()
            }
            _ => unreachable!(), // Already checked above
        };

        // Write the bytes to memory
        mem.write_bytes(ea, &bytes_to_store).map_err(|e| {
            RuntimeError::Memory(format!("v128.store: {}", e))
        })?;

        Ok(())
    }
}

/// Executes a vector instruction
/// 
/// # Arguments
/// 
/// * `store` - The current store state
/// * `thread` - The current thread state
/// * `instruction` - The vector instruction to execute
/// 
/// # Returns
/// 
/// * `RuntimeResult<()>` - The result of the execution
pub fn execute_vector(
    store: &mut Store,
    thread: &mut Thread,
    instruction: &Instruction,
) -> RuntimeResult<()> {
    match instruction {
        Instruction::Vector(vector_instr) => {
            match vector_instr {
                VectorInstruction::V128Const(value) => {
                    // Push the constant value onto the stack
                    thread.stack_mut().push_value(Value::V128(*value));
                    Ok(())
                }
                VectorInstruction::V128VUnOp(op) => {
                    Vector::vvunop(thread, *op)
                        .map_err(|e| RuntimeError::Execution(e.to_string()))
                }
                VectorInstruction::V128VBinOp(op) => {
                    Vector::vvbinop(thread, *op)
                        .map_err(|e| RuntimeError::Execution(e.to_string()))
                }
                VectorInstruction::V128VTestOp(test_op) => {
                    match test_op {
                        crate::wasm::ast::VectorVTestOp::AnyTrue => {
                            Vector::any_true(thread)
                                .map_err(|e| RuntimeError::Execution(e.to_string()))
                        }
                    }
                }
                VectorInstruction::I8X16Swizzle => {
                    Vector::i8x16_swizzle(thread)
                        .map_err(|e| RuntimeError::Execution(e.to_string()))
                }
                VectorInstruction::I8X16Shuffle(lanes) => {
                    Vector::i8x16_shuffle(thread, *lanes)
                        .map_err(|e| RuntimeError::Execution(e.to_string()))
                }
                VectorInstruction::Splat(shape) => {
                    Vector::splat(thread, *shape)
                        .map_err(|e| RuntimeError::Execution(e.to_string()))
                }
                VectorInstruction::ExtractLane { shape, lane, signed } => {
                    Vector::extract_lane(thread, *shape, *lane, *signed)
                        .map_err(|e| RuntimeError::Execution(e.to_string()))
                }
                VectorInstruction::IntUnOp { shape, op } => {
                    match op {
                        VectorIntUnOp::Abs => {
                            // TODO: Implement abs for integer vectors
                            Err(RuntimeError::Execution("Integer vector abs not implemented".to_string()))
                        }
                        VectorIntUnOp::Neg => {
                            // TODO: Implement neg for integer vectors
                            Err(RuntimeError::Execution("Integer vector neg not implemented".to_string()))
                        }
                    }
                }
                VectorInstruction::FloatUnOp { shape, op } => {
                    match op {
                        VectorFloatUnOp::Abs => {
                            // TODO: Implement abs for float vectors
                            Err(RuntimeError::Execution("Float vector abs not implemented".to_string()))
                        }
                        VectorFloatUnOp::Neg => {
                            // TODO: Implement neg for float vectors
                            Err(RuntimeError::Execution("Float vector neg not implemented".to_string()))
                        }
                        VectorFloatUnOp::Sqrt => {
                            // TODO: Implement sqrt for float vectors
                            Err(RuntimeError::Execution("Float vector sqrt not implemented".to_string()))
                        }
                        VectorFloatUnOp::Ceil => {
                            // TODO: Implement ceil for float vectors
                            Err(RuntimeError::Execution("Float vector ceil not implemented".to_string()))
                        }
                        VectorFloatUnOp::Floor => {
                            // TODO: Implement floor for float vectors
                            Err(RuntimeError::Execution("Float vector floor not implemented".to_string()))
                        }
                        VectorFloatUnOp::Trunc => {
                            // TODO: Implement trunc for float vectors
                            Err(RuntimeError::Execution("Float vector trunc not implemented".to_string()))
                        }
                        VectorFloatUnOp::Nearest => {
                            // TODO: Implement nearest for float vectors
                            Err(RuntimeError::Execution("Float vector nearest not implemented".to_string()))
                        }
                    }
                        .map_err(|e| RuntimeError::Execution(e.to_string()))
                }
                VectorInstruction::IntBinOp { shape, op } => {
                    Vector::vbinop(thread, VectorShape::Int(*shape), vector_instr)
                        .map_err(|e| RuntimeError::Execution(e.to_string()))
                }
                VectorInstruction::FloatBinOp { shape, op } => {
                    Vector::vbinop(thread, VectorShape::Float(*shape), vector_instr)
                        .map_err(|e| RuntimeError::Execution(e.to_string()))
                }
                VectorInstruction::IntRelOp { shape, op } => {
                    Vector::vrelop(thread, vector_instr)
                        .map_err(|e| RuntimeError::Execution(e.to_string()))
                }
                VectorInstruction::FloatRelOp { shape, op } => {
                    Vector::vrelop(thread, vector_instr)
                        .map_err(|e| RuntimeError::Execution(e.to_string()))
                }
                VectorInstruction::IntShiftOp { shape, op } => {
                    Vector::vishiftop(thread, vector_instr)
                        .map_err(|e| RuntimeError::Execution(e.to_string()))
                }
                VectorInstruction::IntTestOp { shape, op } => {
                    match op {
                        crate::wasm::ast::VectorIntTestOp::AllTrue => {
                            Vector::all_true(thread, *shape)
                                .map_err(|e| RuntimeError::Execution(e.to_string()))
                        }
                    }
                }
                VectorInstruction::Bitmask(shape) => {
                    Vector::bitmask(thread, *shape)
                        .map_err(|e| RuntimeError::Execution(e.to_string()))
                }
                VectorInstruction::Narrow { shape, signed } => {
                    Vector::narrow(thread, *shape, *signed)
                        .map_err(|e| RuntimeError::Execution(e.to_string()))
                }
                VectorInstruction::TruncSat { shape, signed } => {
                    Vector::vcvtop(thread, vector_instr)
                        .map_err(|e| RuntimeError::Execution(e.to_string()))
                }
                VectorInstruction::Convert { shape, signed } => {
                    Vector::vcvtop(thread, vector_instr)
                        .map_err(|e| RuntimeError::Execution(e.to_string()))
                }
                VectorInstruction::ExtMulHalf { shape, half, signed } => {
                    Vector::extmul_half(thread, *shape, *half, *signed)
                        .map_err(|e| RuntimeError::Execution(e.to_string()))
                }
                VectorInstruction::ExtendHalf { shape, half, signed } => {
                    Vector::vcvtop_zero(thread, *shape, *half, *signed)
                        .map_err(|e| RuntimeError::Execution(e.to_string()))
                }
                VectorInstruction::I32X4DotI16X8S => {
                    Vector::dot_i16x8_s(thread)
                        .map_err(|e| RuntimeError::Execution(e.to_string()))
                }
                VectorInstruction::ExtAddPairwise { shape, signed } => {
                    Vector::extadd_pairwise(thread, *shape, *signed)
                        .map_err(|e| RuntimeError::Execution(e.to_string()))
                }
                VectorInstruction::V128Load8x8S { memarg } => {
                    Vector::v128_load_mxn_sx(store, thread, memarg, 8, 8, true)
                        .map_err(|e| RuntimeError::Execution(e.to_string()))
                }
                VectorInstruction::V128Load8x8U { memarg } => {
                    Vector::v128_load_mxn_sx(store, thread, memarg, 8, 8, false)
                        .map_err(|e| RuntimeError::Execution(e.to_string()))
                }
                VectorInstruction::V128Load16x4S { memarg } => {
                    Vector::v128_load_mxn_sx(store, thread, memarg, 16, 4, true)
                        .map_err(|e| RuntimeError::Execution(e.to_string()))
                }
                VectorInstruction::V128Load16x4U { memarg } => {
                    Vector::v128_load_mxn_sx(store, thread, memarg, 16, 4, false)
                        .map_err(|e| RuntimeError::Execution(e.to_string()))
                }
                VectorInstruction::V128Load32x2S { memarg } => {
                    Vector::v128_load_mxn_sx(store, thread, memarg, 32, 2, true)
                        .map_err(|e| RuntimeError::Execution(e.to_string()))
                }
                VectorInstruction::V128Load32x2U { memarg } => {
                    Vector::v128_load_mxn_sx(store, thread, memarg, 32, 2, false)
                        .map_err(|e| RuntimeError::Execution(e.to_string()))
                }
                VectorInstruction::V128Load8Splat { memarg } => {
                    Vector::v128_load_n_splat(store, thread, memarg, 8)
                        .map_err(|e| RuntimeError::Execution(e.to_string()))
                }
                VectorInstruction::V128Load16Splat { memarg } => {
                    Vector::v128_load_n_splat(store, thread, memarg, 16)
                        .map_err(|e| RuntimeError::Execution(e.to_string()))
                }
                VectorInstruction::V128Load32Splat { memarg } => {
                    Vector::v128_load_n_splat(store, thread, memarg, 32)
                        .map_err(|e| RuntimeError::Execution(e.to_string()))
                }
                VectorInstruction::V128Load64Splat { memarg } => {
                    Vector::v128_load_n_splat(store, thread, memarg, 64)
                        .map_err(|e| RuntimeError::Execution(e.to_string()))
                }
                VectorInstruction::V128Load32Zero { memarg } => {
                    Vector::v128_load_n_zero(store, thread, memarg, 32)
                        .map_err(|e| RuntimeError::Execution(e.to_string()))
                }
                VectorInstruction::V128Load64Zero { memarg } => {
                    Vector::v128_load_n_zero(store, thread, memarg, 64)
                        .map_err(|e| RuntimeError::Execution(e.to_string()))
                }
                VectorInstruction::V128Load8Lane { memarg, lane } => {
                    Vector::v128_load_n_lane(store, thread, memarg, 8, *lane)
                        .map_err(|e| RuntimeError::Execution(e.to_string()))
                }
                VectorInstruction::V128Load16Lane { memarg, lane } => {
                    Vector::v128_load_n_lane(store, thread, memarg, 16, *lane)
                        .map_err(|e| RuntimeError::Execution(e.to_string()))
                }
                VectorInstruction::V128Load32Lane { memarg, lane } => {
                    Vector::v128_load_n_lane(store, thread, memarg, 32, *lane)
                        .map_err(|e| RuntimeError::Execution(e.to_string()))
                }
                VectorInstruction::V128Load64Lane { memarg, lane } => {
                    Vector::v128_load_n_lane(store, thread, memarg, 64, *lane)
                        .map_err(|e| RuntimeError::Execution(e.to_string()))
                }
                VectorInstruction::V128Store8Lane { memarg, lane } => {
                    Vector::v128_store_n_lane(store, thread, memarg, 8, *lane)
                        .map_err(|e| RuntimeError::Execution(e.to_string()))
                }
                VectorInstruction::V128Store16Lane { memarg, lane } => {
                    Vector::v128_store_n_lane(store, thread, memarg, 16, *lane)
                        .map_err(|e| RuntimeError::Execution(e.to_string()))
                }
                VectorInstruction::V128Store32Lane { memarg, lane } => {
                    Vector::v128_store_n_lane(store, thread, memarg, 32, *lane)
                        .map_err(|e| RuntimeError::Execution(e.to_string()))
                }
                VectorInstruction::V128Store64Lane { memarg, lane } => {
                    Vector::v128_store_n_lane(store, thread, memarg, 64, *lane)
                        .map_err(|e| RuntimeError::Execution(e.to_string()))
                }
                // TODO: Implement other vector instructions
                _ => Err(RuntimeError::Execution(format!(
                    "Unimplemented vector instruction: {:?}",
                    vector_instr
                ))),
            }
        }
        _ => Err(RuntimeError::Execution(format!(
            "Expected vector instruction, got: {:?}",
            instruction
        ))),
    }
} 
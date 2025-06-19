use crate::wasm::ast::ValType;
use alloc::string::String;
use core::fmt;

/// WebAssembly value types
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ValueType {
    I32,
    I64,
    F32,
    F64,
    V128,
    FuncRef,
    ExternRef,
}

impl ValueType {
    /// Converts from ast::ValType to ValueType
    pub fn from_val_type(val_type: ValType) -> Self {
        match val_type {
            ValType::I32 => ValueType::I32,
            ValType::I64 => ValueType::I64,
            ValType::F32 => ValueType::F32,
            ValType::F64 => ValueType::F64,
            ValType::V128 => ValueType::V128,
            ValType::FuncRef => ValueType::FuncRef,
            ValType::ExternRef => ValueType::ExternRef,
        }
    }

    /// Converts to ast::ValType
    pub fn to_val_type(&self) -> ValType {
        match self {
            ValueType::I32 => ValType::I32,
            ValueType::I64 => ValType::I64,
            ValueType::F32 => ValType::F32,
            ValueType::F64 => ValType::F64,
            ValueType::V128 => ValType::V128,
            ValueType::FuncRef => ValType::FuncRef,
            ValueType::ExternRef => ValType::ExternRef,
        }
    }

    /// Returns true if this is a reference type
    pub fn is_reference(&self) -> bool {
        matches!(self, ValueType::FuncRef | ValueType::ExternRef)
    }

    /// Returns the default value for this type
    pub fn default_value(&self) -> Value {
        match self {
            ValueType::I32 => Value::I32(0),
            ValueType::I64 => Value::I64(0),
            ValueType::F32 => Value::F32(0.0),
            ValueType::F64 => Value::F64(0.0),
            ValueType::V128 => Value::V128(0),
            ValueType::FuncRef => Value::NullRef(ValueType::FuncRef),
            ValueType::ExternRef => Value::NullRef(ValueType::ExternRef),
        }
    }
}

impl From<ValType> for ValueType {
    fn from(val_type: ValType) -> Self {
        match val_type {
            ValType::I32 => ValueType::I32,
            ValType::I64 => ValueType::I64,
            ValType::F32 => ValueType::F32,
            ValType::F64 => ValueType::F64,
            ValType::V128 => ValueType::V128,
            ValType::FuncRef => ValueType::FuncRef,
            ValType::ExternRef => ValueType::ExternRef,
        }
    }
}

/// WebAssembly values
#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    /// 32-bit integer
    I32(i32),
    /// 64-bit integer
    I64(i64),
    /// 32-bit float
    F32(f32),
    /// 64-bit float
    F64(f64),
    /// 128-bit vector
    V128(i128),
    /// Function reference
    FuncRef(u32),
    /// External reference
    ExternRef(u32),
    /// Null reference
    NullRef(ValueType),
}

impl Value {
    /// Returns the type of this value
    pub fn value_type(&self) -> ValueType {
        match self {
            Value::I32(_) => ValueType::I32,
            Value::I64(_) => ValueType::I64,
            Value::F32(_) => ValueType::F32,
            Value::F64(_) => ValueType::F64,
            Value::V128(_) => ValueType::V128,
            Value::FuncRef(_) => ValueType::FuncRef,
            Value::ExternRef(_) => ValueType::ExternRef,
            Value::NullRef(t) => *t,
        }
    }

    /// Returns true if this value is a number type (i32, i64, f32, f64)
    pub fn is_number(&self) -> bool {
        matches!(self, Value::I32(_) | Value::I64(_) | Value::F32(_) | Value::F64(_))
    }

    /// Returns true if this value is a vector type (v128)
    pub fn is_vector(&self) -> bool {
        matches!(self, Value::V128(_))
    }

    /// Returns true if this value is a reference type (func, extern, or null)
    pub fn is_reference(&self) -> bool {
        matches!(self, Value::FuncRef(_) | Value::ExternRef(_) | Value::NullRef(_))
    }

    /// Returns true if this value is null
    pub fn is_null(&self) -> bool {
        matches!(self, Value::NullRef(_))
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::I32(n) => write!(f, "i32.const {}", n),
            Value::I64(n) => write!(f, "i64.const {}", n),
            Value::F32(n) => write!(f, "f32.const {}", n),
            Value::F64(n) => write!(f, "f64.const {}", n),
            Value::V128(n) => write!(f, "v128.const {}", n),
            Value::FuncRef(addr) => write!(f, "ref.func {}", addr),
            Value::ExternRef(addr) => write!(f, "ref.extern {}", addr),
            Value::NullRef(t) => write!(f, "ref.null {}", t),
        }
    }
}

impl fmt::Display for ValueType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ValueType::I32 => write!(f, "i32"),
            ValueType::I64 => write!(f, "i64"),
            ValueType::F32 => write!(f, "f32"),
            ValueType::F64 => write!(f, "f64"),
            ValueType::V128 => write!(f, "v128"),
            ValueType::FuncRef => write!(f, "funcref"),
            ValueType::ExternRef => write!(f, "externref"),
        }
    }
}

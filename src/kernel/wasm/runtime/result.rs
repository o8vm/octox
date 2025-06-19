use alloc::vec::Vec;
use alloc::string::String;
use core::fmt;

use super::value::Value;

/// WebAssembly execution result
/// 
/// A result is either a sequence of values (success) or a trap (failure).
#[derive(Debug, Clone)]
pub enum ExecutionResult {
    /// Success case: a sequence of values
    Values(Vec<Value>),
    /// Failure case: a trap with a message
    Trap(String),
}

impl ExecutionResult {
    /// Creates a new successful result with a single value
    pub fn ok(value: Value) -> Self {
        Self::Values(Vec::from([value]))
    }

    /// Creates a new successful result with multiple values
    pub fn ok_many(values: Vec<Value>) -> Self {
        Self::Values(values)
    }

    /// Creates a new trap result
    pub fn trap(message: impl Into<String>) -> Self {
        Self::Trap(message.into())
    }

    /// Returns true if this result is a success (contains values)
    pub fn is_ok(&self) -> bool {
        matches!(self, Self::Values(_))
    }

    /// Returns true if this result is a trap
    pub fn is_trap(&self) -> bool {
        matches!(self, Self::Trap(_))
    }

    /// Returns the values if this is a successful result
    pub fn values(&self) -> Option<&[Value]> {
        match self {
            Self::Values(values) => Some(values),
            Self::Trap(_) => None,
        }
    }

    /// Returns the trap message if this is a trap result
    pub fn trap_message(&self) -> Option<&str> {
        match self {
            Self::Values(_) => None,
            Self::Trap(msg) => Some(msg),
        }
    }

    /// Unwraps the values, panicking if this is a trap
    pub fn unwrap_values(&self) -> &[Value] {
        match self {
            Self::Values(values) => values,
            Self::Trap(msg) => panic!("called `ExecutionResult::unwrap_values()` on a trap value: {}", msg),
        }
    }

    /// Unwraps the trap message, panicking if this is a success
    pub fn unwrap_trap(&self) -> &str {
        match self {
            Self::Values(_) => panic!("called `ExecutionResult::unwrap_trap()` on a success value"),
            Self::Trap(msg) => msg,
        }
    }
}

impl fmt::Display for ExecutionResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Values(values) => {
                if values.is_empty() {
                    write!(f, "[]")
                } else {
                    write!(f, "[")?;
                    for (i, value) in values.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}", value)?;
                    }
                    write!(f, "]")
                }
            }
            Self::Trap(msg) => write!(f, "trap: {}", msg),
        }
    }
}

use crate::wasm::ast::{GlobalType, ValType};
use crate::wasm::runtime::value::{Value, ValueType};
use alloc::string::String;
use alloc::string::ToString;
use core::fmt;
use alloc::format;

/// A global instance is the runtime representation of a global variable.
/// It records its type and holds an individual value.
///
/// # Specification
///
/// A global instance is the runtime representation of a global variable.
/// It records its type and holds an individual value.
///
/// globalinst ::= {type globaltype, value val}
///
/// The value of mutable globals can be mutated through variable instructions
/// or by external means provided by the embedder.
///
/// It is an invariant of the semantics that the value has a type equal to
/// the value type of globaltype.
#[derive(Debug)]
pub struct GlobalInstance {
    /// The type of the global variable
    ty: GlobalType,
    /// The value of the global variable
    value: Value,
}

impl GlobalInstance {
    /// Creates a new global instance with the given type and value.
    ///
    /// # Arguments
    ///
    /// * `ty` - The type of the global variable
    /// * `value` - The initial value of the global variable
    ///
    /// # Returns
    ///
    /// A new global instance.
    ///
    /// # Panics
    ///
    /// Panics if the value type does not match the global type's value type.
    pub fn new(ty: GlobalType, value: Value) -> Self {
        assert_eq!(
            value.value_type(),
            ValueType::from_val_type(ty.value_type()),
            "value type does not match global type's value type"
        );
        Self { ty, value }
    }

    /// Returns the type of the global variable.
    pub fn ty(&self) -> &GlobalType {
        &self.ty
    }

    /// Returns the value of the global variable.
    pub fn value(&self) -> &Value {
        &self.value
    }

    /// Sets the value of the global variable.
    ///
    /// # Arguments
    ///
    /// * `value` - The new value to set
    ///
    /// # Returns
    ///
    /// * `Ok(())` if the value was set successfully
    /// * `Err(String)` if the global is immutable or the value type does not match
    pub fn set_value(&mut self, value: Value) -> Result<(), String> {
        if !self.ty.is_mutable() {
            return Err("global is immutable".to_string());
        }
        if value.value_type() != ValueType::from_val_type(self.ty.value_type()) {
            return Err(format!(
                "value type {} does not match global type's value type {}",
                value.value_type(),
                ValueType::from_val_type(self.ty.value_type())
            ));
        }
        self.value = value;
        Ok(())
    }

    /// Returns whether the global variable is mutable.
    pub fn is_mutable(&self) -> bool {
        self.ty.is_mutable()
    }

    /// Returns the value type of the global variable.
    pub fn value_type(&self) -> ValType {
        self.ty.value_type()
    }
}

impl fmt::Display for GlobalInstance {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "global {} {}",
            if self.is_mutable() { "mut" } else { "const" },
            self.value
        )
    }
}

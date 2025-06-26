use crate::wasm::ast::{ValType, FuncType};
use crate::wasm::runtime::value::Value;
use alloc::vec::Vec;
use alloc::string::String;
use alloc::format;
use core::fmt;

/// Element instance represents a runtime element segment
/// 
/// # Specification
/// An element instance is the runtime representation of an element segment.
/// It holds a vector of references and their common type.
/// 
/// eleminst ::= {type reftype, elem vec(ref)}
#[derive(Debug, Clone)]
pub struct ElementInstance {
    /// The type of references stored in this element instance
    element_type: ValType,
    /// The vector of references
    elements: Vec<Value>,
}

impl ElementInstance {
    /// Creates a new element instance
    /// 
    /// # Arguments
    /// * `element_type` - The type of references to be stored
    /// 
    /// # Returns
    /// A new empty element instance
    pub fn new(element_type: ValType) -> Self {
        Self {
            element_type,
            elements: Vec::new(),
        }
    }

    /// Creates a new element instance with initial elements
    /// 
    /// # Arguments
    /// * `element_type` - The type of references to be stored
    /// * `elements` - The initial vector of references
    /// 
    /// # Returns
    /// A new element instance with the given elements
    /// 
    /// # Errors
    /// Returns an error if any element's type doesn't match the element type
    pub fn with_elements(element_type: ValType, elements: Vec<Value>) -> Result<Self, String> {
        // Validate that all elements have the correct type
        for (i, elem) in elements.iter().enumerate() {
            if elem.value_type() != element_type.into() {
                return Err(format!(
                    "Element at index {} has type {}, expected {}",
                    i, elem.value_type(), element_type
                ));
            }
        }

        Ok(Self {
            element_type,
            elements,
        })
    }

    /// Returns the type of references stored in this element instance
    pub fn element_type(&self) -> ValType {
        self.element_type
    }

    /// Returns the number of elements in this instance
    pub fn size(&self) -> usize {
        self.elements.len()
    }

    /// Returns true if this element instance is empty
    pub fn is_empty(&self) -> bool {
        self.elements.is_empty()
    }

    /// Returns a reference to the element at the given index
    /// 
    /// # Arguments
    /// * `index` - The index of the element to get
    /// 
    /// # Returns
    /// Some reference to the element if the index is valid, None otherwise
    pub fn get(&self, index: usize) -> Option<&Value> {
        self.elements.get(index)
    }

    /// Sets the element at the given index
    /// 
    /// # Arguments
    /// * `index` - The index of the element to set
    /// * `value` - The new value for the element
    /// 
    /// # Returns
    /// Ok(()) if successful, Err if the index is invalid or the value type doesn't match
    pub fn set(&mut self, index: usize, value: Value) -> Result<(), String> {
        if index >= self.elements.len() {
            return Err(format!("Element index {} out of bounds", index));
        }

        if value.value_type() != self.element_type.into() {
            return Err(format!(
                "Cannot set element of type {} to value of type {}",
                self.element_type, value.value_type()
            ));
        }

        self.elements[index] = value;
        Ok(())
    }

    /// Appends an element to this instance
    /// 
    /// # Arguments
    /// * `value` - The value to append
    /// 
    /// # Returns
    /// Ok(()) if successful, Err if the value type doesn't match
    pub fn push(&mut self, value: Value) -> Result<(), String> {
        if value.value_type() != self.element_type.into() {
            return Err(format!(
                "Cannot append value of type {} to element instance of type {}",
                value.value_type(), self.element_type
            ));
        }

        self.elements.push(value);
        Ok(())
    }

    /// Returns an iterator over the elements
    pub fn elements(&self) -> impl Iterator<Item = &Value> {
        self.elements.iter()
    }

    /// Returns a mutable iterator over the elements
    pub fn elements_mut(&mut self) -> impl Iterator<Item = &mut Value> {
        self.elements.iter_mut()
    }

    /// Clears all elements from this instance
    pub fn clear(&mut self) {
        self.elements.clear();
    }
}

impl fmt::Display for ElementInstance {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{type: {}, elements: [", self.element_type)?;
        for (i, elem) in self.elements.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", elem)?;
        }
        write!(f, "]}}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new() {
        let elem = ElementInstance::new(ValType::FuncRef);
        assert_eq!(elem.element_type(), ValType::FuncRef);
        assert!(elem.is_empty());
    }

    #[test]
    fn test_with_elements() {
        let elements = vec![
            Value::FuncRef(0),
            Value::FuncRef(1),
            Value::FuncRef(2),
        ];
        let elem = ElementInstance::with_elements(ValType::FuncRef, elements.clone()).unwrap();
        assert_eq!(elem.element_type(), ValType::FuncRef);
        assert_eq!(elem.size(), 3);
        assert_eq!(elem.elements().collect::<Vec<_>>(), elements.iter().collect::<Vec<_>>());
    }

    #[test]
    fn test_with_elements_type_mismatch() {
        let elements = vec![
            Value::I32(0),
            Value::FuncRef(1),
        ];
        let result = ElementInstance::with_elements(ValType::FuncRef, elements);
        assert!(result.is_err());
    }

    #[test]
    fn test_get_set() {
        let mut elem = ElementInstance::new(ValType::FuncRef);
        elem.push(Value::FuncRef(0)).unwrap();
        elem.push(Value::FuncRef(1)).unwrap();

        assert_eq!(elem.get(0), Some(&Value::FuncRef(0)));
        assert_eq!(elem.get(1), Some(&Value::FuncRef(1)));
        assert_eq!(elem.get(2), None);

        elem.set(0, Value::FuncRef(2)).unwrap();
        assert_eq!(elem.get(0), Some(&Value::FuncRef(2)));

        let result = elem.set(0, Value::I32(0));
        assert!(result.is_err());
    }

    #[test]
    fn test_push() {
        let mut elem = ElementInstance::new(ValType::FuncRef);
        elem.push(Value::FuncRef(0)).unwrap();
        elem.push(Value::FuncRef(1)).unwrap();
        assert_eq!(elem.size(), 2);

        let result = elem.push(Value::I32(0));
        assert!(result.is_err());
    }

    #[test]
    fn test_clear() {
        let mut elem = ElementInstance::new(ValType::FuncRef);
        elem.push(Value::FuncRef(0)).unwrap();
        elem.push(Value::FuncRef(1)).unwrap();
        assert_eq!(elem.size(), 2);

        elem.clear();
        assert!(elem.is_empty());
    }
} 
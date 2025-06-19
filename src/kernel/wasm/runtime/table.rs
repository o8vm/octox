use alloc::vec::Vec;
use alloc::format;
use alloc::string::String;
use core::fmt;

use crate::wasm::ast::{TableType, ValType};

/// Table element type
/// 
/// Represents a reference value stored in a table.
/// Currently only function references are supported.
#[derive(Debug, Clone, PartialEq)]
pub enum TableElement {
    /// A function reference
    FuncRef(Option<u32>),  // Function index, None for null
    /// An external reference (not yet implemented)
    ExternRef(Option<u32>), // External reference index, None for null
}

impl TableElement {
    /// Creates a new function reference
    pub fn funcref(func_idx: Option<u32>) -> Self {
        Self::FuncRef(func_idx)
    }

    /// Creates a new external reference
    pub fn externref(ref_idx: Option<u32>) -> Self {
        Self::ExternRef(ref_idx)
    }

    /// Returns true if this is a function reference
    pub fn is_funcref(&self) -> bool {
        matches!(self, Self::FuncRef(_))
    }

    /// Returns true if this is an external reference
    pub fn is_externref(&self) -> bool {
        matches!(self, Self::ExternRef(_))
    }

    /// Returns true if this is a null reference
    pub fn is_null(&self) -> bool {
        match self {
            Self::FuncRef(None) | Self::ExternRef(None) => true,
            _ => false,
        }
    }

    /// Returns the reference type of this element
    pub fn ref_type(&self) -> ValType {
        match self {
            Self::FuncRef(_) => ValType::FuncRef,
            Self::ExternRef(_) => ValType::ExternRef,
        }
    }
}

impl fmt::Display for TableElement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::FuncRef(None) => write!(f, "null funcref"),
            Self::FuncRef(Some(idx)) => write!(f, "funcref {}", idx),
            Self::ExternRef(None) => write!(f, "null externref"),
            Self::ExternRef(Some(idx)) => write!(f, "externref {}", idx),
        }
    }
}

/// Table instance
/// 
/// The runtime representation of a table.
/// It records its type and holds a vector of reference values.
#[derive(Debug)]
pub struct TableInstance {
    /// The type of the table
    ty: TableType,
    /// The elements of the table
    elements: Vec<TableElement>,
}

impl TableInstance {
    /// Creates a new table instance
    pub fn new(ty: TableType) -> Self {
        let mut elements = Vec::with_capacity(ty.min_entries() as usize);
        for _ in 0..ty.min_entries() {
            elements.push(TableElement::funcref(None));
        }
        Self { ty, elements }
    }

    /// Creates a new table instance with a specific initialization value
    /// 
    /// # Arguments
    /// 
    /// * `ty` - The table type
    /// * `init_ref` - The initialization value for all elements
    /// 
    /// # Returns
    /// 
    /// * `Self` - The new table instance
    pub fn new_with_init(ty: TableType, init_ref: TableElement) -> Self {
        let mut elements = Vec::with_capacity(ty.min_entries() as usize);
        for _ in 0..ty.min_entries() {
            elements.push(init_ref.clone());
        }
        Self { ty, elements }
    }

    /// Returns the type of the table
    pub fn ty(&self) -> &TableType {
        &self.ty
    }

    /// Returns the number of elements in the table
    pub fn size(&self) -> u32 {
        self.elements.len() as u32
    }

    /// Returns true if the table has reached its maximum size
    pub fn is_full(&self) -> bool {
        self.ty.max_entries().map_or(false, |max| self.size() >= max)
    }

    /// Returns the element at the given index
    pub fn get(&self, index: u32) -> Option<&TableElement> {
        self.elements.get(index as usize)
    }

    /// Sets the element at the given index
    pub fn set(&mut self, index: u32, element: TableElement) -> Result<(), String> {
        if index >= self.size() {
            return Err(format!("table index {} out of bounds", index));
        }
        if element.ref_type() != self.ty.element_type {
            return Err(format!(
                "table element type mismatch: expected {}, got {}",
                self.ty.element_type, element.ref_type()
            ));
        }
        self.elements[index as usize] = element;
        Ok(())
    }

    /// Grows the table by the given number of elements
    /// 
    /// # Specification (Growing tables)
    /// 
    /// 1. Let tableinst be the table instance to grow, n the number of elements by which to grow it, and ref the initialization value.
    /// 2. Let len be n added to the length of tableinst.elem.
    /// 3. If len is larger than or equal to 2^32, then fail.
    /// 4. Let limits t be the structure of table type tableinst.type.
    /// 5. Let limits' be limits with min updated to len.
    /// 6. If limits' is not valid, then fail.
    /// 7. Append ref n to tableinst.elem.
    /// 8. Set tableinst.type to the table type limits' t.
    /// 
    /// growtable(tableinst, n, ref) = tableinst with type = limits' t with elem = tableinst.elem ref n
    /// (if len = n + |tableinst.elem|
    ///  ∧ len < 2^32
    ///  ∧ limits t = tableinst.type
    ///  ∧ limits' = limits with min = len
    ///  ∧ ⊢ limits' ok)
    pub fn grow(&mut self, delta: u32, init: TableElement) -> Result<u32, String> {
        // 1. Let tableinst be the table instance to grow, n the number of elements by which to grow it, and ref the initialization value.
        // (self is tableinst, delta is n, init is ref)
        
        // 2. Let len be n added to the length of tableinst.elem.
        let len = self.size().checked_add(delta).ok_or_else(|| {
            format!("table size overflow: {} + {}", self.size(), delta)
        })?;
        
        // 3. If len is larger than or equal to 2^32, then fail.
        // Note: The checked_add operation above handles this case.
        // If len would be >= 2^32, checked_add returns None and we fail.
        // This is equivalent to the specification's requirement.
        
        // 4. Let limits t be the structure of table type tableinst.type.
        let limits = self.ty.limits.clone();
        let element_type = self.ty.element_type;
        
        // 5. Let limits' be limits with min updated to len.
        let mut new_limits = limits.clone();
        new_limits.min = len;
        
        // 6. If limits' is not valid, then fail.
        if !new_limits.is_valid() {
            return Err(format!("invalid table limits after growth: min={}, max={:?}", new_limits.min, new_limits.max));
        }
        
        // Validate that the initialization value matches the table element type
        if init.ref_type() != element_type {
            return Err(format!(
                "table element type mismatch: expected {}, got {}",
                element_type, init.ref_type()
            ));
        }
        
        // 7. Append ref n to tableinst.elem.
        let old_size = self.size();
        for _ in 0..delta {
            self.elements.push(init.clone());
        }
        
        // 8. Set tableinst.type to the table type limits' t.
        self.ty = crate::wasm::ast::TableType::new(new_limits, element_type);
        
        Ok(old_size)
    }

    /// Fills a range of the table with a value
    pub fn fill(&mut self, start: u32, len: u32, value: TableElement) -> Result<(), String> {
        if value.ref_type() != self.ty.element_type {
            return Err(format!(
                "table element type mismatch: expected {}, got {}",
                self.ty.element_type, value.ref_type()
            ));
        }
        let end = start.checked_add(len).ok_or_else(|| {
            format!("table fill range overflow: {} + {}", start, len)
        })?;
        if end > self.size() {
            return Err(format!(
                "table fill range out of bounds: {}..{} > {}",
                start, end, self.size()
            ));
        }
        for i in start..end {
            self.elements[i as usize] = value.clone();
        }
        Ok(())
    }

    /// Copies elements from one range to another
    pub fn copy(&mut self, dst: u32, src: u32, len: u32) -> Result<(), String> {
        let dst_end = dst.checked_add(len).ok_or_else(|| {
            format!("table copy destination range overflow: {} + {}", dst, len)
        })?;
        let src_end = src.checked_add(len).ok_or_else(|| {
            format!("table copy source range overflow: {} + {}", src, len)
        })?;
        if dst_end > self.size() {
            return Err(format!(
                "table copy destination range out of bounds: {}..{} > {}",
                dst, dst_end, self.size()
            ));
        }
        if src_end > self.size() {
            return Err(format!(
                "table copy source range out of bounds: {}..{} > {}",
                src, src_end, self.size()
            ));
        }

        // Handle overlapping ranges
        if dst < src {
            // Copy forward
            for i in 0..len {
                self.elements[(dst + i) as usize] = self.elements[(src + i) as usize].clone();
            }
        } else if dst > src {
            // Copy backward
            for i in (0..len).rev() {
                self.elements[(dst + i) as usize] = self.elements[(src + i) as usize].clone();
            }
        }
        // If dst == src, no copy needed
        Ok(())
    }

    /// Initializes a range of the table from a vector of elements
    pub fn init(&mut self, dst: u32, src: &[TableElement]) -> Result<(), String> {
        let len = src.len() as u32;
        let dst_end = dst.checked_add(len).ok_or_else(|| {
            format!("table init range overflow: {} + {}", dst, len)
        })?;
        if dst_end > self.size() {
            return Err(format!(
                "table init range out of bounds: {}..{} > {}",
                dst, dst_end, self.size()
            ));
        }
        for (i, element) in src.iter().enumerate() {
            if element.ref_type() != self.ty.element_type {
                return Err(format!(
                    "table element type mismatch: expected {}, got {}",
                    self.ty.element_type, element.ref_type()
                ));
            }
            self.elements[(dst + i as u32) as usize] = element.clone();
        }
        Ok(())
    }
}

impl fmt::Display for TableInstance {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "table {} ({} elements, type: {})",
            self.size(),
            self.elements.len(),
            self.ty
        )
    }
}
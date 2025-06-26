//! WebAssembly Typing Module
//! 
//! This module implements the typing rules for WebAssembly as described in the specification.
//! It includes external typing (4.5.1) and value typing (4.5.2) rules.

use alloc::format;
use alloc::string::ToString;

use crate::wasm::ast::{FuncType, ValType, TableType, MemoryType, GlobalType};
use crate::wasm::runtime::{
    Store,
    Value,
    RuntimeResult,
    RuntimeError,
    address::{FuncAddr, TableAddr, MemAddr, GlobalAddr},
};

/// External type
/// 
/// Represents the external type of an external value as defined in 4.5.1 External Typing.
#[derive(Debug, Clone, PartialEq)]
pub enum ExternalType {
    /// Function external type
    Func(FuncType),
    /// Table external type
    Table(TableType),
    /// Memory external type
    Memory(MemoryType),
    /// Global external type
    Global(GlobalType),
}

impl ExternalType {
    /// Returns true if this external type matches another external type
    pub fn matches(&self, other: &ExternalType) -> bool {
        match (self, other) {
            (ExternalType::Func(ty1), ExternalType::Func(ty2)) => ty1 == ty2,
            (ExternalType::Table(ty1), ExternalType::Table(ty2)) => ty1 == ty2,
            (ExternalType::Memory(ty1), ExternalType::Memory(ty2)) => ty1 == ty2,
            (ExternalType::Global(ty1), ExternalType::Global(ty2)) => ty1 == ty2,
            _ => false,
        }
    }
}

/// External value
/// 
/// Represents an external value that can be typed according to 4.5.1 External Typing.
#[derive(Debug, Clone, PartialEq)]
pub enum ExternalValue {
    /// Function external value
    Func(FuncAddr),
    /// Table external value
    Table(TableAddr),
    /// Memory external value
    Memory(MemAddr),
    /// Global external value
    Global(GlobalAddr),
}

impl ExternalValue {
    /// Gets the external type of this external value relative to a store
    pub fn external_type(&self, store: &mut Store) -> RuntimeResult<ExternalType> {
        match self {
            ExternalValue::Func(addr) => {
                // The store entry S.funcs[a] must exist
                let func_instance = store.funcs.get(addr.as_usize()).ok_or_else(|| {
                    RuntimeError::TypeError(format!(
                        "Function instance at address {} does not exist in store",
                        addr.as_usize()
                    ))
                })?;
                
                // Then func a is valid with external type func S.funcs[a].type
                Ok(ExternalType::Func(func_instance.ty().clone()))
            }
            ExternalValue::Table(addr) => {
                // The store entry S.tables[a] must exist
                let table_instance = store.tables.get(addr.as_usize()).ok_or_else(|| {
                    RuntimeError::TypeError(format!(
                        "Table instance at address {} does not exist in store",
                        addr.as_usize()
                    ))
                })?;
                
                // Then table a is valid with external type table S.tables[a].type
                Ok(ExternalType::Table(table_instance.ty().clone()))
            }
            ExternalValue::Memory(addr) => {
                // The store entry S.mems[a] must exist
                let memory_instance = store.mems.get(addr.as_usize()).ok_or_else(|| {
                    RuntimeError::TypeError(format!(
                        "Memory instance at address {} does not exist in store",
                        addr.as_usize()
                    ))
                })?;
                
                // Then mem a is valid with external type mem S.mems[a].type
                Ok(ExternalType::Memory(memory_instance.ty().clone()))
            }
            ExternalValue::Global(addr) => {
                // The store entry S.globals[a] must exist
                let global_instance = store.globals.get(addr.as_usize()).ok_or_else(|| {
                    RuntimeError::TypeError(format!(
                        "Global instance at address {} does not exist in store",
                        addr.as_usize()
                    ))
                })?;
                
                // Then global a is valid with external type global S.globals[a].type
                Ok(ExternalType::Global(global_instance.ty().clone()))
            }
        }
    }

    /// Validates that this external value has the expected external type
    pub fn validate_external_type(&self, store: &mut Store, expected_type: &ExternalType) -> RuntimeResult<()> {
        let actual_type = self.external_type(store)?;
        
        if !actual_type.matches(expected_type) {
            return Err(RuntimeError::TypeError(format!(
                "External value type mismatch: expected {:?}, got {:?}",
                expected_type, actual_type
            )));
        }
        
        Ok(())
    }
}

/// Value typing context
/// 
/// Provides methods for checking values against value types as defined in 4.5.2 Value Typing.
pub struct ValueTyping;

impl ValueTyping {
    /// Checks if a value is valid with a given value type relative to a store
    /// 
    /// # Specification (4.5.2 Value Typing)
    /// 
    /// Numeric Values t.const c:
    /// - The value is valid with number type t.
    /// S ⊢ t.const c : t
    /// 
    /// Null References ref.null t:
    /// - The value is valid with reference type t.
    /// S ⊢ ref.null t : t
    /// 
    /// Function References ref a:
    /// - The external value func a must be valid.
    /// - Then the value is valid with reference type funcref.
    /// S ⊢ func a : func functype
    /// S ⊢ ref a : funcref
    /// 
    /// External References ref.extern a:
    /// - The value is valid with reference type externref.
    /// S ⊢ ref.extern a : externref
    pub fn check_value_type(value: &Value, val_type: ValType, store: &mut Store) -> RuntimeResult<()> {
        match (value, val_type) {
            // Numeric Values t.const c
            (Value::I32(_), ValType::I32) => Ok(()),
            (Value::I64(_), ValType::I64) => Ok(()),
            (Value::F32(_), ValType::F32) => Ok(()),
            (Value::F64(_), ValType::F64) => Ok(()),
            (Value::V128(_), ValType::V128) => Ok(()),
            
            // Null References ref.null t
            (Value::NullRef(ref_type), ValType::FuncRef) => {
                match ref_type {
                    crate::wasm::runtime::value::ValueType::FuncRef => Ok(()),
                    _ => Err(RuntimeError::TypeError(format!(
                        "Null reference type mismatch: expected FuncRef, got {:?}",
                        ref_type
                    ))),
                }
            }
            (Value::NullRef(ref_type), ValType::ExternRef) => {
                match ref_type {
                    crate::wasm::runtime::value::ValueType::ExternRef => Ok(()),
                    _ => Err(RuntimeError::TypeError(format!(
                        "Null reference type mismatch: expected ExternRef, got {:?}",
                        ref_type
                    ))),
                }
            }
            
            // Function References ref a
            (Value::FuncRef(addr), ValType::FuncRef) => {
                // The external value func a must be valid
                let func_instance = store.funcs.get(*addr as usize).ok_or_else(|| {
                    RuntimeError::TypeError(format!(
                        "Function reference points to non-existent function at address {}",
                        addr
                    ))
                })?;
                
                // Then the value is valid with reference type funcref
                // (The function instance exists, so the reference is valid)
                Ok(())
            }
            
            // External References ref.extern a
            (Value::ExternRef(_), ValType::ExternRef) => {
                // The value is valid with reference type externref
                Ok(())
            }
            
            // Type mismatch
            _ => Err(RuntimeError::TypeError(format!(
                "Value type mismatch: expected {:?}, got value {:?}",
                val_type, value
            ))),
        }
    }

    /// Validates that a sequence of values matches a sequence of value types
    pub fn check_value_types(values: &[Value], val_types: &[ValType], store: &mut Store) -> RuntimeResult<()> {
        if values.len() != val_types.len() {
            return Err(RuntimeError::TypeError(format!(
                "Value count mismatch: expected {} values, got {}",
                val_types.len(),
                values.len()
            )));
        }
        
        for (i, (value, val_type)) in values.iter().zip(val_types.iter()).enumerate() {
            Self::check_value_type(value, *val_type, store).map_err(|e| {
                RuntimeError::TypeError(format!("Value {}: {}", i, e))
            })?;
        }
        
        Ok(())
    }

    /// Gets the value type of a value
    pub fn get_value_type(value: &Value) -> ValType {
        match value {
            Value::I32(_) => ValType::I32,
            Value::I64(_) => ValType::I64,
            Value::F32(_) => ValType::F32,
            Value::F64(_) => ValType::F64,
            Value::V128(_) => ValType::V128,
            Value::FuncRef(_) => ValType::FuncRef,
            Value::ExternRef(_) => ValType::ExternRef,
            Value::NullRef(ref_type) => {
                if ref_type.is_reference() {
                    ref_type.to_val_type()
                } else {
                    // This should not happen in valid WASM, but we need to handle it
                    ValType::FuncRef // Default fallback
                }
            },
        }
    }
}

/// Module typing context
/// 
/// Provides methods for type-checking modules and their components.
pub struct ModuleTyping;

impl ModuleTyping {
    /// Validates that external values match import requirements
    /// 
    /// This implements the external typing rules for module imports.
    pub fn validate_imports(
        external_values: &[ExternalValue],
        import_types: &[ExternalType],
        store: &mut Store,
    ) -> RuntimeResult<()> {
        if external_values.len() != import_types.len() {
            return Err(RuntimeError::TypeError(format!(
                "Import count mismatch: expected {} imports, got {} external values",
                import_types.len(),
                external_values.len()
            )));
        }
        
        for (i, (external_value, import_type)) in external_values.iter().zip(import_types.iter()).enumerate() {
            external_value.validate_external_type(store, import_type).map_err(|e| {
                RuntimeError::TypeError(format!("Import {}: {}", i, e))
            })?;
        }
        
        Ok(())
    }

    /// Validates that exported values match export requirements
    /// 
    /// This implements the external typing rules for module exports.
    pub fn validate_exports(
        external_values: &[ExternalValue],
        export_types: &[ExternalType],
        store: &mut Store,
    ) -> RuntimeResult<()> {
        if external_values.len() != export_types.len() {
            return Err(RuntimeError::TypeError(format!(
                "Export count mismatch: expected {} exports, got {} external values",
                export_types.len(),
                external_values.len()
            )));
        }
        
        for (i, (external_value, export_type)) in external_values.iter().zip(export_types.iter()).enumerate() {
            external_value.validate_external_type(store, export_type).map_err(|e| {
                RuntimeError::TypeError(format!("Export {}: {}", i, e))
            })?;
        }
        
        Ok(())
    }
} 
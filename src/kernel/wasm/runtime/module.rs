use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::string::ToString;
use alloc::vec::Vec;
use alloc::format;
use core::fmt;

use super::address::{FuncAddr, TableAddr, MemAddr, GlobalAddr, ElemAddr, DataAddr};
use super::typing::{ExternalValue, ExternalType, ModuleTyping};
use super::allocation::Allocation;
use super::instruction::InstructionExecutor;
use super::{Thread, Frame, FrameState};
use crate::wasm::ast::{FuncType, ValType, Module, Import, Export};
use crate::wasm::runtime::{Store, RuntimeResult, RuntimeError};

/// Export instance
#[derive(Debug, Clone, PartialEq)]
pub struct ExportInstance {
    /// Export name
    pub name: String,
    /// Export kind and address
    pub value: ExportValue,
}

/// Export value
#[derive(Debug, Clone, PartialEq)]
pub enum ExportValue {
    /// Function export
    Func(FuncAddr),
    /// Table export
    Table(TableAddr),
    /// Memory export
    Memory(MemAddr),
    /// Global export
    Global(GlobalAddr),
}

impl fmt::Display for ExportValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Func(addr) => write!(f, "func {}", addr),
            Self::Table(addr) => write!(f, "table {}", addr),
            Self::Memory(addr) => write!(f, "memory {}", addr),
            Self::Global(addr) => write!(f, "global {}", addr),
        }
    }
}

/// Module instance
/// 
/// A module instance is the runtime representation of a module.
/// It is created by instantiating a module, and collects runtime
/// representations of all entities that are imported, defined,
/// or exported by the module.
#[derive(Debug, Clone, PartialEq)]
pub struct ModuleInstance {
    /// Function types
    pub types: Vec<FuncType>,
    /// Function addresses
    pub func_addrs: Vec<FuncAddr>,
    /// Table addresses
    pub table_addrs: Vec<TableAddr>,
    /// Memory addresses
    pub mem_addrs: Vec<MemAddr>,
    /// Global addresses
    pub global_addrs: Vec<GlobalAddr>,
    /// Element addresses
    pub elem_addrs: Vec<ElemAddr>,
    /// Data addresses
    pub data_addrs: Vec<DataAddr>,
    /// Exports (name -> export instance)
    pub exports: BTreeMap<String, ExportInstance>,
}

impl ModuleInstance {
    /// Creates a new empty module instance
    pub fn new() -> Self {
        Self {
            types: Vec::new(),
            func_addrs: Vec::new(),
            table_addrs: Vec::new(),
            mem_addrs: Vec::new(),
            global_addrs: Vec::new(),
            elem_addrs: Vec::new(),
            data_addrs: Vec::new(),
            exports: BTreeMap::new(),
        }
    }

    /// Returns the number of function types
    pub fn type_count(&self) -> usize {
        self.types.len()
    }

    /// Returns the number of function addresses
    pub fn func_count(&self) -> usize {
        self.func_addrs.len()
    }

    /// Returns the number of table addresses
    pub fn table_count(&self) -> usize {
        self.table_addrs.len()
    }

    /// Returns the number of memory addresses
    pub fn mem_count(&self) -> usize {
        self.mem_addrs.len()
    }

    /// Returns the number of global addresses
    pub fn global_count(&self) -> usize {
        self.global_addrs.len()
    }

    /// Returns the number of element addresses
    pub fn elem_count(&self) -> usize {
        self.elem_addrs.len()
    }

    /// Returns the number of data addresses
    pub fn data_count(&self) -> usize {
        self.data_addrs.len()
    }

    /// Returns the number of exports
    pub fn export_count(&self) -> usize {
        self.exports.len()
    }

    /// Adds a function type
    pub fn add_type(&mut self, func_type: FuncType) -> u32 {
        let idx = self.types.len() as u32;
        self.types.push(func_type);
        idx
    }

    /// Adds a function address
    pub fn add_func(&mut self, addr: FuncAddr) -> u32 {
        let idx = self.func_addrs.len() as u32;
        self.func_addrs.push(addr);
        idx
    }

    /// Adds a table address
    pub fn add_table(&mut self, addr: TableAddr) -> u32 {
        let idx = self.table_addrs.len() as u32;
        self.table_addrs.push(addr);
        idx
    }

    /// Adds a memory address
    pub fn add_memory(&mut self, addr: MemAddr) -> u32 {
        let idx = self.mem_addrs.len() as u32;
        self.mem_addrs.push(addr);
        idx
    }

    /// Adds a global address
    pub fn add_global(&mut self, addr: GlobalAddr) -> u32 {
        let idx = self.global_addrs.len() as u32;
        self.global_addrs.push(addr);
        idx
    }

    /// Adds an element address
    pub fn add_elem(&mut self, addr: ElemAddr) -> u32 {
        let idx = self.elem_addrs.len() as u32;
        self.elem_addrs.push(addr);
        idx
    }

    /// Adds a data address
    pub fn add_data(&mut self, addr: DataAddr) -> u32 {
        let idx = self.data_addrs.len() as u32;
        self.data_addrs.push(addr);
        idx
    }

    /// Adds an export
    /// 
    /// # Errors
    /// 
    /// Returns an error if an export with the same name already exists.
    pub fn add_export(&mut self, name: impl Into<String>, value: ExportValue) -> Result<(), String> {
        let name = name.into();
        if self.exports.contains_key(&name) {
            return Err(format!("export '{}' already exists", name));
        }
        self.exports.insert(name.clone(), ExportInstance { name, value });
        Ok(())
    }

    /// Gets an export by name
    pub fn get_export(&self, name: &str) -> Option<&ExportInstance> {
        self.exports.get(name)
    }

    /// Gets a function address by index
    pub fn get_func_addr(&self, idx: u32) -> Option<&FuncAddr> {
        self.func_addrs.get(idx as usize)
    }

    /// Gets a table address by index
    pub fn get_table_addr(&self, idx: u32) -> Option<&TableAddr> {
        self.table_addrs.get(idx as usize)
    }

    /// Gets a memory address by index
    pub fn get_memory_addr(&self, idx: u32) -> Option<&MemAddr> {
        self.mem_addrs.get(idx as usize)
    }

    /// Gets a global address by index
    pub fn get_global_addr(&self, idx: u32) -> Option<&GlobalAddr> {
        self.global_addrs.get(idx as usize)
    }

    /// Gets an element address by index
    pub fn get_elem_addr(&self, idx: u32) -> Option<&ElemAddr> {
        self.elem_addrs.get(idx as usize)
    }

    /// Gets a data address by index
    pub fn get_data_addr(&self, idx: u32) -> Option<&DataAddr> {
        self.data_addrs.get(idx as usize)
    }

    /// Allocates a module instance following the exact specification
    /// 
    /// # Specification (4.5 Modules - Allocation)
    /// 
    /// This implements the 21-step process for allocating a module instance:
    /// 1. Let module be the module to allocate and externval*_im the vector of external values providing the module's imports, val* the initialization values of the module's globals, and (ref*)* the reference vectors of the module's element segments.
    /// 2-21. Follow the allocation steps as specified in the WebAssembly specification.
    /// 
    /// # Mathematical Notation
    /// 
    /// allocmodule(S, module, externval*_im, val*, (ref*)*) = S', moduleinst
    /// where:
    /// table* = module.tables
    /// mem* = module.mems
    /// global* = module.globals
    /// elem* = module.elems
    /// data* = module.datas
    /// export* = module.exports
    /// moduleinst = { types module.types,
    ///                funcaddrs funcs(externval*_im) ++ funcaddr*,
    ///                tableaddrs tables(externval*_im) ++ tableaddr*,
    ///                memaddrs mems(externval*_im) ++ memaddr*,
    ///                globaladdrs globals(externval*_im) ++ globaladdr*,
    ///                elemaddrs elemaddr*,
    ///                dataaddrs dataaddr*,
    ///                exports exportinst* }
    /// S1, funcaddr* = allocfunc*(S, module.funcs, moduleinst)
    /// S2, tableaddr* = alloctable*(S1, (table.type)*, (ref.null t)*) (where (table.type)* = (limits t)*)
    /// S3, memaddr* = allocmem*(S2, (mem.type)*)
    /// S4, globaladdr* = allocglobal*(S3, (global.type)*, val*)
    /// S5, elemaddr* = allocelem*(S4, (elem.type)*, (ref*)*)
    /// S', dataaddr* = allocdata*(S5, (data.init)*)
    /// exportinst* = {name (export.name), value externval_ex}*
    /// funcs(externval*_ex) = (moduleinst.funcaddrs[x])* (where x* = funcs(export*))
    /// tables(externval*_ex) = (moduleinst.tableaddrs[x])* (where x* = tables(export*))
    /// mems(externval*_ex) = (moduleinst.memaddrs[x])* (where x* = mems(export*))
    /// globals(externval*_ex) = (moduleinst.globaladdrs[x])* (where x* = globals(export*))
    /// 
    /// # Arguments
    /// 
    /// * `store` - The store to allocate the module in
    /// * `module` - The module to allocate
    /// * `external_values` - The external values for imports
    /// * `global_init_values` - The initialization values for the module's globals
    /// * `element_refs` - The reference vectors for the module's element segments
    /// 
    /// # Returns
    /// 
    /// * `RuntimeResult<ModuleInstance>` - The allocated module instance
    pub fn alloc_module(
        store: &mut Store,
        module: &Module,
        external_values: &[ExternalValue],
        global_init_values: &[super::Value],
        element_refs: &[Vec<super::Value>],
    ) -> RuntimeResult<Self> {
        // 1. Let module be the module to allocate and externval*_im the vector of external values providing the module's imports, val* the initialization values of the module's globals, and (ref*)* the reference vectors of the module's element segments.
        // (Parameters are provided above)
        
        // Validate input parameters
        if global_init_values.len() != module.globals.len() {
            return Err(RuntimeError::Module(format!(
                "Global initialization values count mismatch: expected {}, got {}",
                module.globals.len(),
                global_init_values.len()
            )));
        }
        
        if element_refs.len() != module.elems.len() {
            return Err(RuntimeError::Module(format!(
                "Element reference vectors count mismatch: expected {}, got {}",
                module.elems.len(),
                element_refs.len()
            )));
        }
        
        // Extract external value addresses by kind
        let (import_func_addrs, import_table_addrs, import_mem_addrs, import_global_addrs) = 
            Self::extract_external_value_addresses(external_values)?;
        
        // 2. For each function func_i in module.funcs, do:
        // a. Let funcaddr_i be the function address resulting from allocating func_i for the module instance moduleinst defined below.
        // Note: This is handled in step 8 after we create the module instance due to mutual recursion
        
        // 3. For each table table_i in module.tables, do:
        // a. Let limits_i t_i be the table type table_i.type.
        // b. Let tableaddr_i be the table address resulting from allocating table_i.type with initialization value ref.null t_i.
        let table_addrs = super::allocation::Allocation::alloc_tables(store, &module.tables)?;
        
        // 4. For each memory mem_i in module.mems, do:
        // a. Let memaddr_i be the memory address resulting from allocating mem_i.type.
        let memory_types: Vec<_> = module.mems.iter().map(|m| m.ty).collect();
        let mem_addrs = super::allocation::Allocation::alloc_memories(store, &memory_types)?;
        
        // 5. For each global global_i in module.globals, do:
        // a. Let globaladdr_i be the global address resulting from allocating global_i.type with initializer value val*[i].
        let global_types: Vec<_> = module.globals.iter().map(|g| g.ty).collect();
        let global_addrs = super::allocation::Allocation::alloc_globals(store, &global_types, global_init_values)?;
        
        // 6. For each element segment elem_i in module.elems, do:
        // a. Let elemaddr_i be the element address resulting from allocating an element instance of reference type elem_i.type with contents (ref*)*[i].
        let ref_types: Vec<_> = module.elems.iter().map(|e| e.element_type).collect();
        let elem_addrs = super::allocation::Allocation::alloc_elems(store, &ref_types, element_refs)?;
        
        // 7. For each data segment data_i in module.datas, do:
        // a. Let dataaddr_i be the data address resulting from allocating a data instance with contents data_i.init.
        let data_bytes: Vec<_> = module.datas.iter().map(|d| d.data.clone()).collect();
        let data_addrs = super::allocation::Allocation::alloc_datas(store, &data_bytes)?;
        
        // 8. Let funcaddr* be the concatenation of the function addresses funcaddr_i in index order.
        // Note: We'll handle this after creating the module instance due to mutual recursion
        
        // 9. Let tableaddr* be the concatenation of the table addresses tableaddr_i in index order.
        // (table_addrs already contains the concatenated addresses in index order)
        
        // 10. Let memaddr* be the concatenation of the memory addresses memaddr_i in index order.
        // (mem_addrs already contains the concatenated addresses in index order)
        
        // 11. Let globaladdr* be the concatenation of the global addresses globaladdr_i in index order.
        // (global_addrs already contains the concatenated addresses in index order)
        
        // 12. Let elemaddr* be the concatenation of the element addresses elemaddr_i in index order.
        // (elem_addrs already contains the concatenated addresses in index order)
        
        // 13. Let dataaddr* be the concatenation of the data addresses dataaddr_i in index order.
        // (data_addrs already contains the concatenated addresses in index order)
        
        // 14. Let funcaddr*_mod be the list of function addresses extracted from externval*_im, concatenated with funcaddr*.
        // 15. Let tableaddr*_mod be the list of table addresses extracted from externval*_im, concatenated with tableaddr*.
        // 16. Let memaddr*_mod be the list of memory addresses extracted from externval*_im, concatenated with memaddr*.
        // 17. Let globaladdr*_mod be the list of global addresses extracted from externval*_im, concatenated with globaladdr*.
        
        // Create a temporary module instance for function allocation
        let mut temp_module_inst = ModuleInstance::new();
        
        // Add types (module.types)
        for func_type in &module.types {
            temp_module_inst.add_type(func_type.clone());
        }
        
        // Add import addresses to temporary module instance
        for func_addr in &import_func_addrs {
            temp_module_inst.add_func(*func_addr);
        }
        for table_addr in &import_table_addrs {
            temp_module_inst.add_table(*table_addr);
        }
        for mem_addr in &import_mem_addrs {
            temp_module_inst.add_memory(*mem_addr);
        }
        for global_addr in &import_global_addrs {
            temp_module_inst.add_global(*global_addr);
        }
        
        // Add allocated addresses to temporary module instance
        for table_addr in &table_addrs {
            temp_module_inst.add_table(*table_addr);
        }
        for mem_addr in &mem_addrs {
            temp_module_inst.add_memory(*mem_addr);
        }
        for global_addr in &global_addrs {
            temp_module_inst.add_global(*global_addr);
        }
        for elem_addr in &elem_addrs {
            temp_module_inst.add_elem(*elem_addr);
        }
        for data_addr in &data_addrs {
            temp_module_inst.add_data(*data_addr);
        }
        
        // Now allocate functions with the complete module instance (step 2a)
        let func_addrs = super::allocation::Allocation::alloc_funcs(store, &module.funcs, &temp_module_inst)?;
        
        // 8. Let funcaddr* be the concatenation of the function addresses funcaddr_i in index order.
        // (func_addrs already contains the concatenated addresses in index order)
        
        // 14-17. Concatenate import and allocated addresses
        let mut all_func_addrs = import_func_addrs.clone();
        all_func_addrs.extend(func_addrs); // funcaddr*_mod = funcs(externval*_im) ++ funcaddr*
        
        let mut all_table_addrs = import_table_addrs.clone();
        all_table_addrs.extend(table_addrs); // tableaddr*_mod = tables(externval*_im) ++ tableaddr*
        
        let mut all_mem_addrs = import_mem_addrs.clone();
        all_mem_addrs.extend(mem_addrs); // memaddr*_mod = mems(externval*_im) ++ memaddr*
        
        let mut all_global_addrs = import_global_addrs.clone();
        all_global_addrs.extend(global_addrs); // globaladdr*_mod = globals(externval*_im) ++ globaladdr*
        
        // 18. For each export export_i in module.exports, do:
        // a. If export_i is a function export for function index x, then let externval_i be the external value func (funcaddr*_mod[x]).
        // b. Else, if export_i is a table export for table index x, then let externval_i be the external value table (tableaddr*_mod[x]).
        // c. Else, if export_i is a memory export for memory index x, then let externval_i be the external value mem (memaddr*_mod[x]).
        // d. Else, if export_i is a global export for global index x, then let externval_i be the external value global (globaladdr*_mod[x]).
        // e. Let exportinst_i be the export instance {name (export_i.name), value externval_i}.
        let mut export_instances = Vec::new();
        for export in &module.exports {
            let export_value = match export.kind {
                crate::wasm::ast::ExternKind::Func => {
                    let func_addr = all_func_addrs.get(export.index as usize).ok_or_else(|| {
                        RuntimeError::Module(format!("Function export index {} out of bounds", export.index))
                    })?;
                    ExportValue::Func(*func_addr)
                }
                crate::wasm::ast::ExternKind::Table => {
                    let table_addr = all_table_addrs.get(export.index as usize).ok_or_else(|| {
                        RuntimeError::Module(format!("Table export index {} out of bounds", export.index))
                    })?;
                    ExportValue::Table(*table_addr)
                }
                crate::wasm::ast::ExternKind::Memory => {
                    let mem_addr = all_mem_addrs.get(export.index as usize).ok_or_else(|| {
                        RuntimeError::Module(format!("Memory export index {} out of bounds", export.index))
                    })?;
                    ExportValue::Memory(*mem_addr)
                }
                crate::wasm::ast::ExternKind::Global => {
                    let global_addr = all_global_addrs.get(export.index as usize).ok_or_else(|| {
                        RuntimeError::Module(format!("Global export index {} out of bounds", export.index))
                    })?;
                    ExportValue::Global(*global_addr)
                }
            };
            
            let export_instance = ExportInstance {
                name: export.name.clone(),
                value: export_value,
            };
            export_instances.push(export_instance);
        }
        
        // 19. Let exportinst* be the concatenation of the export instances exportinst_i in index order.
        // (export_instances already contains the concatenated instances in index order)
        
        // 20. Let moduleinst be the module instance {types (module.types), funcaddrs funcs(externval*_im) ++ funcaddr*, tableaddrs tables(externval*_im) ++ tableaddr*, memaddrs mems(externval*_im) ++ memaddr*, globaladdrs globals(externval*_im) ++ globaladdr*, elemaddrs elemaddr*, dataaddrs dataaddr*, exports exportinst*}.
        let mut module_inst = ModuleInstance::new();
        
        // Add types (module.types)
        for func_type in &module.types {
            module_inst.add_type(func_type.clone());
        }
        
        // Add function addresses (funcaddr*_mod)
        for func_addr in all_func_addrs {
            module_inst.add_func(func_addr);
        }
        
        // Add table addresses (tableaddr*_mod)
        for table_addr in all_table_addrs {
            module_inst.add_table(table_addr);
        }
        
        // Add memory addresses (memaddr*_mod)
        for mem_addr in all_mem_addrs {
            module_inst.add_memory(mem_addr);
        }
        
        // Add global addresses (globaladdr*_mod)
        for global_addr in all_global_addrs {
            module_inst.add_global(global_addr);
        }
        
        // Add element addresses (elemaddr*)
        for elem_addr in elem_addrs {
            module_inst.add_elem(elem_addr);
        }
        
        // Add data addresses (dataaddr*)
        for data_addr in data_addrs {
            module_inst.add_data(data_addr);
        }
        
        // Add exports (exportinst*)
        for export_instance in export_instances {
            module_inst.add_export(&export_instance.name, export_instance.value).map_err(|e| {
                RuntimeError::Module(format!("Failed to add export: {}", e))
            })?;
        }
        
        // 21. Return moduleinst.
        Ok(module_inst)
    }

    /// Extracts addresses from external values by kind
    fn extract_external_value_addresses(
        external_values: &[ExternalValue],
    ) -> RuntimeResult<(Vec<FuncAddr>, Vec<TableAddr>, Vec<MemAddr>, Vec<GlobalAddr>)> {
        let mut func_addrs = Vec::new();
        let mut table_addrs = Vec::new();
        let mut mem_addrs = Vec::new();
        let mut global_addrs = Vec::new();
        
        for external_value in external_values {
            match external_value {
                ExternalValue::Func(addr) => func_addrs.push(*addr),
                ExternalValue::Table(addr) => table_addrs.push(*addr),
                ExternalValue::Memory(addr) => mem_addrs.push(*addr),
                ExternalValue::Global(addr) => global_addrs.push(*addr),
            }
        }
        
        Ok((func_addrs, table_addrs, mem_addrs, global_addrs))
    }

    /// Invokes the start function if present
    fn invoke_start_function(
        store: &mut Store,
        module_inst: &ModuleInstance,
        start_func_index: u32,
    ) -> RuntimeResult<()> {
        let func_addr = module_inst.get_func_addr(start_func_index).ok_or_else(|| {
            RuntimeError::Module(format!("Start function at index {} not found", start_func_index))
        })?;
        
        // Create a thread for the start function
        let mut thread = super::Thread::new(
            super::FrameState::new(Vec::new(), module_inst.clone()),
            Vec::new(),
        );
        
        // Invoke the start function
        super::instruction::invoke_with_reduction_rule(store, &mut thread, *func_addr)
    }

    /// Invokes an exported function by name
    /// 
    /// # Specification (4.5 Modules - Invocation of exported functions)
    /// 
    /// This implements the semantics for invoking exported functions from a module instance.
    /// 
    /// # Arguments
    /// 
    /// * `store` - The current store
    /// * `thread` - The current thread
    /// * `name` - The name of the exported function
    /// * `args` - The arguments to pass to the function
    /// 
    /// # Returns
    /// 
    /// * `RuntimeResult<Vec<Value>>` - The function results
    pub fn invoke_exported_function(
        &self,
        store: &mut Store,
        thread: &mut super::Thread,
        name: &str,
        args: &[super::Value],
    ) -> RuntimeResult<Vec<super::Value>> {
        // Get the export
        let export = self.get_export(name).ok_or_else(|| {
            RuntimeError::Module(format!("Export '{}' not found", name))
        })?;
        
        // Check that it's a function export
        let func_addr = match &export.value {
            ExportValue::Func(addr) => *addr,
            _ => return Err(RuntimeError::Module(format!(
                "Export '{}' is not a function", name
            ))),
        };
        
        // Push arguments onto the stack
        for arg in args.iter().rev() {
            thread.stack_mut().push_value(arg.clone());
        }
        
        // Invoke the function
        super::instruction::invoke_with_reduction_rule(store, thread, func_addr)?;
        
        crate::wasm::runtime::debug_log(store.config(), &format!("Stack after function invocation: {} values", thread.stack().value_count()));
        
        // Get the results from the stack
        let func_instance = store.funcs.get(func_addr.as_usize()).ok_or_else(|| {
            RuntimeError::Module("Function instance not found in store".to_string())
        })?;
        
        let result_count = func_instance.ty().results.len();
        crate::wasm::runtime::debug_log(store.config(), &format!("Expected result count: {}", result_count));
        let mut results = Vec::new();
        
        for i in 0..result_count {
            let result = thread.stack_mut().pop_value().ok_or_else(|| {
                RuntimeError::Module(format!("Expected {} results from function invocation", result_count))
            })?;
            crate::wasm::runtime::debug_log(store.config(), &format!("Result {}: {:?}", i, result));
            results.push(result);
        }
        
        // Reverse to get correct order
        results.reverse();
        Ok(results)
    }

    /// Validates that all exports have valid external types
    /// 
    /// # Arguments
    /// 
    /// * `store` - The current store
    /// 
    /// # Returns
    /// 
    /// * `RuntimeResult<()>` - Success if all exports are valid
    pub fn validate_exports(&self, store: &mut Store) -> RuntimeResult<()> {
        for (name, export) in &self.exports {
            let external_value = match &export.value {
                ExportValue::Func(addr) => ExternalValue::Func(*addr),
                ExportValue::Table(addr) => ExternalValue::Table(*addr),
                ExportValue::Memory(addr) => ExternalValue::Memory(*addr),
                ExportValue::Global(addr) => ExternalValue::Global(*addr),
            };
            
            // This will validate that the external value exists and has a valid type
            external_value.external_type(store).map_err(|e| {
                RuntimeError::Module(format!("Export '{}': {}", name, e))
            })?;
        }
        
        Ok(())
    }

    /// Gets the external type of an export
    /// 
    /// # Arguments
    /// 
    /// * `store` - The current store
    /// * `name` - The name of the export
    /// 
    /// # Returns
    /// 
    /// * `RuntimeResult<ExternalType>` - The external type of the export
    pub fn get_export_external_type(
        &self,
        store: &mut Store,
        name: &str,
    ) -> RuntimeResult<ExternalType> {
        let export = self.get_export(name).ok_or_else(|| {
            RuntimeError::Module(format!("Export '{}' not found", name))
        })?;
        
        // Convert export value to external value
        let external_value = match &export.value {
            ExportValue::Func(addr) => ExternalValue::Func(*addr),
            ExportValue::Table(addr) => ExternalValue::Table(*addr),
            ExportValue::Memory(addr) => ExternalValue::Memory(*addr),
            ExportValue::Global(addr) => ExternalValue::Global(*addr),
        };
        
        // Get the external type
        external_value.external_type(store)
    }

    /// Instantiates a module with external values
    /// 
    /// # Specification (4.5.4 Instantiation)
    /// 
    /// Given a store S, a module module is instantiated with a list of external values externval_n
    /// supplying the required imports as follows.
    /// 
    /// Instantiation checks that the module is valid and the provided imports match the declared types,
    /// and may fail with an error otherwise. Instantiation can also result in a trap from initializing
    /// a table or memory from an active segment or from executing the start function.
    /// 
    /// # Arguments
    /// 
    /// * `store` - The store to instantiate the module in
    /// * `module` - The module to instantiate
    /// * `external_values` - The external values supplying the required imports
    /// 
    /// # Returns
    /// 
    /// * `RuntimeResult<Self>` - The instantiated module instance
    pub fn instantiate(
        store: &mut Store,
        module: &Module,
        external_values: &[ExternalValue],
    ) -> RuntimeResult<Self> {
        // 1. If module is not valid, then:
        // a. Fail.
        if !module.validate() {
            return Err(RuntimeError::Module("Module validation failed".to_string()));
        }

        // 2. Assert: module is valid with external types externtype_m classifying its imports.
        // (This is handled by the module validation above)

        // 3. If the number m of imports is not equal to the number n of provided external values, then:
        // a. Fail.
        if external_values.len() != module.imports.len() {
            return Err(RuntimeError::Module(format!(
                "Import count mismatch: expected {} imports, got {} external values",
                module.imports.len(),
                external_values.len()
            )));
        }

        // 4. For each external value externval_i in externval_n and external type externtype'_i in externtype_n^im, do:
        for (i, (import, external_value)) in module.imports.iter().zip(external_values.iter()).enumerate() {
            // a. If externval_i is not valid with an external type externtype_i in store S, then:
            // i. Fail.
            let import_type = Self::import_to_external_type(import)?;
            external_value.validate_external_type(store, &import_type).map_err(|e| {
                RuntimeError::Module(format!("Import {}: {}", i, e))
            })?;

            // b. If externtype_i does not match externtype'_i, then:
            // i. Fail.
            // (This is handled by validate_external_type above)
        }

        // 5. Let moduleinst_init be the auxiliary module instance {globaladdrs globals(externval_n), funcaddrs moduleinst.funcaddrs}
        // that only consists of the imported globals and the imported and allocated functions from the final module
        // instance moduleinst, defined below.
        let mut module_inst_init = ModuleInstance::new();
        
        // Extract global addresses from external values
        let global_addrs = Self::extract_global_addrs_from_external_values(external_values)?;
        for addr in global_addrs {
            module_inst_init.add_global(addr);
        }

        // Extract function addresses from external values
        let func_addrs = Self::extract_func_addrs_from_external_values(external_values)?;
        for addr in func_addrs {
            module_inst_init.add_func(addr);
        }

        // 6. Let F_init be the auxiliary frame {module moduleinst_init, locals ε}.
        let frame_init = Frame::new(0, FrameState::new(Vec::new(), module_inst_init.clone()));

        // 7. Push the frame F_init to the stack.
        let mut thread = Thread::new(
            FrameState::new(Vec::new(), module_inst_init.clone()),
            Vec::new(),
        );
        thread.stack_mut().push_frame(frame_init);

        // 8. Let val* be the vector of global initialization values determined by module and externval_n.
        // These may be calculated as follows.
        let mut global_init_values = Vec::new();
        
        // a. For each global global_i in module.globals, do:
        for global in &module.globals {
            // i. Let val_i be the result of evaluating the initializer expression global_i.init.
            let init_value = Self::evaluate_global_initializer_with_frame(
                store, 
                &mut thread, 
                &global.init
            )?;
            global_init_values.push(init_value);
        }

        // b. Assert: due to validation, the frame F_init is now on the top of the stack.
        // c. Let val* be the concatenation of val_i in index order.
        // (This is handled by the loop above)

        // 9. Let (ref*)* be the list of reference vectors determined by the element segments in module.
        // These may be calculated as follows.
        let mut element_refs = Vec::new();
        
        // a. For each element segment elem_i in module.elems, and for each element expression expr_ij in elem_i.init, do:
        for element in &module.elems {
            let mut refs = Vec::new();
            for expr in &element.elements {
                // i. Let ref_ij be the result of evaluating the initializer expression expr_ij.
                let ref_val = Self::evaluate_element_expression_with_frame(
                    store, 
                    &mut thread, 
                    expr
                )?;
                refs.push(ref_val);
            }
            // b. Let ref*_i be the concatenation of function elements ref_ij in order of index j.
            // c. Let (ref*)* be the concatenation of function element vectors ref*_i in order of index i.
            element_refs.push(refs);
        }

        // 10. Pop the frame F_init from the stack.
        thread.stack_mut().pop_frame().ok_or_else(|| {
            RuntimeError::Stack("Failed to pop initialization frame".to_string())
        })?;

        // 11. Let moduleinst be a new module instance allocated from module in store S with imports externval_n,
        // global initializer values val*, and element segment contents (ref*)*, and let S' be the extended store
        // produced by module allocation.
        let mut module_inst = Self::alloc_module(
            store,
            module,
            external_values,
            &global_init_values,
            &element_refs,
        )?;

        // 12. Let F be the auxiliary frame {module moduleinst, locals ε}.
        let frame = Frame::new(0, FrameState::new(Vec::new(), module_inst.clone()));

        // 13. Push the frame F to the stack.
        thread.stack_mut().push_frame(frame);

        // 14. For each element segment elem_i in module.elems whose mode is of the form
        // active {table tableidx_i, offset einstr*_i end}, do:
        for (i, element) in module.elems.iter().enumerate() {
            if let crate::wasm::ast::ElementMode::Active { table_index, offset } = &element.mode {
                // a. Let n be the length of the vector elem_i.init.
                let n = element.elements.len() as u32;

                // b. Execute the instruction sequence einstr*_i.
                Self::execute_instruction_sequence(store, &mut thread, &[offset.clone()])?;

                // c. Execute the instruction i32.const 0.
                Self::execute_const_instruction(store, &mut thread, 0)?;

                // d. Execute the instruction i32.const n.
                Self::execute_const_instruction(store, &mut thread, n)?;

                // e. Execute the instruction table.init tableidx_i i.
                Self::execute_table_init(store, &mut thread, *table_index, i as u32)?;

                // f. Execute the instruction elem.drop i.
                Self::execute_elem_drop(store, &mut thread, i as u32)?;
            }
        }

        // 15. For each element segment elem_i in module.elems whose mode is of the form declarative, do:
        for (i, element) in module.elems.iter().enumerate() {
            if let crate::wasm::ast::ElementMode::Declarative = element.mode {
                // a. Execute the instruction elem.drop i.
                Self::execute_elem_drop(store, &mut thread, i as u32)?;
            }
        }

        // 16. For each data segment data_i in module.datas whose mode is of the form
        // active {memory memidx_i, offset dinstr*_i end}, do:
        
        // Update the thread's frame state to use the final module instance
        thread.frame_state_mut().set_module(module_inst.clone());
        
        for (i, data) in module.datas.iter().enumerate() {
            if let crate::wasm::ast::DataMode::Active { memory_index, offset } = &data.mode {
                // a. Assert: memidx_i is 0.
                if *memory_index != 0 {
                    return Err(RuntimeError::Module(format!(
                        "Memory index must be 0, got {}", memory_index
                    )));
                }

                // b. Let n be the length of the vector data_i.init.
                let n = data.data.len() as u32;

                // c. Execute the instruction sequence dinstr*_i.
                Self::execute_instruction_sequence(store, &mut thread, &[offset.clone()])?;

                // d. Execute the instruction i32.const 0.
                Self::execute_const_instruction(store, &mut thread, 0)?;

                // e. Execute the instruction i32.const n.
                Self::execute_const_instruction(store, &mut thread, n)?;

                // f. Execute the instruction memory.init i.
                Self::execute_memory_init(store, &mut thread, i as u32)?;

                // g. Execute the instruction data.drop i.
                Self::execute_data_drop(store, &mut thread, i as u32)?;
            }
        }

        // 17. If the start function module.start is not empty, then:
        if let Some(start_func) = &module.start {
            // a. Let start be the start function module.start.
            // b. Execute the instruction call start.func.
            Self::execute_start_function_call(store, &mut thread, start_func.function_index)?;
        }

        // 18. Assert: due to validation, the frame F is now on the top of the stack.
        // 19. Pop the frame F from the stack.
        thread.stack_mut().pop_frame().ok_or_else(|| {
            RuntimeError::Stack("Failed to pop module frame".to_string())
        })?;

        Ok(module_inst)
    }

    /// Extracts global addresses from external values
    fn extract_global_addrs_from_external_values(
        external_values: &[ExternalValue],
    ) -> RuntimeResult<Vec<GlobalAddr>> {
        let mut global_addrs = Vec::new();
        
        for external_value in external_values {
            if let ExternalValue::Global(addr) = external_value {
                global_addrs.push(*addr);
            }
        }
        
        Ok(global_addrs)
    }

    /// Extracts function addresses from external values
    fn extract_func_addrs_from_external_values(
        external_values: &[ExternalValue],
    ) -> RuntimeResult<Vec<FuncAddr>> {
        let mut func_addrs = Vec::new();
        
        for external_value in external_values {
            if let ExternalValue::Func(addr) = external_value {
                func_addrs.push(*addr);
            }
        }
        
        Ok(func_addrs)
    }

    /// Evaluates a global initializer expression with a specific frame
    fn evaluate_global_initializer_with_frame(
        store: &mut Store,
        thread: &mut Thread,
        init_expr: &crate::wasm::ast::ConstExpr,
    ) -> RuntimeResult<super::Value> {
        super::instruction::evaluate_const_expr(store, thread, init_expr)
    }

    /// Evaluates an element expression with a specific frame
    fn evaluate_element_expression_with_frame(
        store: &mut Store,
        thread: &mut Thread,
        expr: &crate::wasm::ast::ConstExpr,
    ) -> RuntimeResult<super::Value> {
        super::instruction::evaluate_const_expr(store, thread, expr)
    }

    /// Executes a sequence of instructions
    fn execute_instruction_sequence(
        store: &mut Store,
        thread: &mut Thread,
        instructions: &[crate::wasm::ast::ConstExpr],
    ) -> RuntimeResult<()> {
        for instruction in instructions {
            // Convert ConstExpr to Instruction and execute
            let converted_instruction = Self::const_expr_to_instruction(instruction)?;
            super::instruction::DefaultInstructionExecutor.execute(
                store, 
                thread, 
                &converted_instruction
            )?;
        }
        Ok(())
    }

    /// Executes a constant instruction (i32.const)
    fn execute_const_instruction(
        store: &mut Store,
        thread: &mut Thread,
        value: u32,
    ) -> RuntimeResult<()> {
        let instruction = crate::wasm::ast::Instruction::Numeric(
            crate::wasm::ast::NumericInstruction::I32Const(value as i32)
        );
        super::instruction::DefaultInstructionExecutor.execute(store, thread, &instruction)
    }

    /// Executes table.init instruction
    fn execute_table_init(
        store: &mut Store,
        thread: &mut Thread,
        table_index: u32,
        elem_index: u32,
    ) -> RuntimeResult<()> {
        let instruction = crate::wasm::ast::Instruction::Table(
            crate::wasm::ast::TableInstruction::Init {
                table_index,
                elem_index,
            }
        );
        super::instruction::DefaultInstructionExecutor.execute(store, thread, &instruction)
    }

    /// Executes elem.drop instruction
    fn execute_elem_drop(
        store: &mut Store,
        thread: &mut Thread,
        elem_index: u32,
    ) -> RuntimeResult<()> {
        let instruction = crate::wasm::ast::Instruction::Table(
            crate::wasm::ast::TableInstruction::ElemDrop(elem_index)
        );
        super::instruction::DefaultInstructionExecutor.execute(store, thread, &instruction)
    }

    /// Executes memory.init instruction
    fn execute_memory_init(
        store: &mut Store,
        thread: &mut Thread,
        data_index: u32,
    ) -> RuntimeResult<()> {
        let instruction = crate::wasm::ast::Instruction::Memory(
            crate::wasm::ast::MemoryInstruction::MemoryInit { data_index }
        );
        super::instruction::DefaultInstructionExecutor.execute(store, thread, &instruction)
    }

    /// Executes data.drop instruction
    fn execute_data_drop(
        store: &mut Store,
        thread: &mut Thread,
        data_index: u32,
    ) -> RuntimeResult<()> {
        let instruction = crate::wasm::ast::Instruction::Memory(
            crate::wasm::ast::MemoryInstruction::DataDrop { data_index }
        );
        super::instruction::DefaultInstructionExecutor.execute(store, thread, &instruction)
    }

    /// Executes start function call
    fn execute_start_function_call(
        store: &mut Store,
        thread: &mut Thread,
        function_index: u32,
    ) -> RuntimeResult<()> {
        let instruction = crate::wasm::ast::Instruction::Control(
            crate::wasm::ast::ControlInstruction::Call { function_index }
        );
        super::instruction::DefaultInstructionExecutor.execute(store, thread, &instruction)
    }

    /// Converts a ConstExpr to an Instruction
    fn const_expr_to_instruction(
        const_expr: &crate::wasm::ast::ConstExpr,
    ) -> RuntimeResult<crate::wasm::ast::Instruction> {
        match const_expr {
            crate::wasm::ast::ConstExpr::Const(val_type, bytes) => {
                match val_type {
                    crate::wasm::ast::ValType::I32 => {
                        if bytes.len() < 4 {
                            return Err(RuntimeError::TypeError(format!(
                                "Insufficient bytes for i32 constant: expected 4, got {}", bytes.len()
                            )));
                        }
                        let value = i32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
                        Ok(crate::wasm::ast::Instruction::Numeric(
                            crate::wasm::ast::NumericInstruction::I32Const(value)
                        ))
                    }
                    crate::wasm::ast::ValType::I64 => {
                        if bytes.len() < 8 {
                            return Err(RuntimeError::TypeError(format!(
                                "Insufficient bytes for i64 constant: expected 8, got {}", bytes.len()
                            )));
                        }
                        let value = i64::from_le_bytes([
                            bytes[0], bytes[1], bytes[2], bytes[3],
                            bytes[4], bytes[5], bytes[6], bytes[7]
                        ]);
                        Ok(crate::wasm::ast::Instruction::Numeric(
                            crate::wasm::ast::NumericInstruction::I64Const(value)
                        ))
                    }
                    crate::wasm::ast::ValType::F32 => {
                        if bytes.len() < 4 {
                            return Err(RuntimeError::TypeError(format!(
                                "Insufficient bytes for f32 constant: expected 4, got {}", bytes.len()
                            )));
                        }
                        let value = f32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
                        Ok(crate::wasm::ast::Instruction::Numeric(
                            crate::wasm::ast::NumericInstruction::F32Const(value)
                        ))
                    }
                    crate::wasm::ast::ValType::F64 => {
                        if bytes.len() < 8 {
                            return Err(RuntimeError::TypeError(format!(
                                "Insufficient bytes for f64 constant: expected 8, got {}", bytes.len()
                            )));
                        }
                        let value = f64::from_le_bytes([
                            bytes[0], bytes[1], bytes[2], bytes[3],
                            bytes[4], bytes[5], bytes[6], bytes[7]
                        ]);
                        Ok(crate::wasm::ast::Instruction::Numeric(
                            crate::wasm::ast::NumericInstruction::F64Const(value)
                        ))
                    }
                    _ => Err(RuntimeError::TypeError(format!(
                        "Unsupported constant type: {:?}", val_type
                    ))),
                }
            }
            crate::wasm::ast::ConstExpr::GlobalGet(global_index) => {
                Ok(crate::wasm::ast::Instruction::Variable(
                    crate::wasm::ast::VariableInstruction::GlobalGet(*global_index)
                ))
            }
            crate::wasm::ast::ConstExpr::RefFunc(func_index) => {
                Ok(crate::wasm::ast::Instruction::Control(
                    crate::wasm::ast::ControlInstruction::RefFunc(*func_index)
                ))
            }
            crate::wasm::ast::ConstExpr::RefNull(ref_type) => {
                Ok(crate::wasm::ast::Instruction::Control(
                    crate::wasm::ast::ControlInstruction::RefNull(*ref_type)
                ))
            }
        }
    }

    /// Converts an import to an external type
    fn import_to_external_type(import: &Import) -> RuntimeResult<ExternalType> {
        // Convert ast::ExternalType to typing::ExternalType
        let external_type = match &import.ty {
            crate::wasm::ast::ExternalType::Func(func_type) => ExternalType::Func(func_type.clone()),
            crate::wasm::ast::ExternalType::Table(table_type) => ExternalType::Table(table_type.clone()),
            crate::wasm::ast::ExternalType::Memory(memory_type) => ExternalType::Memory(memory_type.clone()),
            crate::wasm::ast::ExternalType::Global(global_type) => ExternalType::Global(global_type.clone()),
        };
        Ok(external_type)
    }

    /// Validates that external values match the module's import requirements
    fn validate_imports(
        module: &Module,
        external_values: &[ExternalValue],
        store: &mut Store,
    ) -> RuntimeResult<()> {
        if external_values.len() != module.imports.len() {
            return Err(RuntimeError::Module(format!(
                "Import count mismatch: expected {} imports, got {} external values",
                module.imports.len(),
                external_values.len()
            )));
        }
        
        for (i, (import, external_value)) in module.imports.iter().zip(external_values.iter()).enumerate() {
            let import_type = Self::import_to_external_type(import)?;
            external_value.validate_external_type(store, &import_type).map_err(|e| {
                RuntimeError::Module(format!("Import {}: {}", i, e))
            })?;
        }
        
        Ok(())
    }

    /// Evaluates a global initializer expression
    fn evaluate_global_initializer(
        store: &mut Store,
        init_expr: &crate::wasm::ast::ConstExpr,
    ) -> RuntimeResult<super::Value> {
        let mut thread = super::Thread::new(
            super::FrameState::new(Vec::new(), ModuleInstance::new()),
            Vec::new(),
        );
        
        super::instruction::evaluate_const_expr(store, &mut thread, init_expr)
    }

    /// Evaluates element expressions to get reference vectors
    fn evaluate_element_expressions(
        store: &mut Store,
        elements: &[crate::wasm::ast::ConstExpr],
    ) -> RuntimeResult<Vec<super::Value>> {
        let mut thread = super::Thread::new(
            super::FrameState::new(Vec::new(), ModuleInstance::new()),
            Vec::new(),
        );
        
        super::instruction::evaluate_const_exprs(store, &mut thread, elements)
    }

    /// Extracts function addresses from external values
    /// 
    /// # Specification (4.5 Modules - External Value Extraction)
    /// 
    /// funcs(externval*_ex) = (moduleinst.funcaddrs[x])* (where x* = funcs(export*))
    /// 
    /// This extracts function addresses from external values based on function exports.
    /// 
    /// # Arguments
    /// 
    /// * `external_values` - The external values to extract from
    /// * `exports` - The exports to determine which external values are functions
    /// 
    /// # Returns
    /// 
    /// * `RuntimeResult<Vec<FuncAddr>>` - The extracted function addresses
    pub fn extract_func_addrs(
        external_values: &[ExternalValue],
        exports: &[crate::wasm::ast::Export],
    ) -> RuntimeResult<Vec<FuncAddr>> {
        let mut func_addrs = Vec::new();
        
        for export in exports {
            if export.kind == crate::wasm::ast::ExternKind::Func {
                let external_value = external_values.get(export.index as usize).ok_or_else(|| {
                    RuntimeError::Module(format!("External value at index {} not found", export.index))
                })?;
                
                if let ExternalValue::Func(addr) = external_value {
                    func_addrs.push(*addr);
                } else {
                    return Err(RuntimeError::Module(format!(
                        "Expected function external value at index {}, got {:?}",
                        export.index, external_value
                    )));
                }
            }
        }
        
        Ok(func_addrs)
    }

    /// Extracts table addresses from external values
    /// 
    /// # Specification (4.5 Modules - External Value Extraction)
    /// 
    /// tables(externval*_ex) = (moduleinst.tableaddrs[x])* (where x* = tables(export*))
    /// 
    /// This extracts table addresses from external values based on table exports.
    /// 
    /// # Arguments
    /// 
    /// * `external_values` - The external values to extract from
    /// * `exports` - The exports to determine which external values are tables
    /// 
    /// # Returns
    /// 
    /// * `RuntimeResult<Vec<TableAddr>>` - The extracted table addresses
    pub fn extract_table_addrs(
        external_values: &[ExternalValue],
        exports: &[crate::wasm::ast::Export],
    ) -> RuntimeResult<Vec<TableAddr>> {
        let mut table_addrs = Vec::new();
        
        for export in exports {
            if export.kind == crate::wasm::ast::ExternKind::Table {
                let external_value = external_values.get(export.index as usize).ok_or_else(|| {
                    RuntimeError::Module(format!("External value at index {} not found", export.index))
                })?;
                
                if let ExternalValue::Table(addr) = external_value {
                    table_addrs.push(*addr);
                } else {
                    return Err(RuntimeError::Module(format!(
                        "Expected table external value at index {}, got {:?}",
                        export.index, external_value
                    )));
                }
            }
        }
        
        Ok(table_addrs)
    }

    /// Extracts memory addresses from external values
    /// 
    /// # Specification (4.5 Modules - External Value Extraction)
    /// 
    /// mems(externval*_ex) = (moduleinst.memaddrs[x])* (where x* = mems(export*))
    /// 
    /// This extracts memory addresses from external values based on memory exports.
    /// 
    /// # Arguments
    /// 
    /// * `external_values` - The external values to extract from
    /// * `exports` - The exports to determine which external values are memories
    /// 
    /// # Returns
    /// 
    /// * `RuntimeResult<Vec<MemAddr>>` - The extracted memory addresses
    pub fn extract_mem_addrs(
        external_values: &[ExternalValue],
        exports: &[crate::wasm::ast::Export],
    ) -> RuntimeResult<Vec<MemAddr>> {
        let mut mem_addrs = Vec::new();
        
        for export in exports {
            if export.kind == crate::wasm::ast::ExternKind::Memory {
                let external_value = external_values.get(export.index as usize).ok_or_else(|| {
                    RuntimeError::Module(format!("External value at index {} not found", export.index))
                })?;
                
                if let ExternalValue::Memory(addr) = external_value {
                    mem_addrs.push(*addr);
                } else {
                    return Err(RuntimeError::Module(format!(
                        "Expected memory external value at index {}, got {:?}",
                        export.index, external_value
                    )));
                }
            }
        }
        
        Ok(mem_addrs)
    }

    /// Extracts global addresses from external values
    /// 
    /// # Specification (4.5 Modules - External Value Extraction)
    /// 
    /// globals(externval*_ex) = (moduleinst.globaladdrs[x])* (where x* = globals(export*))
    /// 
    /// This extracts global addresses from external values based on global exports.
    /// 
    /// # Arguments
    /// 
    /// * `external_values` - The external values to extract from
    /// * `exports` - The exports to determine which external values are globals
    /// 
    /// # Returns
    /// 
    /// * `RuntimeResult<Vec<GlobalAddr>>` - The extracted global addresses
    pub fn extract_global_addrs(
        external_values: &[ExternalValue],
        exports: &[crate::wasm::ast::Export],
    ) -> RuntimeResult<Vec<GlobalAddr>> {
        let mut global_addrs = Vec::new();
        
        for export in exports {
            if export.kind == crate::wasm::ast::ExternKind::Global {
                let external_value = external_values.get(export.index as usize).ok_or_else(|| {
                    RuntimeError::Module(format!("External value at index {} not found", export.index))
                })?;
                
                if let ExternalValue::Global(addr) = external_value {
                    global_addrs.push(*addr);
                } else {
                    return Err(RuntimeError::Module(format!(
                        "Expected global external value at index {}, got {:?}",
                        export.index, external_value
                    )));
                }
            }
        }
        
        Ok(global_addrs)
    }
}

impl fmt::Display for ModuleInstance {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "ModuleInstance {{")?;
        writeln!(f, "  types: {} entries", self.type_count())?;
        writeln!(f, "  funcs: {} entries", self.func_count())?;
        writeln!(f, "  tables: {} entries", self.table_count())?;
        writeln!(f, "  memories: {} entries", self.mem_count())?;
        writeln!(f, "  globals: {} entries", self.global_count())?;
        writeln!(f, "  elements: {} entries", self.elem_count())?;
        writeln!(f, "  data: {} entries", self.data_count())?;
        writeln!(f, "  exports:")?;
        for (name, export) in &self.exports {
            writeln!(f, "    {}: {}", name, export.value)?;
        }
        write!(f, "}}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::wasm::ast::{Module, FuncType, ValType, Limits, MemoryType, TableType, GlobalType, Mutability};

    #[test]
    fn test_instantiate_empty_module() {
        // Create an empty module
        let module = Module::new();
        let mut store = Store::new();
        let external_values = Vec::new();

        // This should succeed for an empty module
        let result = ModuleInstance::instantiate(&mut store, &module, &external_values);
        assert!(result.is_ok());
    }

    #[test]
    fn test_instantiate_module_with_imports() {
        // Create a module with imports
        let mut module = Module::new();
        
        // Add a function type
        let func_type = FuncType::new(vec![ValType::I32], vec![ValType::I32]);
        module.types.push(func_type);
        
        // Add an import
        let import = crate::wasm::ast::Import::new(
            "env".to_string(),
            "func".to_string(),
            crate::wasm::ast::ExternalType::Func(FuncType::new(vec![ValType::I32], vec![ValType::I32]))
        );
        module.imports.push(import);

        let mut store = Store::new();
        
        // Create a host function
        let host_func = crate::wasm::runtime::HostFunc::new(
            FuncType::new(vec![ValType::I32], vec![ValType::I32]),
            |_store, _args| Ok(vec![crate::wasm::runtime::Value::I32(42)])
        );
        
        // Allocate the host function in the store
        let func_addr = crate::wasm::runtime::Allocation::alloc_host_func(
            &mut store,
            FuncType::new(vec![ValType::I32], vec![ValType::I32]),
            host_func
        ).unwrap();
        
        let external_values = vec![ExternalValue::Func(func_addr)];

        // This should succeed
        let result = ModuleInstance::instantiate(&mut store, &module, &external_values);
        assert!(result.is_ok());
    }
}

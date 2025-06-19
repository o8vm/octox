//! WebAssembly Allocation Module
//! 
//! This module implements the allocation functions for WebAssembly as described in 4.5.3 Allocation.
//! It provides functions for allocating new instances of functions, tables, memories, and globals.

use alloc::format;
use alloc::vec::Vec;
use alloc::string::ToString;

use crate::wasm::ast::{Function, FuncType, TableType, MemoryType, GlobalType, ValType};
use crate::wasm::runtime::{
    Store,
    FuncInstance,
    ModuleInstance,
    RuntimeResult,
    RuntimeError,
    address::{FuncAddr, TableAddr, MemAddr, GlobalAddr, ElemAddr, DataAddr},
    instruction::evaluate_const_expr,
    table::TableInstance,
    memory::MemoryInstance,
    global::GlobalInstance,
};

/// Allocation context
/// 
/// Provides methods for allocating new instances in a store as defined in 4.5.3 Allocation.
/// 
/// # Multiple Allocation Notation (allocx*)
/// 
/// The notation allocx* is shorthand for multiple allocations of object kind X, defined as follows:
/// 
/// allocx*(S0, X_n, ...) = S_n, a_n
/// where for all i < n:
/// S_{i+1}, a_n[i] = allocx(S_i, X_n[i], ...)
/// 
/// Moreover, if the dots ... are a sequence A_n (as for globals or tables), then the elements
/// of this sequence are passed to the allocation function pointwise.
/// 
/// Examples:
/// - allocfunc*(S0, func_n, moduleinst) = S_n, a_n
/// - alloctable*(S0, (table.type)*, (ref.null t)*) = S_n, a_n
/// - allocmem*(S0, (mem.type)*) = S_n, a_n
/// - allocglobal*(S0, (global.type)*, val*) = S_n, a_n
/// - allocelem*(S0, (elem.type)*, (ref*)*) = S_n, a_n
/// - allocdata*(S0, (data.init)*) = S_n, a_n
pub struct Allocation;

impl Allocation {
    /// Allocates a new function instance in a store
    /// 
    /// # Specification (4.5.3 Allocation - Functions)
    /// 
    /// 1. Let func be the function to allocate and moduleinst its module instance.
    /// 2. Let a be the first free function address in S.
    /// 3. Let functype be the function type moduleinst.types[func.type].
    /// 4. Let funcinst be the function instance {type functype, module moduleinst, code func}.
    /// 5. Append funcinst to the funcs of S.
    /// 6. Return a.
    /// 
    /// allocfunc(S, func, moduleinst) = S', funcaddr
    /// where:
    /// funcaddr = |S.funcs|
    /// functype = moduleinst.types[func.type]
    /// funcinst = {type functype, module moduleinst, code func}
    /// S' = S ⊕ {funcs funcinst}
    pub fn alloc_func(
        store: &mut Store,
        func: &Function,
        module_inst: &ModuleInstance,
    ) -> RuntimeResult<FuncAddr> {
        // 1. Let func be the function to allocate and moduleinst its module instance.
        // (func and module_inst are provided as parameters)
        
        // 2. Let a be the first free function address in S.
        let func_addr = FuncAddr::new(store.func_count() as u32);
        
        // 3. Let functype be the function type moduleinst.types[func.type].
        let func_type = module_inst.types.get(func.type_index as usize).ok_or_else(|| {
            RuntimeError::TypeError(format!(
                "Function type at index {} does not exist in module instance",
                func.type_index
            ))
        })?;
        
        // 4. Let funcinst be the function instance {type functype, module moduleinst, code func}.
        let func_instance = FuncInstance::wasm(
            func_type.clone(),
            module_inst.clone(),
            func.clone(),
        );
        
        // 5. Append funcinst to the funcs of S.
        store.add_func(func_instance);
        
        // 6. Return a.
        Ok(func_addr)
    }

    /// Allocates a new table instance in a store
    /// 
    /// # Specification (4.5.3 Allocation - Tables)
    /// 
    /// 1. Let tabletype be the table type to allocate and ref the initialization value.
    /// 2. Let ({min n, max m?} reftype) be the structure of table type tabletype.
    /// 3. Let a be the first free table address in S.
    /// 4. Let tableinst be the table instance {type tabletype, elem ref n} with n elements set to ref.
    /// 5. Append tableinst to the tables of S.
    /// 6. Return a.
    /// 
    /// alloctable(S, tabletype, ref) = S', tableaddr
    /// where:
    /// tabletype = {min n, max m?} reftype
    /// tableaddr = |S.tables|
    /// tableinst = {type tabletype, elem ref n}
    /// S' = S ⊕ {tables tableinst}
    pub fn alloc_table(
        store: &mut Store,
        table_type: &TableType,
        init_ref: crate::wasm::runtime::TableElement,
    ) -> RuntimeResult<TableAddr> {
        // 1. Let tabletype be the table type to allocate and ref the initialization value.
        // (table_type and init_ref are provided as parameters)
        
        // 2. Let ({min n, max m?} reftype) be the structure of table type tabletype.
        // (table_type already contains this structure)
        
        // 3. Let a be the first free table address in S.
        let table_addr = TableAddr::new(store.table_count() as u32);
        
        // 4. Let tableinst be the table instance {type tabletype, elem ref n} with n elements set to ref.
        let table_instance = TableInstance::new_with_init(table_type.clone(), init_ref);
        
        // 5. Append tableinst to the tables of S.
        store.add_table(table_instance);
        
        // 6. Return a.
        Ok(table_addr)
    }

    /// Allocates a new table instance in a store with default initialization
    /// 
    /// This is a convenience function that uses null references as the default initialization value.
    /// 
    /// # Arguments
    /// 
    /// * `store` - The store to allocate the table in
    /// * `table_type` - The table type
    /// 
    /// # Returns
    /// 
    /// * `RuntimeResult<TableAddr>` - The allocated table address
    pub fn alloc_table_default(
        store: &mut Store,
        table_type: &TableType,
    ) -> RuntimeResult<TableAddr> {
        // Create default initialization value based on table element type
        let init_ref = match table_type.element_type {
            crate::wasm::ast::ValType::FuncRef => {
                crate::wasm::runtime::TableElement::funcref(None)
            }
            crate::wasm::ast::ValType::ExternRef => {
                crate::wasm::runtime::TableElement::externref(None)
            }
            _ => {
                return Err(RuntimeError::TypeError(format!(
                    "Invalid table element type: {:?}",
                    table_type.element_type
                )));
            }
        };
        
        Self::alloc_table(store, table_type, init_ref)
    }

    /// Allocates a new memory instance in a store
    /// 
    /// # Specification (4.5.3 Allocation - Memories)
    /// 
    /// 1. Let mem be the memory to allocate.
    /// 2. Let a be the first free memory address in S.
    /// 3. Let meminst be the memory instance {type mem.type, data mem.data}.
    /// 4. Append meminst to the mems of S.
    /// 5. Return a.
    /// 
    /// allocmem(S, mem) = S', memaddr
    /// where:
    /// memaddr = |S.mems|
    /// meminst = {type mem.type, data mem.data}
    /// S' = S ⊕ {mems meminst}
    pub fn alloc_memory(
        store: &mut Store,
        memory_type: &MemoryType,
    ) -> RuntimeResult<MemAddr> {
        // 1. Let mem be the memory to allocate.
        // (memory_type is provided as parameter)
        
        // 2. Let a be the first free memory address in S.
        let mem_addr = MemAddr::new(store.mem_count() as u32);
        
        // 3. Let meminst be the memory instance {type mem.type, data mem.data}.
        let memory_instance = MemoryInstance::new(memory_type.clone());
        
        // 4. Append meminst to the mems of S.
        store.add_memory(memory_instance);
        
        // 5. Return a.
        Ok(mem_addr)
    }

    /// Allocates a new global instance in a store
    /// 
    /// # Specification (4.5.3 Allocation - Globals)
    /// 
    /// 1. Let global be the global to allocate.
    /// 2. Let a be the first free global address in S.
    /// 3. Let globalinst be the global instance {type global.type, value global.init}.
    /// 4. Append globalinst to the globals of S.
    /// 5. Return a.
    /// 
    /// allocglobal(S, global) = S', globaladdr
    /// where:
    /// globaladdr = |S.globals|
    /// globalinst = {type global.type, value global.init}
    /// S' = S ⊕ {globals globalinst}
    pub fn alloc_global(
        store: &mut Store,
        global_type: &GlobalType,
        init_expr: &crate::wasm::ast::ConstExpr,
    ) -> RuntimeResult<GlobalAddr> {
        // 1. Let global be the global to allocate.
        // (global_type and init_expr are provided as parameters)
        
        // 2. Let a be the first free global address in S.
        let global_addr = GlobalAddr::new(store.global_count() as u32);
        
        // 3. Let globalinst be the global instance {type global.type, value global.init}.
        // First, evaluate the initialization expression
        let mut thread = crate::wasm::runtime::Thread::new(
            crate::wasm::runtime::FrameState::new(
                Vec::new(),
                ModuleInstance::new(),
            ),
            Vec::new(),
        );
        let init_value = evaluate_const_expr(store, &mut thread, init_expr)?;
        
        let global_instance = GlobalInstance::new(global_type.clone(), init_value);
        
        // 4. Append globalinst to the globals of S.
        store.add_global(global_instance);
        
        // 5. Return a.
        Ok(global_addr)
    }

    /// Allocates multiple function instances in a store
    /// 
    /// # Specification (4.5.3 Allocation - Multiple Functions)
    /// 
    /// allocfunc*(S0, func_n, ...) = S_n, a_n
    /// where for all i < n:
    /// S_{i+1}, a_n[i] = allocfunc(S_i, func_n[i], ...)
    /// 
    /// This is a shorthand for multiple allocations of function instances.
    /// 
    /// # Arguments
    /// 
    /// * `store` - The store to allocate functions in
    /// * `funcs` - The functions to allocate
    /// * `module_inst` - The module instance for the functions
    /// 
    /// # Returns
    /// 
    /// * `RuntimeResult<Vec<FuncAddr>>` - The allocated function addresses
    pub fn alloc_funcs(
        store: &mut Store,
        funcs: &[Function],
        module_inst: &ModuleInstance,
    ) -> RuntimeResult<Vec<FuncAddr>> {
        let mut func_addrs = Vec::new();
        
        for func in funcs {
            let func_addr = Self::alloc_func(store, func, module_inst)?;
            func_addrs.push(func_addr);
        }
        
        Ok(func_addrs)
    }

    /// Allocates multiple table instances in a store
    /// 
    /// # Specification (4.5.3 Allocation - Multiple Tables)
    /// 
    /// alloctable*(S0, (table.type)*, (ref.null t)*) = S_n, a_n
    /// where for all i < n:
    /// S_{i+1}, a_n[i] = alloctable(S_i, (table.type)*[i], (ref.null t)*[i])
    /// 
    /// This is a shorthand for multiple allocations of table instances.
    /// 
    /// # Arguments
    /// 
    /// * `store` - The store to allocate tables in
    /// * `table_types` - The table types to allocate
    /// 
    /// # Returns
    /// 
    /// * `RuntimeResult<Vec<TableAddr>>` - The allocated table addresses
    pub fn alloc_tables(
        store: &mut Store,
        table_types: &[TableType],
    ) -> RuntimeResult<Vec<TableAddr>> {
        let mut table_addrs = Vec::new();
        
        for table_type in table_types {
            let table_addr = Self::alloc_table_default(store, table_type)?;
            table_addrs.push(table_addr);
        }
        
        Ok(table_addrs)
    }

    /// Allocates multiple memory instances in a store
    /// 
    /// # Specification (4.5.3 Allocation - Multiple Memories)
    /// 
    /// allocmem*(S0, (mem.type)*) = S_n, a_n
    /// where for all i < n:
    /// S_{i+1}, a_n[i] = allocmem(S_i, (mem.type)*[i])
    /// 
    /// This is a shorthand for multiple allocations of memory instances.
    /// 
    /// # Arguments
    /// 
    /// * `store` - The store to allocate memories in
    /// * `memory_types` - The memory types to allocate
    /// 
    /// # Returns
    /// 
    /// * `RuntimeResult<Vec<MemAddr>>` - The allocated memory addresses
    pub fn alloc_memories(
        store: &mut Store,
        memory_types: &[MemoryType],
    ) -> RuntimeResult<Vec<MemAddr>> {
        let mut mem_addrs = Vec::new();
        
        for memory_type in memory_types {
            let mem_addr = Self::alloc_memory(store, memory_type)?;
            mem_addrs.push(mem_addr);
        }
        
        Ok(mem_addrs)
    }

    /// Allocates multiple global instances in a store
    /// 
    /// # Specification (4.5.3 Allocation - Multiple Globals)
    /// 
    /// allocglobal*(S0, (global.type)*, val*) = S_n, a_n
    /// where for all i < n:
    /// S_{i+1}, a_n[i] = allocglobal(S_i, (global.type)*[i], val*[i])
    /// 
    /// This is a shorthand for multiple allocations of global instances.
    /// 
    /// # Arguments
    /// 
    /// * `store` - The store to allocate globals in
    /// * `global_types` - The global types to allocate
    /// * `init_values` - The initialization values for the globals
    /// 
    /// # Returns
    /// 
    /// * `RuntimeResult<Vec<GlobalAddr>>` - The allocated global addresses
    pub fn alloc_globals(
        store: &mut Store,
        global_types: &[GlobalType],
        init_values: &[crate::wasm::runtime::Value],
    ) -> RuntimeResult<Vec<GlobalAddr>> {
        if global_types.len() != init_values.len() {
            return Err(RuntimeError::TypeError(format!(
                "Global types count ({}) does not match initialization values count ({})",
                global_types.len(),
                init_values.len()
            )));
        }
        
        let mut global_addrs = Vec::new();
        
        for (i, (global_type, init_value)) in global_types.iter().zip(init_values.iter()).enumerate() {
            // Create a global instance directly with the provided value
            let global_addr = GlobalAddr::new(store.global_count() as u32);
            let global_instance = crate::wasm::runtime::GlobalInstance::new(global_type.clone(), init_value.clone());
            store.add_global(global_instance);
            global_addrs.push(global_addr);
        }
        
        Ok(global_addrs)
    }

    /// Allocates a new host function instance in a store
    /// 
    /// # Specification (4.5.3 Allocation - Host Functions)
    /// 
    /// 1. Let hostfunc be the host function to allocate and functype its function type.
    /// 2. Let a be the first free function address in S.
    /// 3. Let funcinst be the function instance {type functype, hostcode hostfunc}.
    /// 4. Append funcinst to the funcs of S.
    /// 5. Return a.
    /// 
    /// allochostfunc(S, functype, hostfunc) = S', funcaddr
    /// where:
    /// funcaddr = |S.funcs|
    /// funcinst = {type functype, hostcode hostfunc}
    /// S' = S ⊕ {funcs funcinst}
    /// 
    /// Note: Host functions are never allocated by the WebAssembly semantics itself,
    /// but may be allocated by the embedder.
    pub fn alloc_host_func(
        store: &mut Store,
        func_type: FuncType,
        host_func: crate::wasm::runtime::HostFunc,
    ) -> RuntimeResult<FuncAddr> {
        // 1. Let hostfunc be the host function to allocate and functype its function type.
        // (host_func and func_type are provided as parameters)
        
        // 2. Let a be the first free function address in S.
        let func_addr = FuncAddr::new(store.func_count() as u32);
        
        // 3. Let funcinst be the function instance {type functype, hostcode hostfunc}.
        let func_instance = FuncInstance::host(func_type, host_func);
        
        // 4. Append funcinst to the funcs of S.
        store.add_func(func_instance);
        
        // 5. Return a.
        Ok(func_addr)
    }

    /// Allocates a new element instance in a store
    /// 
    /// # Specification (4.5.3 Allocation - Element segments)
    /// 
    /// 1. Let reftype be the elements' type and ref* the vector of references to allocate.
    /// 2. Let a be the first free element address in S.
    /// 3. Let eleminst be the element instance {type reftype, elem ref*}.
    /// 4. Append eleminst to the elems of S.
    /// 5. Return a.
    /// 
    /// allocelem(S, reftype, ref*) = S', elemaddr
    /// where:
    /// elemaddr = |S.elems|
    /// eleminst = {type reftype, elem ref*}
    /// S' = S ⊕ {elems eleminst}
    pub fn alloc_elem(
        store: &mut Store,
        ref_type: ValType,
        refs: Vec<crate::wasm::runtime::Value>,
    ) -> RuntimeResult<ElemAddr> {
        // 1. Let reftype be the elements' type and ref* the vector of references to allocate.
        // (ref_type and refs are provided as parameters)
        
        // 2. Let a be the first free element address in S.
        let elem_addr = ElemAddr::new(store.elem_count() as u32);
        
        // 3. Let eleminst be the element instance {type reftype, elem ref*}.
        let elem_instance = crate::wasm::runtime::ElementInstance::with_elements(ref_type, refs)
            .map_err(|e| RuntimeError::Element(format!("Failed to create element instance: {}", e)))?;
        
        // 4. Append eleminst to the elems of S.
        store.add_elem(elem_instance);
        
        // 5. Return a.
        Ok(elem_addr)
    }

    /// Allocates a new element instance with an empty vector of references
    /// 
    /// This is a convenience function for allocating element instances that will be
    /// populated later.
    /// 
    /// # Arguments
    /// 
    /// * `store` - The store to allocate the element instance in
    /// * `ref_type` - The type of references to be stored
    /// 
    /// # Returns
    /// 
    /// * `RuntimeResult<ElemAddr>` - The allocated element address
    pub fn alloc_elem_empty(
        store: &mut Store,
        ref_type: ValType,
    ) -> RuntimeResult<ElemAddr> {
        Self::alloc_elem(store, ref_type, Vec::new())
    }

    /// Allocates a new data instance in a store
    /// 
    /// # Specification (4.5.3 Allocation - Data segments)
    /// 
    /// 1. Let b* be the vector of bytes to allocate.
    /// 2. Let a be the first free data address in S.
    /// 3. Let datainst be the data instance {data b*}.
    /// 4. Append datainst to the datas of S.
    /// 5. Return a.
    /// 
    /// allocdata(S, b*) = S', dataaddr
    /// where:
    /// dataaddr = |S.datas|
    /// datainst = {data b*}
    /// S' = S ⊕ {datas datainst}
    pub fn alloc_data(
        store: &mut Store,
        bytes: Vec<u8>,
    ) -> RuntimeResult<DataAddr> {
        // 1. Let b* be the vector of bytes to allocate.
        // (bytes are provided as parameter)
        
        // 2. Let a be the first free data address in S.
        let data_addr = DataAddr::new(store.data_count() as u32);
        
        // 3. Let datainst be the data instance {data b*}.
        let data_instance = crate::wasm::runtime::DataInstance::with_data(bytes);
        
        // 4. Append datainst to the datas of S.
        store.add_data(data_instance);
        
        // 5. Return a.
        Ok(data_addr)
    }

    /// Allocates a new data instance with an empty vector of bytes
    /// 
    /// This is a convenience function for allocating data instances that will be
    /// populated later.
    /// 
    /// # Arguments
    /// 
    /// * `store` - The store to allocate the data instance in
    /// 
    /// # Returns
    /// 
    /// * `RuntimeResult<DataAddr>` - The allocated data address
    pub fn alloc_data_empty(
        store: &mut Store,
    ) -> RuntimeResult<DataAddr> {
        Self::alloc_data(store, Vec::new())
    }

    /// Allocates multiple element instances in a store
    /// 
    /// # Specification (4.5.3 Allocation - Multiple Element Segments)
    /// 
    /// allocelem*(S0, (elem.type)*, (ref*)*) = S_n, a_n
    /// where for all i < n:
    /// S_{i+1}, a_n[i] = allocelem(S_i, (elem.type)*[i], (ref*)*[i])
    /// 
    /// This is a shorthand for multiple allocations of element instances.
    /// 
    /// # Arguments
    /// 
    /// * `store` - The store to allocate elements in
    /// * `ref_types` - The reference types for the elements
    /// * `ref_vectors` - The reference vectors for the elements
    /// 
    /// # Returns
    /// 
    /// * `RuntimeResult<Vec<ElemAddr>>` - The allocated element addresses
    pub fn alloc_elems(
        store: &mut Store,
        ref_types: &[ValType],
        ref_vectors: &[Vec<crate::wasm::runtime::Value>],
    ) -> RuntimeResult<Vec<ElemAddr>> {
        if ref_types.len() != ref_vectors.len() {
            return Err(RuntimeError::TypeError(format!(
                "Reference types count ({}) does not match reference vectors count ({})",
                ref_types.len(),
                ref_vectors.len()
            )));
        }
        
        let mut elem_addrs = Vec::new();
        
        for (ref_type, refs) in ref_types.iter().zip(ref_vectors.iter()) {
            let elem_addr = Self::alloc_elem(store, *ref_type, refs.clone())?;
            elem_addrs.push(elem_addr);
        }
        
        Ok(elem_addrs)
    }

    /// Allocates multiple data instances in a store
    /// 
    /// # Specification (4.5.3 Allocation - Multiple Data Segments)
    /// 
    /// allocdata*(S0, (data.init)*) = S_n, a_n
    /// where for all i < n:
    /// S_{i+1}, a_n[i] = allocdata(S_i, (data.init)*[i])
    /// 
    /// This is a shorthand for multiple allocations of data instances.
    /// 
    /// # Arguments
    /// 
    /// * `store` - The store to allocate data in
    /// * `data_bytes` - The byte vectors for the data segments
    /// 
    /// # Returns
    /// 
    /// * `RuntimeResult<Vec<DataAddr>>` - The allocated data addresses
    pub fn alloc_datas(
        store: &mut Store,
        data_bytes: &[Vec<u8>],
    ) -> RuntimeResult<Vec<DataAddr>> {
        let mut data_addrs = Vec::new();
        
        for bytes in data_bytes {
            let data_addr = Self::alloc_data(store, bytes.clone())?;
            data_addrs.push(data_addr);
        }
        
        Ok(data_addrs)
    }
} 
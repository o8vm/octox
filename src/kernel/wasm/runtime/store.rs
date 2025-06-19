use alloc::vec::Vec;
use alloc::format;
use core::fmt;

use crate::wasm::ast::{MemoryType, TableType};
use crate::wasm::runtime::function::FuncInstance;
use crate::wasm::runtime::table::{TableInstance};
use crate::wasm::runtime::memory::MemoryInstance;
use crate::wasm::runtime::value::Value;
use crate::wasm::ast::{FuncType, GlobalType};
use crate::wasm::runtime::global::GlobalInstance;
use crate::wasm::runtime::element::ElementInstance;
use crate::wasm::runtime::data::DataInstance;
use crate::wasm::runtime::{
    RuntimeResult,
    RuntimeError,
    RuntimeConfig,
    address::FuncAddr,
    frame::{Frame, FrameState},
    stack::Stack,
    typing::ValueTyping,
};

/// WebAssembly store
/// 
/// The store represents all global state that can be manipulated by WebAssembly programs.
/// It consists of the runtime representation of all instances of functions, tables,
/// memories, and globals, element segments, and data segments.
#[derive(Debug)]
pub struct Store {
    /// Function instances
    pub funcs: Vec<FuncInstance>,
    /// Table instances
    pub tables: Vec<TableInstance>,
    /// Memory instances
    pub mems: Vec<MemoryInstance>,
    /// Global instances
    pub globals: Vec<GlobalInstance>,
    /// Element instances
    pub elems: Vec<ElementInstance>,
    /// Data instances
    pub datas: Vec<DataInstance>,
    /// Runtime configuration
    pub config: RuntimeConfig,
}

impl Store {
    /// Creates a new empty store
    pub fn new() -> Self {
        Self {
            funcs: Vec::new(),
            tables: Vec::new(),
            mems: Vec::new(),
            globals: Vec::new(),
            elems: Vec::new(),
            datas: Vec::new(),
            config: RuntimeConfig::default(),
        }
    }

    /// Creates a new store with the given configuration
    pub fn with_config(config: RuntimeConfig) -> Self {
        Self {
            funcs: Vec::new(),
            tables: Vec::new(),
            mems: Vec::new(),
            globals: Vec::new(),
            elems: Vec::new(),
            datas: Vec::new(),
            config,
        }
    }

    /// Returns a reference to the runtime configuration
    pub fn config(&self) -> &RuntimeConfig {
        &self.config
    }

    /// Returns a mutable reference to the runtime configuration
    pub fn config_mut(&mut self) -> &mut RuntimeConfig {
        &mut self.config
    }

    /// Returns the number of function instances
    pub fn func_count(&self) -> usize {
        self.funcs.len()
    }

    /// Returns the number of table instances
    pub fn table_count(&self) -> usize {
        self.tables.len()
    }

    /// Returns the number of memory instances
    pub fn mem_count(&self) -> usize {
        self.mems.len()
    }

    /// Returns the number of global instances
    pub fn global_count(&self) -> usize {
        self.globals.len()
    }

    /// Returns the number of element instances
    pub fn elem_count(&self) -> usize {
        self.elems.len()
    }

    /// Returns the number of data instances
    pub fn data_count(&self) -> usize {
        self.datas.len()
    }

    /// Adds a function instance to the store
    pub fn add_func(&mut self, func: FuncInstance) -> u32 {
        let idx = self.funcs.len() as u32;
        self.funcs.push(func);
        idx
    }

    /// Adds a table instance to the store
    pub fn add_table(&mut self, table: TableInstance) -> u32 {
        let idx = self.tables.len() as u32;
        self.tables.push(table);
        idx
    }

    /// Creates and adds a new table instance to the store
    pub fn create_table(&mut self, ty: TableType) -> u32 {
        self.add_table(TableInstance::new(ty))
    }

    /// Returns a reference to the table instance at the given index
    pub fn get_table(&self, index: u32) -> Option<&TableInstance> {
        self.tables.get(index as usize)
    }

    /// Returns a mutable reference to the table instance at the given index
    pub fn get_table_mut(&mut self, index: u32) -> Option<&mut TableInstance> {
        self.tables.get_mut(index as usize)
    }

    /// Adds a memory instance to the store
    /// 
    /// # Arguments
    /// 
    /// * `memory` - The memory instance to add
    /// 
    /// # Returns
    /// 
    /// The index of the added memory instance.
    pub fn add_memory(&mut self, memory: MemoryInstance) -> u32 {
        let idx = self.mems.len() as u32;
        self.mems.push(memory);
        idx
    }

    /// Creates a new memory instance and adds it to the store
    /// 
    /// # Arguments
    /// 
    /// * `ty` - The memory type defining the limits
    /// 
    /// # Returns
    /// 
    /// The index of the newly created memory instance.
    pub fn create_memory(&mut self, ty: MemoryType) -> u32 {
        let memory = MemoryInstance::new(ty);
        self.add_memory(memory)
    }

    /// Gets a reference to a memory instance
    /// 
    /// # Arguments
    /// 
    /// * `index` - The index of the memory instance
    /// 
    /// # Returns
    /// 
    /// A reference to the memory instance, or None if the index is invalid.
    pub fn get_memory(&self, index: u32) -> Option<&MemoryInstance> {
        self.mems.get(index as usize)
    }

    /// Gets a mutable reference to a memory instance
    /// 
    /// # Arguments
    /// 
    /// * `index` - The index of the memory instance
    /// 
    /// # Returns
    /// 
    /// A mutable reference to the memory instance, or None if the index is invalid.
    pub fn get_memory_mut(&mut self, index: u32) -> Option<&mut MemoryInstance> {
        self.mems.get_mut(index as usize)
    }

    /// Adds a global instance to the store.
    ///
    /// # Arguments
    ///
    /// * `global` - The global instance to add
    ///
    /// # Returns
    ///
    /// The index of the added global instance.
    pub fn add_global(&mut self, global: GlobalInstance) -> u32 {
        let index = self.globals.len() as u32;
        self.globals.push(global);
        index
    }

    /// Creates a new global instance and adds it to the store.
    ///
    /// # Arguments
    ///
    /// * `ty` - The type of the global variable
    /// * `value` - The initial value of the global variable
    ///
    /// # Returns
    ///
    /// The index of the created global instance.
    pub fn create_global(&mut self, ty: GlobalType, value: Value) -> u32 {
        self.add_global(GlobalInstance::new(ty, value))
    }

    /// Returns a reference to the global instance at the given index.
    ///
    /// # Arguments
    ///
    /// * `index` - The index of the global instance
    ///
    /// # Returns
    ///
    /// * `Some(&GlobalInstance)` if the index is valid
    /// * `None` if the index is invalid
    pub fn get_global(&self, index: u32) -> Option<&GlobalInstance> {
        self.globals.get(index as usize)
    }

    /// Returns a mutable reference to the global instance at the given index.
    ///
    /// # Arguments
    ///
    /// * `index` - The index of the global instance
    ///
    /// # Returns
    ///
    /// * `Some(&mut GlobalInstance)` if the index is valid
    /// * `None` if the index is invalid
    pub fn get_global_mut(&mut self, index: u32) -> Option<&mut GlobalInstance> {
        self.globals.get_mut(index as usize)
    }

    /// Adds an element instance to the store
    /// 
    /// # Arguments
    /// * `elem` - The element instance to add
    /// 
    /// # Returns
    /// The index of the added element instance
    pub fn add_elem(&mut self, elem: ElementInstance) -> u32 {
        let index = self.elems.len() as u32;
        self.elems.push(elem);
        index
    }

    /// Returns a reference to the element instance at the given index
    /// 
    /// # Arguments
    /// * `index` - The index of the element instance to get
    /// 
    /// # Returns
    /// Some reference to the element instance if the index is valid, None otherwise
    pub fn get_elem(&self, index: u32) -> Option<&ElementInstance> {
        self.elems.get(index as usize)
    }

    /// Returns a mutable reference to the element instance at the given index
    /// 
    /// # Arguments
    /// * `index` - The index of the element instance to get
    /// 
    /// # Returns
    /// Some mutable reference to the element instance if the index is valid, None otherwise
    pub fn get_elem_mut(&mut self, index: u32) -> Option<&mut ElementInstance> {
        self.elems.get_mut(index as usize)
    }

    /// Adds a data instance to the store
    /// 
    /// # Arguments
    /// * `data` - The data instance to add
    /// 
    /// # Returns
    /// The index of the added data instance
    pub fn add_data(&mut self, data: DataInstance) -> u32 {
        let index = self.datas.len() as u32;
        self.datas.push(data);
        index
    }

    /// Returns a reference to the data instance at the given index
    /// 
    /// # Arguments
    /// * `index` - The index of the data instance to get
    /// 
    /// # Returns
    /// Some reference to the data instance if the index is valid, None otherwise
    pub fn get_data(&self, index: u32) -> Option<&DataInstance> {
        self.datas.get(index as usize)
    }

    /// Returns a mutable reference to the data instance at the given index
    /// 
    /// # Arguments
    /// 
    /// * `index` - The index of the data instance
    /// 
    /// # Returns
    /// 
    /// A mutable reference to the data instance, or None if the index is invalid.
    pub fn get_data_mut(&mut self, index: u32) -> Option<&mut DataInstance> {
        self.datas.get_mut(index as usize)
    }

    /// Invokes a function at the given address with the provided arguments
    /// 
    /// # Specification (4.5.5 Invocation)
    /// 
    /// Once a module has been instantiated, any exported function can be invoked externally
    /// via its function address funcaddr in the store S and an appropriate list val* of argument values.
    /// 
    /// The following steps are performed:
    /// 1. Assert: S.funcs[funcaddr] exists.
    /// 2. Let funcinst be the function instance S.funcs[funcaddr].
    /// 3. Let [t_n^1] → [t_m^2] be the function type funcinst.type.
    /// 4. If the length |val*| of the provided argument values is different from the number n of expected arguments, then:
    ///    a. Fail.
    /// 5. For each value type t_i in t_n^1 and corresponding value val_i in val*, do:
    ///    a. If val_i is not valid with value type t_i, then:
    ///       i. Fail.
    /// 6. Let F be the dummy frame {module {}, locals ε}.
    /// 7. Push the frame F to the stack.
    /// 8. Push the values val* to the stack.
    /// 9. Invoke the function instance at address funcaddr.
    /// 
    /// Once the function has returned, the following steps are executed:
    /// 1. Assert: due to validation, m values are on the top of the stack.
    /// 2. Pop val_m^res from the stack.
    /// 3. Assert: due to validation, the frame F is now on the top of the stack.
    /// 4. Pop the frame F from the stack.
    /// 
    /// The values val_m^res are returned as the results of the invocation.
    /// 
    /// # Arguments
    /// 
    /// * `func_addr` - The function address to invoke
    /// * `args` - The argument values to pass to the function
    /// 
    /// # Returns
    /// 
    /// * `RuntimeResult<Vec<Value>>` - The result values from the function invocation
    pub fn invoke_function(&mut self, func_addr: FuncAddr, args: &[Value]) -> RuntimeResult<Vec<Value>> {
        // 1. Assert: S.funcs[funcaddr] exists.
        let func_instance = self.funcs.get(func_addr.as_usize()).ok_or_else(|| {
            RuntimeError::Function(format!(
                "Function instance at address {} does not exist in store",
                func_addr.as_usize()
            ))
        })?;

        // 2-3. Clone all needed data before any mutable borrow
        let param_types = func_instance.ty().params.clone();
        let _result_types = func_instance.ty().results.clone(); // not used directly here, but for completeness
        let func_instance_clone = func_instance.clone();

        // 4. If the length |val*| of the provided argument values is different from the number n of expected arguments, then:
        if args.len() != param_types.len() {
            return Err(RuntimeError::Function(format!(
                "Argument count mismatch: expected {} arguments, got {}",
                param_types.len(),
                args.len()
            )));
        }

        // 5. For each value type t_i in t_n^1 and corresponding value val_i in val*, do:
        for (i, (arg, param_type)) in args.iter().zip(param_types.iter()).enumerate() {
            ValueTyping::check_value_type(arg, *param_type, self).map_err(|e| {
                RuntimeError::Function(format!("Argument {} type validation failed: {}", i, e))
            })?;
        }

        // 6. Let F be the dummy frame {module {}, locals ε}.
        let dummy_module = crate::wasm::runtime::ModuleInstance::new();
        let frame = Frame::new(0, FrameState::new(Vec::new(), dummy_module));

        // 7. Push the frame F to the stack.
        let mut stack = Stack::new();
        stack.push_frame(frame);

        // 8. Push the values val* to the stack.
        for arg in args {
            stack.push_value(arg.clone());
        }

        // 9. Invoke the function instance at address funcaddr.
        let results = func_instance_clone.invoke_with_values(&mut stack)?;

        Ok(results)
    }
}

impl fmt::Display for Store {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Store {{ funcs: {}, tables: {}, mems: {}, globals: {}, elems: {}, datas: {} }}",
            self.funcs.len(), self.tables.len(), self.mems.len(), 
            self.globals.len(), self.elems.len(), self.datas.len())
    }
}
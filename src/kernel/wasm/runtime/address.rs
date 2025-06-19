use core::fmt;

/// WebAssembly address type
/// 
/// Addresses are dynamic, globally unique references to runtime objects,
/// in contrast to indices, which are static, module-local references to
/// their original definitions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Address(pub u32);

impl Address {
    /// Creates a new address from a u32 value
    pub fn new(addr: u32) -> Self {
        Self(addr)
    }

    /// Returns the address as a u32 value
    pub fn as_u32(&self) -> u32 {
        self.0
    }

    /// Returns the address as a usize value
    pub fn as_usize(&self) -> usize {
        self.0 as usize
    }
}

impl fmt::Display for Address {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// Function address
pub type FuncAddr = Address;

/// Table address
pub type TableAddr = Address;

/// Memory address
pub type MemAddr = Address;

/// Global address
pub type GlobalAddr = Address;

/// Element address
pub type ElemAddr = Address;

/// Data address
pub type DataAddr = Address;

/// External address (for host functions)
pub type ExternAddr = Address;

/// Address type for runtime objects
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RuntimeAddr {
    /// Function address
    Func(FuncAddr),
    /// Table address
    Table(TableAddr),
    /// Memory address
    Memory(MemAddr),
    /// Global address
    Global(GlobalAddr),
    /// Element address
    Element(ElemAddr),
    /// Data address
    Data(DataAddr),
    /// External address
    Extern(ExternAddr),
}

impl RuntimeAddr {
    /// Creates a new function address
    pub fn func(addr: u32) -> Self {
        Self::Func(FuncAddr::new(addr))
    }

    /// Creates a new table address
    pub fn table(addr: u32) -> Self {
        Self::Table(TableAddr::new(addr))
    }

    /// Creates a new memory address
    pub fn memory(addr: u32) -> Self {
        Self::Memory(MemAddr::new(addr))
    }

    /// Creates a new global address
    pub fn global(addr: u32) -> Self {
        Self::Global(GlobalAddr::new(addr))
    }

    /// Creates a new element address
    pub fn element(addr: u32) -> Self {
        Self::Element(ElemAddr::new(addr))
    }

    /// Creates a new data address
    pub fn data(addr: u32) -> Self {
        Self::Data(DataAddr::new(addr))
    }

    /// Creates a new external address
    pub fn extern_(addr: u32) -> Self {
        Self::Extern(ExternAddr::new(addr))
    }

    /// Returns the raw address value
    pub fn as_u32(&self) -> u32 {
        match self {
            Self::Func(addr) => addr.as_u32(),
            Self::Table(addr) => addr.as_u32(),
            Self::Memory(addr) => addr.as_u32(),
            Self::Global(addr) => addr.as_u32(),
            Self::Element(addr) => addr.as_u32(),
            Self::Data(addr) => addr.as_u32(),
            Self::Extern(addr) => addr.as_u32(),
        }
    }
}

impl fmt::Display for RuntimeAddr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Func(addr) => write!(f, "func[{}]", addr),
            Self::Table(addr) => write!(f, "table[{}]", addr),
            Self::Memory(addr) => write!(f, "memory[{}]", addr),
            Self::Global(addr) => write!(f, "global[{}]", addr),
            Self::Element(addr) => write!(f, "element[{}]", addr),
            Self::Data(addr) => write!(f, "data[{}]", addr),
            Self::Extern(addr) => write!(f, "extern[{}]", addr),
        }
    }
}
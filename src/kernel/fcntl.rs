pub mod omode {
    pub const RDONLY: usize = 0x000;
    pub const WRONLY: usize = 0x001;
    pub const RDWR: usize = 0x002;
    pub const CREATE: usize = 0x200;
    pub const TRUNC: usize = 0x400;
    pub const APPEND: usize = 0x800;
    pub const CLOEXEC: usize = 0x1000;
}

pub struct OMode {
    read: bool,
    write: bool,
    truncate: bool,
    create: bool,
    append: bool,
    cloexec: bool,
}

impl Default for OMode {
    fn default() -> Self {
        Self::new()
    }
}

impl OMode {
    pub fn new() -> Self {
        Self {
            read: false,
            write: false,
            truncate: false,
            create: false,
            append: false,
            cloexec: false,
        }
    }

    pub fn read(&mut self, read: bool) -> &mut Self {
        self.read = read;
        self
    }
    pub fn write(&mut self, write: bool) -> &mut Self {
        self.write = write;
        self
    }
    pub fn append(&mut self, append: bool) -> &mut Self {
        self.append = append;
        self
    }
    pub fn cloexec(&mut self, cloexec: bool) -> &mut Self {
        self.cloexec = cloexec;
        self
    }
    fn truncate(&mut self, truncate: bool) -> &mut Self {
        self.truncate = truncate;
        self
    }
    fn create(&mut self, create: bool) -> &mut Self {
        self.create = create;
        self
    }

    pub fn from_usize(bits: usize) -> Self {
        let mut mode = Self::new();
        mode.read(bits & omode::WRONLY == 0)
            .write(bits & omode::WRONLY != 0 || bits & omode::RDWR != 0)
            .create(bits & omode::CREATE != 0)
            .truncate(bits & omode::TRUNC != 0)
            .append(bits & omode::APPEND != 0)
            .cloexec(bits & omode::CLOEXEC != 0);
        mode
    }

    pub fn is_read(&self) -> bool {
        self.read
    }

    pub fn is_write(&self) -> bool {
        self.write
    }

    pub fn is_create(&self) -> bool {
        self.create
    }

    pub fn is_trunc(&self) -> bool {
        self.truncate
    }

    pub fn is_rdonly(&self) -> bool {
        self.read && !self.write
    }

    pub fn is_cloexec(&self) -> bool {
        self.cloexec
    }

    pub fn is_append(&self) -> bool {
        self.append
    }
}

#[repr(usize)]
pub enum FcntlCmd {
    SetCloexec = 1,
    Invalid,
}

impl FcntlCmd {
    pub fn from_usize(bits: usize) -> Self {
        match bits {
            1 => Self::SetCloexec,
            _ => Self::Invalid,
        }
    }
}

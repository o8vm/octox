#[cfg(all(target_os = "none", feature = "kernel"))]
use crate::array;
#[cfg(all(target_os = "none", feature = "kernel"))]
use crate::error::{Error::*, Result};
#[cfg(all(target_os = "none", feature = "kernel"))]
use crate::fcntl::{FcntlCmd, OMode};
#[cfg(all(target_os = "none", feature = "kernel"))]
use crate::fs::{create, IData, Inode, Path, BSIZE};
#[cfg(all(target_os = "none", feature = "kernel"))]
use crate::log::LOG;
#[cfg(all(target_os = "none", feature = "kernel"))]
use crate::param::{MAXOPBLOCKS, NDEV, NFILE};
#[cfg(all(target_os = "none", feature = "kernel"))]
use crate::pipe::Pipe;
#[cfg(all(target_os = "none", feature = "kernel"))]
use crate::proc::either_copyout;
#[cfg(all(target_os = "none", feature = "kernel"))]
use crate::sleeplock::{SleepLock, SleepLockGuard};
#[cfg(all(target_os = "none", feature = "kernel"))]
use crate::spinlock::Mutex;
#[cfg(all(target_os = "none", feature = "kernel"))]
use crate::stat::{FileType, Stat};
#[cfg(all(target_os = "none", feature = "kernel"))]
use crate::sync::{LazyLock, OnceLock};
#[cfg(all(target_os = "none", feature = "kernel"))]
use crate::vm::VirtAddr;
#[cfg(all(target_os = "none", feature = "kernel"))]
use alloc::sync::Arc;
#[cfg(all(target_os = "none", feature = "kernel"))]
use core::cell::UnsafeCell;
#[cfg(all(target_os = "none", feature = "kernel"))]
use core::ops::Deref;

#[cfg(all(target_os = "none", feature = "kernel"))]
pub static DEVSW: DevSW = DevSW::new();
#[cfg(all(target_os = "none", feature = "kernel"))]
pub static FTABLE: LazyLock<FTable> = LazyLock::new(|| Mutex::new(array![None; NFILE], "ftable"));

#[cfg(all(target_os = "none", feature = "kernel"))]
type FTable = Mutex<[Option<Arc<VFile>>; NFILE]>;

#[cfg(all(target_os = "none", feature = "kernel"))]
#[derive(Default, Clone, Debug)]
pub struct File {
    f: Option<Arc<VFile>>,
    readable: bool,
    writable: bool,
    cloexec: bool,
}

#[cfg(all(target_os = "none", feature = "kernel"))]
#[derive(Debug)]
pub enum VFile {
    Device(DNod),
    Inode(FNod),
    Pipe(Pipe),
    None,
}

// Device Node
#[cfg(all(target_os = "none", feature = "kernel"))]
#[derive(Debug)]
pub struct DNod {
    driver: &'static dyn Device,
    ip: Inode,
}

// Device functions, map this trait using dyn
#[cfg(all(target_os = "none", feature = "kernel"))]
pub trait Device: Send + Sync {
    fn read(&self, dst: VirtAddr, n: usize) -> Result<usize>;
    fn write(&self, src: VirtAddr, n: usize) -> Result<usize>;
    fn major(&self) -> Major;
}

#[cfg(all(target_os = "none", feature = "kernel"))]
impl core::fmt::Debug for dyn Device {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "Device fn {:?}", self.major())
    }
}

#[cfg(all(target_os = "none", feature = "kernel"))]
impl Deref for DNod {
    type Target = dyn Device;
    fn deref(&self) -> &Self::Target {
        self.driver
    }
}

// File & directory Node
#[cfg(all(target_os = "none", feature = "kernel"))]
#[derive(Debug)]
pub struct FNod {
    off: UnsafeCell<u32>, // Safety: If inode lock is obtained.
    ip: Inode,
}
#[cfg(all(target_os = "none", feature = "kernel"))]
unsafe impl Send for FNod {}
#[cfg(all(target_os = "none", feature = "kernel"))]
unsafe impl Sync for FNod {}

#[cfg(all(target_os = "none", feature = "kernel"))]
impl FNod {
    pub fn new(ip: Inode, offset: u32) -> Self {
        Self {
            off: UnsafeCell::new(offset),
            ip,
        }
    }
    fn read(&self, dst: VirtAddr, n: usize) -> Result<usize> {
        let mut ip = self.ip.lock();
        let off = unsafe { &mut *self.off.get() };

        let r = ip.read(dst, *off, n)?;
        *off += r as u32;
        Ok(r)
    }
    fn write(&self, src: VirtAddr, n: usize) -> Result<usize> {
        // write a few blocks at a time to avoid exceeding the maximum
        // log transaction size, including i-node, indirect block,
        // allocation blocks, and 2 blocks of slop for non-aligned
        // writes. this really belongs lower down, since inode write()
        // might be writing a device like the console.
        let max = ((MAXOPBLOCKS - 1 - 1 - 2) / 2) * BSIZE;
        let mut ret: Result<usize> = Ok(0);
        let mut i: usize = 0;

        while i < n {
            let mut n1 = n - i;
            if n1 > max {
                n1 = max
            }

            LOG.begin_op();
            {
                let mut guard = self.ip.lock();
                let off = unsafe { &mut *self.off.get() };
                ret = guard.write(src, *off, n1);
                match ret {
                    Ok(r) => {
                        *off += r as u32;
                        i += r;
                        ret = Ok(i);
                    }
                    _ => break, // error from inode write
                }
            }
            LOG.end_op();
        }
        if ret.is_err() {
            LOG.end_op();
        }
        ret
    }
}

#[cfg(all(target_os = "none", feature = "kernel"))]
impl VFile {
    fn read(&self, dst: VirtAddr, n: usize) -> Result<usize> {
        match self {
            VFile::Device(d) => d.read(dst, n),
            VFile::Inode(f) => f.read(dst, n),
            VFile::Pipe(p) => p.read(dst, n),
            _ => panic!("file read"),
        }
    }
    fn write(&self, src: VirtAddr, n: usize) -> Result<usize> {
        match self {
            VFile::Device(d) => d.write(src, n),
            VFile::Inode(f) => f.write(src, n),
            VFile::Pipe(p) => p.write(src, n),
            _ => panic!("file write"),
        }
    }
    // Get metadata about file.
    // addr pointing to a struct stat.
    pub fn stat(&self, addr: VirtAddr) -> Result<()> {
        let mut stat: Stat = Default::default();

        match self {
            VFile::Device(DNod { driver: _, ref ip }) | VFile::Inode(FNod { off: _, ref ip }) => {
                {
                    ip.lock().stat(&mut stat);
                }
                either_copyout(addr, &stat)
            }
            _ => Err(BadFileDescriptor),
        }
    }
}

#[cfg(all(target_os = "none", feature = "kernel"))]
impl File {
    // Read from file.
    pub fn read(&mut self, dst: VirtAddr, n: usize) -> Result<usize> {
        if !self.readable {
            return Err(InvalidArgument);
        }
        self.f.as_ref().unwrap().read(dst, n)
    }

    // Write to file.
    pub fn write(&mut self, src: VirtAddr, n: usize) -> Result<usize> {
        if !self.writable {
            return Err(InvalidArgument);
        }
        self.f.as_ref().unwrap().write(src, n)
    }

    pub fn is_cloexec(&self) -> bool {
        self.cloexec
    }

    pub fn clear_cloexec(&mut self) {
        self.cloexec = false;
    }

    pub fn do_fcntl(&mut self, cmd: FcntlCmd) -> Result<usize> {
        use FcntlCmd::*;
        match cmd {
            SetCloexec => self.cloexec = true,
            _ => return Err(InvalidArgument),
        }
        Ok(0)
    }
}

#[cfg(all(target_os = "none", feature = "kernel"))]
impl Deref for File {
    type Target = Arc<VFile>;
    fn deref(&self) -> &Self::Target {
        self.f.as_ref().unwrap()
    }
}

#[cfg(all(target_os = "none", feature = "kernel"))]
impl Drop for File {
    fn drop(&mut self) {
        let f = self.f.take().unwrap();
        if Arc::strong_count(&f) < 2 {
            panic!("file drop");
        }

        if Arc::strong_count(&f) == 2 {
            let mut guard = FTABLE.lock();
            // drop arc<vfile> in table
            for ff in guard.iter_mut() {
                match ff {
                    Some(vff) if Arc::ptr_eq(&f, vff) => {
                        ff.take(); // drop ref in table. ref count = 1;
                    }
                    _ => (),
                }
            }
        }

        // if ref count == 1
        if let Ok(VFile::Inode(FNod { off: _, ip }) | VFile::Device(DNod { driver: _, ip })) =
            Arc::try_unwrap(f)
        {
            LOG.begin_op();
            drop(ip);
            LOG.end_op();
        }
    }
}

// File Allocation Type Source
#[cfg(all(target_os = "none", feature = "kernel"))]
pub enum FType<'a> {
    Node(&'a Path),
    Pipe(Pipe),
}

#[cfg(all(target_os = "none", feature = "kernel"))]
impl FTable {
    // Allocate a file structure
    // Must be called inside transaction if FType == FType::Node.
    pub fn alloc(&self, opts: OMode, ftype: FType<'_>) -> Result<File> {
        let inner: Arc<VFile> = Arc::new(match ftype {
            FType::Node(path) => {
                let ip: Inode;
                let mut ip_guard: SleepLockGuard<'_, IData>;

                if opts.is_create() {
                    ip = create(path, FileType::File, 0, 0)?;
                    ip_guard = ip.lock();
                } else {
                    (_, ip) = path.namei()?;
                    ip_guard = ip.lock();
                    if ip_guard.itype() == FileType::Dir && !opts.is_rdonly() {
                        return Err(IsADirectory);
                    }
                }
                // ?
                match ip_guard.itype() {
                    FileType::Device if ip_guard.major() != Major::Invalid => {
                        let driver = DEVSW.get(ip_guard.major()).unwrap();
                        SleepLock::unlock(ip_guard);
                        VFile::Device(DNod { driver, ip })
                    }
                    FileType::Dir | FileType::File => {
                        let mut offset = 0;
                        if opts.is_trunc() && ip_guard.itype() == FileType::File {
                            ip_guard.trunc();
                        } else if opts.is_append() && ip_guard.itype() == FileType::File {
                            offset = ip_guard.size();
                        }
                        SleepLock::unlock(ip_guard);
                        VFile::Inode(FNod::new(ip, offset))
                    }
                    _ => return Err(NoSuchNode),
                }
            }
            FType::Pipe(pi) => VFile::Pipe(pi),
        });

        let mut guard = self.lock();

        let mut empty: Option<&mut Option<Arc<VFile>>> = None;
        for f in guard.iter_mut() {
            match f {
                None if empty.is_none() => {
                    empty = Some(f);
                    break;
                }
                _ => continue,
            }
        }

        let f = empty.ok_or(FileTableOverflow)?;
        f.replace(inner);
        Ok(File {
            f: f.clone(), // ref count = 2
            readable: opts.is_read(),
            writable: opts.is_write(),
            cloexec: opts.is_cloexec(),
        })
    }
}

#[cfg(all(target_os = "none", feature = "kernel"))]
pub struct DevSW {
    table: [OnceLock<&'static dyn Device>; NDEV],
}

#[cfg(all(target_os = "none", feature = "kernel"))]
impl core::fmt::Debug for DevSW {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "[")?;
        for (count, v) in self.table.iter().enumerate() {
            if count != 0 {
                write!(f, ", ")?;
            }
            if let Some(&v) = v.get() {
                write!(f, "{:?}", v)?;
            } else {
                write!(f, "None")?;
            }
        }
        write!(f, "]")
    }
}

#[cfg(all(target_os = "none", feature = "kernel"))]
impl DevSW {
    pub const fn new() -> Self {
        Self {
            table: array![OnceLock::new(); NDEV],
        }
    }
    pub fn set(
        &self,
        devnum: Major,
        dev: &'static dyn Device,
    ) -> core::result::Result<(), &'static (dyn Device + 'static)> {
        self.table[devnum as usize].set(dev)
    }

    pub fn get(&self, devnum: Major) -> Option<&'static dyn Device> {
        match self.table[devnum as usize].get() {
            Some(&dev) => Some(dev),
            None => None,
        }
    }
}

// Device Major Number
#[repr(u16)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Major {
    Null = 0,
    Console = 1,
    Invalid,
}
impl Default for Major {
    fn default() -> Self {
        Self::Invalid
    }
}

impl Major {
    pub fn from_u16(bits: u16) -> Major {
        match bits {
            0 => Major::Null,
            1 => Major::Console,
            _ => Major::Invalid,
        }
    }
}

#[cfg(all(target_os = "none", feature = "kernel"))]
use crate::array;
#[cfg(all(target_os = "none", feature = "kernel"))]
use crate::bio::BCACHE;
#[cfg(all(target_os = "none", feature = "kernel"))]
use crate::error::{Error::*, Result};
use crate::file::Major;
#[cfg(all(target_os = "none", feature = "kernel"))]
use crate::log::LOG;
#[cfg(all(target_os = "none", feature = "kernel"))]
use crate::param::{NINODE, ROOTDEV};
#[cfg(all(target_os = "none", feature = "kernel"))]
use crate::proc::{either_copyin, either_copyout, Cpus};
#[cfg(all(target_os = "none", feature = "kernel"))]
use crate::sleeplock::{SleepLock, SleepLockGuard};
#[cfg(all(target_os = "none", feature = "kernel"))]
use crate::spinlock::Mutex;
use crate::stat::FileType;
#[cfg(all(target_os = "none", feature = "kernel"))]
use crate::stat::Stat;
#[cfg(all(target_os = "none", feature = "kernel"))]
use crate::{
    sync::{LazyLock, OnceLock},
    vm::VirtAddr,
};
#[cfg(all(target_os = "none", feature = "kernel"))]
use alloc::sync::Arc;
#[cfg(all(target_os = "none", feature = "kernel"))]
use core::mem::size_of;
#[cfg(all(target_os = "none", feature = "kernel"))]
use core::ops::Deref;

// File system implementation. Five layers:
//   - Blocks: allocator for raw disk blocks.
//   - Log: crash recovery for multi-step updates.
//   - Files: inode allocator, reading, writing, metadata.
//   - Directories: inode with special contents (list of other inodes!)
//   - Names: paths like /octox/src/kernel/fs.rs for convenient naming.
//
// This file contains the low-level file system manipulation
// routines. The (higher-level) system call implementations
// are in syscall.rs

pub const ROOTINO: u32 = 1; // root i-number
pub const BSIZE: usize = 1024; // block size

// there should be one superblock per disk device, but we run with
// only one device
#[cfg(all(target_os = "none", feature = "kernel"))]
pub static SB: OnceLock<SuperBlock> = OnceLock::new();

// Disk layout:
// [ root block | super block | log | inode blocks |
//                                          free bit map | data blocks ]
//
// mkfs computes the super block and builds an initial file system. The
// super block describes the disk layout:
#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct SuperBlock {
    pub magic: u32,      // Must be FSMAGIC
    pub size: u32,       // Size of file system image (blocks)
    pub nblocks: u32,    // Number of data blocks
    pub ninodes: u32,    // Number of inodes.
    pub nlog: u32,       // Number of log blocks
    pub logstart: u32,   // Block number of first log block
    pub inodestart: u32, // Block number of first inode block
    pub bmapstart: u32,  // Block number of first free map block
}

pub const FSMAGIC: u32 = 0x10203040;

pub const NDIRECT: usize = 11;
pub const NINDIRECT: usize = BSIZE / core::mem::size_of::<u32>();
pub const NDINDIRECT: usize = NINDIRECT * NINDIRECT;
pub const MAXFILE: usize = NDIRECT + NINDIRECT + NDINDIRECT;

// On-disk inode structure
#[repr(C)]
#[derive(Debug, Clone, Copy, Default)]
struct DInode {
    itype: FileType,           // File type
    major: Major,              // Major Device Number (T_DEVICE only)
    minor: u16,                // Minor Device Number (T_DEVICE only)
    nlink: u16,                // Number of links to inode in file system
    size: u32,                 // Size of data (bytes)
    addrs: [u32; NDIRECT + 2], // Data block address
}

// Inodes per block
pub const IPB: usize = BSIZE / core::mem::size_of::<DInode>();

// Bitmap bits per block
pub const BPB: u32 = (BSIZE * 8) as u32;

// Directory is a file containing a sequence of dirent structures.
pub const DIRSIZ: usize = 14;

#[repr(C)]
#[derive(Debug, Clone, Copy, Default)]
pub struct DirEnt {
    pub inum: u16,
    pub name: [u8; DIRSIZ],
}

impl SuperBlock {
    #[cfg(all(target_os = "none", feature = "kernel"))]
    fn read(dev: u32) -> Self {
        let bp = BCACHE.read(dev, 1);
        *bp.align_to::<SuperBlock>().get(0).unwrap()
    }

    // Block containing inode i
    pub fn iblock(&self, i: u32) -> u32 {
        i / IPB as u32 + self.inodestart
    }

    // Block of free map containing bit for block b
    pub fn bblock(&self, b: u32) -> u32 {
        b / BPB + self.bmapstart
    }
}

// Init fs
#[cfg(all(target_os = "none", feature = "kernel"))]
pub fn init(dev: u32) {
    SB.set(SuperBlock::read(dev)).unwrap();
    let sb = SB.get().unwrap();
    assert!(sb.magic == FSMAGIC, "invalid file system");
    LOG.init();
}

// Zero a block
#[cfg(all(target_os = "none", feature = "kernel"))]
fn bzero(dev: u32, bno: u32) {
    let mut bp = BCACHE.read(dev, bno);
    bp.copy_from_slice(&[0; BSIZE]);
    LOG.write(bp);
}

// Blocks.

// Allocate a zeroed disk block.
#[cfg(all(target_os = "none", feature = "kernel"))]
fn balloc(dev: u32) -> u32 {
    let sb = SB.get().unwrap();

    for b in (0..sb.size).step_by(BPB as usize) {
        let mut bp = BCACHE.read(dev, sb.bblock(b));

        let mut bi = 0;
        while bi < BPB && b + bi < sb.size {
            let m = 1 << (bi % 8);
            if bp.get((bi / 8) as usize).unwrap() & m == 0 {
                // Is block free?
                *bp.get_mut((bi / 8) as usize).unwrap() |= m; // Mark block in use.
                LOG.write(bp);
                bzero(dev, b + bi);
                return b + bi;
            }
            bi += 1;
        }
    }
    unreachable!("balloc: out of blocks");
}

// Free a disk block
#[cfg(all(target_os = "none", feature = "kernel"))]
fn bfree(dev: u32, b: u32) {
    let sb = SB.get().unwrap();
    let mut bp = BCACHE.read(dev, sb.bblock(b));
    let bi = b % BPB;
    let m = 1 << (bi % 8);
    if bp.get((bi / 8) as usize).unwrap() & m == 0 {
        panic!("freeing free block");
    }
    *bp.get_mut((bi / 8) as usize).unwrap() &= !m;
    LOG.write(bp);
}

// Inodes.
//
// An inode describes a single unnamed file.
// The inode disk structure holds metadata such as the type of file,
// its size, the number of links that reference that file, and a list
// of blocks that hold the contents of the file.
//
// The inodes are placed sequentially at sb.startinode on the disk.
// Each inode has a number indicating its location on the disk.
//
// The kernel keeps a table of in-use inodes in memory to provide a
// place to synchronize access to inodes used by multiple processes.
// The in-memory inodes represented Arc<MInode> has book-keeping info
// that is not stored on disk: atomic ref count and ip.valid.
//
// The inode and its in-memory representation go through the following
// sequence of states before being used by the file system code.
//
// * Allocation: alloc() allocates an inode if inode's type (on disk)
//   is non-zero. put() frees if the Arc::strong_count<Arc<MInode>>
//   have fallen to 2 and link counts have fallen to zero.
//
// * Referencing in table: an entry in the inode table
//   is free if Arc::strong_count(&Arc<MInode>) is 2(what is in the
//   table and what is being processed at the time). Otherwise Arc
//   count tracks the number of in-memory pointers to the entry (open
//   files and current directories). get() finds or creates a table
//   entry and increments its Arc count; put() consume Arc<MInode>.
//
// * Valid: the type and size in an inode table entry is only correct
//   when ip.valid is true. MInode.lock() reads the inode from the
//   disk and sets valid, when put() clears valid if
//   Arc::strong_count(&Arc<MInode>) has fallen to 2.
//
// * Locked: file system code may only examine and modify the
//   information in an inode and its property if it has first locked
//   the inode.
//
// Thus a typical sequence is:
//   ip = ITABLE.get(dev, inum);  // get inode
//   guard = ip.lock();           // return SleeplockGuard
//   .. examine and modify inode contents
//   // drop(guard)
//   // drop(inode)
//
// Because MInode.lock() is separated from ITABLE.get(), system calls
// can obtain a long-term reference to the MInode (as for an open file)
// and only lock it for a short period of time (e.g., in read()). This
// separation also helps avoid deadlocks and races during path-name
// lookup. ITABLE.get() increments the Arc count, so the inode remains
// in the table and the pointer to it remains valid.
//
// The ITABLE lock protects the allocation of itable entries. MInode.dev
// and Minode.num indicates which i-node an entry holds, one must hold
// itable lock while using any of those fields.
//
// An MInode.lock sleeplock protects all ip fields, dev, and inum. One
// must hold MInode.lock() in order to read or write that inode's
// ip.valid, ip.size, ip.type.

#[cfg(all(target_os = "none", feature = "kernel"))]
pub static ITABLE: LazyLock<Mutex<[Option<Arc<MInode>>; NINODE]>> =
    LazyLock::new(|| Mutex::new(array![None; NINODE], "itable"));

// Inode passed from ITABLE.
// Wrapper for in-memory inode i.e. MInode
#[cfg(all(target_os = "none", feature = "kernel"))]
#[derive(Default, Clone, Debug)]
pub struct Inode {
    ip: Option<Arc<MInode>>,
}

// in-memory copy of an inode
#[cfg(all(target_os = "none", feature = "kernel"))]
#[derive(Debug)]
pub struct MInode {
    dev: u32,
    inum: u32,
    data: SleepLock<IData>,
}

#[cfg(all(target_os = "none", feature = "kernel"))]
#[derive(Debug, Default)]
pub struct IData {
    dev: u32,
    inum: u32,
    valid: bool,
    itype: FileType,
    major: Major,
    minor: u16,
    nlink: u16,
    size: u32,
    addrs: [u32; NDIRECT + 2],
}

#[cfg(all(target_os = "none", feature = "kernel"))]
enum LinkOp {
    Plus,
    Minus,
    Init(u16),
}

#[cfg(all(target_os = "none", feature = "kernel"))]
impl IData {
    fn new(dev: u32, inum: u32) -> Self {
        Self {
            dev,
            inum,
            ..Default::default()
        }
    }

    pub fn size(&self) -> u32 {
        self.size
    }

    pub fn itype(&self) -> FileType {
        self.itype
    }

    pub fn major(&self) -> Major {
        self.major
    }

    // inode is write through, so change about MInode is also must be written into disk
    fn set_type(&mut self, itype: FileType) {
        self.itype = itype;
        self.update();
    }

    // inode is write through, so change about MInode is also must be written into disk
    fn set_major_minor(&mut self, major: Major, minor: u16) {
        self.major = major;
        self.minor = minor;
        self.update();
    }

    // inode is write through, so change about MInode is also must be written into disk
    fn set_size(&mut self, size: u32) {
        self.size = size;
        self.update();
    }

    // inode is write through, so change about MInode is also must be written into disk
    fn set_addrs(&mut self, bn: usize, addr: u32) {
        self.addrs[bn] = addr;
        self.update();
    }

    // inode is write through, so change about MInode is also must be written into disk.
    fn set_nlink(&mut self, op: LinkOp) {
        match op {
            LinkOp::Plus => self.nlink += 1,
            LinkOp::Minus => self.nlink -= 1,
            LinkOp::Init(num) => self.nlink = num,
        }
        self.update();
    }

    // Copy a modified in-memory inode to disk.
    // Must be called after every change to an inode field
    // that lives on disk.
    // Caller must hold inode sleeplock.
    fn update(&self) {
        let sb = SB.get().unwrap();
        let mut bp = BCACHE.read(self.dev, sb.iblock(self.inum));
        let dip = bp
            .align_to_mut::<DInode>()
            .get_mut(self.inum as usize % IPB)
            .unwrap();
        dip.itype = self.itype;
        dip.major = self.major;
        dip.minor = self.minor;
        dip.nlink = self.nlink;
        dip.size = self.size;
        dip.addrs.copy_from_slice(&self.addrs);
        LOG.write(bp);
    }

    // Truncate inode (discard contents).
    // Caller must hold inode sleeplock.
    pub fn trunc(&mut self) {
        for addr in self.addrs.iter_mut().take(NDIRECT) {
            if *addr > 0 {
                bfree(self.dev, *addr);
                *addr = 0;
            }
        }

        let naddr = self.addrs.get_mut(NDIRECT).unwrap();
        if *naddr > 0 {
            let bp = BCACHE.read(self.dev, *naddr);
            let a = bp.align_to::<u32>();
            for &addr in a.iter() {
                // 0 .. NINDIRECT = BISIZE / u32
                if addr > 0 {
                    bfree(self.dev, addr);
                }
            }
            drop(bp);
            bfree(self.dev, *naddr);
            *naddr = 0;
        }

        let ndaddr = self.addrs.get_mut(NDIRECT + 1).unwrap();
        if *ndaddr > 0 {
            let bp = BCACHE.read(self.dev, *ndaddr);
            let a = bp.align_to::<u32>();
            for &a_addr in a.iter() {
                if a_addr > 0 {
                    let cp = BCACHE.read(self.dev, a_addr);
                    let b = cp.align_to::<u32>();
                    for &b_addr in b.iter() {
                        if b_addr > 0 {
                            bfree(self.dev, b_addr);
                        }
                    }
                    drop(cp);
                    bfree(self.dev, a_addr);
                }
            }
            drop(bp);
            bfree(self.dev, *ndaddr);
            *ndaddr = 0;
        }
        self.size = 0;
        // update is needed, because size and addrs are updated.
        self.update();
    }

    // Inode content
    //
    // The content (data) associated with each inode is stored
    // in blocks on the disk. The first NDIRECT block numbers
    // are listed in idata.addrs[]. The next NINDIRECT blocks
    // are listed in block idata.addrs[NDIRECT].
    // The next NDINDIRECT blocks are listed in block
    // idata.addrs[NDIRECT + 1].
    //
    // Return the disk block address of the nth block in inode ip.
    // If there is no such block, bmap allocates one.
    pub fn bmap(&mut self, bn: u32, alloc: bool) -> Result<u32> {
        let mut addr;
        let mut bn = bn as usize;

        if bn < NDIRECT {
            addr = self.addrs[bn];
            if addr == 0 && alloc {
                addr = balloc(self.dev);
                self.set_addrs(bn, addr);
            }
            return Ok(addr);
        }
        bn -= NDIRECT;

        if bn < NINDIRECT {
            // Load indirect block, allocating if necessary.
            addr = self.addrs[NDIRECT];
            if addr == 0 && alloc {
                addr = balloc(self.dev);
                self.set_addrs(NDIRECT, addr);
            }
            let mut bp = BCACHE.read(self.dev, addr);
            let a = bp.align_to_mut::<u32>();
            addr = a[bn];
            if addr == 0 && alloc {
                addr = balloc(self.dev);
                a[bn] = addr;
                LOG.write(bp);
            }
            return Ok(addr);
        }
        bn -= NINDIRECT;

        if bn < NDINDIRECT {
            // Load double indirect block, allocating if necessary.
            addr = self.addrs[NDIRECT + 1];
            if addr == 0 && alloc {
                addr = balloc(self.dev);
                self.set_addrs(NDIRECT + 1, addr);
            }
            // Load 2nd layer block.
            {
                let mut bp = BCACHE.read(self.dev, addr);
                let a = bp.align_to_mut::<u32>();
                let dbn = bn / NINDIRECT;
                addr = a[dbn];
                if addr == 0 && alloc {
                    addr = balloc(self.dev);
                    a[dbn] = addr;
                    LOG.write(bp);
                }
            }
            // now find disk block
            let mut bp = BCACHE.read(self.dev, addr);
            let a = bp.align_to_mut::<u32>();
            let bn = bn % NINDIRECT;
            addr = a[bn];
            if addr == 0 && alloc {
                addr = balloc(self.dev);
                a[bn] = addr;
                LOG.write(bp);
            }
            return Ok(addr);
        }

        Err(StorageFull)
    }

    // Copy stat information from inode.
    // Caller must hold sleeplock
    pub fn stat(&self, st: &mut Stat) {
        st.dev = self.dev;
        st.ino = self.inum;
        st.ftype = self.itype;
        st.nlink = self.nlink;
        st.size = self.size as usize;
    }

    // Read data from inode.
    // dst is UVAddr or KVAddr
    pub fn read(&mut self, mut dst: VirtAddr, off: u32, mut n: usize) -> Result<usize> {
        let mut tot = 0;
        let mut off = off as usize;

        if off > self.size as usize {
            return Ok(0);
        }
        if off + n > self.size as usize {
            n = self.size as usize - off;
        }

        while tot < n {
            let bp = BCACHE.read(self.dev, self.bmap((off / BSIZE) as u32, false)?);
            let m = core::cmp::min(n - tot, BSIZE - off % BSIZE);
            either_copyout(dst, &bp[(off % BSIZE)..(off % BSIZE + m)])?;
            tot += m;
            off += m;
            dst += m;
        }
        Ok(tot)
    }

    // Write data to inode.
    // Caller must hold sleeplock.
    // dst is UVAddr or KVAddr
    // Returns the number of bytes successfully written.
    // If the return value is less then the requested n,
    // there was an error of some kind.
    pub fn write(&mut self, mut src: VirtAddr, off: u32, n: usize) -> Result<usize> {
        let mut tot = 0;
        let mut off = off as usize;

        if off > self.size as usize || off + n > MAXFILE * BSIZE {
            return Err(FileTooLarge);
        }

        while tot < n {
            let mut bp = BCACHE.read(self.dev, self.bmap((off / BSIZE) as u32, true)?);
            let m = core::cmp::min(n - tot, BSIZE - off % BSIZE);
            either_copyin(&mut bp[(off % BSIZE)..(off % BSIZE + m)], src)?;
            tot += m;
            off += m;
            src += m;
            LOG.write(bp);
        }

        if off > self.size as usize {
            self.set_size(off as u32);
        }

        Ok(tot)
    }

    // Directories

    // Look for a directory entry in a directory.
    // If found, set *poff to byte offset of entry.
    pub fn dirlookup(&mut self, name: &str, poff: Option<&mut u32>) -> Result<Inode> {
        let mut de: DirEnt = Default::default();
        if self.itype != FileType::Dir {
            return Err(NotADirectory);
        }

        for off in (0..self.size).step_by(size_of::<DirEnt>()) {
            self.read(
                VirtAddr::Kernel(&mut de as *mut _ as usize),
                off,
                size_of::<DirEnt>(),
            )?;
            if de.inum == 0 {
                continue;
            }
            if name
                == core::str::from_utf8(&de.name)
                    .unwrap()
                    .trim_matches(char::from(0))
            {
                // entry matches path element
                if let Some(poff) = poff {
                    *poff = off;
                }
                return ITABLE.get(self.dev, de.inum as u32);
            }
        }
        Err(NotFound)
    }

    // Write a new directory entry (name, inum) into the directory dp.
    pub fn dirlink(&mut self, name: &str, inum: u32) -> Result<()> {
        let mut de: DirEnt = Default::default();

        // check that name is not present.
        self.dirlookup(name, None).map_or_else(
            |err| if err == NotFound { Ok(()) } else { Err(err) },
            |_| Err(AlreadyExists),
        )?;

        // Look for an empty dirent
        let mut off = 0;
        while off < self.size {
            self.read(
                VirtAddr::Kernel(&mut de as *mut _ as usize),
                off,
                size_of::<DirEnt>(),
            )?;
            if de.inum == 0 {
                break;
            }
            off += size_of::<DirEnt>() as u32;
        }

        let len = core::cmp::min(name.len(), DIRSIZ);
        de.name.copy_from_slice(&[0; DIRSIZ]);
        de.name[0..len].copy_from_slice(&name.as_bytes()[0..len]);
        de.inum = inum as u16;
        self.write(
            VirtAddr::Kernel(&mut de as *mut _ as usize),
            off,
            size_of::<DirEnt>(),
        )?;
        Ok(())
    }

    // Is the directory dp empty except for "." and ".." ?
    pub fn is_dir_empty(&mut self) -> bool {
        let mut de: DirEnt = Default::default();
        for off in ((2 * size_of::<DirEnt>() as u32)..self.size).step_by(size_of::<DirEnt>()) {
            if self
                .read(
                    VirtAddr::Kernel(&mut de as *mut _ as usize),
                    off,
                    size_of::<DirEnt>(),
                )
                .is_err()
            {
                panic!("isdirempty: inode read");
            }
            if de.inum != 0 {
                return false;
            }
        }
        true
    }
}

#[cfg(all(target_os = "none", feature = "kernel"))]
impl MInode {
    fn new(dev: u32, inum: u32) -> Self {
        Self {
            dev,
            inum,
            data: SleepLock::new(IData::new(dev, inum), "inode"),
        }
    }

    // unlock function is no need.
    // because SleepLockGuard impl Drop trait.

    // Lock the inode
    // Reads the inode from disk if necessary.
    pub fn lock(&self) -> SleepLockGuard<IData> {
        let sb = SB.get().unwrap();
        let mut guard = self.data.lock();
        if !guard.valid {
            let bp = BCACHE.read(self.dev, sb.iblock(self.inum));
            let dip = bp
                .align_to::<DInode>()
                .get(self.inum as usize % IPB)
                .unwrap();
            guard.itype = dip.itype;
            guard.major = dip.major;
            guard.minor = dip.minor;
            guard.nlink = dip.nlink;
            guard.size = dip.size;
            guard.addrs.copy_from_slice(&dip.addrs);
            guard.valid = true;
            guard.dev = self.dev;
            guard.inum = self.inum;
            if guard.itype == FileType::Empty {
                panic!("ilock: no type");
            }
        }
        guard
    }
}

#[cfg(all(target_os = "none", feature = "kernel"))]
impl Inode {
    fn new(ip: Arc<MInode>) -> Self {
        Self { ip: Some(ip) }
    }
    // Increments reference count fot Inode.
    // Return cloned Inode to enable ip = ip1.dup() idiom.
    pub fn dup(&self) -> Self {
        Self {
            ip: self.ip.clone(),
        }
    }
    pub fn is_some(&self) -> bool {
        self.ip.is_some()
    }
    pub fn is_none(&self) -> bool {
        self.ip.is_none()
    }
}

#[cfg(all(target_os = "none", feature = "kernel"))]
impl Drop for Inode {
    fn drop(&mut self) {
        ITABLE.put(self.ip.take().unwrap());
    }
}

#[cfg(all(target_os = "none", feature = "kernel"))]
impl Deref for Inode {
    type Target = MInode;
    fn deref(&self) -> &Self::Target {
        // ref count >2 ?
        self.ip.as_ref().unwrap()
    }
}

#[cfg(all(target_os = "none", feature = "kernel"))]
type ITable = Mutex<[Option<Arc<MInode>>; NINODE]>;

#[cfg(all(target_os = "none", feature = "kernel"))]
impl ITable {
    // Allocate an inode on device dev.
    // Mark it as allocated by giving it type.
    // Returns an unlocked but allocated and referenced inode.
    fn alloc(&self, dev: u32, itype: FileType) -> Result<Inode> {
        let sb = SB.get().unwrap();
        for inum in 1..sb.ninodes {
            let mut bp = BCACHE.read(dev, sb.iblock(inum));
            let dip = bp
                .align_to_mut::<DInode>()
                .get_mut(inum as usize % IPB)
                .unwrap();
            if dip.itype == FileType::Empty {
                // a free inode
                *dip = Default::default();
                dip.itype = itype;
                LOG.write(bp);
                return self.get(dev, inum);
            }
        }
        Err(StorageFull) // no inodes
    }

    // Find the inode with number inum on device dev
    // and return the in-memoroy copy. Does not lock
    // the inode and does not read it from disk.
    fn get(&self, dev: u32, inum: u32) -> Result<Inode> {
        let mut guard = self.lock();

        // Is the inode already in the table?
        let mut empty: Option<&mut Option<Arc<MInode>>> = None;
        for ip in guard.iter_mut() {
            match ip {
                Some(ip) if ip.dev == dev && ip.inum == inum => {
                    return Ok(Inode::new(Arc::clone(ip)));
                }
                None if empty.is_none() => {
                    empty = Some(ip);
                }
                _ => (),
            }
        }

        // Recycle an inode entry
        let empty = match empty {
            Some(ip) => ip,
            None => return Err(FileTableOverflow),
        };

        let ip = Arc::new(MInode::new(dev, inum));
        empty.replace(Arc::clone(&ip));
        Ok(Inode::new(ip))
    }

    // Drop a reference to an in-memory inode.
    // If that was the last reference, the inode table entry can
    // be recycled.
    // If that was the last reference and the inode has no links
    // to it, free the inode (and its content) on disk.
    // All calls to put() must be inside a transaction in
    // case it has to free the inode.
    fn put(&self, inode: Arc<MInode>) {
        let mut guard = self.lock();

        if Arc::strong_count(&inode) == 2 {
            // Arc::strong_count(inode) == 2 means no other process can have inode sleeplocked,
            // so this sleeplock won't block (or dead lock).
            let mut idata = inode.data.lock();
            let itable = Mutex::unlock(guard);

            if idata.valid && idata.nlink == 0 {
                // inode has no links and no other references: truncate and free.
                idata.trunc();
                idata.set_type(FileType::Empty);
                idata.valid = false;
            }

            guard = itable.lock();
            // drop in-memory inode.
            for mip in guard.iter_mut() {
                match mip {
                    Some(ip) if Arc::ptr_eq(&inode, ip) => {
                        mip.take();
                    }
                    _ => (),
                }
            }
        }
    }
}

// Create the path new as a link to the same inode as old.
#[cfg(all(target_os = "none", feature = "kernel"))]
pub fn link(old: &Path, new: &Path) -> Result<()> {
    let (_, ip) = old.namei()?;
    {
        let ip_guard = ip.lock();
        if ip_guard.itype == FileType::Dir {
            return Err(IsADirectory);
        }
    }
    // ?

    let (name, dp) = new.nameiparent()?;
    let mut dp_guard = dp.lock();
    if dp.dev != ip.dev {
        return Err(CrossesDevices);
    }
    dp_guard.dirlink(name, ip.inum)?;

    {
        let mut ip_guard = ip.lock();
        ip_guard.nlink += 1;
        ip_guard.update();
    }
    Ok(())
}

#[cfg(all(target_os = "none", feature = "kernel"))]
pub fn unlink(path: &Path) -> Result<()> {
    let de: DirEnt = Default::default();
    let mut off: u32 = 0;

    let (name, dp) = path.nameiparent()?;
    let mut dp_guard = dp.lock();

    // Cannot unlink "." or ".."
    if name == "." || name == ".." {
        return Err(PermissionDenied);
    }

    let ip = dp_guard.dirlookup(name, Some(&mut off))?;
    let mut ip_guard = ip.lock();

    if ip_guard.nlink < 1 {
        panic!("unlink: nlink < 1");
    }
    if ip_guard.itype == FileType::Dir && !ip_guard.is_dir_empty() {
        return Err(DirectoryNotEmpty);
    }

    dp_guard.write(
        VirtAddr::Kernel(&de as *const _ as usize),
        off,
        size_of::<DirEnt>(),
    )?;
    if ip_guard.itype == FileType::Dir {
        dp_guard.set_nlink(LinkOp::Minus);
    }

    ip_guard.set_nlink(LinkOp::Minus);

    Ok(())
}

#[cfg(all(target_os = "none", feature = "kernel"))]
pub fn create(path: &Path, type_: FileType, major: u16, minor: u16) -> Result<Inode> {
    let (name, dp) = path.nameiparent()?;

    let ip: Inode;
    {
        let mut dp_guard = dp.lock();

        if let Ok(ip) = dp_guard.dirlookup(name, None) {
            SleepLock::unlock(dp_guard);
            let ip_guard = ip.lock();
            match type_ {
                FileType::File
                    if ip_guard.itype == FileType::File || ip_guard.itype == FileType::Device =>
                {
                    SleepLock::unlock(ip_guard);
                    return Ok(ip);
                }
                _ => return Err(AlreadyExists),
            }
        }

        ip = ITABLE.alloc(dp.dev, type_)?;
        let mut ip_guard = ip.lock();

        if type_ == FileType::Dir {
            // Create . and .. entries.
            // No ip->nlink++ for ".": avoid cyclic ref count.
            ip_guard.dirlink(".", ip.inum)?;
            ip_guard.dirlink("..", dp.inum)?;
        }

        dp_guard.dirlink(name, ip.inum)?;

        // now that success is guaranteed

        if type_ == FileType::Dir {
            dp_guard.set_nlink(LinkOp::Plus); // for ".."
        }

        ip_guard.set_major_minor(Major::from_u16(major), minor);
        ip_guard.set_nlink(LinkOp::Init(1));
    }

    Ok(ip)
}

// Paths
// A slice of a path (akin to str)
#[cfg(all(target_os = "none", feature = "kernel"))]
#[derive(Debug)]
#[repr(C)]
pub struct Path {
    inner: str,
}

#[cfg(all(target_os = "none", feature = "kernel"))]
impl AsRef<Path> for str {
    fn as_ref(&self) -> &Path {
        Path::new(self)
    }
}

#[cfg(all(target_os = "none", feature = "kernel"))]
impl Path {
    pub fn new<S: AsRef<str> + ?Sized>(s: &S) -> &Path {
        unsafe { &*(s.as_ref() as *const str as *const Path) }
    }

    pub fn file_name(&self) -> Option<&str> {
        if self.inner.ends_with("..") {
            return None;
        }
        match self.inner.rsplit_once('/') {
            Some((_, file_name)) => Some(file_name),
            None => Some(&self.inner),
        }
    }

    // Get next path element from path as name &str,
    // the element following the name as &Path
    //
    // Examples:
    //   skip_elem("a/bb/c") = (Some("a"), Some("bb/c")),
    //   skip_elem("///a//bb") = (Some("a"), Some("/bb")),
    //   skipelem("a") = (Some("a"), None)
    //   skipelem("") = skipelem("////") = (None, None)
    //   if name: &str > DIRSIZE return (None, None)
    pub fn skip_elem(&self) -> (Option<&str>, Option<&Path>) {
        match self.inner.trim_matches('/').split_once('/') {
            Some((name, path)) if name.len() <= DIRSIZ => (Some(name), Some(Path::new(path))),
            None if !self.inner.trim_matches('/').is_empty()
                && self.inner.trim_matches('/').len() < DIRSIZ =>
            {
                (Some(self.inner.trim_matches('/')), None)
            }
            _ => (None, None),
        }
    }

    // Look up and return the inode for a path name.
    // If `parent` is true, return the inode for the parent.
    // Must be called inside a transaction since it calls ITABLE.put()
    // when dropping an inode.
    // # Safety:
    // call inside a transaction.
    pub fn namex(path: &Path, parent: bool) -> Result<(&str, Inode)> {
        let mut ip = match path.inner.get(0..1) {
            Some("/") => ITABLE.get(ROOTDEV, ROOTINO)?,
            _ => Cpus::myproc().unwrap().data().cwd.as_ref().unwrap().dup(),
        };

        let mut path = path;
        loop {
            let mut guard = ip.lock();
            if guard.itype != FileType::Dir {
                return Err(NotADirectory);
            }
            match path.skip_elem() {
                (Some(name), Some(npath)) => {
                    let nip = guard.dirlookup(name, None)?;
                    SleepLock::unlock(guard);
                    ip = nip;
                    path = npath;
                    continue;
                }
                (Some(name), None) if !parent => {
                    let ip = guard.dirlookup(name, None)?;
                    SleepLock::unlock(guard);
                    break Ok((name, ip));
                }
                (Some(name), None) => {
                    SleepLock::unlock(guard);
                    break Ok((name, ip));
                }
                _ => {
                    if let Some("/") = path.inner.get(..) {
                        SleepLock::unlock(guard);
                        break Ok(("/", ip));
                    } else {
                        break Err(NotFound);
                    }
                }
            }
        }
    }

    pub fn namei(&self) -> Result<(&str, Inode)> {
        Self::namex(self, false)
    }

    pub fn nameiparent(&self) -> Result<(&str, Inode)> {
        Self::namex(self, true)
    }
}

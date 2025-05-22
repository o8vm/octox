use crate::defs::AsBytes;
use crate::error::{Error::*, Result};
use crate::memlayout::{
    KERNBASE, PHYSTOP, PLIC, STACK_PAGE_NUM, TRAMPOLINE, TRAPFRAME, UART0, VIRTIO0,
};
use crate::proc::PROCS;
use crate::riscv::{pgroundup, pteflags::*, registers::satp, sfence_vma, PGSHIFT, PGSIZE};
use crate::sync::OnceLock;
use alloc::boxed::Box;
use core::cmp::{Ord, PartialEq, PartialOrd};
use core::convert::From;
use core::fmt::Debug;
use core::marker::PhantomData;
use core::ops::{Add, AddAssign, Deref, DerefMut, Index, IndexMut, Sub, SubAssign};

use crate::trampoline::trampoline; // trampoline.rs
extern "C" {
    // kernel.ld sets this to end of kernel code.
    fn etext();
}

pub static mut KVM: OnceLock<Kvm> = OnceLock::new();

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct PAddr(usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct KVAddr(pub usize);

impl KVAddr {
    pub const fn new(address: usize) -> Self {
        Self(address)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Default)]
#[repr(transparent)]
pub struct UVAddr(usize);

unsafe impl AsBytes for UVAddr {}

#[derive(Debug, Copy, Clone)]
pub enum VirtAddr {
    User(usize),
    Kernel(usize),
    Physical(usize),
}

impl From<UVAddr> for VirtAddr {
    fn from(uv: UVAddr) -> Self {
        VirtAddr::User(uv.0)
    }
}

impl From<KVAddr> for VirtAddr {
    fn from(kv: KVAddr) -> Self {
        VirtAddr::Kernel(kv.0)
    }
}

impl From<PAddr> for VirtAddr {
    fn from(pv: PAddr) -> Self {
        VirtAddr::Physical(pv.0)
    }
}

pub trait Addr
where
    Self: Copy
        + From<usize>
        + Add<usize, Output = Self>
        + Sub<usize, Output = Self>
        + AddAssign<usize>
        + SubAssign<usize>
        + PartialEq
        + Eq
        + Ord
        + PartialOrd,
{
    fn get(&self) -> &usize;

    fn get_mut(&mut self) -> &mut usize;

    fn into_usize(self) -> usize;

    fn is_aligned(&self) -> bool {
        self.get() % PGSIZE == 0
    }
    fn roundup(&mut self) {
        *self.get_mut() = (*self.get() + PGSIZE - 1) & !(PGSIZE - 1);
    }
    fn rounddown(&mut self) {
        *self.get_mut() = *self.get() & !(PGSIZE - 1);
    }
}

pub trait VAddr: Addr + Debug {
    // extract the three 9-bit page table indices from a virtual address.
    const PXMASK: usize = 0x1FF; // 9 bits
    fn px(&self, level: usize) -> usize;
    // one beyond the highest possible virtual address.
    // MAXVA is actually one bit less than the max allowed by
    // Sv39, to avoid having to sign-extend virtual addresses
    // that have the high bit set.
    const MAXVA: usize = 1 << (9 + 9 + 9 + 12 - 1);
}

macro_rules! impl_addr {
    ($typ:ident) => {
        impl From<usize> for $typ {
            fn from(value: usize) -> Self {
                Self(value)
            }
        }
        impl Add<usize> for $typ {
            type Output = Self;
            fn add(self, rhs: usize) -> Self::Output {
                Self(self.0 + rhs)
            }
        }
        impl AddAssign<usize> for $typ {
            fn add_assign(&mut self, rhs: usize) {
                self.0 += rhs;
            }
        }
        impl Sub<usize> for $typ {
            type Output = Self;
            fn sub(self, rhs: usize) -> Self::Output {
                Self(self.0 - rhs)
            }
        }
        impl SubAssign<usize> for $typ {
            fn sub_assign(&mut self, other: usize) {
                self.0 -= other;
            }
        }
        impl Sub for $typ {
            type Output = usize;
            fn sub(self, rhs: Self) -> Self::Output {
                self.0 - rhs.0
            }
        }
        impl Addr for $typ {
            fn get(&self) -> &usize {
                &self.0
            }
            fn get_mut(&mut self) -> &mut usize {
                &mut self.0
            }
            fn into_usize(self) -> usize {
                self.0
            }
        }
    };
}

macro_rules! impl_vaddr {
    ($typ:ident) => {
        impl VAddr for $typ {
            fn px(&self, level: usize) -> usize {
                (self.0 >> (PGSHIFT + 9 * level)) & Self::PXMASK
            }
        }
    };
}

impl_addr!(PAddr);
impl_addr!(KVAddr);
impl_addr!(UVAddr);
impl_vaddr!(KVAddr);
impl_vaddr!(UVAddr);

impl Add<usize> for VirtAddr {
    type Output = Self;
    fn add(self, rhs: usize) -> Self::Output {
        match self {
            VirtAddr::Kernel(addr) => VirtAddr::Kernel(addr + rhs),
            VirtAddr::User(addr) => VirtAddr::User(addr + rhs),
            VirtAddr::Physical(addr) => VirtAddr::Physical(addr + rhs),
        }
    }
}
impl AddAssign<usize> for VirtAddr {
    fn add_assign(&mut self, rhs: usize) {
        *self = match *self {
            VirtAddr::Kernel(addr) => VirtAddr::Kernel(addr + rhs),
            VirtAddr::User(addr) => VirtAddr::User(addr + rhs),
            VirtAddr::Physical(addr) => VirtAddr::Physical(addr + rhs),
        };
    }
}

// safety: ptr must have been dropped with box::from_raw().
pub unsafe trait PageAllocator: Sized {
    unsafe fn try_new_zeroed() -> Option<*mut Self> {
        match Box::<Self>::try_new_zeroed() {
            Ok(mem) => Some(Box::into_raw(mem.assume_init())),
            Err(_) => None,
        }
    }
}

#[derive(Clone)]
#[repr(C, align(4096))]
pub struct Page([u8; 4096]);
unsafe impl PageAllocator for Page {}

#[allow(dead_code)]
pub struct Stack([u8; PGSIZE * STACK_PAGE_NUM]);
unsafe impl PageAllocator for Stack {}

#[derive(Debug, Clone, Copy)]
#[repr(C, align(4096))]
struct RawPageTable {
    entries: [PageTableEntry; 512],
}
unsafe impl PageAllocator for RawPageTable {}

impl Index<usize> for RawPageTable {
    type Output = PageTableEntry;
    fn index(&self, index: usize) -> &Self::Output {
        &self.entries[index]
    }
}

impl IndexMut<usize> for RawPageTable {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.entries[index]
    }
}

impl Deref for RawPageTable {
    type Target = [PageTableEntry; 512];
    fn deref(&self) -> &Self::Target {
        &self.entries
    }
}

impl DerefMut for RawPageTable {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.entries
    }
}

#[derive(Debug, Clone, Copy)]
#[repr(transparent)]
pub struct PageTableEntry(usize);

impl PageTableEntry {
    pub const fn new(value: usize) -> Self {
        Self(value)
    }

    pub fn is_v(&self) -> bool {
        self.0 & PTE_V != 0
    }

    pub fn is_u(&self) -> bool {
        self.0 & PTE_U != 0
    }

    pub fn rm_u(&mut self) {
        self.0 &= !PTE_U;
    }

    pub fn is_leaf(&self) -> bool {
        (self.0 & (PTE_R | PTE_W | PTE_X)) != 0
    }

    pub fn flags(&self) -> usize {
        self.0 & 0x3FF
    }

    pub fn to_pa(&self) -> PAddr {
        ((self.0 >> 10) << 12).into()
    }

    pub fn set(&mut self, pa: usize, attr: usize) {
        self.0 = ((pa >> 12) << 10) | attr;
    }
}

#[derive(Debug, Clone)]
pub struct PageTable<V: VAddr> {
    ptr: *mut RawPageTable,
    _marker: PhantomData<V>,
}

impl<V: VAddr> PageTable<V> {
    pub fn new() -> Option<Self> {
        Some(Self {
            ptr: unsafe { RawPageTable::try_new_zeroed()? },
            _marker: PhantomData,
        })
    }

    fn from_pa(addr: PAddr) -> Self {
        Self {
            ptr: addr.into_usize() as *mut RawPageTable,
            _marker: PhantomData,
        }
    }

    pub fn as_satp(&self) -> usize {
        satp::make(satp::Mode::Sv39, 0, self.ptr as usize)
    }

    // Find the address of the PTE in page table pagetable
    // that corresponds to virtual address va. if alloc == true
    // create any required page-table pages.
    //
    // The risc-v Sv39 scheme has three levels of page-table
    // pages. A page-table page contains 512 64-bit PTEs.
    // A 64-bit virtual address is split into five fields:
    //   39..63 -- must be zero.
    //   30..38 -- 9 bits of level-2 index.
    //   21..29 -- 9 bits of level-1 index.
    //   12..20 -- 9 bits of level-0 index.
    //    0..11 -- 12 bits of byte offset within the page.
    pub fn walk(&mut self, va: V, alloc: bool) -> Option<&mut PageTableEntry> {
        let mut pagetable = self.ptr;
        if va.into_usize() >= V::MAXVA {
            panic!("walk");
        }

        unsafe {
            for level in (1..3).rev() {
                let pte = (*pagetable).get_mut(va.px(level))?;
                if pte.is_v() {
                    pagetable = pte.to_pa().into_usize() as *mut RawPageTable;
                } else {
                    if !alloc {
                        return None;
                    }
                    pagetable = RawPageTable::try_new_zeroed()?;
                    pte.set(pagetable as usize, PTE_V);
                }
            }
            (*pagetable).get_mut(va.px(0))
        }
    }

    // Look up a virtual address, return the physical address,
    // or None if not mapped.
    // Can only be used to look up user pages.
    pub fn walkaddr(&mut self, va: V) -> Result<PAddr> {
        if va.into_usize() >= V::MAXVA {
            return Err(BadVirtAddr);
        }
        match self.walk(va, false) {
            None => Err(BadVirtAddr),
            Some(pte) if !pte.is_v() => Err(BadVirtAddr),
            Some(pte) if !pte.is_u() => Err(BadVirtAddr),
            Some(pte) => Ok(pte.to_pa()),
        }
    }

    // Create PTEs for Virtual addresses starting at va that refer to
    // physical addresses starting at pa. va and size might not
    // be page-aligned. Returns Ok(()) on success, Err(()) if walk() couldn't
    // allocate a needed page-table page.
    pub fn mappages(&mut self, mut va: V, mut pa: PAddr, size: usize, perm: usize) -> Result<()> {
        if size == 0 {
            panic!("mappages: size");
        }

        let mut last = va + size - 1;
        va.rounddown();
        last.rounddown();
        loop {
            let pte = self.walk(va, true).ok_or(OutOfMemory)?;
            if pte.is_v() {
                panic!("mappages: remap");
            }
            pte.set(pa.into_usize(), perm | PTE_V);
            if va == last {
                break;
            }
            va += PGSIZE;
            pa += PGSIZE;
        }
        Ok(())
    }

    // Recursively free page-table pages.
    // All leaf mappings must be already have been removed.
    pub fn freewalk(self) {
        let pagetable = unsafe { &mut *self.ptr };
        for pte in pagetable.iter_mut() {
            if pte.is_v() && !pte.is_leaf() {
                let child: PageTable<V> = PageTable::from_pa(pte.to_pa());
                child.freewalk();
                *pte = PageTableEntry::new(0);
            } else if pte.is_v() {
                panic!("freewalk: leaf");
            }
        }
        // RawPageTable ptr must be dropped with Box::from_raw()
        let _pg = unsafe { Box::from_raw(self.ptr) };
    }
}

#[derive(Debug, Clone)]
pub struct Uvm {
    page_table: PageTable<UVAddr>,
}

impl Deref for Uvm {
    type Target = PageTable<UVAddr>;
    fn deref(&self) -> &Self::Target {
        &self.page_table
    }
}

impl DerefMut for Uvm {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.page_table
    }
}

impl Uvm {
    // Remove npages of mappings starting from va. va must be
    // page-aligned. The mappings must exist.
    // Optionally free the physical memory.
    pub fn unmap(&mut self, va: UVAddr, npages: usize, do_free: bool) {
        if !va.is_aligned() {
            panic!("uvmunmap: not aligned");
        }

        let mut a = va;
        while a < va + npages * PGSIZE {
            match self.page_table.walk(a, false) {
                None => panic!("uvmunmap(): walk"),
                Some(pte) if !pte.is_v() => panic!("uvmunmap(): not mapped"),
                Some(pte) if !pte.is_leaf() => panic!("uvmunmap(): not a leaf"),
                Some(pte) => {
                    if do_free {
                        let pa = pte.to_pa();
                        unsafe {
                            let _pg = Box::from_raw(pa.into_usize() as *mut Page);
                        }
                    }
                    *pte = PageTableEntry(0);
                }
            }
            a += PGSIZE;
        }
    }

    // create an empty user page table.
    // return None if out of memory.
    pub fn create() -> Result<Uvm> {
        Ok(Uvm {
            page_table: PageTable::new().ok_or(OutOfMemory)?,
        })
    }

    // Allocate PTEs and physical memory to grow process from oldsz to
    // newsz, which need not be page aligned. Returns Result<newsz>.
    pub fn alloc(&mut self, mut oldsz: usize, newsz: usize, xperm: usize) -> Result<usize> {
        if newsz < oldsz {
            return Ok(oldsz);
        }

        oldsz = pgroundup(oldsz);
        for a in (oldsz..newsz).step_by(PGSIZE) {
            let mem = match Box::<Page>::try_new_zeroed() {
                Ok(mem) => Box::into_raw(unsafe { mem.assume_init() }),
                Err(_) => {
                    self.dealloc(a, oldsz);
                    return Err(OutOfMemory);
                }
            };
            if let Err(err) = self.mappages(
                a.into(),
                (mem as usize).into(),
                PGSIZE,
                PTE_R | PTE_U | xperm,
            ) {
                unsafe {
                    let _pg = Box::from_raw(mem);
                }
                self.dealloc(a, oldsz);
                return Err(err);
            }
        }
        Ok(newsz)
    }

    // Deallocate user pages to bring the process size from oldsz to
    // newsz. oldsz and newsz need not be page-aligned, nor does newsz
    // need to be less than oldsz, oldsz can be larger than actual
    // process size. Returns the new process size.
    pub fn dealloc(&mut self, oldsz: usize, newsz: usize) -> usize {
        if newsz >= oldsz {
            return oldsz;
        }

        if pgroundup(newsz) < pgroundup(oldsz) {
            let npages = (pgroundup(oldsz) - pgroundup(newsz)) / PGSIZE;
            self.unmap(pgroundup(newsz).into(), npages, true);
        }
        newsz
    }

    // Free user memory pages,
    // then free page-table pages.
    pub fn free(mut self, size: usize) {
        if size > 0 {
            self.unmap(0.into(), pgroundup(size) / PGSIZE, true);
        }
        self.page_table.freewalk();
    }

    // Given a parent process's page table, copy
    // its memory into a child's page table.
    // Copies both the page table and physical memory.
    // returns Result<()>
    pub fn copy(&mut self, new: &mut Self, size: usize) -> Result<()> {
        let mut va = UVAddr::from(0);
        while va.into_usize() < size {
            match self.walk(va, false) {
                Some(pte) => {
                    if !pte.is_v() {
                        panic!("uvmcopy: page not present");
                    }
                    let pa = pte.to_pa();
                    let flags = pte.flags();
                    let mem = if let Some(mem) = unsafe { Page::try_new_zeroed() } {
                        mem
                    } else {
                        new.unmap(0.into(), va.into_usize() / PGSIZE, true);
                        return Err(OutOfMemory);
                    };
                    unsafe {
                        *mem = (*(pa.into_usize() as *mut Page)).clone();
                    }
                    if let Err(err) = new.mappages(va, (mem as usize).into(), PGSIZE, flags) {
                        unsafe {
                            let _pg = Box::from_raw(mem);
                        }
                        new.unmap(0.into(), va.into_usize() / PGSIZE, true);
                        return Err(err);
                    }
                }
                None => {
                    panic!("uvmcopy: pte should exist");
                }
            }
            va += PGSIZE;
        }
        Ok(())
    }

    // mark a PTE invalid for user access.
    // used by exec for the user stack guard page.
    pub fn clear(&mut self, va: UVAddr) {
        if let Some(pte) = self.walk(va, false) {
            pte.rm_u();
        } else {
            panic!("uvmclear");
        }
    }

    // Copy from kernel to user.
    // Copy bytes from src to virtual address dstva in a given page table.
    // Return Result<()>
    // # Safety
    // T mem layout is fixed
    pub fn copyout<T: ?Sized + AsBytes>(&mut self, mut dstva: UVAddr, src: &T) -> Result<()> {
        let src = src.as_bytes();
        let mut len = src.len();
        let mut offset = 0;
        while len > 0 {
            let mut va0 = dstva;
            va0.rounddown();
            let pa0 = self.page_table.walkaddr(va0)?;
            let n = core::cmp::min(PGSIZE - (dstva - va0), len);
            let dst = unsafe {
                core::slice::from_raw_parts_mut((pa0.into_usize() + (dstva - va0)) as *mut u8, n)
            };
            dst.copy_from_slice(&src[offset..(offset + n)]);
            len -= n;
            offset += n;
            dstva = va0 + PGSIZE;
        }
        Ok(())
    }

    // Copy from user to kernel.
    // Copy len bytes to dst from virtual address srcva in a given page table.
    // Return Result<()>
    // # safety:
    // T mem layout is fixed.
    pub fn copyin<T: ?Sized + AsBytes>(&mut self, dst: &mut T, mut srcva: UVAddr) -> Result<()> {
        let dst = dst.as_bytes_mut();
        let mut len = dst.len();
        let mut offset = 0;
        while len > 0 {
            let mut va0 = srcva;
            va0.rounddown();
            let pa0 = self.page_table.walkaddr(va0)?;
            let n = core::cmp::min(PGSIZE - (srcva - va0), len);
            let src = unsafe {
                core::slice::from_raw_parts((pa0.into_usize() + (srcva - va0)) as *mut u8, n)
            };
            dst[offset..(offset + n)].copy_from_slice(src);
            len -= n;
            offset += n;
            srcva = va0 + PGSIZE;
        }
        Ok(())
    }

    // Free a process's page table, and free the
    // physical memory it refers to.
    pub fn proc_uvmfree(mut self, size: usize) {
        self.unmap(TRAMPOLINE.into(), 1, false);
        self.unmap(TRAPFRAME.into(), 1, false);
        self.free(size);
    }
}

#[derive(Debug, Clone)]
pub struct Kvm {
    page_table: PageTable<KVAddr>,
}

impl Deref for Kvm {
    type Target = PageTable<KVAddr>;
    fn deref(&self) -> &Self::Target {
        &self.page_table
    }
}

impl DerefMut for Kvm {
    fn deref_mut(&mut self) -> &mut PageTable<KVAddr> {
        &mut self.page_table
    }
}

impl Kvm {
    pub unsafe fn new() -> Option<Self> {
        Some(Self {
            page_table: PageTable::new()?,
        })
    }
    // add a mapping to the kernel page table.
    // only used when booting.
    // does not flush TLB or enable paging.
    pub fn map(&mut self, va: KVAddr, pa: PAddr, size: usize, perm: usize) {
        if self.page_table.mappages(va, pa, size, perm).is_err() {
            panic!("kvmmap");
        }
    }
    unsafe fn make(&mut self) {
        self.map(UART0.into(), UART0.into(), PGSIZE, PTE_R | PTE_W);

        // virtio mmio disk interface
        self.map(VIRTIO0.into(), VIRTIO0.into(), PGSIZE, PTE_R | PTE_W);

        // PLIC
        self.map(PLIC.into(), PLIC.into(), 0x0040_0000, PTE_R | PTE_W);

        // map kernel text executable and read-only.
        self.map(
            KERNBASE.into(),
            KERNBASE.into(),
            (etext as usize) - KERNBASE,
            PTE_R | PTE_X,
        );

        // map kernel data and the physical RAM we'll make use of.
        self.map(
            (etext as usize).into(),
            (etext as usize).into(),
            PHYSTOP - (etext as usize),
            PTE_R | PTE_W,
        );

        // map the trampoline for trap entry/exit to
        // the highest virtual address in the kernel.
        self.map(
            TRAMPOLINE.into(),
            (trampoline as usize).into(),
            PGSIZE,
            PTE_R | PTE_X,
        );

        // map kernel stacks
        PROCS.mapstacks();
    }
}

// Initialize the one kernel_pagetable
#[allow(static_mut_refs)]
pub fn kinit() {
    unsafe {
        KVM.set(Kvm::new().unwrap()).unwrap();
        KVM.get_mut().unwrap().make();
    }
}

// Switch h/w page table register to the kernel's page table,
// and enable paging.
#[allow(static_mut_refs)]
pub fn kinithart() {
    unsafe {
        satp::write(KVM.get().unwrap().as_satp());
        sfence_vma();
    }
}

use crate::bio::BCACHE;
use crate::defs::AsBytes;
use crate::elf::{self, ElfHdr, ProgHdr};
use crate::error::{Error::*, Result};
use crate::exec::flags2perm;
use crate::file::File;
use crate::fs::{self, Inode};
use crate::log::LOG;
use crate::memlayout::{kstack, STACK_PAGE_NUM, TRAMPOLINE, TRAPFRAME};
use crate::param::*;
use crate::riscv::{pteflags::*, *};
use crate::spinlock::{Mutex, MutexGuard};
use crate::swtch::swtch;
use crate::sync::{LazyLock, OnceLock};
use crate::trampoline::trampoline;
use crate::trap::usertrap_ret;
use crate::vm::{Addr, KVAddr, PAddr, PageAllocator, UVAddr, Uvm, VirtAddr, KVM};
use crate::{array, println};
use alloc::string::String;
use alloc::vec::Vec;
use alloc::{boxed::Box, sync::Arc};
use core::arch::asm;
use core::mem::size_of;
use core::sync::atomic::{AtomicUsize, Ordering};
use core::{cell::UnsafeCell, ops::Drop};

pub static CPUS: Cpus = Cpus::new();

#[allow(clippy::redundant_closure)]
pub static PROCS: LazyLock<Procs> = LazyLock::new(|| Procs::new());
pub static INITPROC: OnceLock<Arc<Proc>> = OnceLock::new();

pub struct Cpus([UnsafeCell<Cpu>; NCPU]);
unsafe impl Sync for Cpus {}

// Per-CPU state
#[derive(Debug)]
pub struct Cpu {
    pub proc: Option<Arc<Proc>>,  // The process running on this cpu, or None.
    pub context: Context,         // swtch() here to enter scheduler().
    pub noff: isize,              // Depth of interrupts lock(lock_mycpu() depth).
    pub nest: [&'static str; 20], // manage nest for debugging.
    pub intena: bool,             // Were interrupts enabled before lock_mycpu()?
}

impl Cpus {
    const fn new() -> Self {
        Self(array![UnsafeCell::new(Cpu::new()); NCPU])
    }

    // # Safety
    // Must be called with interrupts disabled,
    // to prevent race with process being moved
    // to a different CPU.
    #[inline]
    pub unsafe fn cpu_id() -> usize {
        let id;
        asm!("mv {0}, tp", out(reg) id);
        id
    }

    // Return the reference to this Cpus's Cpu struct.
    // # Safety
    // interrupts must be disabled.
    #[allow(clippy::mut_from_ref)]
    pub unsafe fn mycpu(&self) -> *mut Cpu {
        let id = Self::cpu_id();
        self.0[id].get()
    }

    // Return the current proc pointer: Some(Arc<Proc>), or None if none.
    pub fn myproc() -> Option<Arc<Proc>> {
        let _intr_lock = Self::lock_mycpu("withoutspin");
        let c;
        unsafe {
            c = &*CPUS.mycpu();
        }
        c.proc.clone()
    }

    // disable interrupts on mycpu().
    // if all `IntrLock` are dropped, interrupts may recover
    // to previous state.
    pub fn lock_mycpu(name: &str) -> IntrLock {
        let old = intr_get();
        intr_off();
        unsafe { (*CPUS.mycpu()).locked(old, name) }
    }
}

impl Cpu {
    const fn new() -> Self {
        Self {
            proc: None,
            context: Context::new(),
            noff: 0,
            nest: [
                "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "",
            ],
            intena: false,
        }
    }

    // if all `IntrLock`'s are dropped, interrupts may recover
    // to previous state.
    fn locked(&mut self, old: bool, _name: &str) -> IntrLock {
        if self.noff == 0 {
            self.intena = old;
        }
        self.noff += 1;
        IntrLock
    }

    pub fn unlock(&mut self) {
        // interrupts must be disabled.
        assert!(!intr_get(), "core unlock - interruptible");
        assert!(self.noff >= 1, "unlock");
        self.nest[(self.noff - 1) as usize] = "";

        self.noff -= 1;
        if self.noff == 0 && self.intena {
            intr_on()
        }
    }
}

#[derive(Debug)]
pub struct IntrLock;

impl Drop for IntrLock {
    fn drop(&mut self) {
        unsafe { (&mut *CPUS.mycpu()).unlock() }
    }
}

// Saved registers for kernel context switches.
#[derive(Clone, Copy, Debug)]
#[repr(C)]
pub struct Context {
    pub ra: usize,
    pub sp: usize,

    // callee-saved
    pub s0: usize,
    pub s1: usize,
    pub s2: usize,
    pub s3: usize,
    pub s4: usize,
    pub s5: usize,
    pub s6: usize,
    pub s7: usize,
    pub s8: usize,
    pub s9: usize,
    pub s10: usize,
    pub s11: usize,
}

// Per-process data for the trampoline.rs trap processing code, mapped
// to the page immediately below the trampoline page in the user page
// table. It is not mapped in the kernel page table. uservec() in trampoline.rs
// stores user registers in trapframe, restore registers from kernel_sp,
// kernel_hertid, and kernel_satp of trapframe, and jumps to the address
// pointed to by kernel_trap (usertrap()). The sequence of usertrap_ret()
// in trap.rs and userret() in trampoline.rs sets up kernel_* in trapframe,
// restores the user registers from trapframe, switches to the user page
// table and user space enters the user space. The return path to the
// user via usertrap_ret() does not return through the entire kernel
// call stack, so the trapframe contains calle-saved user registers
// such as s0-s11.
#[derive(Clone, Copy, Default, Debug)]
#[repr(C, align(4096))]
pub struct Trapframe {
    /*   0 */ pub kernel_satp: usize, // kernel page table
    /*   8 */ pub kernel_sp: usize, // top of process's kernel stack
    /*  16 */ pub kernel_trap: usize, // usertrap()
    /*  24 */ pub epc: usize, // saved user program counter
    /*  32 */ pub kernel_hartid: usize, // saved kernel tp
    /*  40 */ pub ra: usize,
    /*  48 */ pub sp: usize,
    /*  56 */ pub gp: usize,
    /*  64 */ pub tp: usize,
    /*  72 */ pub t0: usize,
    /*  80 */ pub t1: usize,
    /*  88 */ pub t2: usize,
    /*  96 */ pub s0: usize,
    /* 104 */ pub s1: usize,
    /* 112 */ pub a0: usize,
    /* 120 */ pub a1: usize,
    /* 128 */ pub a2: usize,
    /* 136 */ pub a3: usize,
    /* 144 */ pub a4: usize,
    /* 152 */ pub a5: usize,
    /* 160 */ pub a6: usize,
    /* 168 */ pub a7: usize,
    /* 176 */ pub s2: usize,
    /* 184 */ pub s3: usize,
    /* 192 */ pub s4: usize,
    /* 200 */ pub s5: usize,
    /* 208 */ pub s6: usize,
    /* 216 */ pub s7: usize,
    /* 224 */ pub s8: usize,
    /* 232 */ pub s9: usize,
    /* 240 */ pub s10: usize,
    /* 248 */ pub s11: usize,
    /* 256 */ pub t3: usize,
    /* 264 */ pub t4: usize,
    /* 272 */ pub t5: usize,
    /* 280 */ pub t6: usize,
}

#[derive(Debug)]
pub struct Procs {
    pub pool: [Arc<Proc>; NPROC],
    parents: Mutex<[Option<Arc<Proc>>; NPROC]>,
}
unsafe impl Sync for Procs {}

#[derive(Debug)]
pub struct Proc {
    // process table index.
    idx: usize,
    // lock must be held when using inner data:
    pub inner: Mutex<ProcInner>,
    // these are private to the process, so lock need not be held.
    pub data: UnsafeCell<ProcData>,
}
unsafe impl Sync for Proc {}

// lock must be held when uding these:
#[derive(Clone, Copy, Debug)]
pub struct ProcInner {
    pub state: ProcState, // Process state
    pub chan: usize,      // if non-zero, sleeping on chan
    pub killed: bool,     // if true, have been killed
    pub xstate: i32,      // Exit status to be returned to parent's wait
    pub pid: PId,         // Process ID
}

// These are private to the process, so lock need not be held.
#[derive(Debug)]
pub struct ProcData {
    pub kstack: KVAddr,                    // Virtual address of kernel stack
    pub sz: usize,                         // Size of process memory (bytes)
    pub uvm: Option<Uvm>,                  // User Memory Page Tabel
    pub trapframe: Option<Box<Trapframe>>, // data page for trampline.rs
    pub context: Context,                  // swtch() here to run process
    pub name: String,                      // Process name (debuggig)
    pub ofile: [Option<File>; NOFILE],     // Open files
    pub cwd: Option<Inode>,                // Current directory
}
unsafe impl Sync for ProcData {}
unsafe impl Send for ProcData {}

#[derive(PartialEq, Clone, Copy, Debug)]
pub enum ProcState {
    UNUSED,
    USED,
    SLEEPING,
    RUNNABLE,
    RUNNING,
    ZOMBIE,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct PId(usize);

impl PId {
    fn alloc() -> Self {
        static NEXTID: AtomicUsize = AtomicUsize::new(0);
        PId(NEXTID.fetch_add(1, Ordering::Relaxed))
    }
}

impl Context {
    pub const fn new() -> Self {
        Self {
            ra: 0,
            sp: 0,
            s0: 0,
            s1: 0,
            s2: 0,
            s3: 0,
            s4: 0,
            s5: 0,
            s6: 0,
            s7: 0,
            s8: 0,
            s9: 0,
            s10: 0,
            s11: 0,
        }
    }
    pub fn write_zero(&mut self) {
        self.ra = 0;
        self.sp = 0;
        self.s0 = 0;
        self.s1 = 0;
        self.s2 = 0;
        self.s3 = 0;
        self.s4 = 0;
        self.s5 = 0;
        self.s6 = 0;
        self.s7 = 0;
        self.s8 = 0;
        self.s9 = 0;
        self.s10 = 0;
        self.s11 = 0;
    }
}

impl Default for Procs {
    fn default() -> Self {
        Self::new()
    }
}

impl Procs {
    pub fn new() -> Self {
        let mut i = 0;
        Self {
            pool: core::iter::repeat_with(|| {
                let p = Arc::new(Proc::new(i));
                i += 1;
                p
            })
            .take(NPROC)
            .collect::<Vec<_>>()
            .try_into()
            .unwrap(),
            parents: Mutex::new(
                core::iter::repeat_with(|| None)
                    .take(NPROC)
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap(),
                "parents",
            ),
        }
    }

    // Allocate STACK_PAGE_NUM pages for each process's kernel stack.
    // map it high in memory, followed by an invalid guard page.
    #[allow(static_mut_refs)]
    pub unsafe fn mapstacks(&self) {
        use crate::vm::Stack;
        for (p, _) in self.pool.iter().enumerate() {
            let pa = Stack::try_new_zeroed().unwrap() as usize;
            let va = kstack(p);
            KVM.get_mut()
                .unwrap()
                .map(va, pa.into(), PGSIZE * STACK_PAGE_NUM, PTE_R | PTE_W);
        }
    }

    // Look in the process table for an UNUSED proc. If found,
    // initialize state required to run in the kernel, and return
    // reference to the proc with "proc" lock held. If there are
    // no free procs, or a memory allocation fails, return None.
    fn alloc(&self) -> Result<(&Arc<Proc>, MutexGuard<'_, ProcInner>)> {
        for p in self.pool.iter() {
            let mut lock = p.inner.lock();
            match lock.state {
                ProcState::UNUSED => {
                    lock.pid = PId::alloc();
                    lock.state = ProcState::USED;

                    let data = p.data_mut();
                    // Allocate a trapframe page.
                    if let Ok(tf) = Box::<Trapframe>::try_new_zeroed() {
                        data.trapframe.replace(unsafe { tf.assume_init() });
                    } else {
                        p.free(lock);
                        return Err(OutOfMemory);
                    }

                    // An empty user page table.
                    match p.uvmcreate() {
                        Ok(uvm) => {
                            data.uvm.replace(uvm);
                        }
                        Err(err) => {
                            p.free(lock);
                            return Err(err);
                        }
                    }

                    // Set up new context to start executing at forkret,
                    // which returns to user space.
                    data.context.write_zero();
                    data.context.ra = fork_ret as usize;
                    data.context.sp = data.kstack.into_usize() + PGSIZE * STACK_PAGE_NUM;
                    return Ok((p, lock));
                }
                _ => continue,
            }
        }
        Err(WouldBlock)
    }
}

// initialize the proc table at boottime.
pub fn init() {
    for (i, proc) in PROCS.pool.iter().enumerate() {
        proc.data_mut().kstack = kstack(i);
    }
}

impl Proc {
    pub fn new(idx: usize) -> Self {
        Self {
            idx,
            inner: Mutex::new(ProcInner::new(), "proc"),
            data: UnsafeCell::new(ProcData::new()),
        }
    }
    pub fn pid(&self) -> usize {
        self.inner.lock().pid.0
    }

    pub fn data(&self) -> &'static ProcData {
        unsafe { &*(self.data.get()) }
    }

    pub fn data_mut(&self) -> &'static mut ProcData {
        unsafe { &mut *(self.data.get()) }
    }

    fn free(&self, mut guard: MutexGuard<'_, ProcInner>) {
        let data = self.data_mut();
        data.trapframe.take();
        if let Some(uvm) = data.uvm.take() {
            uvm.proc_uvmfree(data.sz);
        }
        data.sz = 0;
        guard.pid = PId(0);
        data.name.clear();
        guard.chan = 0;
        guard.killed = false;
        guard.xstate = 0;
        guard.state = ProcState::UNUSED;
    }

    // Create a user page table with no user memory
    // but with trampoline and trapframe pages.
    pub fn uvmcreate(&self) -> Result<Uvm> {
        // An empty user page table.
        let mut uvm = Uvm::create()?;

        // map the trampoline code (for system call return)
        // at the highest user virtual address.
        // only the supervisor uses it, on the way
        // to/from user space, so not PTE_U
        if let Err(err) = uvm.mappages(
            UVAddr::from(TRAMPOLINE),
            PAddr::from(trampoline as usize),
            PGSIZE,
            PTE_R | PTE_X,
        ) {
            uvm.free(0);
            return Err(err);
        }

        let data = self.data();
        // map the trapframe page just below the trampoline page, for
        // trampoline.rs
        if let Err(err) = uvm.mappages(
            UVAddr::from(TRAPFRAME),
            PAddr::from(data.trapframe.as_deref().unwrap() as *const _ as usize),
            PGSIZE,
            PTE_R | PTE_W,
        ) {
            uvm.unmap(UVAddr::from(TRAMPOLINE), 1, false);
            uvm.free(0);
            return Err(err);
        }

        Ok(uvm)
    }
}

pub fn either_copyout<T: ?Sized + AsBytes>(dst: VirtAddr, src: &T) -> Result<()> {
    match dst {
        VirtAddr::User(addr) => {
            let p = Cpus::myproc().unwrap();
            let uvm = p.data_mut().uvm.as_mut().unwrap();
            uvm.copyout(addr.into(), src)
        }
        VirtAddr::Kernel(addr) | VirtAddr::Physical(addr) => {
            let src = src.as_bytes();
            let len = src.len();
            assert!(PGSIZE > len, "either_copyout: len must be less than PGSIZE");
            let dst = unsafe { core::slice::from_raw_parts_mut(addr as *mut u8, len) };
            dst.copy_from_slice(src);
            Ok(())
        }
    }
}

pub fn either_copyin<T: ?Sized + AsBytes>(dst: &mut T, src: VirtAddr) -> Result<()> {
    match src {
        VirtAddr::User(addr) => {
            let p = Cpus::myproc().unwrap();
            let uvm = p.data_mut().uvm.as_mut().unwrap();
            uvm.copyin(dst, addr.into())
        }
        VirtAddr::Kernel(addr) | VirtAddr::Physical(addr) => {
            let dst = dst.as_bytes_mut();
            let len = dst.len();
            let src = unsafe { core::slice::from_raw_parts(addr as *const u8, len) };
            dst.copy_from_slice(src);
            Ok(())
        }
    }
}

// Set up first user process.
pub fn user_init(initcode: &'static [u8]) {
    let (p, ref mut guard) = PROCS.alloc().unwrap();
    INITPROC.set(p.clone()).unwrap();

    let data = p.data_mut();
    let uvm = data.uvm.as_mut().unwrap();

    let elf;
    unsafe {
        let (head, body, _) = initcode[0..size_of::<ElfHdr>()].align_to::<ElfHdr>();
        assert!(head.is_empty(), "elf_img is not aligned");
        elf = body.get(0).unwrap();
    }
    if elf.e_ident[elf::EI_MAG0] != elf::ELFMAG0
        || elf.e_ident[elf::EI_MAG1] != elf::ELFMAG1
        || elf.e_ident[elf::EI_MAG2] != elf::ELFMAG2
        || elf.e_ident[elf::EI_MAG3] != elf::ELFMAG3
    {
        panic!("initcode is not an elf img");
    }
    // Load program into user memory.
    let mut phdr: ProgHdr;
    let mut off = elf.e_phoff;
    let mut sz = 0;
    for _ in 0..elf.e_phnum {
        unsafe {
            let (head, body, _) = initcode[off..(off + size_of::<ProgHdr>())].align_to::<ProgHdr>();
            assert!(head.is_empty(), "elf prong header is not aligned");
            phdr = *body.get(0).unwrap();
        }
        if phdr.p_type != elf::PT_LOAD || phdr.p_fsize == 0 {
            continue;
        }
        if phdr.p_msize < phdr.p_fsize {
            panic!("p_msize >= p_fsize");
        }
        if phdr.p_vaddr + phdr.p_msize < phdr.p_msize {
            panic!("p_vaddr + p_msize < p_msize");
        }
        let va = UVAddr::from(phdr.p_vaddr);
        assert!(va.is_aligned(), "init program va's must be aligned");

        sz = uvm
            .alloc(sz, phdr.p_vaddr + phdr.p_msize, flags2perm(phdr.p_flags))
            .unwrap();

        uvm.copyout(va, &initcode[phdr.p_offset..(phdr.p_offset + phdr.p_fsize)])
            .unwrap();
        off += size_of::<ProgHdr>();
    }
    // Allocate two pages at the next page boundary.
    // Make the first inaccessible as a stack guard.
    // use the second as the user stack.
    sz = pgroundup(sz);
    sz = uvm.alloc(sz, sz + 2 * PGSIZE, pteflags::PTE_W).unwrap();
    uvm.clear(From::from(sz - 2 * PGSIZE));

    // prepare for the very first "return" from kernel to user.
    data.sz = sz;
    let tf = data.trapframe.as_mut().unwrap();
    tf.epc = elf.e_entry; // user program counter
    tf.sp = UVAddr::from(sz).into_usize(); // user stack pointer

    data.name.push_str("initcode");
    guard.state = ProcState::RUNNABLE;
}

impl ProcInner {
    pub const fn new() -> Self {
        Self {
            state: ProcState::UNUSED,
            chan: 0,
            killed: false,
            xstate: 0,
            pid: PId(0),
        }
    }
}

impl ProcData {
    pub fn new() -> Self {
        Self {
            kstack: KVAddr::from(0),
            sz: 0,
            uvm: None,
            trapframe: None,
            context: Context::new(),
            name: String::new(),
            ofile: array![None; NOFILE],
            cwd: Default::default(),
        }
    }
}

impl Default for ProcData {
    fn default() -> Self {
        Self::new()
    }
}

// A fork child's very first scheduling by shceduler()
// will swtch to fork_ret().
pub unsafe extern "C" fn fork_ret() -> ! {
    static mut FIRST: bool = true;

    // still holding "proc" lock from scheduler.
    // force_unlock() from my_proc() is needed because the stack is different
    Cpus::myproc().unwrap().inner.force_unlock();

    if FIRST {
        // File system initialization must be run in the context of a
        // regular process (e.g., because it calls sleep), and thus cannot
        // be run from main().
        FIRST = false;
        fs::init(ROOTDEV);
        // register initproc here, because namei must be called after fs initialization.
        INITPROC.get().unwrap().data_mut().cwd = Some(crate::fs::Path::new("/").namei().unwrap().1)
    }
    usertrap_ret()
}

// Print a process listing to console. For debugging.
// Runs when user types ^P on console.
// No lock to avoid wedging a stuck machine further.
pub fn dump() {
    println!("");
    for proc in PROCS.pool.iter() {
        let inner = unsafe { proc.inner.get_mut() };
        let data = unsafe { &(*proc.data.get()) };
        if inner.state != ProcState::UNUSED {
            println!(
                "pid: {:?} state: {:?} name: {:?}, chan: {}",
                inner.pid, inner.state, data.name, inner.chan
            );
        }
    }
}

// Per-CPU process scheduler.
// Each CPU calls scheduler() after setting itself up.
// Scheduler never returns. It loops, doing:
//  - choose a process to run.
//  - swtch to start running thet process.
//  - eventually that process transfers control
//    via swtch back to the scheduler.
pub fn scheduler() -> ! {
    let c = unsafe { CPUS.mycpu() };

    loop {
        // Avoid deadlock by ensuring thet devices can interrupt.
        intr_on();

        for p in PROCS.pool.iter() {
            let mut inner = p.inner.lock();
            if inner.state == ProcState::RUNNABLE {
                // Switch to chosen process. It is the process's job
                // to release its lock and then reacquire it
                // before jumping back to us.
                inner.state = ProcState::RUNNING;
                unsafe {
                    (*c).proc.replace(Arc::clone(p));
                    swtch(&mut (*c).context, &p.data().context);
                    // Process is done running for now.
                    // It should have changed its p->state before coming back.
                    (*c).proc.take();
                }
            }
        }
    }
}

// Switch to scheduler. Must hold only "proc" lock
// and have changed proc.state. Saves and restores
// intena because intena is a property of this
// kernel thread, not this CPU.
fn sched<'a>(guard: MutexGuard<'a, ProcInner>, ctx: &mut Context) -> MutexGuard<'a, ProcInner> {
    unsafe {
        let c = &mut *CPUS.mycpu();
        assert!(guard.holding(), "sched proc lock");
        assert!(
            c.noff == 1,
            "sched multiple locks {}, {:#?}, {:?}, {:?}, {:?}",
            c.noff,
            *PROCS,
            c.nest,
            guard,
            BCACHE
        );
        assert!(guard.state != ProcState::RUNNING, "shced running");
        assert!(!intr_get(), "sched interruptible");

        let intena = c.intena;
        // to scheduler
        swtch(ctx, &c.context);
        c.intena = intena;

        guard
    }
}

// Give up the CPU for one scheduling round.
pub fn yielding() {
    let p = Cpus::myproc().unwrap();
    let mut guard = p.inner.lock();
    guard.state = ProcState::RUNNABLE;
    sched(guard, &mut p.data_mut().context);
}

pub fn exit(status: i32) -> ! {
    let p = Cpus::myproc().unwrap();
    assert!(!Arc::ptr_eq(&p, INITPROC.get().unwrap()), "init exiting");

    // Close all open files
    let data = p.data_mut();
    for fd in data.ofile.iter_mut() {
        let _file = fd.take();
    }

    LOG.begin_op();
    {
        let _ip = data.cwd.take();
    }
    LOG.end_op();

    let mut proc_guard;
    {
        let mut parents = PROCS.parents.lock();
        // Pass p's abandoned children to init.
        for opp in parents.iter_mut().filter(|pp| pp.is_some()) {
            match opp {
                Some(ref pp) if Arc::ptr_eq(pp, &p) => {
                    let initproc = INITPROC.get().unwrap();
                    opp.replace(Arc::clone(initproc));
                    self::wakeup(Arc::as_ptr(initproc) as usize);
                }
                _ => (),
            }
        }
        // Parent might be sleeping in wait().
        self::wakeup(Arc::as_ptr(parents[p.idx].as_ref().unwrap()) as usize);
        proc_guard = p.inner.lock();
        proc_guard.xstate = status;
        proc_guard.state = ProcState::ZOMBIE;
    }

    // jump into scheduler, never to return.
    sched(proc_guard, &mut data.context);

    panic!("zombie exit");
}

// Atomically release lock and sleep on chan.
// Reacquires lock when awakend.
pub fn sleep<T>(chan: usize, mutex_guard: MutexGuard<'_, T>) -> MutexGuard<'_, T> {
    // Must acquire "proc" lock in order to
    // change proc.state and then call sched.
    // Once we hold "proc" lock, we can be
    // guaranteed that we won't miss any wakeup
    // (wakeup() locks "proc" lock),
    // so it's okay to release lock of mutex_guard.
    let mutex;
    {
        let p = Cpus::myproc().unwrap();
        let mut proc_lock = p.inner.lock();
        mutex = Mutex::unlock(mutex_guard);

        proc_lock.chan = chan;
        proc_lock.state = ProcState::SLEEPING;

        // to scheduler
        proc_lock = sched(proc_lock, &mut p.data_mut().context);

        // tidy up
        proc_lock.chan = 0;
    }
    // Reacquires original lock.
    mutex.lock()
}

// Wake up all processes sleeping on chan.
// Must be called without any "proc" lock.
pub fn wakeup(chan: usize) {
    for p in PROCS.pool.iter() {
        match Cpus::myproc() {
            Some(ref cp) if Arc::ptr_eq(p, cp) => (),
            _ => {
                let mut guard = p.inner.lock();
                if guard.state == ProcState::SLEEPING && guard.chan == chan {
                    guard.state = ProcState::RUNNABLE;
                }
            }
        }
    }
}

// Create a new process, copying the parent.
// Sets up child kernel stack to return as if from fork() system call.
pub fn fork() -> Result<usize> {
    let p = Cpus::myproc().unwrap();
    let p_data = p.data_mut();
    let (c, c_guard) = PROCS.alloc()?;
    let c_data = c.data_mut();

    // Copy user memory from parent to child.
    let p_uvm = p_data.uvm.as_mut().unwrap();
    let c_uvm = c_data.uvm.as_mut().unwrap();
    if let Err(err) = p_uvm.copy(c_uvm, p_data.sz) {
        c.free(c_guard);
        return Err(err);
    }
    c_data.sz = p_data.sz;

    // copy saved user registers
    let p_tf = p_data.trapframe.as_ref().unwrap();
    let c_tf = c_data.trapframe.as_mut().unwrap();
    c_tf.clone_from(p_tf);

    // Cause fork to return 0 in the child.
    c_tf.a0 = 0;

    // increment reference counts on open file descriptors.
    c_data.ofile.clone_from_slice(&p_data.ofile);
    c_data.cwd = p_data.cwd.clone();

    c_data.name.push_str(&p_data.name);

    let pid = c_guard.pid;

    let c_inner = Mutex::unlock(c_guard);
    {
        let mut parents = PROCS.parents.lock();
        parents[c.idx] = Some(Arc::clone(&p));
    }
    c_inner.lock().state = ProcState::RUNNABLE;

    Ok(pid.0)
}

// Kill the process with the given pid.
// The victim won't exit until it tries to return
// to user space (see usertrap in trap.rs)
pub fn kill(pid: usize) -> Result<()> {
    for p in PROCS.pool.iter() {
        let mut guard = p.inner.lock();
        if guard.pid.0 == pid {
            guard.killed = true;
            if guard.state == ProcState::SLEEPING {
                // Wake process from sleep().
                guard.state = ProcState::RUNNABLE;
            }
            return Ok(());
        }
    }
    Err(NoSuchProcess)
}

// Wait for a child process to exit and return its pid.
// Return Err, if this process has no children.
pub fn wait(addr: UVAddr) -> Result<usize> {
    let pid;
    let mut havekids;
    let p = Cpus::myproc().unwrap();

    let mut parents = PROCS.parents.lock();

    loop {
        // Scan through table looking for exited children.
        havekids = false;
        for c in PROCS.pool.iter() {
            match parents[c.idx] {
                Some(ref pp) if Arc::ptr_eq(pp, &p) => {
                    // macke sure the child isn't still in exit() or swtch().
                    let c_guard = c.inner.lock();
                    havekids = true;
                    if c_guard.state == ProcState::ZOMBIE {
                        // Found one.
                        pid = c_guard.pid.0;
                        p.data_mut()
                            .uvm
                            .as_mut()
                            .unwrap()
                            .copyout(addr, &c_guard.xstate)?;
                        c.free(c_guard);
                        parents[c.idx].take();
                        return Ok(pid);
                    }
                }
                _ => continue,
            }
        }
        // No point waiting if we don't have any children.
        if !havekids || p.inner.lock().killed {
            break Err(NoChildProcesses);
        }

        // wait for a child to exit
        parents = sleep(Arc::as_ptr(&p) as usize, parents);
    }
}

pub fn grow(n: isize) -> Result<()> {
    use core::cmp::Ordering;
    let p = Cpus::myproc().unwrap();
    let data = p.data_mut();
    let mut sz = data.sz;
    let uvm = data.uvm.as_mut().unwrap();

    match n.cmp(&0) {
        Ordering::Greater => sz = uvm.alloc(sz, sz + n as usize, PTE_W)?,
        Ordering::Less => sz = uvm.dealloc(sz, (sz as isize + n) as usize),
        _ => (),
    }
    data.sz = sz;
    Ok(())
}

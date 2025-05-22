use crate::{
    elf::{self, ElfHdr, ProgHdr},
    error::{Error::*, Result},
    fs::{IData, Path},
    log::LOG,
    memlayout::STACK_PAGE_NUM,
    param::MAXARG,
    proc::Cpus,
    riscv::{pgroundup, pteflags, PGSIZE},
    sleeplock::SleepLockGuard,
    vm::{Addr, UVAddr, Uvm, VirtAddr},
};
use alloc::string::{String, ToString};
use core::mem::size_of;

pub const fn flags2perm(flags: u32) -> usize {
    let mut perm = 0;
    if flags & 0x1 != 0 {
        perm = pteflags::PTE_X;
    }
    if flags & 0x2 != 0 {
        perm |= pteflags::PTE_W;
    }
    perm
}

// Load a program segment into pagetable at virtual address va.
// va must be page-aligned
// and the pages from va to va+sz must already be mapped.
// Returns Ok(()) on success, Err(_) on failure.
impl Uvm {
    pub fn loadseg(
        &mut self,
        va: UVAddr,
        ip_guard: &mut SleepLockGuard<IData>,
        offset: usize,
        sz: usize,
    ) -> Result<()> {
        if !va.is_aligned() {
            panic!("loadseg(): va must be aligned.");
        }

        let mut i: usize = 0;

        while i < sz {
            let pa = self.walkaddr(va + i)?;
            let n = if sz - i < PGSIZE { sz - i } else { PGSIZE };
            ip_guard.read(From::from(pa), (offset + i) as u32, n)?;
            i += PGSIZE;
        }
        Ok(())
    }
}

#[allow(clippy::redundant_closure_call)]
#[no_mangle]
pub fn exec(
    path: &Path,
    argv: [Option<String>; MAXARG],
    envp: [Option<String>; MAXARG],
) -> Result<usize> {
    let p = Cpus::myproc().unwrap();

    let mut uvm: Option<Uvm> = None;
    let mut ustack = [0usize; MAXARG * 2]; // &str = [usize, usize]
    let mut elf: ElfHdr = Default::default();
    let mut res;
    let mut sz = 0;

    {
        LOG.begin_op();
        let mut load = || -> Result<usize> {
            let (_, ip) = path.namei()?;
            let mut ip_guard = ip.lock();

            // Load & Check ELF header
            ip_guard.read(
                VirtAddr::Kernel(&mut elf as *mut _ as usize),
                0,
                size_of::<ElfHdr>(),
            )?;
            if elf.e_ident[elf::EI_MAG0] != elf::ELFMAG0
                || elf.e_ident[elf::EI_MAG1] != elf::ELFMAG1
                || elf.e_ident[elf::EI_MAG2] != elf::ELFMAG2
                || elf.e_ident[elf::EI_MAG3] != elf::ELFMAG3
            {
                return Err(ExecFileFormatError);
            }

            uvm = Some(p.uvmcreate()?);

            //  Load program into memory.
            let mut phdr: ProgHdr = Default::default();
            let mut off = elf.e_phoff;
            for _ in 0..elf.e_phnum {
                ip_guard.read(
                    VirtAddr::Kernel(&mut phdr as *mut _ as usize),
                    off as u32,
                    size_of::<ProgHdr>(),
                )?;
                if phdr.p_type != elf::PT_LOAD {
                    continue;
                }
                if phdr.p_msize < phdr.p_fsize {
                    return Err(ExecFileFormatError);
                }
                if phdr.p_vaddr + phdr.p_msize < phdr.p_msize {
                    return Err(ExecFileFormatError);
                }
                if phdr.p_vaddr % PGSIZE != 0 {
                    return Err(ExecFileFormatError);
                }
                sz = uvm.as_mut().unwrap().alloc(
                    sz,
                    phdr.p_vaddr + phdr.p_msize,
                    flags2perm(phdr.p_flags),
                )?;
                uvm.as_mut().unwrap().loadseg(
                    From::from(phdr.p_vaddr),
                    &mut ip_guard,
                    phdr.p_offset,
                    phdr.p_fsize,
                )?;
                off += size_of::<ProgHdr>();
            }
            Ok(0)
        };
        res = load();
        LOG.end_op();
    }

    let exec = || -> Result<usize> {
        res?;
        let p = Cpus::myproc().unwrap();
        let proc_data = p.data_mut();

        let tf = proc_data.trapframe.as_mut().unwrap();

        let oldsz = proc_data.sz;

        // Allocate some pages at the next page boundary.
        // Make the first inaccessible as a stack guard.
        // Use the next STACK_PAGE_NUM pages as the user stack.
        let pgnum = 1 + STACK_PAGE_NUM;
        sz = pgroundup(sz);
        sz = uvm
            .as_mut()
            .unwrap()
            .alloc(sz, sz + pgnum * PGSIZE, pteflags::PTE_W)?;
        uvm.as_mut().unwrap().clear(From::from(sz - pgnum * PGSIZE));
        let mut sp: UVAddr = UVAddr::from(sz);
        let stackbase: UVAddr = sp - PGSIZE * STACK_PAGE_NUM;

        // Push argument strings, prepare rest of stack in ustack.
        let mut argc = 0;
        for arg in argv.into_iter().take_while(|e| e.is_some()).flatten() {
            sp -= arg.len();
            sp -= sp.into_usize() % 16; // riscv sp must be 16-byte aligned
            if sp < stackbase {
                return Err(NoBufferSpace);
            }
            // copyout str to sp
            uvm.as_mut().unwrap().copyout(sp, arg.as_str())?;
            // now sp = *const str
            // make &str from sp  and len, and store it in ustack[].
            *ustack.get_mut(argc * 2).ok_or(ArgumentListTooLong)? = sp.into_usize();
            *ustack.get_mut(argc * 2 + 1).ok_or(ArgumentListTooLong)? = arg.len();
            argc += 1;
        }
        let mut envc = 0;
        for env in envp.into_iter() {
            match env {
                Some(env_str) => {
                    sp -= env_str.len();
                    sp -= sp.into_usize() % 16; // riscv sp must be 16-byte aligned
                    if sp < stackbase {
                        return Err(NoBufferSpace);
                    }
                    // copyout str to sp
                    uvm.as_mut().unwrap().copyout(sp, env_str.as_str())?;
                    // now sp = *const str
                    // make &str from sp and len, and store it in ustack[].
                    *ustack
                        .get_mut((argc + envc) * 2)
                        .ok_or(ArgumentListTooLong)? = sp.into_usize();
                    *ustack
                        .get_mut((argc + envc) * 2 + 1)
                        .ok_or(ArgumentListTooLong)? = env_str.len();
                    envc += 1;
                }
                None => {}
            }
        }
        // now &ustack = &[Option<&str>]

        // Push [&str] to stack.
        sp -= MAXARG * 2 * size_of::<usize>();
        sp -= sp.into_usize() % 16;
        if sp < stackbase {
            return Err(NoBufferSpace);
        }
        uvm.as_mut().unwrap().copyout(sp, &ustack)?;
        // now sp = *const [Option<&str>]

        // make &[Option<&str>] from sp(=*const [Option<&str>]) and argc(= slice len) at stack
        let slice: [usize; 2] = [sp.into_usize(), MAXARG];
        sp -= size_of::<[usize; 2]>();
        sp -= sp.into_usize() % 16;
        if sp < stackbase {
            return Err(NoBufferSpace);
        }
        uvm.as_mut().unwrap().copyout(sp, &slice)?;
        // now sp = *const &[Option<&str>]

        // arguments to user main(argc: i32, args: usize) generated by rustc
        // argc is returned via the system call return value, which goes in a0.
        // argc does not need to be i32 at all, so here we return usize.
        // Note that argc is treated as i32 in the main generated by rustc.
        //
        // The second argument is treated as *const *const u8 in rustc,
        // but it is still a pointer which size is usize, so here we set
        // *const &[&str] to the second argument. In rust_main, It should be
        // able to be treated as an Option<&[&str]> by NullPo Optimization in
        // main(.., args).
        tf.a1 = if argc > 0 { sp.into_usize() } else { 0 };

        // Save program name for debugging.
        if let Some(name) = path.file_name() {
            proc_data.name = name.to_string();
        }

        // Commit to the user image.
        let olduvm = proc_data.uvm.replace(uvm.take().unwrap());
        proc_data.sz = sz;
        tf.epc = elf.e_entry; // initial program counter = main
        tf.sp = sp.into_usize(); // initial stack pointer
        olduvm.unwrap().proc_uvmfree(oldsz);

        Ok(argc) // this ends up in a0, the first argument to main(argc, args: &[&str])
    };
    res = exec();

    match res {
        Err(_) => {
            if let Some(uvm) = uvm {
                uvm.proc_uvmfree(sz)
            }
        }
        _ => {
            // close on exec
            for file in p.data_mut().ofile.iter_mut() {
                match file {
                    Some(f) if f.is_cloexec() => {
                        file.take();
                    }
                    _ => continue,
                }
            }
        }
    }

    res
}

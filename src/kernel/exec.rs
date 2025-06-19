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
    wasm,
    wasm::runtime,
};
use alloc::{string::String, string::ToString, vec::Vec};
use core::mem::size_of;

// WebAssembly binary format magic number
const WASM_MAGIC: [u8; 4] = [0x00, 0x61, 0x73, 0x6D]; // "\0asm"

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
    let mut res;
    let mut sz = 0;
    let mut magic = [0u8; 4];  // Move magic to outer scope
    let mut entry_point = 0;   // Add entry_point to store the result

    {
        LOG.begin_op();
        let (_, ip) = path.namei()?;
        let mut ip_guard = ip.lock();

        // Read magic number to determine file type
        ip_guard.read(
            VirtAddr::Kernel(magic.as_mut_ptr() as usize),
            0,
            4,
        )?;

        // Check file type and load accordingly
        if magic == WASM_MAGIC {
            // println!("Loading WebAssembly module...");
            // WebAssembly binary
            let file_size = ip_guard.size() as usize;
            // println!("File size: {}", file_size);
            let mut wasm_bytes = Vec::with_capacity(file_size);
            unsafe {
                wasm_bytes.set_len(file_size);
            }
            ip_guard.read(
                VirtAddr::Kernel(wasm_bytes.as_mut_ptr() as usize),
                0,
                file_size,
            )?;

            // Execute the WebAssembly module using the unified interface
            // debug option
            let config = runtime::RuntimeConfig { debug: false, ..runtime::RuntimeConfig::default() };
            match wasm::execute_auto(&wasm_bytes, Some(config)) {
                Ok(result) => {
                    // For WASM execution, we don't need to set up user memory
                    // since the execution happens in kernel space
                    // Just return success with a dummy entry point
                    entry_point = 0x1000; // Dummy entry point for WASM
                    res = Ok(entry_point);
                },
                Err(e) => {
                    // println!("WebAssembly execution failed: {:?}", e);
                    // Use InvalidArgument for WASM execution errors since the file format
                    // was correctly identified but execution failed
                    return Err(Uncategorized);
                }
            }
        } else if magic[0] == elf::ELFMAG0
            && magic[1] == elf::ELFMAG1
            && magic[2] == elf::ELFMAG2
            && magic[3] == elf::ELFMAG3
        {
            // ELF binary
            let mut elf: ElfHdr = Default::default();
            ip_guard.read(
                VirtAddr::Kernel(&mut elf as *mut _ as usize),
                0,
                size_of::<ElfHdr>(),
            )?;

            uvm = Some(p.uvmcreate()?);

            // Load program into memory
            let mut phdr: ProgHdr = Default::default();
            let mut off = elf.e_phoff;
            for _ in 0..elf.e_phnum {
                ip_guard.read(
                    VirtAddr::Kernel(&mut phdr as *mut _ as usize),
                    off as u32,
                    size_of::<ProgHdr>(),
                )?;
                if phdr.p_type != elf::PT_LOAD || phdr.p_fsize == 0 {
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
            entry_point = elf.e_entry;  // Store the entry point
            res = Ok(elf.e_entry);
        } else {
            // Unknown file format
            res = Err(ExecFileFormatError);
        }
        LOG.end_op();
    }

    let exec = || -> Result<usize> {
        res?;
        let p = Cpus::myproc().unwrap();
        let proc_data = p.data_mut();
        let tf = proc_data.trapframe.as_mut().unwrap();
        let oldsz = proc_data.sz;

        // Check if this is a WASM execution (entry_point == 0x1000 indicates WASM)
        let is_wasm = entry_point == 0x1000;

        if is_wasm {
            // For WASM execution, we don't need user memory setup
            // since execution happens in kernel space
            // println!("WASM execution completed, setting up process...");
            
            // Save program name
            if let Some(name) = path.file_name() {
                proc_data.name = name.to_string();
            }
            
            // For WASM execution, we should exit the process after successful execution
            // since there's no user space code to run
            // println!("WASM execution successful, exiting process");
            
            // Exit the process with success status (0)
            crate::proc::exit(0);
            
            // This line should never be reached
            unreachable!();
        } else {
            // ELF execution - normal user memory setup
            // Set entry point based on file type
            tf.epc = entry_point;

            // Allocate stack pages
            let pgnum = 1 + STACK_PAGE_NUM;
            sz = pgroundup(sz);
            sz = uvm
                .as_mut()
                .unwrap()
                .alloc(sz, sz + pgnum * PGSIZE, pteflags::PTE_W)?;
            uvm.as_mut().unwrap().clear(From::from(sz - pgnum * PGSIZE));
            let mut sp: UVAddr = UVAddr::from(sz);
            let stackbase: UVAddr = sp - PGSIZE * STACK_PAGE_NUM;

            // Push arguments to stack (similar to exec)
            let mut argc = 0;
            for arg in argv.into_iter().take_while(|e| e.is_some()).flatten() {
                sp -= arg.len();
                sp -= sp.into_usize() % 16;
                if sp < stackbase {
                    return Err(NoBufferSpace);
                }
                uvm.as_mut().unwrap().copyout(sp, arg.as_str())?;
                *ustack.get_mut(argc * 2).ok_or(ArgumentListTooLong)? = sp.into_usize();
                *ustack.get_mut(argc * 2 + 1).ok_or(ArgumentListTooLong)? = arg.len();
                argc += 1;
            }

            // Push environment variables
            let mut envc = 0;
            for env in envp.into_iter() {
                if let Some(env_str) = env {
                    sp -= env_str.len();
                    sp -= sp.into_usize() % 16;
                    if sp < stackbase {
                        return Err(NoBufferSpace);
                    }
                    uvm.as_mut().unwrap().copyout(sp, env_str.as_str())?;
                    *ustack
                        .get_mut((argc + envc) * 2)
                        .ok_or(ArgumentListTooLong)? = sp.into_usize();
                    *ustack
                        .get_mut((argc + envc) * 2 + 1)
                        .ok_or(ArgumentListTooLong)? = env_str.len();
                    envc += 1;
                }
            }

            // Push argument array
            sp -= MAXARG * 2 * size_of::<usize>();
            sp -= sp.into_usize() % 16;
            if sp < stackbase {
                return Err(NoBufferSpace);
            }
            uvm.as_mut().unwrap().copyout(sp, &ustack)?;

            // Push argument array pointer and length
            let slice: [usize; 2] = [sp.into_usize(), MAXARG];
            sp -= size_of::<[usize; 2]>();
            sp -= sp.into_usize() % 16;
            if sp < stackbase {
                return Err(NoBufferSpace);
            }
            uvm.as_mut().unwrap().copyout(sp, &slice)?;

            // Set up trap frame
            tf.a1 = if argc > 0 { sp.into_usize() } else { 0 };

            // Save program name
            if let Some(name) = path.file_name() {
                proc_data.name = name.to_string();
            }

            // Commit to user image
            let olduvm = proc_data.uvm.replace(uvm.take().unwrap());
            proc_data.sz = sz;

            tf.sp = sp.into_usize();
            olduvm.unwrap().proc_uvmfree(oldsz);

            Ok(argc)
        }
    };

    res = exec();

    match res {
        Err(_) => {
            if let Some(uvm) = uvm {
                uvm.proc_uvmfree(sz)
            }
            // For WASM execution, uvm might be None, which is fine
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
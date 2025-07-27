#[cfg(all(target_os = "none", feature = "kernel"))]
use crate::error::Error::*;
use crate::{error::Result, syscall};
#[cfg(all(target_os = "none", feature = "kernel"))]
use crate::{
    array,
    defs::AsBytes,
    exec::exec,
    fcntl::{FcntlCmd, OMode},
    file::{FTABLE, FType, File},
    fs::{self, Path},
    log::LOG,
    param::{MAXARG, MAXPATH},
    pipe::Pipe,
    proc::*,
    riscv::PGSIZE,
    stat::{FileType, Stat},
    trap::TICKS,
    vm::{Addr, UVAddr},
};
#[cfg(all(target_os = "none", feature = "kernel"))]
use alloc::string::{String, ToString};
use core::mem::variant_count;
#[cfg(all(target_os = "none", feature = "kernel"))]
use core::mem::{size_of, size_of_val};
#[cfg(all(target_os = "none", feature = "kernel"))]
use core::{concat, str};

// Import the derive macro from the derive crate
use derive::SysCalls as SysCallsDerive;

pub struct PId(pub usize);
pub struct Fd(pub usize);

impl From<usize> for Fd {
    fn from(value: usize) -> Self {
        Fd(value)
    }
}

impl From<usize> for PId {
    fn from(value: usize) -> Self {
        PId(value)
    }
}

#[derive(Copy, Clone, Debug, SysCallsDerive)]
#[repr(usize)]
pub enum SysCalls {
    #[syscall(params(), ret(!))]
    Invalid = 0,
    #[syscall(params(), ret(Result<usize>))]
    Fork = 1,
    #[syscall(params(xstatus: i32), ret(Result<()>))]
    Exit = 2,
    #[syscall(params(xstatus: &mut i32), ret(Result<usize>))]
    Wait = 3,
    #[syscall(params(p: &mut [usize]), ret(Result<()>))]
    Pipe = 4,
    #[syscall(params(fd: Fd, buf: &mut [u8]), ret(Result<usize>))]
    Read = 5,
    #[syscall(params(pid: PId), ret(Result<()>))]
    Kill = 6,
    #[syscall(params(filename: &str, argv: &[&str], envp: Option<&[Option<&str>]>), ret(Result<usize>))]
    Exec = 7,
    #[syscall(params(fd: Fd, st: &mut Stat), ret(Result<()>))]
    Fstat = 8,
    #[syscall(params(dirname: &str), ret(Result<()>))]
    Chdir = 9,
    #[syscall(params(fd: Fd), ret(Result<usize>))]
    Dup = 10,
    #[syscall(params(), ret(Result<usize>))]
    Getpid = 11,
    #[syscall(params(n: isize), ret(Result<usize>))]
    Sbrk = 12,
    #[syscall(params(n: usize), ret(Result<()>))]
    Sleep = 13,
    #[syscall(params(), ret(Result<usize>))]
    Uptime = 14,
    #[syscall(params(filename: &str, flags: usize), ret(Result<usize>))]
    Open = 15,
    #[syscall(params(fd: Fd, buf: &[u8]), ret(Result<usize>))]
    Write = 16,
    #[syscall(params(file: &str, major: u16, minor: u16), ret(Result<()>))]
    Mknod = 17,
    #[syscall(params(file: &str), ret(Result<()>))]
    Unlink = 18,
    #[syscall(params(file1: &str, file2: &str), ret(Result<()>))]
    Link = 19,
    #[syscall(params(dir: &str), ret(Result<()>))]
    Mkdir = 20,
    #[syscall(params(fd: Fd), ret(Result<()>))]
    Close = 21,
    #[syscall(params(src: Fd, dst: Fd), ret(Result<usize>))]
    Dup2 = 22,
    #[syscall(params(fd: Fd, cmd: FcntlCmd), ret(Result<usize>))]
    Fcntl = 23,
}

// The derive macro will generate the necessary implementation code
// including dispatch tables and wrapper functions

#[cfg(all(target_os = "none", feature = "kernel"))]
fn fdalloc(file: File) -> Result<usize> {
    for (fd, f) in Cpus::myproc()
        .unwrap()
        .data_mut()
        .ofile
        .iter_mut()
        .enumerate()
    {
        if f.is_none() {
            f.replace(file);
            return Ok(fd);
        }
    }
    Err(FileDescriptorTooLarge)
}

// Process related system calls
impl SysCalls {
    pub fn exit() -> ! {
        #[cfg(not(all(target_os = "none", feature = "kernel")))]
        unimplemented!();
        #[cfg(all(target_os = "none", feature = "kernel"))]
        {
            exit(argraw(0) as i32)
            // not reached
        }
    }
    pub fn getpid() -> Result<usize> {
        #[cfg(not(all(target_os = "none", feature = "kernel")))]
        return Ok(0);
        #[cfg(all(target_os = "none", feature = "kernel"))]
        {
            Ok(Cpus::myproc().unwrap().pid())
        }
    }
    pub fn fork() -> Result<usize> {
        #[cfg(not(all(target_os = "none", feature = "kernel")))]
        return Ok(0);
        #[cfg(all(target_os = "none", feature = "kernel"))]
        {
            fork()
        }
    }
    pub fn wait() -> Result<usize> {
        #[cfg(not(all(target_os = "none", feature = "kernel")))]
        return Ok(0);
        #[cfg(all(target_os = "none", feature = "kernel"))]
        {
            let addr: UVAddr = argraw(0).into();
            wait(addr)
        }
    }
    pub fn sbrk() -> Result<usize> {
        #[cfg(not(all(target_os = "none", feature = "kernel")))]
        return Ok(0);
        #[cfg(all(target_os = "none", feature = "kernel"))]
        {
            let p = Cpus::myproc().unwrap();
            let n = argraw(0) as isize;
            let addr = p.data().sz;
            grow(n).and(Ok(addr))
        }
    }
    pub fn sleep() -> Result<()> {
        #[cfg(not(all(target_os = "none", feature = "kernel")))]
        return Ok(());
        #[cfg(all(target_os = "none", feature = "kernel"))]
        {
            let p = Cpus::myproc().unwrap();
            let n = argraw(0);
            let mut ticks = TICKS.lock();
            let ticks0 = *ticks;
            while *ticks - ticks0 < n {
                if p.inner.lock().killed {
                    return Err(Interrupted);
                }
                ticks = sleep(&(*ticks) as *const _ as usize, ticks);
            }
            Ok(())
        }
    }
    pub fn kill() -> Result<()> {
        #[cfg(not(all(target_os = "none", feature = "kernel")))]
        return Ok(());
        #[cfg(all(target_os = "none", feature = "kernel"))]
        {
            let pid = argraw(0);

            if pid == 0 {
                Err(PermissionDenied)
            } else {
                kill(pid)
            }
        }
    }
    pub fn uptime() -> Result<usize> {
        #[cfg(not(all(target_os = "none", feature = "kernel")))]
        return Ok(0);
        #[cfg(all(target_os = "none", feature = "kernel"))]
        {
            Ok(*TICKS.lock())
        }
    }
}

// System Calls related to File operations
impl SysCalls {
    pub fn dup() -> Result<usize> {
        #[cfg(not(all(target_os = "none", feature = "kernel")))]
        return Ok(0);
        #[cfg(all(target_os = "none", feature = "kernel"))]
        {
            let mut _fd = 0;
            let (f, _) = File::from_arg(0, &mut _fd)?;
            fdalloc(f.clone())
        }
    }
    pub fn dup2() -> Result<usize> {
        #[cfg(not(all(target_os = "none", feature = "kernel")))]
        return Ok(0);
        #[cfg(all(target_os = "none", feature = "kernel"))]
        {
            // src , dst
            let p = Cpus::myproc().unwrap().data_mut();
            let src_fd = argraw(0);
            let dst_fd = argraw(1);
            if src_fd != dst_fd {
                let mut src = p.ofile.get_mut(src_fd).unwrap().take().unwrap();
                src.clear_cloexec();
                p.ofile
                    .get_mut(dst_fd)
                    .ok_or(FileDescriptorTooLarge)?
                    .replace(src);
            }
            Ok(dst_fd)
        }
    }
    pub fn read() -> Result<usize> {
        #[cfg(not(all(target_os = "none", feature = "kernel")))]
        return Ok(0);
        #[cfg(all(target_os = "none", feature = "kernel"))]
        {
            let mut _fd = 0;
            let mut sbinfo: SBInfo = Default::default();

            let (f, _) = File::from_arg(0, &mut _fd)?;
            let sbinfo = SBInfo::from_arg(1, &mut sbinfo)?;

            f.read(sbinfo.ptr.into(), sbinfo.len)
        }
    }
    pub fn write() -> Result<usize> {
        #[cfg(not(all(target_os = "none", feature = "kernel")))]
        return Ok(0);
        #[cfg(all(target_os = "none", feature = "kernel"))]
        {
            let mut _fd = 0;
            let mut sbinfo: SBInfo = Default::default();

            let (f, _) = File::from_arg(0, &mut _fd)?;
            let sbinfo = SBInfo::from_arg(1, &mut sbinfo)?;

            f.write(sbinfo.ptr.into(), sbinfo.len)
        }
    }
    pub fn close() -> Result<()> {
        #[cfg(not(all(target_os = "none", feature = "kernel")))]
        return Ok(());
        #[cfg(all(target_os = "none", feature = "kernel"))]
        {
            let mut fd = 0;
            File::from_arg(0, &mut fd)?;
            let _f = Cpus::myproc().unwrap().data_mut().ofile[fd].take().unwrap();
            drop(_f);
            Ok(())
        }
    }
    pub fn fstat() -> Result<()> {
        #[cfg(not(all(target_os = "none", feature = "kernel")))]
        return Ok(());
        #[cfg(all(target_os = "none", feature = "kernel"))]
        {
            let mut fd = 0;
            let st: UVAddr = argraw(1).into();
            let (f, _) = File::from_arg(0, &mut fd)?;

            f.stat(From::from(st))
        }
    }
    pub fn link() -> Result<()> {
        #[cfg(not(all(target_os = "none", feature = "kernel")))]
        return Ok(());
        #[cfg(all(target_os = "none", feature = "kernel"))]
        {
            let mut old = [0; MAXPATH];
            let mut new = [0; MAXPATH];
            let old_path = Path::from_arg(0, &mut old)?;
            let new_path = Path::from_arg(1, &mut new)?;

            let res;
            {
                LOG.begin_op();
                res = fs::link(old_path, new_path);
                LOG.end_op();
            }
            res
        }
    }
    pub fn unlink() -> Result<()> {
        #[cfg(not(all(target_os = "none", feature = "kernel")))]
        return Ok(());
        #[cfg(all(target_os = "none", feature = "kernel"))]
        {
            let mut path = [0; MAXPATH];
            let path = Path::from_arg(0, &mut path)?;

            let res;
            {
                LOG.begin_op();
                res = fs::unlink(path);
                LOG.end_op();
            }
            res
        }
    }
    pub fn open() -> Result<usize> {
        #[cfg(not(all(target_os = "none", feature = "kernel")))]
        return Ok(0);
        #[cfg(all(target_os = "none", feature = "kernel"))]
        {
            let mut path = [0u8; MAXPATH];
            let omode = argraw(1);
            let path = Path::from_arg(0, &mut path)?;

            let fd;
            {
                LOG.begin_op();
                fd = FTABLE
                    .alloc(OMode::from_usize(omode), FType::Node(path))
                    .and_then(fdalloc);
                LOG.end_op();
            }
            fd
        }
    }
    pub fn mkdir() -> Result<()> {
        #[cfg(not(all(target_os = "none", feature = "kernel")))]
        return Ok(());
        #[cfg(all(target_os = "none", feature = "kernel"))]
        {
            let mut path = [0u8; MAXPATH];
            let path = Path::from_arg(0, &mut path)?;

            let res;
            {
                LOG.begin_op();
                res = fs::create(path, FileType::Dir, 0, 0).and(Ok(()));
                LOG.end_op();
            }
            res
        }
    }
    pub fn mknod() -> Result<()> {
        #[cfg(not(all(target_os = "none", feature = "kernel")))]
        return Ok(());
        #[cfg(all(target_os = "none", feature = "kernel"))]
        {
            let mut path = [0u8; MAXPATH];
            let path = Path::from_arg(0, &mut path)?;
            let major = argraw(1) as u16;
            let minor = argraw(2) as u16;

            let res;
            {
                LOG.begin_op();
                res = fs::create(path, FileType::Device, major, minor).and(Ok(()));
                LOG.end_op();
            }
            res
        }
    }
    #[allow(clippy::redundant_closure_call)]
    pub fn chdir() -> Result<()> {
        #[cfg(not(all(target_os = "none", feature = "kernel")))]
        return Ok(());
        #[cfg(all(target_os = "none", feature = "kernel"))]
        {
            let mut path = [0u8; MAXPATH];
            let data = Cpus::myproc().unwrap().data_mut();
            let path = Path::from_arg(0, &mut path)?;

            let res;
            {
                LOG.begin_op();
                let mut chidr = || -> Result<()> {
                    let (_, ip) = path.namei()?;
                    {
                        let ip_guard = ip.lock();
                        if ip_guard.itype() != FileType::Dir {
                            return Err(NotADirectory);
                        }
                    }
                    data.cwd.replace(ip);
                    Ok(())
                };
                res = chidr();
                LOG.end_op();
            }
            res
        }
    }
    pub fn exec() -> Result<usize> {
        #[cfg(not(all(target_os = "none", feature = "kernel")))]
        return Ok(0);
        #[cfg(all(target_os = "none", feature = "kernel"))]
        {
            let mut path = [0u8; MAXPATH];
            let mut uargv: [SBInfo; MAXARG] = Default::default();
            let mut uenvp: [SBInfo; MAXARG] = Default::default();
            let path = Path::from_arg(0, &mut path)?;
            let argv = Argv::from_arg(1, &mut uargv)?;
            let envp = Envp::from_arg(2, &mut uenvp)?;
            exec(path, argv.0, envp.0)
        }
    }
    pub fn pipe() -> Result<()> {
        #[cfg(not(all(target_os = "none", feature = "kernel")))]
        return Ok(());
        #[cfg(all(target_os = "none", feature = "kernel"))]
        {
            let slice_addr: UVAddr = argraw(0).into();
            let mut ptr: UVAddr = UVAddr::from(0);
            let mut len: usize = 0;
            fetch_addr(slice_addr, &mut ptr)?;
            fetch_addr(slice_addr + core::mem::size_of::<usize>(), &mut len)?;

            if len > 3 {
                return Err(InvalidArgument);
            }

            let (rf, wf) = Pipe::alloc()?;
            let fd0 = fdalloc(rf)?;
            let fd1 = match fdalloc(wf) {
                Ok(fd) => fd,
                Err(err) => {
                    Cpus::myproc().unwrap().data_mut().ofile[fd0].take();
                    return Err(err);
                }
            };

            if either_copyout(ptr.into(), &fd0).is_err()
                || either_copyout((ptr + size_of::<usize>()).into(), &fd1).is_err()
            {
                let p_data = Cpus::myproc().unwrap().data_mut();
                p_data.ofile[fd0].take();
                p_data.ofile[fd1].take();
                return Err(BadVirtAddr);
            }
            Ok(())
        }
    }
    pub fn fcntl() -> Result<usize> {
        #[cfg(not(all(target_os = "none", feature = "kernel")))]
        return Ok(0);
        #[cfg(all(target_os = "none", feature = "kernel"))]
        {
            let mut _fd = 0;

            let (f, _) = File::from_arg(0, &mut _fd)?;
            let cmd = FcntlCmd::from_usize(argraw(1));

            f.do_fcntl(cmd)
        }
    }
}

// The remaining functionality will be automatically generated by the derive macro

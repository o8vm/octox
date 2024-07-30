#[cfg(all(target_os = "none", feature = "kernel"))]
use crate::error::Error::*;
use crate::error::Result;
#[cfg(all(target_os = "none", feature = "kernel"))]
use crate::{
    array,
    defs::AsBytes,
    exec::exec,
    fcntl::{FcntlCmd, OMode},
    file::{FType, File, FTABLE},
    fs::{self, Path},
    log::LOG,
    param::{MAXARG, MAXPATH},
    pipe::Pipe,
    proc::*,
    riscv::PGSIZE,
    stat::FileType,
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

#[derive(Copy, Clone, Debug)]
#[repr(usize)]
pub enum SysCalls {
    Fork = 1,
    Exit = 2,
    Wait = 3,
    Pipe = 4,
    Read = 5,
    Kill = 6,
    Exec = 7,
    Fstat = 8,
    Chdir = 9,
    Dup = 10,
    Getpid = 11,
    Sbrk = 12,
    Sleep = 13,
    Uptime = 14,
    Open = 15,
    Write = 16,
    Mknod = 17,
    Unlink = 18,
    Link = 19,
    Mkdir = 20,
    Close = 21,
    Dup2 = 22,
    Fcntl = 23,
    Invalid = 0,
}

#[derive(Debug, Clone, Copy)]
pub enum Fn {
    U(fn() -> Result<()>),    // return unit type
    I(fn() -> Result<usize>), // return integer
    N(fn() -> !),             // return never
}
impl Fn {
    pub fn call(self) -> isize {
        match self {
            Fn::U(uni) => uni()
                .and(Ok(0))
                .or_else(|err| Ok::<isize, ()>(err as isize))
                .unwrap(),
            Fn::I(int) => int()
                .map(|i| i as isize)
                .or_else(|err| Ok::<isize, ()>(err as isize))
                .unwrap(),
            Fn::N(nev) => nev(),
        }
    }
}
impl SysCalls {
    pub const TABLE: [(Fn, &'static str); variant_count::<Self>()] = [
        (Fn::N(Self::invalid), ""),
        (Fn::I(Self::fork), "()"), // Create a process, return child's PID.
        (Fn::N(Self::exit), "(xstatus: i32)"), // Terminate the current process; status reported to wait(). No Return.
        (Fn::I(Self::wait), "(xstatus: &mut i32)"), // Wait for a child to exit; exit status in &status; retunrs child PID.
        (Fn::U(Self::pipe), "(p: &mut [usize])"), // Create a pipe, put read/write file descpritors in p[0] and p[1].
        (Fn::I(Self::read), "(fd: usize, buf: &mut [u8])"), // Read n bytes into buf; returns number read; or 0 if end of file
        (Fn::U(Self::kill), "(pid: usize)"), // Terminate process PID. Returns Ok(()) or Err(())
        (
            Fn::I(Self::exec),
            "(filename: &str, argv: &[&str], envp: Option<&[Option<&str>]>)",
        ), // Load a file and execute it with arguments; only returns if error.
        (Fn::U(Self::fstat), "(fd: usize, st: &mut Stat)"), // Place info about an open file into st.
        (Fn::U(Self::chdir), "(dirname: &str)"),            // Change the current directory.
        (Fn::I(Self::dup), "(fd: usize)"), // Return a new file descpritor referring to the same file as fd.
        (Fn::I(Self::getpid), "()"),       // Return the current process's PID.
        (Fn::I(Self::sbrk), "(n: usize)"), // Grow process's memory by n bytes. Returns start fo new memory.
        (Fn::U(Self::sleep), "(n: usize)"), // Pause for n clock ticks.
        (Fn::I(Self::uptime), "()"),       // Return how many clock ticks since start.
        (Fn::I(Self::open), "(filename: &str, flags: usize)"), // Open a file; flags indicate read/write; returns an fd.
        (Fn::I(Self::write), "(fd: usize, b: &[u8])"), // Write n bytes from buf to file descpritor fd; returns n.
        (Fn::U(Self::mknod), "(file: &str, mj: usize, mi: usize)"), // Create a device file
        (Fn::U(Self::unlink), "(file: &str)"),         // Remove a file
        (Fn::U(Self::link), "(file1: &str, file2: &str)"), // Create another name (file2) for the file file1.
        (Fn::U(Self::mkdir), "(dir: &str)"),               // Create a new directory.
        (Fn::U(Self::close), "(fd: usize)"),               // Release open file fd.
        (Fn::I(Self::dup2), "(src: usize, dst: usize)"),   //
        (Fn::I(Self::fcntl), "(fd: usize, cmd: FcntlCmd)"), //
    ];
    pub fn invalid() -> ! {
        unimplemented!()
    }
}

#[cfg(all(target_os = "none", feature = "kernel"))]
pub fn syscall() {
    let p = Cpus::myproc().unwrap();
    let pdata = p.data_mut();
    let tf = pdata.trapframe.as_mut().unwrap();
    let syscall_id = SysCalls::from_usize(tf.a7);
    tf.a0 = match syscall_id {
        SysCalls::Invalid => {
            println!("{} {}: unknown sys call {}", p.pid(), pdata.name, tf.a7);
            -1_isize as usize
        }
        _ => SysCalls::TABLE[syscall_id as usize].0.call() as usize,
    }
}

#[cfg(all(target_os = "none", feature = "kernel"))]
enum Slice {
    Ref(UVAddr),
    Buf(SBInfo),
}

#[cfg(all(target_os = "none", feature = "kernel"))]
#[derive(Debug, Default, Clone, Copy)]
#[repr(C)]
struct SBInfo {
    ptr: UVAddr,
    len: usize,
}

#[cfg(all(target_os = "none", feature = "kernel"))]
unsafe impl AsBytes for SBInfo {}

#[cfg(all(target_os = "none", feature = "kernel"))]
fn fetch_addr<T: AsBytes>(addr: UVAddr, buf: &mut T) -> Result<()> {
    let p_data = Cpus::myproc().unwrap().data();
    if addr.into_usize() >= p_data.sz || addr.into_usize() + size_of_val(buf) > p_data.sz {
        return Err(BadVirtAddr);
    }
    either_copyin(buf, addr.into())
}

#[cfg(all(target_os = "none", feature = "kernel"))]
fn fetch_slice<T: AsBytes>(slice_info: Slice, buf: &mut [T]) -> Result<Option<usize>> {
    let mut sbinfo: SBInfo = Default::default();
    match slice_info {
        Slice::Ref(addr) => {
            fetch_addr(addr, &mut sbinfo)?;
        }
        Slice::Buf(info) => {
            sbinfo = info;
        }
    }
    if *sbinfo.ptr.get() == 0 {
        // Option<&[&T]> = None
        // sbinfo.len = 0;
        return Ok(None);
    }
    if sbinfo.len > buf.len() {
        return Err(NoBufferSpace);
    } else {
        either_copyin(&mut buf[..sbinfo.len], sbinfo.ptr.into())?;
    }
    Ok(Some(sbinfo.len))
}

#[cfg(all(target_os = "none", feature = "kernel"))]
fn argraw(n: usize) -> usize {
    let tf = Cpus::myproc().unwrap().data().trapframe.as_ref().unwrap();
    match n {
        0 => tf.a0,
        1 => tf.a1,
        2 => tf.a2,
        3 => tf.a3,
        4 => tf.a4,
        5 => tf.a5,
        _ => panic!("arg"),
    }
}

#[cfg(all(target_os = "none", feature = "kernel"))]
trait Arg {
    type Out<'a>;
    type In<'a>: AsBytes;
    fn from_arg<'a>(n: usize, input: &'a mut Self::In<'a>) -> Result<Self::Out<'a>>;
}

#[cfg(all(target_os = "none", feature = "kernel"))]
impl Arg for SBInfo {
    type In<'a> = SBInfo;
    type Out<'a> = &'a SBInfo;
    fn from_arg<'a>(n: usize, input: &'a mut Self::In<'a>) -> Result<Self::Out<'a>> {
        let addr: UVAddr = argraw(n).into();
        fetch_addr(addr, input)?;
        Ok(&*input)
    }
}

#[cfg(all(target_os = "none", feature = "kernel"))]
impl Arg for Path {
    type In<'a> = [u8; MAXPATH];
    type Out<'a> = &'a Self;
    fn from_arg<'a>(n: usize, input: &'a mut Self::In<'a>) -> Result<Self::Out<'a>> {
        let addr: UVAddr = argraw(n).into();
        let len = fetch_slice(Slice::Ref(addr), input)?.ok_or(InvalidArgument)?;
        Ok(Self::new(
            str::from_utf8_mut(&mut input[..len])
                .or(Err(Utf8Error))?
                .trim_end_matches(char::from(0)),
        ))
    }
}

#[cfg(all(target_os = "none", feature = "kernel"))]
impl Arg for File {
    type In<'a> = usize;
    type Out<'a> = (&'a mut File, usize);
    fn from_arg<'a>(n: usize, input: &'a mut Self::In<'a>) -> Result<Self::Out<'a>> {
        let p_data = Cpus::myproc().unwrap().data_mut();

        *input = argraw(n);
        match p_data.ofile.get_mut(*input).ok_or(FileDescriptorTooLarge)? {
            Some(f) => Ok((f, *input)),
            None => Err(BadFileDescriptor),
        }
    }
}

#[cfg(all(target_os = "none", feature = "kernel"))]
#[derive(Debug)]
struct Argv([Option<String>; MAXARG]);

#[cfg(all(target_os = "none", feature = "kernel"))]
impl Arg for Argv {
    type In<'a> = [SBInfo; MAXARG];
    type Out<'a> = Self;
    fn from_arg<'a>(n: usize, input: &'a mut Self::In<'a>) -> Result<Self::Out<'a>> {
        let mut argv = Argv(array![None; MAXARG]);
        let mut buf = [0u8; PGSIZE];
        let addr = UVAddr::from(argraw(n));

        let n = fetch_slice(Slice::Ref(addr), input)?.ok_or(InvalidArgument)?;
        for (i, &argument) in input.iter().take(n).enumerate() {
            if let Some(len) = fetch_slice(Slice::Buf(argument), &mut buf).unwrap() {
                let arg_str = str::from_utf8_mut(&mut buf[..len])
                    .or(Err(Utf8Error))
                    .unwrap();
                argv.0[i].replace(arg_str.to_string());
            }
        }
        Ok(argv)
    }
}

#[cfg(all(target_os = "none", feature = "kernel"))]
#[derive(Debug)]
struct Envp([Option<String>; MAXARG]);

#[cfg(all(target_os = "none", feature = "kernel"))]
impl Arg for Envp {
    type In<'a> = [SBInfo; MAXARG];
    type Out<'a> = Self;
    fn from_arg<'a>(n: usize, input: &'a mut Self::In<'a>) -> Result<Self::Out<'a>> {
        let mut envp = Envp(array![None; MAXARG]);
        let mut buf = [0u8; PGSIZE];
        let addr = UVAddr::from(argraw(n));

        let Some(n) = fetch_slice(Slice::Ref(addr), input)? else { return Ok(envp) };
        for (i, &env) in input.iter().take(n).enumerate() {
            if let Some(len) = fetch_slice(Slice::Buf(env), &mut buf).unwrap() {
                let env_str = str::from_utf8_mut(&mut buf[..len])
                    .or(Err(Utf8Error))
                    .unwrap();
                envp.0[i].replace(env_str.to_string());
            }
        }
        Ok(envp)
    }
}

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

impl SysCalls {
    pub fn from_usize(n: usize) -> Self {
        match n {
            1 => Self::Fork,
            2 => Self::Exit,
            3 => Self::Wait,
            4 => Self::Pipe,
            5 => Self::Read,
            6 => Self::Kill,
            7 => Self::Exec,
            8 => Self::Fstat,
            9 => Self::Chdir,
            10 => Self::Dup,
            11 => Self::Getpid,
            12 => Self::Sbrk,
            13 => Self::Sleep,
            14 => Self::Uptime,
            15 => Self::Open,
            16 => Self::Write,
            17 => Self::Mknod,
            18 => Self::Unlink,
            19 => Self::Link,
            20 => Self::Mkdir,
            21 => Self::Close,
            22 => Self::Dup2,
            23 => Self::Fcntl,
            _ => Self::Invalid,
        }
    }
}

// Generate system call interface for userland
#[cfg(not(target_os = "none"))]
impl SysCalls {
    pub fn into_enum_iter() -> std::vec::IntoIter<SysCalls> {
        (0..core::mem::variant_count::<SysCalls>())
            .map(SysCalls::from_usize)
            .collect::<Vec<SysCalls>>()
            .into_iter()
    }
    pub fn signature(self) -> String {
        let syscall = Self::TABLE[self as usize];
        format!(
            "fn {}{} -> {}",
            self.fn_name(),
            syscall.1,
            self.return_type()
        )
    }
    pub fn return_type(&self) -> &'static str {
        match Self::TABLE[*self as usize].0 {
            Fn::I(_) => "Result<usize>",
            Fn::U(_) => "Result<()>",
            Fn::N(_) => "!",
        }
    }
    pub fn fn_name(&self) -> String {
        format!("{:?}", self).to_lowercase()
    }
    pub fn args(&self) -> Vec<(&'static str, &'static str)> {
        Self::TABLE[*self as usize]
            .1
            .strip_suffix(')')
            .unwrap()
            .strip_prefix('(')
            .unwrap()
            .split(',')
            .filter_map(|s| s.trim().split_once(": "))
            .collect::<Vec<(&str, &str)>>()
    }

    pub fn gen_usys(self) -> String {
        let mut i = 0;
        let indent = 4;
        let part1 = format!(
            r#"
pub {} {{
    let _ret: isize;
    unsafe {{
        asm!(
            "ecall",{}"#,
            self.signature(),
            "\n",
        );
        let mut part2 = self
            .args()
            .iter()
            .map(|s| match s {
                (_, s1) if s1.contains("&str") | s1.contains("&[") | s1.contains("&mut [") => {
                    let ret = format!(
                        "{:indent$}in(\"a{}\") &{} as *const _ as usize,\n",
                        "",
                        i,
                        s.0,
                        indent = indent * 3
                    );
                    i += 1;
                    ret
                }
                (_, s1) if !s1.contains(']') && s1.contains("&mut ") => {
                    let ret = format!(
                        "{:indent$}in(\"a{}\") {} as *mut _ as usize,\n",
                        "",
                        i,
                        s.0,
                        indent = indent * 3
                    );
                    i += 1;
                    ret
                }
                (_, s1) if !s1.contains(']') && s1.contains('&') => {
                    let ret = format!(
                        "{:indent$}in(\"a{}\") {} as *const _ as usize,\n",
                        "",
                        i,
                        s.0,
                        indent = indent * 3
                    );
                    i += 1;
                    ret
                }
                (_, s1) if s1.contains("FcntlCmd") => {
                    let ret = format!(
                        "{:indent$}in(\"a{}\") {} as usize,\n",
                        "",
                        i,
                        s.0,
                        indent = indent * 3
                    );
                    i += 1;
                    ret
                }
                (_, _) => {
                    let ret = format!(
                        "{:indent$}in(\"a{}\") {},\n",
                        "",
                        i,
                        s.0,
                        indent = indent * 3
                    );
                    i += 1;
                    ret
                }
            })
            .collect::<Vec<String>>();
        let part3 = format!(
            r#"{:indent$}in("a7") {},
            lateout("a0") _ret,
        );
    }}
"#,
            "",
            self as usize,
            indent = indent * 3
        );
        let part4 = format!(
            "{:indent$}{}\n}}",
            "",
            match Self::TABLE[self as usize].0 {
                Fn::I(_) =>
                    "match _ret { 0.. => Ok(_ret as usize), _ => Err(Error::from_isize(_ret)) }",
                Fn::U(_) => "match _ret { 0 => Ok(()), _ => Err(Error::from_isize(_ret)) }",
                Fn::N(_) => "unreachable!()",
            },
            indent = indent
        );
        let mut gen: Vec<String> = Vec::new();
        gen.push(part1);
        gen.append(&mut part2);
        gen.push(part3);
        gen.push(part4);
        gen.iter().flat_map(|s| s.chars()).collect::<String>()
    }
}

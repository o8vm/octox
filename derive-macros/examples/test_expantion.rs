#![no_std]
#![no_main]
use derive_macros::Syscalls;

// AsBytes trait for kernel types
trait AsBytes {
    fn as_bytes(&self) -> &[u8];
    fn as_bytes_mut(&mut self) -> &mut [u8];
}

#[repr(transparent)]
struct Fd(usize);

#[repr(transparent)]
struct PId(usize);

#[derive(Default)]
#[repr(C)]
struct Stat {
    dev: u64,
    ino: u64,
    mode: u32,
    nlink: u32,
    uid: u32,
    gid: u32,
    rdev: u64,
    size: u64,
    blksize: u64,
    blocks: u64,
    atime: u64,
    mtime: u64,
    ctime: u64,
}

impl AsBytes for Stat {
    fn as_bytes(&self) -> &[u8] {
        unsafe {
            core::slice::from_raw_parts(
                self as *const _ as *const u8,
                core::mem::size_of::<Self>()
            )
        }
    }
    
    fn as_bytes_mut(&mut self) -> &mut [u8] {
        unsafe {
            core::slice::from_raw_parts_mut(
                self as *mut _ as *mut u8,
                core::mem::size_of::<Self>()
            )
        }
    }
}

#[derive(Debug)]
enum Error {
    EINVAL,
    ENOSYS,
}

type Result<T> = core::result::Result<T, Error>;

struct TrapFrame {
    syscall_num: usize,
    args: [usize; 6],
}

impl TrapFrame {
    fn arg(&self, n: usize) -> usize {
        self.args[n]
    }
    
    fn set_return(&mut self, val: usize) {
        self.args[0] = val;
    }
}

trait FromIsize {
    fn from_isize(val: isize) -> Self;
}

impl<T: FromIsize> FromIsize for Result<T> {
    fn from_isize(val: isize) -> Self {
        if val >= 0 {
            Ok(T::from_isize(val))
        } else {
            Err(match -val {
                22 => Error::EINVAL,
                38 => Error::ENOSYS,
                _ => Error::EINVAL,
            })
        }
    }
}

impl FromIsize for () {
    fn from_isize(_: isize) -> Self {
        ()
    }
}

impl FromIsize for usize {
    fn from_isize(val: isize) -> Self {
        val as usize
    }
}

impl FromIsize for Fd {
    fn from_isize(val: isize) -> Self {
        Fd(val as usize)
    }
}

impl FromIsize for PId {
    fn from_isize(val: isize) -> Self {
        PId(val as usize)
    }
}

trait IntoIsize {
    fn into_isize(self) -> isize;
}

impl<T: IntoIsize> IntoIsize for Result<T> {
    fn into_isize(self) -> isize {
        match self {
            Ok(v) => v.into_isize(),
            Err(Error::EINVAL) => -22,
            Err(Error::ENOSYS) => -38,
        }
    }
}

impl IntoIsize for usize {
    fn into_isize(self) -> isize {
        self as isize
    }
}

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

#[derive(Syscalls)]
enum SysCalls {
    #[syscall(id = 0, params(fd: Fd, buf: &mut [u8]), ret(Result<usize>))]
    Read,
    #[syscall(id = 1, params(fd: Fd, buf: &[u8]), ret(Result<usize>))]
    Write,
    #[syscall(id = 2, params(path: &str, flags: usize), ret(Result<Fd>))]
    Open,
    #[syscall(id = 3, params(filename: &str, argv: &[&str], envp: Option<&[Option<&str>]>), ret(Result<()>))]
    Exec,
    #[syscall(id = 4, params(), ret(Result<PId>))]
    Fork,
    #[syscall(id = 5, params(fd: Fd, st: &mut Stat), ret(Result<usize>))]
    Fstat,
    Invalid,
}
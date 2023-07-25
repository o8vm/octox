use alloc::string::String;
use alloc::vec::Vec;

use crate::fs::File;
use crate::io::{self, Read, Write};
use crate::mutex::Mutex;
use crate::sys::{self, sync::OnceLock, Error::AlreadyExists, Error::Utf8Error};
use core::fmt;

pub const STDIN_FILENO: usize = 0;
pub const STDOUT_FILENO: usize = 1;
pub const STDERR_FILENO: usize = 2;

static mut STDIN: OnceLock<Mutex<File>> = OnceLock::new();
static mut STDOUT: OnceLock<Mutex<File>> = OnceLock::new();
static mut STDERR: OnceLock<Mutex<File>> = OnceLock::new();

pub struct Stdin {
    inner: &'static mut OnceLock<Mutex<File>>,
}

pub fn stdin() -> Stdin {
    unsafe { Stdin { inner: &mut STDIN } }
}

impl Stdin {
    pub fn set(&self, file: File) -> sys::Result<()> {
        self.inner.set(Mutex::new(file)).or(Err(AlreadyExists))
    }
    pub fn replace(&mut self, src: &File) -> sys::Result<()> {
        File::dup2(src, &mut self.inner.get().unwrap().lock())
    }

    pub fn read_line(&mut self, buf: &mut String) -> sys::Result<usize> {
        let mut char: [u8; 1] = [0];
        let mut bytes: Vec<u8> = Vec::new();
        loop {
            let cc = self.read(&mut char)?;
            if cc < 1 {
                break;
            }
            bytes.extend_from_slice(&char);
            if char[0] == b'\n' || char[0] == b'\r' {
                break;
            }
        }
        buf.push_str(core::str::from_utf8(&bytes).or(Err(Utf8Error))?);
        Ok(buf.len())
    }
}

impl Read for Stdin {
    fn read(&mut self, buf: &mut [u8]) -> sys::Result<usize> {
        self.inner
            .get_or_init(|| Mutex::new(unsafe { File::from_raw_fd(STDIN_FILENO) }))
            .lock()
            .read(buf)
    }
}

pub struct Stdout {
    inner: &'static mut OnceLock<Mutex<File>>,
}

pub fn stdout() -> Stdout {
    unsafe { Stdout { inner: &mut STDOUT } }
}

impl Stdout {
    pub fn set(&self, file: File) -> sys::Result<()> {
        self.inner.set(Mutex::new(file)).or(Err(AlreadyExists))
    }
    pub fn replace(&mut self, src: &File) -> sys::Result<()> {
        File::dup2(src, &mut self.inner.get().unwrap().lock())
    }
}

impl Write for Stdout {
    fn write(&mut self, buf: &[u8]) -> sys::Result<usize> {
        self.inner
            .get_or_init(|| Mutex::new(unsafe { File::from_raw_fd(STDOUT_FILENO) }))
            .lock()
            .write(buf)
    }
}

pub struct Stderr {
    inner: &'static mut OnceLock<Mutex<File>>,
}

pub fn stderr() -> Stderr {
    unsafe { Stderr { inner: &mut STDERR } }
}

impl Stderr {
    pub fn set(&self, file: File) -> sys::Result<()> {
        self.inner.set(Mutex::new(file)).or(Err(AlreadyExists))
    }
    pub fn replace(&mut self, src: &File) -> sys::Result<()> {
        File::dup2(src, &mut self.inner.get().unwrap().lock())
    }
}

impl Write for Stderr {
    fn write(&mut self, buf: &[u8]) -> sys::Result<usize> {
        self.inner
            .get_or_init(|| Mutex::new(unsafe { File::from_raw_fd(STDERR_FILENO) }))
            .lock()
            .write(buf)
    }
}

fn print_to<T>(args: fmt::Arguments<'_>, global_s: fn() -> T)
where
    T: Write,
{
    if let Err(e) = global_s().write_fmt(args) {
        panic!("failed printing {e}");
    }
}

pub fn _print(args: fmt::Arguments<'_>) {
    print_to(args, stdout);
}

pub fn _eprint(args: fmt::Arguments<'_>) {
    print_to(args, stderr);
}

#[macro_export]
macro_rules! print {
    ($($arg:tt)*) => {
        $crate::stdio::_print(format_args!($($arg)*))
    };
}

#[macro_export]
macro_rules! println {
    ($fmt:expr) => {
        print!(concat!($fmt, "\n"))
    };
    ($fmt:expr, $($arg:tt)*) => {
        print!(concat!($fmt, "\n"), $($arg)*)
    };
}

#[macro_export]
macro_rules! eprint {
    ($($arg:tt)*) => {
        $crate::stdio::_eprint(format_args!($($arg)*))
    };
}

#[macro_export]
macro_rules! eprintln {
    ($fmt:expr) => {
        eprint!(concat!($fmt, "\n"))
    };
    ($fmt:expr, $($arg:tt)*) => {
        eprint!(concat!($fmt, "\n"), $($arg)*)
    };
}

pub fn panic_output() -> Option<&'static mut impl io::Write> {
    unsafe {
        Some(
            stderr()
                .inner
                .get_or_init(|| Mutex::new(File::from_raw_fd(STDERR_FILENO)))
                .get_mut(),
        )
    }
}

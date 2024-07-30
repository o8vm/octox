use crate::sys::{self, Error::*};
use core::fmt;

pub trait Write {
    fn write(&mut self, buf: &[u8]) -> sys::Result<usize>;
    fn write_all(&mut self, mut buf: &[u8]) -> sys::Result<()> {
        while !buf.is_empty() {
            match self.write(buf) {
                Ok(0) => return Err(WriteZero),
                Ok(n) => buf = &buf[n..],
                Err(Interrupted) => {}
                Err(e) => return Err(e),
            }
        }
        Ok(())
    }
    fn write_fmt(&mut self, fmt: fmt::Arguments<'_>) -> sys::Result<()> {
        struct Adapter<'a, T: ?Sized + 'a> {
            inner: &'a mut T,
            error: sys::Result<()>,
        }

        impl<T: Write + ?Sized> fmt::Write for Adapter<'_, T> {
            fn write_str(&mut self, s: &str) -> fmt::Result {
                match self.inner.write_all(s.as_bytes()) {
                    Ok(()) => Ok(()),
                    Err(e) => {
                        self.error = Err(e);
                        Err(fmt::Error)
                    }
                }
            }
        }

        let mut output = Adapter {
            inner: self,
            error: Ok(()),
        };
        match fmt::write(&mut output, fmt) {
            Ok(()) => Ok(()),
            Err(_) => {
                if output.error.is_err() {
                    output.error
                } else {
                    Err(Uncategorized)
                }
            }
        }
    }
}

use alloc::{string::String, vec::Vec};
pub trait Read {
    fn read(&mut self, buf: &mut [u8]) -> sys::Result<usize>;
    fn read_to_end(&mut self, buf: &mut Vec<u8>) -> sys::Result<usize> {
        let start_len = buf.len();
        loop {
            let mut space = [0u8; 32];
            match self.read(&mut space) {
                Ok(0) => return Ok(buf.len() - start_len),
                Ok(n) => {
                    buf.extend_from_slice(&space[..n]);
                    continue;
                }
                Err(e) if e == sys::Error::Interrupted => continue,
                Err(e) => return Err(e),
            }
        }
    }
    fn read_to_string(&mut self, buf: &mut String) -> sys::Result<usize> {
        let len = buf.len();
        let buf_as_vec = unsafe { buf.as_mut_vec() };
        let ret = self.read_to_end(buf_as_vec);
        if core::str::from_utf8(&buf_as_vec[len..]).is_err() {
            Err(Utf8Error)
        } else {
            ret
        }
    }
}

pub struct BufReader<R: ?Sized> {
    inner: R,
}

impl<R: Read> BufReader<R> {
    pub fn new(inner: R) -> BufReader<R> {
        Self { inner }
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

impl<R: ?Sized + Read> Read for BufReader<R> {
    fn read(&mut self, buf: &mut [u8]) -> sys::Result<usize> {
        self.inner.read(buf)
    }
}

pub struct Lines<B> {
    buf: B
}

impl<B: BufRead> Iterator for Lines<B> {
    type Item = sys::Result<String>;
    fn next(&mut self) -> Option<Self::Item> {
        let mut buf = String::new();
        match self.buf.read_line(&mut buf) {
            Ok(0) => None,
            Ok(_n) => {
                if buf.ends_with('\n') {
                    buf.pop();
                    if buf.ends_with('\r') {
                        buf.pop();
                    }
                }
                Some(Ok(buf))
            },
            Err(e) => Some(Err(e)),
        }
    }
}

pub trait BufRead: Read {
    fn lines(self) -> Lines<Self>
        where
        Self: Sized,
    {
        Lines { buf: self }
    }
    fn read_line(&mut self, buf: &mut String) -> sys::Result<usize> {
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

impl<R: ?Sized + Read> BufRead for BufReader<R> {}

# Design MEMO of this proc_macro
## Example of input

```rust
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
```

## Example of output

```rust
// for userspace
#[cfg(all(target_os = "none", feature = "user"))]
impl SysCalls {
    fn read(fd: Fd, buf: &mut [u8]) -> Result<usize, Error> {
        let _ret: isize;
        unsafe {
            core::arch::asm!(
                "svc #0",  // AArch64
                in("x8") 0u16,
                in("x0") fd as usize,
                in("x1") &buf as *mut _ as usize,
                lateout("x0") _ret,
            );
        }
        use crate::syscall_return::FromIsize;
        <Result<usize, Error>>::from_isize(_ret)
    }

    fn write(fd: Fd, buf: &[u8]) -> Result<usize, Error> {
        let _ret: isize;
        unsafe {
            core::arch::asm!(
                "svc #0",
                in("x8") 1u16,
                in("x0") fd as usize,
                in("x1") &buf as *const _ as usize,
                lateout("x0") _ret,
            );
        }
        use crate::syscall_return::FromIsize;
        <Result<usize, Error>>::from_isize(_ret)
    }

    fn open(path: &str, flags: usize) -> Result<Fd, Error> {
        let _ret: isize;
        unsafe {
            core::arch::asm!(
                "svc #0",
                in("x8") 2u16,
                in("x0") &path  as *const _ as usize,
                in("x1") flags as usize,
                lateout("x0") _ret,
            );
        }
        use crate::syscall_return::FromIsize;
        <Result<Fd, Error>>::from_isize(_ret)
    }

    fn exec(filename: &str, argv: &[&str], envp: Option<&[Option<&str>]>) -> Result<(), Error> {
        let _ret: isize;
        unsafe {
            core::arch::asm!(
                "svc #0",
                in("x8") 3u16,
                in("x0") &filename as *const _ as usize,
                in("x1") &argv as *const _ as usize,
                in("x2") &envp as *const _ as usize,
                lateout("x0") _ret,
            );
        }
        use crate::syscall_return::FromIsize;
        <Result<(), Error>>::from_isize(_ret)
    }

    fn fork() -> Result<PId, Error> {
        let _ret: isize;
        unsafe {
            core::arch::asm!(
                "svc #0",
                in("x8") 4u16,
                lateout("x0") _ret,
            );
        }
        use crate::syscall_return::FromIsize;
        <Result<PId, Error>>::from_isize(_ret)
    }

    fn fstat(fd: Fd, st: &mut Stat) -> Result<usize, Error> {
        let _ret: isize;
        unsafe {
            core::arch::asm!(
                "svc #0",
                in("x8") 5u16,
                in("x0") fd as usize,
                in("x1") st as *mut _ as usize,
                lateout("x0") _ret,
            );
        }
        use crate::syscall_return::FromIsize;
        <Result<usize, Error>>::from_isize(_ret)
    }
}

// for kernel land
#[cfg(all(target_os = "none", feature = "kernel"))]
trait SyscallDispatch {
// default implementation
    fn copyin<T: AsBytes>(dst: &mut T, src: usize) -> Result<(), Error> {
        unimplemented!("copyin must be implemented by kernel")
    }
    
    fn dispatch(tf: &mut TrapFrame) -> Result<(), Error> {
        let result = match tf.syscall_num as u16 {
            0 => {
                let arg0 = Fd(tf.arg(0));
                let arg1 = {
                    let mut fat: (*const u8, usize) = (core::ptr::null(), 0);
                    Self::copyin(&mut fat, tf.arg(1))?;
                    
                    let mut buf = vec![Default::default(); fat.1];
                    Self::copyin(&mut buf[..], fat.0 as usize)?;
                    
                    buf
                };
                let arg2 = tf.arg(2) as usize;
                Self::read(arg0, &mut arg1, arg2)
            }
            1 => {
                let arg0 = Fd(tf.arg(0));
                let arg1 = {
                    let mut fat: (*const u8, usize) = (core::ptr::null(), 0);
                    Self::copyin(&mut fat, tf.arg(1))?;
                    
                    let mut buf = vec![Default::default(); fat.1];
                    Self::copyin(&mut buf[..], fat.0 as usize)?;
                    
                    buf
                };
                let arg2 = tf.arg(2) as usize;
                Self::write(arg0, &arg1, arg2)
            }
            2 => {
                let arg0 = {
                    let mut fat: (*const u8, usize) = (core::ptr::null(), 0);
                    Self::copyin(&mut fat, tf.arg(0))?;
                    
                    let mut buf = vec![0u8; fat.1];
                    Self::copyin(&mut buf[..], fat.0 as usize)?;
                    
                    String::from_utf8(buf)
                        .map_err(|_| Error::EINVAL)?
                };
                let arg1 = tf.arg(1) as u32;
                Self::open(&arg0, arg1)
            }
            3 => {
                // exec(filename: &str, argv: &[&str], envp: Option<&[Option<&str>]>)
                let arg0 = {
                    // filename: &str
                    let mut fat: (*const u8, usize) = (core::ptr::null(), 0);
                    Self::copyin(&mut fat, tf.arg(0))?;
                    
                    let mut buf = vec![0u8; fat.1];
                    Self::copyin(&mut buf[..], fat.0 as usize)?;
                    
                    String::from_utf8(buf)
                        .map_err(|_| Error::EINVAL)?
                };
                let arg1 = {
                    // argv: &[&str]
                    let mut fat: (*const (*const u8, usize), usize) = (core::ptr::null(), 0);
                    Self::copyin(&mut fat, tf.arg(1))?;
                    
                    // get fat pointer per str
                    let mut str_fats = vec![(core::ptr::null(), 0usize); fat.1];
                    Self::copyin(&mut str_fats[..], fat.0 as usize)?;
                    
                    // get str
                    let mut argv_vec = Vec::with_capacity(fat.1);
                    for str_fat in str_fats {
                        let mut buf = vec![0u8; str_fat.1];
                        Self::copyin(&mut buf[..], str_fat.0 as usize)?;
                        
                        let s = String::from_utf8(buf)
                            .map_err(|_| Error::EINVAL)?;
                        argv_vec.push(s);
                    }
                    argv_vec
                };
                let arg2 = {
                    // envp: Option<&[Option<&str>]>
                    let opt_addr = tf.arg(2);
                    if opt_addr == 0 {
                        None
                    } else {
                        let mut fat: (*const usize, usize) = (core::ptr::null(), 0);
                        Self::copyin(&mut fat, opt_addr)?;
                        
                        // Read an array of Option<&str>
                        // Each element is either 0 (None) or the address of a fat pointer
                        let mut opt_ptrs = vec![0usize; fat.1];
                        Self::copyin(&mut opt_ptrs[..], fat.0 as usize)?;
                        
                        let mut envp_vec = Vec::with_capacity(fat.1);
                        for opt_ptr in opt_ptrs {
                            if opt_ptr == 0 {
                                envp_vec.push(None);
                            } else {
                                // fat pointer
                                let mut str_fat: (*const u8, usize) = (core::ptr::null(), 0);
                                Self::copyin(&mut str_fat, opt_ptr)?;
                                
                                // get str
                                let mut buf = vec![0u8; str_fat.1];
                                Self::copyin(&mut buf[..], str_fat.0 as usize)?;
                                
                                let s = String::from_utf8(buf)
                                    .map_err(|_| Error::EINVAL)?;
                                envp_vec.push(Some(s));
                            }
                        }
                        Some(envp_vec)
                    }
                };
                Self::exec(&arg0, &arg1, arg2.as_deref())
            }
            4 => {
                // fork() - no args
                Self::fork()
            }
            5 => {
                // fstat(fd: Fd, st: &mut Stat)
                let arg0 = Fd(tf.arg(0));
                let arg1_ptr = tf.arg(1);
                
                // prepare Stat buffer 
                let mut stat_buf = Stat::default();
                
                let result = Self::fstat(arg0, &mut stat_buf)?;
                
                // Write the result back to user space (copyout is required)
                Self::copyout(arg1_ptr, &stat_buf)?;
                
                Ok(result)
            }
            _ => Err(Error::ENOSYS),
        };
        
        tf.set_return(result.into_isize() as usize);
        Ok(())
    }
    
    // to write back results of &mut arguments
    fn copyout<T: AsBytes>(dst: usize, src: &T) -> Result<(), Error> {
        unimplemented!("copyout must be implemented by kernel")
    }
    
    // system call impl (kernelside impl)
    fn read(fd: Fd, buf: &mut [u8], n: usize) -> Result<usize, Error>;
    fn write(fd: Fd, buf: &[u8], n: usize) -> Result<usize, Error>;
    fn open(path: &str, flags: u32) -> Result<Fd, Error>;
    fn exec(filename: &str, argv: &[&str], envp: Option<&[Option<&str>]>) -> Result<(), Error>;
    fn fork() -> Result<PId, Error>;
    fn fstat(fd: Fd, st: &mut Stat) -> Result<usize, Error>;
}

#[cfg(all(target_os = "none", feature = "kernel"))]
impl SyscallDispatch for SysCalls {}

impl SysCalls {
    fn from_usize(n: usize) -> Self {
        match n as u16 {
            0 => SysCalls::Read,
            1 => SysCalls::Write,
            2 => SysCalls::Open,
            3 => SysCalls::Exec,
            4 => SysCalls::Fork,
            5 => SysCalls::Fstat,
            _ => SysCalls::Invalid,
        }
    }
}
```

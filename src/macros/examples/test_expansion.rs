//! Test file demonstrating syscall derive macro expansion.
//!
//! This file serves as a test case and example for the derive macros
//! provided by this crate. It shows how to use both the `Syscalls` and
//! `SyscallError` derive macros to generate syscall wrappers and error
//! handling code.
//!
//! # Usage
//!
//! This file can be used to test macro expansion during development
//! and serves as documentation for the expected macro usage patterns.

#![no_std]
#![no_main]
#![allow(dead_code)]

extern crate alloc;
use derive::{SysCalls, SysErrs};

use core::alloc::{GlobalAlloc, Layout};
// Import common types that might be used by generated code
#[allow(unused_imports)]
use alloc::{boxed::Box, collections::BTreeMap, string::String, vec, vec::Vec};

/// Dummy global allocator for no_std environment.
/// This is a minimal allocator that just panics on allocation attempts.
/// In a real implementation, you would use a proper allocator.
struct DummyAllocator;

unsafe impl GlobalAlloc for DummyAllocator {
    unsafe fn alloc(&self, _layout: Layout) -> *mut u8 {
        panic!("Allocation not supported in this test environment");
    }

    unsafe fn dealloc(&self, _ptr: *mut u8, _layout: Layout) {
        panic!("Deallocation not supported in this test environment");
    }
}

#[global_allocator]
static GLOBAL: DummyAllocator = DummyAllocator;

/// Test error enum demonstrating SyscallError derive macro usage.
///
/// This enum represents various error conditions that can be returned
/// by system calls. Each variant has an explicit negative discriminant
/// value that corresponds to standard Unix error codes.
#[derive(SysErrs, PartialEq, Debug)]
#[repr(isize)]
pub enum Error {
    /// Default/uncategorized error when no specific error code matches
    Uncategorized,
    /// Resource is currently busy or locked
    ResourceBusy = -2,
    /// Requested resource or file not found  
    NotFound = -3,
    /// System is out of memory
    OutOfMemory = -4,
    /// Invalid virtual address provided
    BadVirtAddr = -5,
    /// Invalid argument passed to syscall
    InvalidArgument = -23,
    /// Invalid argument passed to syscall
    EINVAL = -22,
    /// System call not implemented
    ENOSYS = -38,
}

/// File descriptor wrapper type for type safety.
///
/// Wraps a raw usize file descriptor value to provide type safety
/// and prevent accidental misuse of file descriptor values.
#[derive(Debug, Clone, Copy)]
pub struct Fd(pub usize);

/// Process ID wrapper type for type safety.
///
/// Wraps a raw usize process ID value to provide type safety
/// and prevent accidental confusion with other numeric types.
#[derive(Debug, Clone, Copy)]
pub struct PId(pub usize);

/// File statistics structure for file metadata.
///
/// Contains standard file metadata fields that can be populated
/// by file stat system calls.
#[derive(Debug, Default)]
pub struct Stat {
    /// Device ID containing the file
    pub dev: u64,
    /// Inode number of the file
    pub ino: u64,
    /// Number of hard links to the file
    pub nlink: u64,
    /// Size of the file in bytes
    pub size: u64,
}

/// Result type alias for syscall operations.
///
/// Provides a convenient Result type that uses our Error enum
/// for representing syscall failures.
pub type Result<T> = core::result::Result<T, Error>;

/// Test syscalls enum demonstrating Syscalls derive macro usage.
///
/// This enum defines a set of system calls with their IDs, parameters,
/// and return types. The derive macro will generate appropriate wrapper
/// functions for both userspace and kernel contexts.
#[derive(SysCalls)]
enum SysCalls {
    /// Read data from a file descriptor into a buffer.
    #[syscall(params(fd: Fd, buf: &mut [u8]), ret(Result<usize>))]
    Read = 0,
    /// Write data from a buffer to a file descriptor.
    #[syscall(params(fd: Fd, buf: &[u8]), ret(Result<usize>))]
    Write = 1,
    /// Open a file with specified flags and return a file descriptor.
    #[syscall(params(path: &str, flags: usize), ret(Result<Fd>))]
    Open = 2,
    /// Execute a program with given arguments and environment.
    #[syscall(params(filename: &str, argv: &[&str], envp: Option<&[Option<&str>]>), ret(Result<()>))]
    Exec = 3,
    /// Fork the current process and return the new process ID.
    #[syscall(params(), ret(Result<PId>))]
    Fork = 4,
    /// Get file statistics for a file descriptor.
    #[syscall(params(fd: Fd, st: &mut Stat), ret(Result<usize>))]
    Fstat = 5,
    /// Invalid syscall variant for testing purposes.
    Invalid,
}

/// Marker trait for types that can be safely converted to/from byte arrays.
///
/// This trait is used by the kernel dispatch logic to handle copying data
/// between userspace and kernel space. Types implementing this trait can
/// be safely reinterpreted as byte sequences.
pub trait AsBytes {}

/// AsBytes implementation for single bytes.
impl AsBytes for u8 {}

/// AsBytes implementation for byte slices.

/// AsBytes implementation for generic slices of AsBytes types.
impl<T> AsBytes for [T] where T: AsBytes {}

/// AsBytes implementation for file statistics structure.
impl AsBytes for Stat {}

/// AsBytes implementation for usize.
impl AsBytes for usize {}

/// AsBytes implementation for (*const u8, usize) tuples.
//impl AsBytes for (*const u8, usize) {}

impl<T> AsBytes for (*const T, usize) where T: AsBytes {}
/// AsBytes implementation for (*const (*const u8, usize), usize) tuples.
//impl AsBytes for (*const (*const u8, usize), usize) {}

/// AsBytes implementation for (*const usize, usize) tuples.
//:impl AsBytes for (*const usize, usize) {}

/// AsBytes implementation for vectors.
impl<T> AsBytes for Vec<T> where T: Copy {}

/// Kernel trap frame structure for syscall handling.
///
/// This structure represents the CPU state when a system call trap occurs.
/// It provides access to syscall numbers, arguments, and return value storage.
pub struct TrapFrame {
    /// Core trap frame functionality
    pub core: TrapFrameCore,
}

impl TrapFrame {
    /// Gets the syscall number from the trap frame.
    ///
    /// # Returns
    /// The syscall number that was invoked
    pub fn syscall_num(&self) -> usize {
        self.core.syscall_num()
    }

    /// Gets a syscall argument by index.
    ///
    /// # Arguments
    /// * `n` - The argument index (0-based)
    ///
    /// # Returns
    /// The value of the nth syscall argument
    pub fn arg(&self, n: usize) -> usize {
        self.core.arg(n)
    }

    /// Sets the syscall return value in the trap frame.
    ///
    /// # Arguments
    /// * `val` - The return value to store
    pub fn set_return(&mut self, val: usize) {
        self.core.set_return(val)
    }
}

/// Panic handler required for no_std environments.
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

/// Entry point for no_main environments.
#[unsafe(no_mangle)]
pub extern "C" fn _start() -> ! {
    loop {}
}

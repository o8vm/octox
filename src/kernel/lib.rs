#![cfg_attr(target_os = "none", no_std)]
#![cfg_attr(
    all(target_os = "none", feature = "kernel"),
    feature(alloc_error_handler)
)]
#![cfg_attr(all(target_os = "none", feature = "kernel"), feature(allocator_api))]
#![feature(negative_impls)]
#![feature(fn_align)]
#![feature(variant_count)]
#![allow(clippy::missing_safety_doc)]

#[cfg(all(target_os = "none", feature = "kernel"))]
extern crate alloc;

#[cfg(all(target_os = "none", feature = "kernel"))]
pub mod condvar;
#[cfg(all(target_os = "none", feature = "kernel"))]
pub mod console;
#[cfg(all(target_os = "none", feature = "kernel"))]
pub mod entry;
#[cfg(all(target_os = "none", feature = "kernel"))]
pub mod kernelvec;
#[cfg(all(target_os = "none", feature = "kernel"))]
pub mod memlayout;
#[cfg(all(target_os = "none", feature = "kernel"))]
pub mod mpmc;
#[cfg(all(target_os = "none", feature = "kernel"))]
pub mod null;
pub mod param;
#[cfg(all(target_os = "none", feature = "kernel"))]
pub mod proc;
#[cfg(all(target_os = "none", feature = "kernel"))]
pub mod semaphore;
#[cfg(all(target_os = "none", feature = "kernel"))]
pub mod sleeplock;
#[cfg(all(target_os = "none", feature = "kernel"))]
pub mod spinlock;
#[cfg(all(target_os = "none", feature = "kernel"))]
pub mod start;
#[cfg(all(target_os = "none", feature = "kernel"))]
pub mod uart;
#[cfg(all(target_os = "none", feature = "kernel"))]
#[macro_use]
pub mod printf;
#[cfg(all(target_os = "none", feature = "kernel"))]
pub mod bio;
#[cfg(all(target_os = "none", feature = "kernel"))]
pub mod buddy;
pub mod defs;
#[cfg(all(target_os = "none", feature = "kernel"))]
pub mod elf;
pub mod error;
#[cfg(all(target_os = "none", feature = "kernel"))]
pub mod exec;
#[cfg(target_os = "none")]
pub mod fcntl;
pub mod file;
pub mod fs;
#[cfg(all(target_os = "none", feature = "kernel"))]
pub mod kalloc;
#[cfg(all(target_os = "none", feature = "kernel"))]
pub mod list;
#[cfg(all(target_os = "none", feature = "kernel"))]
pub mod log;
#[cfg(all(target_os = "none", feature = "kernel"))]
pub mod pipe;
#[cfg(all(target_os = "none", feature = "kernel"))]
pub mod plic;
#[cfg(all(target_os = "none", feature = "kernel"))]
pub mod riscv;
pub mod stat;
#[cfg(all(target_os = "none", feature = "kernel"))]
pub mod swtch;
#[cfg(target_os = "none")]
pub mod sync;
pub mod syscall;
#[cfg(all(target_os = "none", feature = "kernel"))]
pub mod trampoline;
#[cfg(all(target_os = "none", feature = "kernel"))]
pub mod trap;
#[cfg(all(target_os = "none", feature = "kernel"))]
pub mod virtio_disk;
#[cfg(all(target_os = "none", feature = "kernel"))]
pub mod vm;

#[macro_export]
macro_rules! kmain {
    ($path:path) => {
        #[export_name = "main"]
        pub extern "C" fn __main() -> ! {
            // type check the given path
            let f: extern "C" fn() -> ! = $path;

            f()
        }
    };
}

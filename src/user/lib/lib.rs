#![no_std]
#![feature(lang_items, never_type, allocator_api, alloc_error_handler)]
#![allow(clippy::missing_safety_doc)]
#![allow(internal_features)]

pub mod sys {
    use core::arch::asm;
    use fcntl::FcntlCmd;
    pub use kernel::defs;
    pub use kernel::error::Error;
    pub use kernel::error::Result;
    pub use kernel::fcntl;
    pub use kernel::file::Major;
    pub use kernel::fs;
    pub use kernel::stat;
    pub use kernel::sync;
    use stat::Stat;
    include!(concat!(env!("OUT_DIR"), "/usys.rs"));
}
pub extern crate alloc;
#[macro_use]
pub mod stdio;
pub mod env;
pub mod fs;
pub mod io;
pub mod mutex;
pub mod path;
pub mod pipe;
pub mod process;
pub mod umalloc;
//pub mod regex;

use crate::env::ARGS;
use core::panic;
use env::ENVIRON;
use io::Write;

// wrapper so that it's ok if main() does not call exit().
#[lang = "start"]
fn lang_start<T: Termination + 'static>(
    main: fn() -> T,
    argc: isize,
    argv: *const *const u8,
    _: u8,
) -> isize {
    unsafe {
        if let Some(argv) = (argv as *mut &mut [Option<&str>]).as_mut() {
            let (args, environ) = argv.split_at_mut(argc as usize);
            ARGS = Some(args);
            ENVIRON = Some(environ);
        }
    }
    let xstatus = main().report() as i32;
    sys::exit(xstatus)
}

pub enum ExitCode {
    SUCCESS = 0x0isize,
    FAILURE = 0x1isize,
}

#[lang = "termination"]
pub trait Termination {
    fn report(self) -> ExitCode;
}

impl Termination for () {
    fn report(self) -> ExitCode {
        ExitCode::SUCCESS
    }
}

impl Termination for ! {
    fn report(self) -> ExitCode {
        self
    }
}

impl Termination for ExitCode {
    #[inline]
    fn report(self) -> ExitCode {
        self
    }
}

impl<T: Termination, E> Termination for core::result::Result<T, E> {
    fn report(self) -> ExitCode {
        match self {
            Ok(val) => val.report(),
            Err(_) => ExitCode::FAILURE,
        }
    }
}

#[panic_handler]
fn panic(_info: &panic::PanicInfo<'_>) -> ! {
    if let Some(out) = crate::stdio::panic_output() {
        let _ = out.write_fmt(format_args!("{}\n", _info));
    }
    sys::exit(-1)
}

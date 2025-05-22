use crate::console;
use crate::spinlock::Mutex;
use core::fmt;
use core::panic;
use core::sync::atomic::{AtomicBool, Ordering};

pub static PR: Pr = Pr {
    writer: Mutex::new(Writer, "pr"),
    panicked: AtomicBool::new(false),
    locking: AtomicBool::new(true),
};

// lock to avoid interleaving concurrent println!'s.
// Pr struct is slightly different, i.e.,
// it is not wrapped in a Mutex
// Because we need another field(locking),
// This trick can make `panic` print something to the console quicker.
pub struct Pr {
    writer: Mutex<Writer>,
    panicked: AtomicBool,
    locking: AtomicBool,
}

impl Pr {
    pub fn panicked(&self) -> &AtomicBool {
        &self.panicked
    }
}

pub struct Writer;

impl Writer {
    fn print(&self, c: u8) {
        console::putc(c)
    }
}

impl fmt::Write for Writer {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        for byte in s.bytes() {
            self.print(byte);
        }
        Ok(())
    }
}

pub fn _print(args: fmt::Arguments<'_>) {
    use fmt::Write;

    if PR.locking.load(Ordering::Relaxed) {
        PR.writer.lock().write_fmt(args).expect("_print: error");
    } else {
        // for panic!
        unsafe {
            PR.writer.get_mut().write_fmt(args).expect("_print: error");
        }
    }
}

#[macro_export]
macro_rules! print {
    ($($arg:tt)*) => {
        $crate::printf::_print(format_args!($($arg)*))
    };
}
#[macro_export]
macro_rules! println {
    ($fmt:literal$(, $($arg: tt)+)?) => {
        $crate::printf::_print(format_args!(concat!($fmt, "\n") $(,$($arg)+)?))
    };
}

pub static mut EWRITER: Writer = Writer;

#[allow(static_mut_refs)]
pub fn _eprint(args: fmt::Arguments<'_>) {
    use fmt::Write;
    unsafe {
        EWRITER.write_fmt(args).expect("_print: error");
    }
}

#[macro_export]
macro_rules! eprint {
    ($($arg:tt)*) => {
        $crate::printf::_eprint(format_args!($($arg)*))
    };
}

#[allow(clippy::empty_loop)]
pub fn panic_inner(info: &panic::PanicInfo<'_>) -> ! {
    PR.locking.store(false, Ordering::Relaxed);
    crate::println!("core {}: {}", unsafe { crate::proc::Cpus::cpu_id() }, info);
    PR.panicked.store(true, Ordering::Relaxed);
    loop {}
}

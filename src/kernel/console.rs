// Console input and output, to the uart.
// Reads are line at a time.
// Implements special input characters:
//   newline -- end of line
//   control-h -- backspace
//   control-u -- kill line
//   control-d -- end of line
//   control-p -- print process list

use crate::error::{Error::*, Result};
use crate::file::{Device, Major, DEVSW};
use crate::proc::{dump, either_copyin, either_copyout, sleep, wakeup, Cpus};
use crate::spinlock::Mutex;
use crate::uart;
use crate::vm::VirtAddr;
use core::num::Wrapping;

pub static CONS: Mutex<Cons> = Mutex::new(Cons::new(), "cons");

const BS: u8 = 0x08;

// Control-x
const fn ctrl(x: u8) -> u8 {
    x - b'@'
}

const INPUT_BUF_SIZE: usize = 128;
pub struct Cons {
    buf: [u8; INPUT_BUF_SIZE],
    r: Wrapping<usize>, // Read index
    w: Wrapping<usize>, // Write index
    e: Wrapping<usize>, // Edit index
}

impl Cons {
    const fn new() -> Cons {
        Cons {
            buf: [0; INPUT_BUF_SIZE],
            r: Wrapping(0),
            w: Wrapping(0),
            e: Wrapping(0),
        }
    }
}

impl Device for Mutex<Cons> {
    //
    // user read()s from the console go here.
    // copy (up to) a whole input line to dst.
    //
    fn read(&self, mut dst: VirtAddr, mut n: usize) -> Result<usize> {
        let mut cons_guard = self.lock();
        let p = Cpus::myproc().unwrap();

        let target = n;
        while n > 0 {
            // wait until interrupt handler has put some
            // input into CONS.buf
            while cons_guard.r == cons_guard.w {
                if p.inner.lock().killed {
                    return Err(Interrupted);
                }
                cons_guard = sleep(&cons_guard.r as *const _ as usize, cons_guard);
            }
            let c = cons_guard.buf[cons_guard.r.0 % INPUT_BUF_SIZE];
            cons_guard.r += Wrapping(1);

            if c == ctrl(b'D') {
                // end of line
                if n < target {
                    // Save ^D for nexst time, to make sure
                    // caller gets a 0-bytes result.
                    cons_guard.r -= Wrapping(1);
                }
                break;
            }

            // copy the input byte to the user-space buffer.
            either_copyout(dst, &c)?;

            dst += 1;
            n -= 1;

            if c == b'\n' {
                // a whole line has arrived, return to
                // the user-level read().
                break;
            }
        }

        Ok(target - n)
    }

    //
    // user write()s to the console go here.
    //
    fn write(&self, src: VirtAddr, n: usize) -> Result<usize> {
        for i in 0..n {
            let mut c = 0;
            either_copyin(&mut c, src + i)?;
            putc(c)
        }
        Ok(n)
    }

    fn major(&self) -> Major {
        Major::Console
    }
}

impl Mutex<Cons> {
    //
    // the console input interrupt handler.
    // CONS.intr() calls this for input character.
    // do erase/kill processing, append to cons.buf,
    // wake up CONS.read() if a whole line has arrived.
    //
    pub fn intr(&self, c: u8) {
        let mut cons_guard = self.lock();
        match c {
            // Print process list
            m if m == ctrl(b'P') => dump(),
            // Kill line
            m if m == ctrl(b'U') => {
                while cons_guard.e != cons_guard.w
                    && cons_guard.buf[(cons_guard.e - Wrapping(1)).0 % INPUT_BUF_SIZE] != b'\n'
                {
                    cons_guard.e -= Wrapping(1);
                    putc(ctrl(b'H'));
                }
            }
            // Backspace
            m if m == ctrl(b'H') | b'\x7f' => {
                if cons_guard.e != cons_guard.w {
                    cons_guard.e -= Wrapping(1);
                    putc(ctrl(b'H'));
                }
            }
            _ => {
                if c != 0 && (cons_guard.e - cons_guard.r).0 < INPUT_BUF_SIZE {
                    let c = if c == b'\r' { b'\n' } else { c };

                    // echo back to the user
                    putc(c);

                    // store for consumption by CONS.read().
                    let e_idx = cons_guard.e.0 % INPUT_BUF_SIZE;
                    cons_guard.buf[e_idx] = c;
                    cons_guard.e += Wrapping(1);

                    if c == b'\n'
                        || c == ctrl(b'D')
                        || (cons_guard.e - cons_guard.r).0 == INPUT_BUF_SIZE
                    {
                        // wake up CONS.read() if a whole line (or end of line)
                        // has arrived
                        cons_guard.w = cons_guard.e;
                        wakeup(&cons_guard.r as *const _ as usize);
                    }
                }
            }
        }
    }
}

pub fn init() {
    unsafe { uart::init() }
    DEVSW.set(Major::Console, &CONS).unwrap();
}

//
// send one character to the uart.
// called by printf, and to echo input characters,
// but not from write().
//
pub fn putc(c: u8) {
    if c == ctrl(b'H') {
        uart::putc_sync(BS);
        uart::putc_sync(b' ');
        uart::putc_sync(BS);
    } else {
        uart::putc_sync(c);
    }
}

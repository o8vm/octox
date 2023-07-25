use crate::{
    console::CONS,
    memlayout::UART0,
    printf::PR,
    proc::{self, Cpus},
    spinlock::Mutex,
};
use core::{num::Wrapping, ptr, sync::atomic::Ordering};
use Register::*;

#[allow(clippy::identity_op)]
const LCR_EIGHT_BITS: u8 = 3 << 0;
const LCR_BAUD_LATCH: u8 = 1 << 7;
const IER_RX_ENABLE: u8 = 1 << 0;
const IER_TX_ENABLE: u8 = 1 << 1;
const FCR_FIFO_ENABLE: u8 = 1 << 0;
const FCR_FIFO_CLEAR: u8 = 3 << 1;
const _LSR_RX_READY: u8 = 1 << 0;
const LSR_TX_IDLE: u8 = 1 << 5;

// UART driver object
pub static UART: Mutex<Uart> = Mutex::new(Uart::new(UART0), "uart");

const UART_TX_BUF_SIZE: usize = 32;
pub struct Uart {
    base_address: usize,
    tx_buf: [u8; UART_TX_BUF_SIZE], // the transmit output buffer
    tx_w: Wrapping<usize>,          // write next to tx_buf[tx_w % UART_TX_BUF_SIZE]
    tx_r: Wrapping<usize>,          // read next from tx_buf[tx_r % UART_TX_BUF_SIZE]
}

enum Register {
    Rbr,
    Thr,
    Ier,
    _IIR,
    Fcr,
    Lcr,
    Lsr,
}

impl Register {
    fn addr(self, base_addr: usize) -> *mut u8 {
        match self {
            Self::Rbr | Self::Thr => base_addr as *mut u8,
            Self::Ier => (base_addr + 1) as *mut u8,
            Self::_IIR | Self::Fcr => (base_addr + 2) as *mut u8,
            Self::Lcr => (base_addr + 3) as *mut u8,
            Self::Lsr => (base_addr + 5) as *mut u8,
        }
    }
}

impl Uart {
    pub const fn new(base_address: usize) -> Self {
        Self {
            base_address,
            tx_buf: [0; UART_TX_BUF_SIZE],
            tx_w: Wrapping(0),
            tx_r: Wrapping(0),
        }
    }

    pub fn init(&mut self) {
        // diable interrupts.
        self.write(Ier, 0x00);

        // special mode to set baud rate.
        self.write(Lcr, LCR_BAUD_LATCH);

        // LSB for baud rate of 38.4K.
        self.write(Rbr, 0x03);

        // MSB for baud rate of 38.4K
        self.write(Ier, 0x00);

        // leave set-baud mode,
        // and set worf length to 8 bits, no parity.
        self.write(Lcr, LCR_EIGHT_BITS);

        // reset and enable FIFOs
        self.write(Fcr, FCR_FIFO_ENABLE | FCR_FIFO_CLEAR);

        // enable transmit and receive interrupts
        self.write(Ier, IER_TX_ENABLE | IER_RX_ENABLE);
    }

    fn read(&self, reg: Register) -> u8 {
        unsafe { ptr::read_volatile(reg.addr(self.base_address)) }
    }

    fn write(&mut self, reg: Register, val: u8) {
        unsafe { ptr::write_volatile(reg.addr(self.base_address), val) }
    }

    // if the UART is idle, and a character is waiting
    // in the transmit buffer, send it.
    // caller must hold "uart" lock.
    // called from both top- and bottom-half.
    fn start(&mut self) {
        loop {
            if self.tx_w == self.tx_r {
                // trasnmit buffer is empty.
                break;
            }

            if self.read(Lsr) & LSR_TX_IDLE == 0 {
                // the UART transmit holding register is full,
                // so we cannot give it another byte.
                // it will interrupt when it's ready for a new byte.
                break;
            }

            let c = *self.tx_buf.get(self.tx_r.0 % UART_TX_BUF_SIZE).unwrap();
            self.tx_r += Wrapping(1);

            // maybe putc() is waiting for space in the buffer
            proc::wakeup(&self.tx_r as *const _ as usize);
            self.write(Thr, c);
        }
    }
}

impl Mutex<Uart> {
    // add a character to the output buffer and tell the
    // UART to start sending if it isn't already.
    // blocks if the output buffer is full.
    // because it may block, it can't be called
    // from interrupts; it's only suitable for use
    // by write()
    pub fn putc(&self, c: u8) {
        let mut uart_guard = self.lock();

        #[allow(clippy::empty_loop)]
        if PR.panicked().load(Ordering::Relaxed) {
            loop {}
        }

        loop {
            if uart_guard.tx_w == uart_guard.tx_r + Wrapping(UART_TX_BUF_SIZE) {
                // buffer is full.
                // wait for self.start() to open up space in the buffer
                uart_guard = proc::sleep(&uart_guard.tx_r as *const _ as usize, uart_guard);
            } else {
                let write_idx = uart_guard.tx_w.0 % UART_TX_BUF_SIZE;
                *uart_guard.tx_buf.get_mut(write_idx).unwrap() = c;
                uart_guard.tx_w += Wrapping(1);
                uart_guard.start();
                break;
            }
        }
    }

    // read one input character from the UART.
    // return Option<u8>
    fn getc(&self) -> Option<u8> {
        let uart = unsafe { self.get_mut() };
        if uart.read(Lsr) & 0x01 != 0 {
            Some(uart.read(Rbr))
        } else {
            None
        }
    }

    // handle a uart interrupt, raised because input has
    // arraived, or the uart is ready more output, or
    // both. called from trap.c
    pub fn intr(&self) {
        // read and process incoming characters
        while let Some(c) = self.getc() {
            CONS.intr(c);
        }

        // send buffered characters.
        self.lock().start();
    }
}

pub(crate) unsafe fn init() {
    UART.get_mut().init();
}

// alternate version of putc that doesn't
// use interrupts, for use by kernel printf() and
// to echo characters.  it spins wating for the uart's
// output register to be empty.
pub fn putc_sync(c: u8) {
    let _intr_lock = Cpus::lock_mycpu("putcwithoutspin");
    let uart = unsafe { UART.get_mut() };

    #[allow(clippy::empty_loop)]
    if PR.panicked().load(Ordering::Relaxed) {
        loop {}
    }

    // wait for Transmit Holding Empty to be set in LSR.
    loop {
        if uart.read(Lsr) & LSR_TX_IDLE != 0 {
            break;
        }
    }
    uart.write(Thr, c);
}

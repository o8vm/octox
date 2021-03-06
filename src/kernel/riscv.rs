use core::arch::asm;
use riscv::register::*;

pub fn w_sstatus(sstatus: usize) {
    unsafe {
        asm!("csrw sstatus, {}", in(reg) sstatus);
    }
}

pub fn r_sstatus() -> usize {
    let sstatus: usize;
    unsafe { asm!("csrr {}, sstatus", out(reg) sstatus) }
    sstatus
}

pub fn w_sip(sip: usize) {
    unsafe {
        asm!("csrw sip, {}", in(reg) sip);
    }
}
// use riscv's sv39 page table scheme
const SATP_SV39: usize = 8 << 60;

pub const fn make_satp(pagetable: usize) -> usize {
    SATP_SV39 | (pagetable >> 12)
}

// enable device interrupts
pub fn intr_on() {
    unsafe {
        sstatus::set_sie();
    }
}

// disable device interrupts
pub fn intr_off() {
    unsafe {
        sstatus::clear_sie();
    }
}

// are device interrupts enabled?
pub fn intr_get() -> bool {
    sstatus::read().sie()
}

pub const PGSIZE: usize = 4096; // bytes per page
pub const PGSHIFT: usize = 12; // bits of offset within a page

pub const fn pgroundup(sz: usize) -> usize {
    (sz + PGSIZE - 1) & !(PGSIZE - 1)
}

pub const fn pgrounddown(sz: usize) -> usize {
    sz & !(PGSIZE - 1)
}

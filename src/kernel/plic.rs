use crate::{
    memlayout::{PLIC_PRIORITY, PLIC_SCLAIM, PLIC_SENABLE, PLIC_SPRIORITY, UART0_IRQ, VIRTIO0_IRQ},
    proc::Cpus,
};

// the riscv Platform Level Interrupt Controller (PLIC).

pub fn init() {
    let priority = PLIC_PRIORITY as *mut u32;
    unsafe {
        priority.add(UART0_IRQ as usize).write_volatile(1);
        priority.add(VIRTIO0_IRQ as usize).write_volatile(1);
    }
}

pub fn inithart() {
    unsafe {
        let hart = Cpus::cpu_id();

        // set uart's enable bit for this hart's S-mode.
        let senable = PLIC_SENABLE(hart) as *mut u32;
        senable.write_volatile((1 << UART0_IRQ) | (1 << VIRTIO0_IRQ));

        // set this hart's S-mode priority threshold to 0.
        let spriority = PLIC_SPRIORITY(hart) as *mut u32;
        spriority.write_volatile(0);
    }
}

// ask the PLIC what interrupt we shold serve.
pub fn claim() -> Option<u32> {
    unsafe {
        let hart = Cpus::cpu_id();
        let reg = PLIC_SCLAIM(hart) as *mut u32;
        let irq = reg.read_volatile();
        if irq == 0 {
            None
        } else {
            Some(irq)
        }
    }
}

// tell the PLIC we've served this IRQ.
pub fn complete(irq: u32) {
    unsafe {
        let hart = Cpus::cpu_id();
        let reg = PLIC_SCLAIM(hart) as *mut u32;
        reg.write_volatile(irq);
    }
}

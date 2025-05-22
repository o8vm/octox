use core::arch::naked_asm;

// interrupts and exceptions while in supervisor mode come here.
// push all registers, call kerneltrap(), restorem return.
#[unsafe(naked)]
#[repr(align(16))]
#[no_mangle]
pub unsafe extern "C" fn kernelvec() -> ! {
    naked_asm!(
        // make room to save registers.
        "addi sp, sp, -256",
        // save the registers.
        "sd ra, 0(sp)",
        "sd sp, 8(sp)",
        "sd gp, 16(sp)",
        "sd tp, 24(sp)",
        "sd t0, 32(sp)",
        "sd t1, 40(sp)",
        "sd t2, 48(sp)",
        "sd s0, 56(sp)",
        "sd s1, 64(sp)",
        "sd a0, 72(sp)",
        "sd a1, 80(sp)",
        "sd a2, 88(sp)",
        "sd a3, 96(sp)",
        "sd a4, 104(sp)",
        "sd a5, 112(sp)",
        "sd a6, 120(sp)",
        "sd a7, 128(sp)",
        "sd s2, 136(sp)",
        "sd s3, 144(sp)",
        "sd s4, 152(sp)",
        "sd s5, 160(sp)",
        "sd s6, 168(sp)",
        "sd s7, 176(sp)",
        "sd s8, 184(sp)",
        "sd s9, 192(sp)",
        "sd s10, 200(sp)",
        "sd s11, 208(sp)",
        "sd t3, 216(sp)",
        "sd t4, 224(sp)",
        "sd t5, 232(sp)",
        "sd t6, 240(sp)",
        // call the Rust trap handler in trap.rs
        "call kerneltrap",
        // restore registers.
        "ld ra, 0(sp)",
        "ld sp, 8(sp)",
        "ld gp, 16(sp)",
        // not this, in case we moved CPUs: ld tp, 24(sp)
        "ld t0, 32(sp)",
        "ld t1, 40(sp)",
        "ld t2, 48(sp)",
        "ld s0, 56(sp)",
        "ld s1, 64(sp)",
        "ld a0, 72(sp)",
        "ld a1, 80(sp)",
        "ld a2, 88(sp)",
        "ld a3, 96(sp)",
        "ld a4, 104(sp)",
        "ld a5, 112(sp)",
        "ld a6, 120(sp)",
        "ld a7, 128(sp)",
        "ld s2, 136(sp)",
        "ld s3, 144(sp)",
        "ld s4, 152(sp)",
        "ld s5, 160(sp)",
        "ld s6, 168(sp)",
        "ld s7, 176(sp)",
        "ld s8, 184(sp)",
        "ld s9, 192(sp)",
        "ld s10, 200(sp)",
        "ld s11, 208(sp)",
        "ld t3, 216(sp)",
        "ld t4, 224(sp)",
        "ld t5, 232(sp)",
        "ld t6, 240(sp)",
        "addi sp, sp, 256",
        // return to whatever we were doing in the kernel.
        "sret",
    );
}

#[unsafe(naked)]
#[repr(align(16))] // if miss this alignment, a load access fault will occur.
#[no_mangle]
pub unsafe extern "C" fn timervec() -> ! {
    // start.rs has set up the memory that mscratch points to:
    // scratch[0,8,16] : register save area.
    // scratch[24] : address of CLINT's MTIMECMP register.
    // scratch[32] : desired interval between interrupts.

    // Now, mscrach has a pointer to an additional scratch space.
    // to aboid overwriting the contents of the integer registers,
    // the prologue of an interrupts handler usually begins by swapping
    // an integer register(say a0) with mscratch CSR.
    // The interrupt handler stores the integer registers
    // used for processing in this scratch space.
    // a0 saved in mscrach, a1 ~ a3 saved in scratch space.
    //loop {}
    naked_asm!(
        "csrrw a0, mscratch, a0",
        "sd a1, 0(a0)",
        "sd a2, 8(a0)",
        "sd a3, 16(a0)",
        // schedule the next timer interrupt
        // by adding interval to mtimecmp.
        "ld a1, 24(a0)", // CLINT_MTIMECMP(hartid) contents
        "ld a2, 32(a0)", // interval
        "ld a3, 0(a1)",
        "add a3, a3, a2",
        "sd a3, 0(a1)",
        // raise a supervisor software interrupt.
        "li a1, 2",
        "csrw sip, a1",
        // restore and return
        "ld a3, 16(a0)",
        "ld a2, 8(a0)",
        "ld a1, 0(a0)",
        "csrrw a0, mscratch, a0",
        "mret",
    );
}

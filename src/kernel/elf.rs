pub const EI_MAG0: usize = 0;
pub const EI_MAG1: usize = 1;
pub const EI_MAG2: usize = 2;
pub const EI_MAG3: usize = 3;
pub const EI_CLSS: usize = 4;
pub const EI_DATA: usize = 5;

pub const ELFMAG0: u8 = 127;
pub const ELFMAG1: u8 = b'E';
pub const ELFMAG2: u8 = b'L';
pub const ELFMAG3: u8 = b'F';

pub const ELF64CL: u8 = 2;

pub const ELFDATA2LSB: u8 = 1;

pub const PT_LOAD: u32 = 1;

#[derive(Copy, Clone, Default)]
#[repr(C, packed)]
pub struct ElfHdr {
    pub e_ident: [u8; 16],
    pub e_type: u16,
    pub e_cpu: u16,
    pub e_version: u32,
    pub e_entry: usize,
    pub e_phoff: usize,
    pub e_shoff: usize,
    pub e_flags: u32,
    pub e_ehsize: u16,
    pub e_phsize: u16,
    pub e_phnum: u16,
    pub e_shsize: u16,
    pub e_shnum: u16,
    pub e_shname: u16,
}

#[derive(Copy, Clone, Default)]
#[repr(C, packed)]
pub struct ProgHdr {
    pub p_type: u32,
    pub p_flags: u32,
    pub p_offset: usize,
    pub p_vaddr: usize,
    pub p_paddr: usize,
    pub p_fsize: usize,
    pub p_msize: usize,
    pub p_align: usize,
}

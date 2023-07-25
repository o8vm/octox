use crate::error::Result;
use crate::file::{Device, Major, DEVSW};
use crate::vm::VirtAddr;

pub static NULL: Null = Null;
pub struct Null;

impl Device for Null {
    fn read(&self, _dst: VirtAddr, _n: usize) -> Result<usize> {
        Ok(0)
    }
    fn write(&self, _src: VirtAddr, n: usize) -> Result<usize> {
        Ok(n)
    }
    fn major(&self) -> crate::file::Major {
        crate::file::Major::Null
    }
}

pub fn init() {
    DEVSW.set(Major::Null, &NULL).unwrap();
}

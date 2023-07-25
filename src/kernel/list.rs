// double-linked, circular list. double-linked makes remove
// fast. circular simplifies code, because don't have to check for
// empty list in insert and remove.
// ref: https://github.com/mit-pdos/xv6-riscv-fall19/blob/xv6-riscv-fall19/kernel/list.c
use core::ptr;

pub struct List {
    next: *mut List,
    prev: *mut List,
}

impl List {
    pub fn init(&mut self) {
        self.prev = self;
        self.next = self;
    }

    pub fn is_empty(&self) -> bool {
        ptr::eq(self.next, self)
    }

    pub unsafe fn remove(e: *mut List) {
        (*(*e).prev).next = (*e).next;
        (*(*e).next).prev = (*e).prev;
    }

    pub unsafe fn pop(&mut self) -> Option<usize> {
        if self.is_empty() {
            return None;
        }
        let raw_addr = self.next as usize;
        Self::remove(self.next);
        Some(raw_addr)
    }

    pub unsafe fn push(&mut self, raw_addr: usize) {
        let e = raw_addr as *mut List;
        ptr::write(
            e,
            List {
                prev: self,
                next: self.next,
            },
        );
        (*self.next).prev = e;
        self.next = e;
    }
}

// Physical memory allocator based on BuddyAllocator.

use crate::buddy::BuddyAllocator;
use crate::memlayout::PHYSTOP;
use crate::spinlock::Mutex;
use core::alloc::{GlobalAlloc, Layout};
use core::ptr;

extern "C" {
    // first address after kernel.
    // defined by kernel.ld
    static mut end: [u8; 0];
}

#[global_allocator]
pub static KMEM: Kmem = Kmem(Mutex::new(BuddyAllocator::new(), "kmem"));

#[alloc_error_handler]
fn on_oom(layout: Layout) -> ! {
    panic!("alloc error: {:?}", layout)
}

pub struct Kmem(Mutex<BuddyAllocator>);

unsafe impl GlobalAlloc for Kmem {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        self.0
            .lock()
            .alloc(layout)
            .map_or(ptr::null_mut(), |p| p.as_ptr())
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        self.0.lock().dealloc(ptr, layout)
    }
}

#[allow(static_mut_refs)]
pub fn init() {
    unsafe {
        KMEM.0.lock().init(end.as_ptr() as usize, PHYSTOP).unwrap();
    }
}

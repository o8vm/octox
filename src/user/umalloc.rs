use crate::{mutex::Mutex, sys};
use core::alloc::{GlobalAlloc, Layout};
use core::{mem::size_of, ptr::NonNull};

#[global_allocator]
static UMEM: UMem = UMem(Mutex::new(Allocator::new()));

struct UMem(Mutex<Allocator>);
unsafe impl GlobalAlloc for UMem {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        self.0.lock().alloc(layout)
    }
    unsafe fn dealloc(&self, ptr: *mut u8, _layout: Layout) {
        self.0.lock().free(ptr)
    }
}

#[alloc_error_handler]
fn on_oom(layout: Layout) -> ! {
    panic!("alloc error: {:?}", layout)
}

struct Allocator {
    base: Header,
    freep: Option<NonNull<Header>>,
}
unsafe impl Send for Allocator {}

#[repr(C, align(16))]
struct Header {
    ptr: Option<NonNull<Header>>,
    size: usize,
}

impl Header {
    const fn new() -> Self {
        Self { ptr: None, size: 0 }
    }
}

impl Allocator {
    const fn new() -> Self {
        Self {
            base: Header::new(),
            freep: None,
        }
    }

    unsafe fn alloc(&mut self, layout: Layout) -> *mut u8 {
        let nbytes = layout.size();
        let mut p: Option<NonNull<Header>>;
        let mut prevp: Option<NonNull<Header>>;

        let nunits = (nbytes + size_of::<Header>() - 1) / size_of::<Header>() + 1;
        prevp = self.freep;

        if prevp.is_none() {
            prevp = NonNull::new(&mut self.base as *mut _);
            self.freep = prevp;
            self.base.ptr = prevp;
            self.base.size = 0;
        }

        p = prevp.unwrap().as_ref().ptr;
        loop {
            if p.unwrap().as_ref().size >= nunits {
                if p.unwrap().as_ref().size == nunits {
                    prevp.unwrap().as_mut().ptr = p.unwrap().as_ref().ptr;
                } else {
                    p.unwrap().as_mut().size -= nunits;
                    p = NonNull::new(p.unwrap().as_ptr().add(p.unwrap().as_ref().size));
                    p.unwrap().as_mut().size = nunits;
                }
                self.freep = prevp;
                break p.unwrap().as_ptr().add(1) as *mut u8;
            }
            if p == self.freep {
                match self.morecore(nunits) {
                    None => break core::ptr::null_mut(),
                    np => p = np,
                }
            }
            prevp = p;
            p = p.unwrap().as_ref().ptr;
        }
    }

    unsafe fn morecore(&mut self, mut nu: usize) -> Option<NonNull<Header>> {
        if nu < 4096 {
            nu = 4096
        }
        let p = NonNull::new(sys::sbrk(nu * size_of::<Header>()).ok()? as *mut Header);
        p.unwrap().as_mut().size = nu;
        self.free(p.unwrap().as_ptr().add(1) as *mut u8);
        self.freep
    }

    unsafe fn free(&mut self, ap: *mut u8) {
        let bp: Option<NonNull<Header>> = NonNull::new((ap as *mut Header).sub(1));
        let mut p = self.freep;

        while !(bp > p && bp < p.unwrap().as_ref().ptr) {
            if p >= p.unwrap().as_ref().ptr && (bp > p || bp < p.unwrap().as_ref().ptr) {
                break;
            }
            p = p.unwrap().as_ref().ptr;
        }

        if NonNull::new(bp.unwrap().as_ptr().add(bp.unwrap().as_ref().size))
            == p.unwrap().as_ref().ptr
        {
            let p_ptr = p.unwrap().as_ref().ptr;
            bp.unwrap().as_mut().size += p_ptr.unwrap().as_ref().size;
            bp.unwrap().as_mut().ptr = p_ptr.unwrap().as_ref().ptr;
        } else {
            bp.unwrap().as_mut().ptr = p.unwrap().as_ref().ptr;
        }

        if NonNull::new(p.unwrap().as_ptr().add(p.unwrap().as_ref().size)) == bp {
            p.unwrap().as_mut().size += bp.unwrap().as_ref().size;
            p.unwrap().as_mut().ptr = bp.unwrap().as_ref().ptr;
        } else {
            p.unwrap().as_mut().ptr = bp;
        }
        self.freep = p;
    }
}

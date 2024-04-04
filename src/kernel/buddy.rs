// buddy memory allocator

use crate::list::List;
use core::alloc::Layout;
use core::cmp;
use core::ptr::{self, NonNull};

const fn round_up(n: usize, sz: usize) -> usize {
    (((n - 1) / sz) + 1) * sz
}
const fn round_down(n: usize, sz: usize) -> usize {
    (n / sz) * sz
}

type BdList = List;

pub struct BuddyAllocator {
    initialized: bool, // initialization flag
    base: usize,       // memory start address
    end: usize,        // memory end address
    nsize: usize,      // number of entries in self.sizes array
    sizes: Option<NonNull<[SzInfo]>>,
}
unsafe impl Send for BuddyAllocator {}

// The allocator has SzInfo for each size k. Each SzInfo has a free
// list, an array alloc to keep track which blocks have been
// allocated, and an split array to keep track which blocks have
// been split. The arrays are of type u8 (which is 1 byte), but the
// allocator uses 1 bit per block (thus, one byte records the info of
// 8 blocks).
struct SzInfo {
    free: BdList,
    alloc: Option<NonNull<[u8]>>,
    split: Option<NonNull<[u8]>>,
}

trait Array {
    fn bit_set(&mut self, index: usize, set_or_clear: bool);
    fn bit_isset(&self, index: usize) -> bool;
}

impl Array for Option<NonNull<[u8]>> {
    fn bit_set(&mut self, index: usize, set_or_clear: bool) {
        if let Some(array) = self {
            let m = 1 << (index % 8);
            match (unsafe { array.as_mut() }.get_mut(index / 8), set_or_clear) {
                (Some(b), true) => *b |= m,
                (Some(b), false) => *b &= !m,
                _ => unreachable!(),
            }
        }
    }
    fn bit_isset(&self, index: usize) -> bool {
        match self {
            Some(array) => {
                let m = 1 << (index % 8);
                match unsafe { array.as_ref() }.get(index / 8) {
                    Some(b) => *b & m == m,
                    _ => false,
                }
            }
            _ => false,
        }
    }
}

impl BuddyAllocator {
    // The smallest block size
    const LEAF_SIZE: usize = 16;
    // The largest block size
    const MAX_ALIGN: usize = 4096;

    // Largest index in self.sizes array
    const fn max_size(&self) -> usize {
        self.nsize - 1
    }

    // Size of block at size k
    const fn blk_size(k: usize) -> usize {
        (1 << k) * Self::LEAF_SIZE
    }

    // Number of block at size k
    const fn nblk(&self, k: usize) -> usize {
        1 << (self.max_size() - k)
    }

    // What is the first k such that LEAF_SIZE * 2^k > n?
    fn firstk(&self, n: usize) -> usize {
        if n <= Self::LEAF_SIZE {
            0
        } else {
            (n.next_power_of_two() / Self::LEAF_SIZE).trailing_zeros() as usize
        }
    }

    fn blk_index(&self, k: usize, p: usize) -> usize {
        (p - self.base) / Self::blk_size(k)
    }

    fn addr(&self, k: usize, bi: usize) -> usize {
        self.base + bi * Self::blk_size(k)
    }

    fn blk_index_next(&self, k: usize, p: usize) -> usize {
        let mut n = (p - self.base) / Self::blk_size(k);
        if (p - self.base) % Self::blk_size(k) != 0 {
            n += 1;
        }
        n
    }

    // New
    pub const fn new() -> Self {
        Self {
            initialized: false,
            base: 0,
            end: 0,
            nsize: 0,
            sizes: None,
        }
    }

    // allocate a range of memory satisfying `layout` requirements.
    pub fn alloc(&mut self, layout: Layout) -> Option<NonNull<u8>> {
        if let Some(mut sizes_ptr) = self.sizes {
            let sizes = unsafe { sizes_ptr.as_mut() };

            if layout.align() > Self::MAX_ALIGN {
                return None;
            }
            // Note: The size of the value is always a multiple of the alignment.
            // In this case, since self.base and self.end are already aligned to
            // max_align, we only need to consider the size.

            // Find a free block > layout.size, staring with smallest k possible
            let fk = self.firstk(layout.size());
            let mut k = fk;
            for szinfo in sizes.get(fk..self.nsize)?.iter() {
                if !szinfo.free.is_empty() {
                    break;
                }
                k += 1;
            }
            if k >= self.nsize {
                // No free blocks?
                return None;
            }

            // Found a block; pop it and potentially split it.
            let p = match unsafe { sizes[k].free.pop() } {
                Some(raw_addr) => raw_addr,
                None => return None,
            };
            sizes[k].alloc.bit_set(self.blk_index(k, p), true);
            while k > fk {
                // split a block at size k and mark one half allocated at size k-1
                // and put the buddy on the free list at size k-1.
                let q = p + Self::blk_size(k - 1);
                sizes[k].split.bit_set(self.blk_index(k, p), true);
                sizes[k - 1].alloc.bit_set(self.blk_index(k - 1, p), true);
                unsafe {
                    sizes[k - 1].free.push(q);
                }
                k -= 1;
            }
            NonNull::new(p as *mut u8)
        } else {
            None
        }
    }

    // Find the size of the block that p points to.
    fn size(&self, p: usize) -> usize {
        if let Some(sizes_ptr) = self.sizes {
            let sizes = unsafe { sizes_ptr.as_ref() };
            for (k, (_, szinfo1)) in sizes.iter().zip(sizes.iter().skip(1)).enumerate() {
                if szinfo1.split.bit_isset(self.blk_index(k + 1, p)) {
                    return k;
                }
            }
            0
        } else {
            0
        }
    }

    // Free memory pointed by p, which earlier allocated using
    // alloc
    pub fn dealloc(&mut self, p: *mut u8, _layout: Layout) {
        let mut p = p as usize;
        let mut fk = self.size(p);
        let mut q;
        if let Some(mut sizes_ptr) = self.sizes {
            let sizes = unsafe { sizes_ptr.as_mut() };
            for k in self.size(p)..self.max_size() {
                let bi = self.blk_index(k, p);
                let buddy = if bi % 2 == 0 { bi + 1 } else { bi - 1 };
                sizes[k].alloc.bit_set(bi, false); // free p at size k
                if sizes[k].alloc.bit_isset(buddy) {
                    // is buddy allocated?
                    break; // break out of loop
                }
                // buddy is free; merge with buddy
                q = self.addr(k, buddy);
                unsafe { List::remove(q as *mut List) } // remove buddy from free list
                if buddy % 2 == 0 {
                    p = q;
                }
                // at size k + 1, mark that the merged buddy pair isn't split
                // anymore
                sizes[k + 1].split.bit_set(self.blk_index(k + 1, p), false);
                fk += 1;
            }
            unsafe {
                sizes[fk].free.push(p);
            }
        }
    }

    // Mark memory from [start, stop), starting at size 0, as allocated.
    fn mark(&mut self, start: usize, stop: usize) {
        assert_eq!(start % Self::LEAF_SIZE, 0);
        assert_eq!(stop % Self::LEAF_SIZE, 0);

        let mut sizes_ptr = self.sizes.unwrap();
        let sizes = unsafe { sizes_ptr.as_mut() };
        for (k, szinfo) in sizes.iter_mut().enumerate() {
            let mut bi: usize = self.blk_index(k, start);
            let bj: usize = self.blk_index_next(k, stop);
            while bi < bj {
                if k > 0 {
                    // if a block is allocated at size k, mark it as split too.
                    szinfo.split.bit_set(bi, true);
                }
                szinfo.alloc.bit_set(bi, true);
                bi += 1;
            }
        }
    }

    // If a block is marked as allocated and buddy is free, put the
    // buddy on the free list at size k.
    fn initfree_pair(&mut self, k: usize, bi: usize) -> usize {
        let buddy = if bi % 2 == 0 { bi + 1 } else { bi - 1 };
        if let Some(mut sizes_ptr) = self.sizes {
            let sizes = unsafe { sizes_ptr.as_mut() };

            if sizes[k].alloc.bit_isset(bi) != sizes[k].alloc.bit_isset(buddy) {
                // one of the pair is free
                unsafe {
                    if sizes[k].alloc.bit_isset(bi) {
                        sizes[k].free.push(self.addr(k, buddy)); // put buddy on free list
                    } else {
                        sizes[k].free.push(self.addr(k, bi)); // put bi on free list
                    }
                }
                Self::blk_size(k)
            } else {
                0
            }
        } else {
            0
        }
    }

    // Initialize the free lists for each size k. For each size k, there
    // are only two pairs that may have a buddy that should be on free lists:
    // bd_left and bd_right
    fn initfree(&mut self, bd_left: usize) -> usize {
        let bd_right = self.end;
        let mut free = 0;

        for k in 0..self.max_size() {
            // skip max size
            let left = self.blk_index_next(k, bd_left);
            let right = self.blk_index(k, bd_right);
            free += self.initfree_pair(k, left);
            if left < right {
                free += self.initfree_pair(k, right);
            }
        }
        free
    }

    // Mark the range [base, p) as allocated
    fn mark_data_structures(&mut self, p: usize) -> usize {
        let meta = p - self.base;
        println!(
            "bd: {} meta bytes for managing {} bytes of memory",
            meta,
            Self::blk_size(self.max_size())
        );
        self.mark(self.base, p);
        meta
    }

    // Mark the range [end, self.heap_size()) as allocated
    fn mark_unavailable(&mut self) -> usize {
        let mut unavailable = Self::blk_size(self.max_size()) - (self.end - self.base);
        if unavailable > 0 {
            unavailable = round_up(unavailable, Self::LEAF_SIZE);
        }
        println!("bd: {} bytes unavailable", unavailable);

        self.mark(self.end, self.base + Self::blk_size(self.max_size()));
        unavailable
    }

    // Initialize the buddy allocator: it manages memory from [base, end)
    pub unsafe fn init(&mut self, base: usize, end: usize) -> Result<(), &'static str> {
        if self.initialized {
            return Err("allocator init called twice");
        }

        let mut p = round_up(base, cmp::max(Self::LEAF_SIZE, Self::MAX_ALIGN));
        self.base = p;
        self.end = round_down(end, cmp::max(Self::LEAF_SIZE, Self::MAX_ALIGN));

        // compute the number of sizes we need to manage [base, end)
        self.nsize = log2((self.end - p) / Self::LEAF_SIZE) + 1;
        if self.end - p > Self::blk_size(self.max_size()) {
            self.nsize += 1; // round up to the next power of 2
        }

        println!(
            "bd: memory sz is {} bytes; allocate an size array of length {}",
            self.end - p,
            self.nsize
        );

        // allocate self.sizes array
        self.sizes.replace(init_nonnull_slice(&mut p, self.nsize));

        // initialize free list and allocate the alloc array for each size k
        for (k, szinfo) in self.sizes.unwrap().as_mut().iter_mut().enumerate() {
            szinfo.free.init();
            let sz = round_up(self.nblk(k), 8) / 8;
            szinfo.alloc.replace(init_nonnull_slice(&mut p, sz));
        }

        // allocate the split array for each size k, except for k = 0, since
        // we will not split blocks of size k = 0, the smallest size.
        for (k, szinfo) in self.sizes.unwrap().as_mut().iter_mut().enumerate().skip(1) {
            let sz = round_up(self.nblk(k), 8) / 8;
            szinfo.split.replace(init_nonnull_slice(&mut p, sz));
        }

        // p address my not be aligned now
        p = round_up(p, Self::LEAF_SIZE);

        // done allocating; mark the memory range [base, p) as allocated, so
        // that buddy will not hand out the memory.
        let meta = self.mark_data_structures(p);

        // mark the unavailable memory range [end, self.heap_size()) as allocated,
        // so that buddy will not hand out that memory.
        let unavailable = self.mark_unavailable();
        self.end = self.base + Self::blk_size(self.max_size()) - unavailable;

        // initialize free lists for each size k
        let free = self.initfree(p);

        // check if the amount that is free is what we except
        if free != Self::blk_size(self.max_size()) - meta - unavailable {
            return Err("allocator bug: free != total - meta - unavailable");
        }

        self.initialized = true;
        Ok(())
    }
}

unsafe fn init_nonnull_slice<T>(p: &mut usize, len: usize) -> NonNull<[T]> {
    let nonnull_ptr = NonNull::new(*p as *mut T).unwrap();
    *p += core::mem::size_of::<T>() * len;
    ptr::write_bytes(nonnull_ptr.as_ptr(), 0, len);
    NonNull::slice_from_raw_parts(nonnull_ptr, len)
}

fn log2(mut n: usize) -> usize {
    let mut k = 0;
    while n > 1 {
        k += 1;
        n >>= 1;
    }
    k
}

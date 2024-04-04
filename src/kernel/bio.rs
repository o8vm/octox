// Buffer cache.
//
// The buffer cache is a linked list of buf structures holding
// cached copies of disk block contents. Caching disk blocks
// in memory reduces the number of disk blocks used by multiple processes.
//
// Interface:
// * To get a buffer for a particular disk block, call BCAHCE.read() and get BufGuard.
// * After changing buffer data, call BufGuard.write to write it to disk.
// * When done with the buffer, drop(BufGuard) with relse.
// * Only one process at a time can use a buffer,
//     so do not keep them longer than necessary.
#![allow(clippy::redundant_allocation)]
use crate::{
    array,
    fs::BSIZE,
    param::NBUF,
    sleeplock::{SleepLock, SleepLockGuard},
    spinlock::Mutex,
    virtio_disk::DISK,
};
use alloc::{
    rc::{Rc, Weak},
    sync::Arc,
};
use core::{
    cell::RefCell,
    ops::{Deref, DerefMut},
};

pub static BCACHE: BCache = BCache::new();

#[derive(Debug)]
pub struct BCache {
    buf: [SleepLock<Data>; NBUF],
    // Linked list of all buffers, sorted by how recently the
    // buffer was used.
    lru: Mutex<Lru>,
}

#[derive(Debug)]
pub struct Data {
    pub data: [u8; BSIZE],
    pub disk: bool, // does disk "own" buf?
    blockno: u32,   // sync with Meta
    dev: u32,       // sync with Meta
    valid: bool,    // has data been read from disk?
}

#[derive(Debug)]
pub struct Lru {
    head: Option<Rc<Buf>>,
    tail: Option<Weak<Buf>>,
    n: usize,
}
unsafe impl Send for Lru {}

#[derive(Debug)]
pub struct Buf {
    data: Arc<&'static SleepLock<Data>>,
    meta: RefCell<Meta>,
}

#[derive(Default, Debug)]
struct Meta {
    dev: u32,
    blockno: u32,
    next: Option<Rc<Buf>>,
    prev: Option<Weak<Buf>>,
}

impl Lru {
    const fn new() -> Self {
        Self {
            head: None,
            tail: None,
            n: 0,
        }
    }

    fn add(&mut self, data: &'static SleepLock<Data>) {
        let data = Arc::new(data);
        let buf = Rc::new(Buf::new(data));
        match self.tail.take() {
            Some(old_tail) => {
                old_tail.upgrade().unwrap().meta.borrow_mut().next = Some(Rc::clone(&buf));
                buf.meta.borrow_mut().prev = Some(old_tail);
            }
            None => {
                self.head = Some(Rc::clone(&buf));
            }
        }
        self.tail = Some(Rc::downgrade(&buf));
        self.n += 1;
    }

    fn _get(&self, dev: u32, blockno: u32) -> (bool, Rc<Buf>) {
        // Is the block already cached?
        for (i, b) in self.iter().enumerate() {
            assert!(i < 30, "iter could be an infinite loop.");
            if b.meta.borrow().dev == dev && b.meta.borrow().blockno == blockno {
                return (false, b);
            }
        }

        // Not cached
        // Recycle the least recently used LRU unused buffer
        for (i, b) in self.iter().rev().enumerate() {
            assert!(i < 30, "iter could be an infinite loop.");
            if Arc::strong_count(&b.data) == 1 {
                b.meta.borrow_mut().dev = dev;
                b.meta.borrow_mut().blockno = blockno;
                return (true, b);
            }
        }
        panic!("no buffers");
    }

    fn relse(&mut self, buf: Rc<Buf>) {
        if Arc::strong_count(&buf.data) == 1 {
            // if b is head, Do nothing.
            if buf.meta.borrow().prev.is_none() {
                return;
            }

            // detach b
            let detached_next = buf.meta.borrow_mut().next.take();
            let detached_prev = buf.meta.borrow_mut().prev.take();
            if let Some(ref n) = detached_next {
                n.meta.borrow_mut().prev = detached_prev.clone();
            }
            if let Some(ref p) = detached_prev {
                p.upgrade().unwrap().meta.borrow_mut().next = detached_next.clone();
            }

            // attach b to the head.
            match self.head.take() {
                Some(old_head) => {
                    old_head.meta.borrow_mut().prev = Some(Rc::downgrade(&buf));
                    buf.meta.borrow_mut().next = Some(old_head);
                }
                None => {
                    self.tail = Some(Rc::downgrade(&buf));
                }
            }
            self.head = Some(buf);

            // update tail if b was tail
            if detached_next.is_none() {
                self.tail = detached_prev;
            }
        }
    }

    fn iter(&self) -> Iter {
        Iter {
            head: self.head.clone(),
            tail: self.tail.as_ref().and_then(|tail| tail.upgrade()),
        }
    }
}

struct Iter {
    head: Option<Rc<Buf>>,
    tail: Option<Rc<Buf>>,
}

impl Iterator for Iter {
    type Item = Rc<Buf>;
    fn next(&mut self) -> Option<Self::Item> {
        match self.head.take() {
            Some(old_head) => {
                self.head = old_head.meta.borrow().next.clone();
                Some(old_head)
            }
            None => None,
        }
    }
}

impl DoubleEndedIterator for Iter {
    fn next_back(&mut self) -> Option<Self::Item> {
        match self.tail.take() {
            Some(old_tail) => {
                self.tail = old_tail
                    .meta
                    .borrow()
                    .prev
                    .as_ref()
                    .and_then(|p| p.upgrade());
                Some(old_tail)
            }
            None => None,
        }
    }
}

pub struct BufGuard {
    data_guard: Option<SleepLockGuard<'static, Data>>,
    _ref: Option<Arc<&'static SleepLock<Data>>>,
    _link: Option<Rc<Buf>>,
}

impl Deref for BufGuard {
    type Target = SleepLockGuard<'static, Data>;
    fn deref(&self) -> &Self::Target {
        self.data_guard.as_ref().unwrap()
    }
}

impl DerefMut for BufGuard {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.data_guard.as_mut().unwrap()
    }
}

impl BufGuard {
    // Write buf's content to disk. Must be locked.
    pub fn write(&mut self) {
        if !self.holding() {
            panic!("bwrite");
        }
        self.data_guard = DISK.rw(self.data_guard.take(), true);
    }

    pub fn pin(&self) {
        unsafe { Arc::increment_strong_count(Arc::as_ptr(self._ref.as_ref().unwrap())) }
    }
    pub fn unpin(&self) {
        unsafe { Arc::decrement_strong_count(Arc::as_ptr(self._ref.as_ref().unwrap())) }
    }

    pub fn align_to<U>(&self) -> &[U] {
        let (head, body, _) = unsafe { self.data_guard.as_ref().unwrap().data.align_to::<U>() };
        assert!(head.is_empty(), "Data was not aligned");
        body
    }
    pub fn align_to_mut<U>(&mut self) -> &mut [U] {
        let (head, body, _) = unsafe { self.data_guard.as_mut().unwrap().data.align_to_mut::<U>() };
        assert!(head.is_empty(), "Data was not aligned");
        body
    }
}

impl Drop for BufGuard {
    fn drop(&mut self) {
        if !self.holding() {
            panic!("drop - brelse");
        }
        {
            self.data_guard.take(); // unlock sleep
            self._ref.take(); // Decrement refcnt
        }
        BCACHE.lru.lock().relse(self._link.take().unwrap());
    }
}

impl Buf {
    fn new(data: Arc<&'static SleepLock<Data>>) -> Self {
        Self {
            data,
            meta: Default::default(),
        }
    }
}

impl Data {
    const fn new() -> Self {
        Self {
            data: [0; BSIZE],
            disk: false,
            blockno: 0,
            dev: 0,
            valid: false,
        }
    }

    pub fn blockno(&self) -> u32 {
        self.blockno
    }

    pub fn dev(&self) -> u32 {
        self.dev
    }
}

impl Deref for Data {
    type Target = [u8];
    fn deref(&self) -> &Self::Target {
        &self.data
    }
}

impl DerefMut for Data {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.data
    }
}

impl BCache {
    const fn new() -> Self {
        Self {
            buf: array![SleepLock::new(Data::new(), "buffer"); NBUF],
            lru: Mutex::new(Lru::new(), "bcache"),
        }
    }

    fn get(&self, dev: u32, blockno: u32) -> BufGuard {
        let (recycle, b) = self.lru.lock()._get(dev, blockno);
        let mut sleeplock = b.data.lock();
        if recycle {
            sleeplock.valid = false;
            sleeplock.blockno = blockno;
            sleeplock.dev = dev;
        }
        BufGuard {
            data_guard: Some(sleeplock),
            _ref: Some(Arc::clone(&b.data)),
            _link: Some(b), // Do Not touch outside this function
        }
    }

    // Return a locked buf with the contents of the indicated block.
    pub fn read(&self, dev: u32, blockno: u32) -> BufGuard {
        let mut b = self.get(dev, blockno);
        if !b.valid {
            b.data_guard = DISK.rw(b.data_guard.take(), false);
            b.valid = true;
        }
        b
    }
}

pub fn init() {
    let mut lru = BCACHE.lru.lock();
    for b in BCACHE.buf.iter() {
        lru.add(b);
    }
}

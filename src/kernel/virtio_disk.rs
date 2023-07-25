use crate::{
    array, bio::Data, fs::BSIZE, memlayout::VIRTIO0, proc, sleeplock::SleepLockGuard,
    spinlock::Mutex,
};
use core::{
    convert::TryInto,
    sync::atomic::{fence, Ordering},
};

//
// driver for qemu's virtio disk device.
// uses qemu's mmio interface to virtio.
//
// qemu ... -drive file=fs.img,if=none,format=raw,id=x0 -device virtio-blk-device,drive=x0,bus=virtio-mmio-bus.0

pub static DISK: Mutex<Disk> = Mutex::new(Disk::new(), "virtio_disk");

// Memory mapped IO registers.
#[repr(usize)]
enum VirtioMMIO {
    // 0x74726976
    MagicValue = 0x00,
    // version; should be 2
    Version = 0x004,
    // device type; 1 is net, 2 is disk
    DeviceId = 0x008,
    // 0x554d4552
    VenderId = 0x00c,
    DeviceFeatures = 0x010,
    DriverFeatures = 0x020,
    // select queue, write-only
    QueueSel = 0x030,
    // max size of current queue, read-only
    QueueNumMax = 0x034,
    // size of current queue, write-only
    QueueNum = 0x038,
    // ready bit
    QueueReady = 0x044,
    // write-only
    QueueNotify = 0x050,
    // read-only
    InterruptStatus = 0x060,
    // write-only
    InterruptAck = 0x064,
    // read/write
    Status = 0x070,
    // physical address for descpritor table, write-only
    QueueDescLow = 0x080,
    QueueDescHigh = 0x084,
    // physical address for available ring, write-only
    DriverDescLow = 0x090,
    DriverDescHigh = 0x094,
    // physical address for used ring, write-only
    DeviceDescLow = 0x0a0,
    DeviceDescHigh = 0x0a4,
}

impl VirtioMMIO {
    fn read(self) -> u32 {
        unsafe { core::ptr::read_volatile((VIRTIO0 + self as usize) as *const u32) }
    }
    unsafe fn write(self, data: u32) {
        core::ptr::write_volatile((VIRTIO0 + self as usize) as *mut u32, data);
    }
}

type VirtioStatus = u32;
// Status register bits, from qemu virtio_config.h
mod virtio_status {
    pub(crate) const ACKNOWLEDGE: u32 = 0b0001;
    pub(crate) const DRIVER: u32 = 0b0010;
    pub(crate) const DRIVER_OK: u32 = 0b0100;
    pub(crate) const FEATURES_OK: u32 = 0b1000;
}

// Device feature bits
mod virtio_features {
    // Disk is read-only
    pub(crate) const BLK_F_RO: u32 = 1 << 5;
    // Supports scsi command passthru
    pub(crate) const BLK_F_SCSI: u32 = 1 << 7;
    // Writeback mode available in config
    pub(crate) const BLK_F_CONFIG_WCE: u32 = 1 << 11;
    // support more than one vq
    pub(crate) const BLK_F_MQ: u32 = 1 << 12;
    pub(crate) const F_ANY_LAYOUT: u32 = 1 << 27;
    pub(crate) const RING_F_INDIRECT_DESC: u32 = 1 << 28;
    pub(crate) const RING_F_EVENT_IDX: u32 = 1 << 29;
}

// this many virtio descriptors.
// must be a power of 2.
const NUM: usize = 8;

#[repr(C)]
pub struct Disk {
    // a set (not a ring) of DMA descpritors, with which the
    // driver tells the device where to read and write individual
    // disk operations. there are NUM descpritors.
    // most commands consists of a "chain" (a linked list) of couple of
    // these descriptors.
    desc: [VirtqDesc; NUM],

    // a ring in which the driver writes descriptor numbers
    // that the driver would like the device to process. it only
    // includes the head descriptor of each chain. the ring has
    // NUM elements.
    avail: VirtqAvail,

    // a ring in which the device writes descriptor numbers that
    // the device has finished processing (just the head of each chain).
    // there are NUM used ring entries
    used: VirtqUsed,

    // our own book-keeping
    free: [bool; NUM], // is a descriptor free ?
    used_idx: u16,     // we've looked this far in used[2..NUM].

    // track info aboud in-flight operations,
    // for use when completion interrupt arrives.
    // indexed by first descriptor index of chain.
    info: [Info; NUM],

    // disk command handlers.
    // one-for-one with descriptors, for convenience.
    ops: [VirtioBlkReq; NUM],
}

// a single descriptor, from the spc
#[derive(Debug, Clone, Copy)]
#[repr(C, align(16))]
struct VirtqDesc {
    addr: u64,
    len: u32,
    flags: VirtqDescFlags,
    next: u16,
}

type VirtqDescFlags = u16;
mod virtq_desc_flags {
    pub(crate) const FREED: u16 = 0b00;
    // chained with another descriptor
    pub(crate) const NEXT: u16 = 0b01;
    // device writes (vs read)
    pub(crate) const WRITE: u16 = 0b10;
}

impl VirtqDesc {
    const fn new() -> Self {
        Self {
            addr: 0,
            len: 0,
            flags: virtq_desc_flags::FREED,
            next: 0,
        }
    }
}

// the (entire) avail ring, from the spc
#[derive(Debug, Clone, Copy)]
#[repr(C, align(2))]
struct VirtqAvail {
    flags: u16,       // always zero,
    idx: u16,         // driver will write ring[idx] next
    ring: [u16; NUM], // descriptor numbers of chain heads
    unused: u16,
}

impl VirtqAvail {
    const fn new() -> Self {
        Self {
            flags: 0,
            idx: 0,
            ring: [0; NUM],
            unused: 0,
        }
    }
}

// one entry in the "used" ring, with which the
// device tells the driver about completed requests.
#[derive(Debug, Clone, Copy)]
#[repr(C)]
struct VirtqUsedElem {
    id: u32, // index of start of completes descriptor chain
    len: u32,
}

impl VirtqUsedElem {
    const fn new() -> Self {
        Self { id: 0, len: 0 }
    }
}

#[derive(Debug, Clone, Copy)]
#[repr(C, align(4))]
struct VirtqUsed {
    flags: u16, // always zero
    idx: u16,   // device increments when it adds a ring[] entry
    ring: [VirtqUsedElem; NUM],
}

impl VirtqUsed {
    const fn new() -> Self {
        Self {
            flags: 0,
            idx: 0,
            ring: [VirtqUsedElem::new(); NUM],
        }
    }
}

// track info aboud in-flight operations,
// for use when completion interrupt arrives.
// indexed by first descriptor index of chain.
#[repr(C)]
struct Info {
    buf: Option<SleepLockGuard<'static, Data>>,
    status: u8,
}

impl Info {
    const fn new() -> Self {
        Self {
            buf: None,
            status: 0,
        }
    }
}

// these are specific to virtio block devices, e.g. disks,
// described in Section 5.2 of the spec.

pub const VIRTIO_BLK_T_IN: u32 = 0;
pub const VIRTIO_BLK_T_OUT: u32 = 1;

// the format of the first descriptor in a disk request.
// to be followed by two more descriptors containing
// the block, and a one-byte status.
#[derive(Debug, Clone, Copy)]
#[repr(C)]
struct VirtioBlkReq {
    type_: u32, // VIRTIO_BLK_T_IN or ..._OUT
    reserved: u32,
    sector: u64,
}

impl VirtioBlkReq {
    const fn new() -> Self {
        Self {
            type_: 0,
            reserved: 0,
            sector: 0,
        }
    }
}

impl Disk {
    const fn new() -> Self {
        Self {
            desc: [VirtqDesc::new(); NUM],
            avail: VirtqAvail::new(),
            used: VirtqUsed::new(),
            free: [false; NUM],
            used_idx: 0,
            info: array![Info::new(); NUM],
            ops: [VirtioBlkReq::new(); NUM],
        }
    }

    unsafe fn init(&mut self) {
        let mut status: VirtioStatus = 0;

        if VirtioMMIO::MagicValue.read() != 0x74726976
            || VirtioMMIO::Version.read() != 2
            || VirtioMMIO::DeviceId.read() != 2
            || VirtioMMIO::VenderId.read() != 0x554d4551
        {
            panic!("could not find virtio disk");
        }

        // reset device
        VirtioMMIO::Status.write(status);

        // set ACKNOWLEDGE status bit
        status |= virtio_status::ACKNOWLEDGE;
        VirtioMMIO::Status.write(status);

        // set DRIVER status bit
        status |= virtio_status::DRIVER;
        VirtioMMIO::Status.write(status);

        // negotiate features
        let mut features = VirtioMMIO::DeviceFeatures.read();
        features &= !(virtio_features::BLK_F_RO);
        features &= !(virtio_features::BLK_F_SCSI);
        features &= !(virtio_features::BLK_F_CONFIG_WCE);
        features &= !(virtio_features::BLK_F_MQ);
        features &= !(virtio_features::F_ANY_LAYOUT);
        features &= !(virtio_features::RING_F_EVENT_IDX);
        features &= !(virtio_features::RING_F_INDIRECT_DESC);
        VirtioMMIO::DriverFeatures.write(features);

        // tell device that feature negotiation is complete.
        status |= virtio_status::FEATURES_OK;
        VirtioMMIO::Status.write(status);

        // re-read status to ensure FEATURES_OK is set.
        status = VirtioMMIO::Status.read();
        assert!(
            status & virtio_status::FEATURES_OK != 0,
            "virtio disk FEATURES_OK unset"
        );

        // initialize queue 0.
        VirtioMMIO::QueueSel.write(0);

        // ensure queue 0 is not in use
        assert!(
            VirtioMMIO::QueueReady.read() == 0,
            "virtio disk shoud not be ready"
        );

        // check maximum queue size.
        let max = VirtioMMIO::QueueNumMax.read();
        assert!(max != 0, "virtio disk has no queue 0");
        assert!(max >= NUM as u32, "virtio disk max queue too short");

        // set queue size.
        VirtioMMIO::QueueNum.write(NUM as _);

        // write physical addresses.
        VirtioMMIO::QueueDescLow.write(&self.desc as *const _ as u64 as u32);
        VirtioMMIO::QueueDescHigh.write((&self.desc as *const _ as u64 >> 32) as u32);
        VirtioMMIO::DriverDescLow.write(&self.avail as *const _ as u64 as u32);
        VirtioMMIO::DriverDescHigh.write((&self.avail as *const _ as u64 >> 32) as u32);
        VirtioMMIO::DeviceDescLow.write(&self.used as *const _ as u64 as u32);
        VirtioMMIO::DeviceDescHigh.write((&self.used as *const _ as u64 >> 32) as u32);

        // queue is ready.
        VirtioMMIO::QueueReady.write(0x1);

        // all NUM descriptors start out unused.
        self.free.iter_mut().for_each(|f| *f = true);

        // tell device we're completely ready.
        status |= virtio_status::DRIVER_OK;
        VirtioMMIO::Status.write(status);

        // plic.rs and trap.rs arrange for interrupts from VIRTIO0_IRQ.
    }

    // find a free descriptor, mark it non-free, return its index.
    fn alloc_desc(&mut self) -> Option<usize> {
        let ret = self
            .free
            .iter_mut()
            .enumerate()
            .filter(|(_, v)| **v)
            .take(1)
            .map(|(i, v)| {
                *v = false;
                i
            })
            .next();
        ret
    }

    // mark a descriptor as free.
    fn free_desc(&mut self, i: usize) {
        assert!(i < NUM, "free_dec 1");
        assert!(!self.free[i], "free_desc 2");
        self.desc[i].addr = 0;
        self.desc[i].len = 0;
        self.desc[i].flags = 0;
        self.desc[i].next = 0;
        self.free[i] = true;
        proc::wakeup(&self.free[0] as *const _ as usize);
    }

    // free a chain of descriptors.
    fn free_chain(&mut self, mut i: usize) {
        loop {
            let desc = self.desc.get(i).unwrap();
            let flag = desc.flags;
            let nxt = desc.next;
            self.free_desc(i);
            if (flag & virtq_desc_flags::NEXT) != 0 {
                i = nxt as usize;
            } else {
                break;
            }
        }
    }

    // allocate three descriptors (they need not be contiguous).
    // disk transfers always use three descriptors.
    fn alloc3_desc(&mut self, idx: &mut [usize; 3]) -> Result<(), ()> {
        for (i, idxi) in idx.iter_mut().enumerate() {
            match self.alloc_desc() {
                Some(ix) => *idxi = ix,
                None => {
                    for j in 0..i {
                        self.free_desc(j)
                    }
                    return Err(());
                }
            }
        }
        Ok(())
    }
}

impl Mutex<Disk> {
    pub fn rw(
        &self,
        b: Option<SleepLockGuard<'static, Data>>,
        write: bool,
    ) -> Option<SleepLockGuard<'static, Data>> {
        let mut b = b.unwrap();
        let sector = b.blockno() as usize * (BSIZE / 512);

        let mut guard = self.lock();
        // let p = CPUS.my_proc().unwrap();

        // the spec's Section 5.2 says that legacy block operations use
        // three descriptors: one for type/reserved/sector, one for the
        // data, one for a 1-byte status result.

        // allocate the three descriptors.
        let mut idx: [usize; 3] = [0; 3];
        loop {
            if guard.alloc3_desc(&mut idx).is_ok() {
                break;
            }
            guard = proc::sleep(&guard.free[0] as *const _ as usize, guard);
        }

        // format the three descriptors.
        // qemu's virtio-blk.c reads them.

        let buf0 = guard.ops.get_mut(idx[0]).unwrap();
        buf0.type_ = if write {
            VIRTIO_BLK_T_OUT // write the disk
        } else {
            VIRTIO_BLK_T_IN // read the disk
        };
        buf0.reserved = 0;
        buf0.sector = sector as u64;

        guard.desc[idx[0]].addr = buf0 as *mut _ as u64;
        guard.desc[idx[0]].len = core::mem::size_of::<VirtioBlkReq>().try_into().unwrap();
        guard.desc[idx[0]].flags = virtq_desc_flags::NEXT;
        guard.desc[idx[0]].next = idx[1].try_into().unwrap();

        guard.desc[idx[1]].addr = &b.data as *const _ as u64;
        guard.desc[idx[1]].len = BSIZE.try_into().unwrap();
        guard.desc[idx[1]].flags = if write {
            0
        } else {
            virtq_desc_flags::WRITE // device writes b->data
        };
        guard.desc[idx[1]].flags |= virtq_desc_flags::NEXT;
        guard.desc[idx[1]].next = idx[2].try_into().unwrap();

        guard.info[idx[0]].status = 0xff; // device writes 0 on success
        guard.desc[idx[2]].addr = &mut guard.info[idx[0]].status as *mut _ as u64;
        guard.desc[idx[2]].len = 1;
        guard.desc[idx[2]].flags = virtq_desc_flags::WRITE; // device write the status
        guard.desc[idx[2]].next = 0;

        // record struct buf for intr()
        b.disk = true;
        guard.info[idx[0]].buf.replace(b);

        // tell the device the first index in our chain of decriptors.
        let i = guard.avail.idx as usize % NUM;
        guard.avail.ring[i] = idx[0].try_into().unwrap();

        fence(Ordering::SeqCst);

        // tell the device another avail ring entry is available.
        guard.avail.idx += 1; // not % NUM ...

        fence(Ordering::SeqCst);

        unsafe {
            VirtioMMIO::QueueNotify.write(0); // value is queue number
        }

        // wait for intr() to say request has finished.
        while let Some(ref b) = guard.info[idx[0]].buf {
            if b.disk {
                guard = proc::sleep(&b.data as *const _ as usize, guard);
            } else {
                break;
            }
        }

        guard.free_chain(idx[0]);
        guard.info[idx[0]].buf.take()
    }

    pub fn intr(&self) {
        let mut guard = self.lock();
        // the device won't raise another interrupt until we tell it
        // we've seen this interrupt, which the following line does.
        // this may race with the device writing new entries to
        // the "used" ring, in which case we may process the new
        // completion entries in this interrupt, and have nothing to do
        // in the next interrup, whish is harmless.
        let intr_stat = VirtioMMIO::InterruptStatus.read();
        unsafe {
            VirtioMMIO::InterruptAck.write(intr_stat & 0x3);
        }

        fence(Ordering::SeqCst);

        // the device increments disk.used.idx when it
        // adds an entry to the used ring.
        while guard.used_idx != guard.used.idx {
            fence(Ordering::SeqCst);
            let id = guard.used.ring[guard.used_idx as usize % NUM].id as usize;

            if guard.info[id].status != 0 {
                panic!("disk intr status");
            }

            let b = guard.info[id].buf.as_mut().unwrap();
            b.disk = false; // disk is done with buf
            proc::wakeup(&b.data as *const _ as usize);
            guard.used_idx += 1;
        }
    }
}

pub fn init() {
    unsafe {
        DISK.get_mut().init();
    }
}

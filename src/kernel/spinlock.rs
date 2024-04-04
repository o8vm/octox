use crate::riscv::intr_get;

use super::proc::{Cpu, Cpus, IntrLock, CPUS};
use core::cell::UnsafeCell;
use core::ops::{Deref, DerefMut, Drop};
use core::{
    ptr,
    sync::atomic::{AtomicPtr, Ordering},
};

#[derive(Debug)]
pub struct Mutex<T> {
    name: &'static str,     // Name of lock
    locked: AtomicPtr<Cpu>, // Is the lock held?
    data: UnsafeCell<T>,    // actual data
}

#[derive(Debug)]
pub struct MutexGuard<'a, T: 'a> {
    mutex: &'a Mutex<T>,
    _intr_lock: IntrLock,
}

impl<T> Mutex<T> {
    pub const fn new(value: T, name: &'static str) -> Mutex<T> {
        Mutex {
            locked: AtomicPtr::new(ptr::null_mut()),
            data: UnsafeCell::new(value),
            name,
        }
    }

    pub fn lock(&self) -> MutexGuard<'_, T> {
        let _intr_lock = Cpus::lock_mycpu(self.name); // disable interrupts to avoid deadlock.

        unsafe {
            assert!(!self.holding(), "acquire {}", self.name);

            loop {
                if self
                    .locked
                    .compare_exchange(
                        ptr::null_mut(),
                        CPUS.mycpu(),
                        Ordering::Acquire,
                        Ordering::Relaxed,
                    )
                    .is_ok()
                {
                    break MutexGuard {
                        mutex: self,
                        _intr_lock,
                    };
                }
                core::hint::spin_loop()
            }
        }
    }

    // Check whether this cpu is holding the lock.
    // Interrupts must be off.
    unsafe fn holding(&self) -> bool {
        self.locked.load(Ordering::Relaxed) == CPUS.mycpu()
    }

    pub fn unlock(guard: MutexGuard<'_, T>) -> &'_ Mutex<T> {
        guard.mutex()
    }

    #[allow(clippy::mut_from_ref)]
    pub unsafe fn get_mut(&self) -> &mut T {
        &mut *self.data.get()
    }

    // It is only safe when used in functions such as fork_ret(),
    // where passing guards is difficult.
    pub unsafe fn force_unlock(&self) {
        assert!(self.holding(), "force unlock {}", self.name);
        self.locked.store(ptr::null_mut(), Ordering::Release);
        (&mut *CPUS.mycpu()).unlock()
    }
}

unsafe impl<T: Send> Sync for Mutex<T> {}

impl<'a, T: 'a> MutexGuard<'a, T> {
    // Returns a reference to the original 'Mutex' object.
    pub fn mutex(&self) -> &'a Mutex<T> {
        self.mutex
    }

    pub fn holding(&self) -> bool {
        assert!(!intr_get(), "interrupts enabled");
        unsafe { self.mutex.holding() }
    }
}

impl<'a, T: 'a> Drop for MutexGuard<'a, T> {
    fn drop(&mut self) {
        assert!(self.holding(), "release {}", self.mutex.name);
        self.mutex.locked.store(ptr::null_mut(), Ordering::Release);
    }
}

impl<'a, T: 'a> Deref for MutexGuard<'a, T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        unsafe { &*self.mutex.data.get() }
    }
}

impl<'a, T: 'a> DerefMut for MutexGuard<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut *self.mutex.data.get() }
    }
}

unsafe impl<T: Sync> Sync for MutexGuard<'_, T> {}

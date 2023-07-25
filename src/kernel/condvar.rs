use crate::{proc, spinlock::MutexGuard};

#[derive(Debug)]
pub struct Condvar;

impl Condvar {
    pub const fn new() -> Self {
        Self
    }
    pub fn wait<'a, T>(&self, guard: MutexGuard<'a, T>) -> MutexGuard<'a, T> {
        proc::sleep(self as *const _ as usize, guard)
    }
    pub fn notify_all(&self) {
        proc::wakeup(self as *const _ as usize);
    }
}

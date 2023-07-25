use crate::{
    condvar::Condvar,
    error::{Error::InvalidArgument, Result},
    spinlock::Mutex,
};

#[derive(Debug)]
pub struct Semaphore {
    mutex: Mutex<isize>,
    cond: Condvar,
    max: isize,
}

impl Semaphore {
    pub fn new(max: isize, name: &'static str) -> Self {
        Self {
            mutex: Mutex::new(0, name),
            cond: Condvar::new(),
            max,
        }
    }

    pub fn wait(&self) -> Result<()> {
        let mut cnt = self.mutex.lock();
        loop {
            if *cnt == -1 {
                return Err(InvalidArgument);
            }
            if *cnt >= self.max {
                cnt = self.cond.wait(cnt);
            } else {
                break;
            }
        }
        *cnt += 1;
        Ok(())
    }

    pub fn post(&self) {
        let mut cnt = self.mutex.lock();
        assert!(*cnt > 0);
        *cnt -= 1;
        if *cnt <= self.max {
            self.cond.notify_all();
        }
    }

    pub fn close(&self) {
        let mut cnt = self.mutex.lock();
        *cnt = -1;
        self.cond.notify_all();
    }
}

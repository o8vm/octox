use core::cell::{Cell, UnsafeCell};
use core::mem::MaybeUninit;
use core::ops::Deref;
use core::sync::atomic::{AtomicUsize, Ordering};

const IMCOMPLETE: usize = 0x0;
const POISONED: usize = 0x1;
const RUNNING: usize = 0x2;
const COMPLETE: usize = 0x3;

pub struct OnceLock<T> {
    state: AtomicUsize,
    inner: UnsafeCell<MaybeUninit<T>>,
}

unsafe impl<T: Sync + Send> Sync for OnceLock<T> {}
unsafe impl<T: Send> Send for OnceLock<T> {}

struct OnceLockGuard<'a, T> {
    oncecell: &'a OnceLock<T>,
    poison: bool,
}

impl<T> OnceLock<T> {
    pub const fn new() -> Self {
        Self {
            state: AtomicUsize::new(IMCOMPLETE),
            inner: UnsafeCell::new(MaybeUninit::uninit()),
        }
    }
    fn try_get(&self) -> Result<&T, usize> {
        match self.state.load(Ordering::Acquire) {
            POISONED => panic!("poisoned"),
            COMPLETE => Ok(unsafe { self.get_unchecked() }),
            IMCOMPLETE => Err(IMCOMPLETE),
            RUNNING => Err(RUNNING),
            _ => unreachable!(),
        }
    }

    pub fn get(&self) -> Option<&T> {
        if self.is_initialized() {
            Some(unsafe { self.get_unchecked() })
        } else {
            None
        }
    }

    pub fn get_mut(&mut self) -> Option<&mut T> {
        if self.is_initialized() {
            Some(unsafe { self.get_unchecked_mut() })
        } else {
            None
        }
    }

    #[allow(clippy::result_unit_err)]
    pub fn get_or_try_init(&self, func: impl FnOnce() -> T) -> Result<&T, ()> {
        match self.try_get() {
            Ok(res) => Ok(res),
            Err(RUNNING) => Err(()),
            Err(IMCOMPLETE) => {
                let mut func = Some(func);
                let res = self.try_init_inner(&mut || func.take().unwrap()())?;
                Ok(res)
            }
            Err(_) => unreachable!(),
        }
    }
    pub fn get_or_init(&self, func: impl FnOnce() -> T) -> &T {
        match self.get_or_try_init(func) {
            Ok(res) => res,
            Err(_) => loop {
                if self.state.load(Ordering::Acquire) == COMPLETE {
                    break unsafe { self.get_unchecked() };
                }
                core::hint::spin_loop()
            },
        }
    }
    pub fn set(&self, value: T) -> Result<(), T> {
        let mut value = Some(value);
        self.get_or_init(|| value.take().unwrap());
        match value {
            None => Ok(()),
            Some(value) => Err(value),
        }
    }

    fn try_block(&self, order: Ordering) -> Result<OnceLockGuard<'_, T>, ()> {
        match self
            .state
            .compare_exchange(IMCOMPLETE, RUNNING, order, Ordering::Acquire)
        {
            Ok(prev) if prev == IMCOMPLETE => Ok(OnceLockGuard {
                oncecell: self,
                poison: true,
            }),
            _ => Err(()),
        }
    }

    fn try_init_inner(&self, func: &mut dyn FnMut() -> T) -> Result<&T, ()> {
        unsafe {
            let mut guard = self.try_block(Ordering::Acquire)?;
            let inner = &mut *self.inner.get();
            inner.as_mut_ptr().write(func());
            guard.poison = false;
        }
        Ok(unsafe { self.get_unchecked() })
    }

    unsafe fn get_unchecked(&self) -> &T {
        (*self.inner.get()).assume_init_ref()
    }

    unsafe fn get_unchecked_mut(&mut self) -> &mut T {
        (*self.inner.get()).assume_init_mut()
    }

    fn unblock(&self, state: usize, order: Ordering) {
        self.state.swap(state, order);
    }

    pub fn into_inner(mut self) -> Option<T> {
        self.take()
    }

    fn is_initialized(&self) -> bool {
        self.state.load(Ordering::Acquire) == COMPLETE
    }

    pub fn take(&mut self) -> Option<T> {
        if self.is_initialized() {
            self.state = AtomicUsize::new(IMCOMPLETE);
            unsafe { Some((*self.inner.get()).assume_init_read()) }
        } else {
            None
        }
    }
}

impl<T> Drop for OnceLock<T> {
    fn drop(&mut self) {
        if self.is_initialized() {
            unsafe { (*self.inner.get()).assume_init_drop() }
        }
    }
}

impl<'a, T: 'a> Drop for OnceLockGuard<'a, T> {
    fn drop(&mut self) {
        let state = if self.poison { POISONED } else { COMPLETE };
        self.oncecell.unblock(state, Ordering::AcqRel);
    }
}

pub struct LazyLock<T, F = fn() -> T> {
    cell: OnceLock<T>,
    init: Cell<Option<F>>,
}

unsafe impl<T, F: Send> Sync for LazyLock<T, F> where OnceLock<T>: Sync {}
// auto-derived Send impl is OK.

impl<T, F> LazyLock<T, F> {
    pub const fn new(init: F) -> Self {
        Self {
            cell: OnceLock::new(),
            init: Cell::new(Some(init)),
        }
    }
}

impl<T, F: FnOnce() -> T> LazyLock<T, F> {
    pub fn force(this: &LazyLock<T, F>) -> &T {
        this.cell.get_or_init(|| match this.init.take() {
            Some(f) => f(),
            None => panic!("Lazy instance has previously been poisoned"),
        })
    }
}

impl<T, F: FnOnce() -> T> Deref for LazyLock<T, F> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        LazyLock::force(self)
    }
}

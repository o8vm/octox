use crate::{path::Path, sys};

pub static mut ARGS: Option<&[&str]> = None;

pub fn args() -> Args {
    Args {
        iter: if let Some(args) = unsafe { ARGS } {
            args.iter()
        } else {
            [].iter()
        },
    }
}

pub struct Args {
    iter: core::slice::Iter<'static, &'static str>,
}

impl Iterator for Args {
    type Item = &'static str;
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().copied()
    }
}

impl ExactSizeIterator for Args {
    fn len(&self) -> usize {
        self.iter.len()
    }
}

pub fn set_current_dir<P: AsRef<Path>>(path: P) -> sys::Result<()> {
    sys::chdir(path.as_ref().as_ref())
}

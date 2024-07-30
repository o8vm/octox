use crate::{path::Path, sys};
use alloc::{
    boxed::Box,
    string::ToString,
    vec::{self, Vec},
};

pub static mut ARGS: Option<&[Option<&str>]> = None;
pub static mut ENVIRON: Option<&mut [Option<&str>]> = None;

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
    iter: core::slice::Iter<'static, Option<&'static str>>,
}

impl Iterator for Args {
    type Item = &'static str;
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().copied().flatten()
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

pub struct Vars {
    iter: vec::IntoIter<(&'static str, &'static str)>,
}

pub fn vars() -> Vars {
    unsafe {
        let mut result = Vec::new();
        if let Some(ref environ) = ENVIRON {
            for key_value in environ.iter().filter_map(|&e| e) {
                if let Some(key_value) = key_value.split_once('=') {
                    result.push(key_value);
                }
            }
        }
        Vars {
            iter: result.into_iter(),
        }
    }
}

impl Iterator for Vars {
    type Item = (&'static str, &'static str);
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}
pub enum VarError {
    NotPresent,
}

pub fn var(key: &str) -> Result<&'static str, VarError> {
    vars()
        .find_map(|(k, v)| if k == key { Some(v) } else { None })
        .ok_or(VarError::NotPresent)
}

pub fn set_var(key: &str, value: &str) -> sys::Result<()> {
    let mut new_key_value = key.to_string();
    new_key_value.push('=');
    new_key_value.push_str(value);
    let new_key_value: &'static str = Box::leak(Box::new(new_key_value));

    unsafe {
        if let Some(ref mut environ) = ENVIRON {
            for key_val in environ.iter_mut() {
                match key_val {
                    Some(existing_key_val) if existing_key_val.starts_with(key) => {
                        key_val.replace(new_key_value);
                        return Ok(());
                    }
                    Some(_) => {},
                    None => {
                        key_val.replace(new_key_value);
                        return Ok(());
                    }
                }
            }
        }
    }
    Err(sys::Error::ArgumentListTooLong)
}

pub fn remove_var(key: &str) -> sys::Result<()> {
    unsafe {
        if let Some(ref mut environ) = ENVIRON {
            for key_val in environ.iter_mut() {
                match key_val {
                    Some(existing_key_val) if existing_key_val.starts_with(key) => {
                        key_val.take();
                        return Ok(());
                    }
                    Some(_) | None => {},
                }
            }
        }
    }
    Err(sys::Error::InvalidArgument)
}

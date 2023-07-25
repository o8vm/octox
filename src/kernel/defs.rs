// Gets the bytes of the value.
//
// as_bytes() provides access to the bytes of the value as an immutable
// byte slice.
//
// # Safety:
// If the memory layout of T is fixed
pub unsafe fn as_bytes<T: ?Sized>(refs: &T) -> &[u8] {
    let len = core::mem::size_of_val(refs);
    core::slice::from_raw_parts(refs as *const T as *const u8, len)
}

// Gets the bytes of the value mutably.
//
// as_bytes_mut() provides access to the bytes of the value as a mutable
// byte slice.
//
// # Safety:
// If the memory layout of T is fixed
pub unsafe fn as_bytes_mut<T: ?Sized>(refs: &mut T) -> &mut [u8] {
    let len = core::mem::size_of_val(refs);
    core::slice::from_raw_parts_mut(refs as *mut T as *mut u8, len)
}

// Array Macro for const variables
pub use core::mem::{ManuallyDrop, MaybeUninit};

use crate::{fs::DirEnt, stat::Stat};

#[repr(C)]
pub union _transmuter<T, const N: usize> {
    pub arr_in: ManuallyDrop<[MaybeUninit<T>; N]>,
    pub arr_out: ManuallyDrop<[T; N]>,
}

#[macro_export]
macro_rules! array {
    [$e:expr; $count:expr] => {
        unsafe {
            use $crate::defs::{ManuallyDrop, MaybeUninit, _transmuter};

            let mut arr_in: [MaybeUninit<_>; $count] = MaybeUninit::uninit().assume_init();
            let mut idx = 0;
            while idx < $count {
                arr_in[idx] = MaybeUninit::new($e);
                idx += 1;
            }
            ManuallyDrop::into_inner(_transmuter { arr_in: ManuallyDrop::new(arr_in) }.arr_out)
        }
    };
}

pub unsafe trait AsBytes {
    fn as_bytes(&self) -> &[u8] {
        unsafe {
            let len = core::mem::size_of_val(self);
            let slf: *const Self = self;
            core::slice::from_raw_parts(slf.cast::<u8>(), len)
        }
    }
    fn as_bytes_mut(&mut self) -> &mut [u8] {
        unsafe {
            let len = core::mem::size_of_val(self);
            let slf: *mut Self = self;
            core::slice::from_raw_parts_mut(slf.cast::<u8>(), len)
        }
    }
}
// u8, [u8; N], [u8], stats
unsafe impl AsBytes for Stat {}
unsafe impl AsBytes for str {}
unsafe impl AsBytes for u8 {}
unsafe impl AsBytes for usize {}
unsafe impl AsBytes for i32 {}
unsafe impl<T: AsBytes> AsBytes for [T] {}
unsafe impl<T: AsBytes, const N: usize> AsBytes for [T; N] {}
// null pointer optimization
unsafe impl AsBytes for Option<&str> {}
unsafe impl AsBytes for Option<&[u8]> {}
unsafe impl AsBytes for DirEnt {}

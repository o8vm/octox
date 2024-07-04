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
use core::net::Ipv4Addr;

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

// # Safety
// - The memory layout of T must be fixed and all bytes of T must be valid.
// - It must be safe to interpret an instance of T as a slice of bytes.
// - A reference to T must be able to coexist with a byte slice reference to the same memory.
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

// # Safety
// - The memory layout of T must be fixed and all bytes of T must be valid.
// - It must be safe to interpret a properly aligned byte slice of the correct length as an instance of T.
// - A reference to T must be able to coexist with a byte slice reference to the same memory.
pub unsafe trait FromBytes: Sized {
    fn ref_from(bytes: &[u8]) -> Option<&Self> {
        if bytes.len() < core::mem::size_of::<Self>() {
            None
        } else {
            unsafe { Some(&*(bytes.as_ptr() as *const Self)) }
        }
    }
    fn mut_from(bytes: &mut [u8]) -> Option<&mut Self> {
        if bytes.len() < core::mem::size_of::<Self>() {
            None
        } else {
            unsafe { Some(&mut *(bytes.as_mut_ptr() as *mut Self)) }
        }
    }
    fn read_from(bytes: &[u8]) -> Option<Self> {
        if bytes.len() < core::mem::size_of::<Self>() {
            None
        } else {
            let mut value = core::mem::MaybeUninit::<Self>::uninit();
            unsafe {
                core::ptr::copy_nonoverlapping(
                    bytes.as_ptr(),
                    value.as_mut_ptr() as *mut u8,
                    core::mem::size_of::<Self>(),
                );
                Some(value.assume_init())
            }
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
unsafe impl AsBytes for DirEnt {}
unsafe impl AsBytes for Ipv4Addr {}
// null pointer optimization
unsafe impl AsBytes for Option<&str> {}
unsafe impl AsBytes for Option<&[u8]> {}

unsafe impl FromBytes for u8 {}
unsafe impl FromBytes for u16 {}
unsafe impl FromBytes for u32 {}
unsafe impl FromBytes for u64 {}
unsafe impl FromBytes for usize {}
unsafe impl<T: FromBytes, const N: usize> FromBytes for [T; N] {}
unsafe impl FromBytes for Ipv4Addr {}

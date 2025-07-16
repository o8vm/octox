#![no_std]
use derive_macros::Syscalls;

#[repr(transparent)]
struct Fd(usize);

fn main() {}

#[derive(Syscalls)]
enum TestSyscalls {
    #[syscall(id = 1, params(), ret(Result<usize>))]
    Fork,
    Invalid,
}
extern crate proc_macro;
use proc_macro::TokenStream;

mod syscall;
mod utils;

#[proc_macro_derive(Syscalls, attributes(syscall))]
pub fn derive_syscalls(input: TokenStream) -> TokenStream {
    syscall::derive_syscalls_impl(input)
}

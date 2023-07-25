#![no_std]
use ulib::{env, fs};

fn main() {
    let mut args = env::args().skip(1).peekable();

    if args.peek().is_none() {
        panic!("Usage: rm files...")
    }
    for arg in args {
        fs::remove_file(arg).unwrap()
    }
}

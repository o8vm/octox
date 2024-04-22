#![no_std]
use ulib::{env, fs};

fn main() {
    let mut args = env::args().skip(1).peekable();

    if args.peek().is_none() {
        panic!("Usage: touch files...")
    }
    for arg in args {
        
        fs::create_file(arg).unwrap();
    }
}

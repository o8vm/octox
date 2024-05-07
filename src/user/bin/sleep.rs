#![no_std]
use ulib::{env, sys};

fn main() {
    let mut args = env::args().skip(1).peekable();

    if args.peek().is_none() {
        panic!("Usage: sleep TIME...")
    }

    let n = args.next().unwrap();
    sys::sleep(n.parse().unwrap()).unwrap();
}

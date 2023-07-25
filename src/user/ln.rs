#![no_std]
use ulib::{env, fs};

fn main() {
    let mut args = env::args();

    if args.len() != 3 {
        panic!("Usage: ln old new");
    }
    let _ = args.next();
    fs::hard_link(args.next().unwrap(), args.next().unwrap()).unwrap()
}

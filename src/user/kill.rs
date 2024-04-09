#![no_std]
use ulib::{env, sys};

fn main() {
    let mut args = env::args().skip(1).peekable();

    if args.peek().is_none() {
        panic!("usage: kill pid...");
    }

    for arg in args {

        if arg.parse::<usize>().unwrap() != 0{
            sys::kill(arg.parse::<usize>().unwrap()).unwrap()
        }else{
            panic!("Operation not permitted: Kill root process")
        }
    }
}

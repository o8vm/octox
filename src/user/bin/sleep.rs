#![no_std]
use ulib::{env, sys};

fn main(){

    let mut args = env::args().skip(1).peekable();
    
    if args.peek().is_none() {
        panic!("Usage: sleep TIME...")
    }
    
    for arg in args {
        
        match arg.parse::<usize>() {
            Ok(n)  => sys::sleep(n).unwrap(),
            Err(n) => panic!("This entry is invalid!"),
        }
    }
}
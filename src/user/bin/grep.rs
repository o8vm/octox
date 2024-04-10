#![no_std]
extern crate alloc;

use alloc::string::String;
use ulib::{env, fs::File, io::Read, print, println, stdio::stdin, sys};

fn main() {
    let args = env::args();
    let len = args.len();
    let mut args = args.skip(1);
    let Some(pat) = args.next() else {
        panic!("usage: grep patern [file ...]")
    };

    if len < 3 {
        grep(pat, stdin()).unwrap();
        return;
    }

    for arg in args {
        let file = File::open(arg).unwrap();
        grep(pat, file).unwrap();
    }
}

fn grep(pat: &str, mut fd: impl Read) -> sys::Result<()> {
    let mut contents = String::new();
    fd.read_to_string(&mut contents)?;

    for line in contents.lines() {
        if line.contains(pat) {
            println!("{}", line);
        }
    }
    Ok(())
}

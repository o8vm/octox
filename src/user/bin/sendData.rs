#![no_std]

use ulib::{
    println,print,
    eprint, eprintln,
    env,
    fs::File,
    io::{Read, Write},
    stdio::{stdin, stdout},
    sys,
};
fn main(){
    let mut args = env::args().skip(2).peekable();
    let initial_sleep_time: &str = args.next().unwrap();
    sys::sleep(initial_sleep_time.parse().unwrap());
    let mut idx = 0;
    loop {
        if idx == 5 {
            break;
        }
        let mut buf = [65u8; 512];
        stdout().write(&buf);
        sys::sleep(10);
        idx += 1;
        };
    }

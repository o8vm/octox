#![no_std]

use ulib::{
    env,
    fs::File,
    io::{Read, Write},
    stdio::{stdin, stdout},
    sys,
};
fn main(){
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

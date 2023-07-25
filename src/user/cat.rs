#![no_std]

use ulib::{
    env,
    fs::File,
    io::{Read, Write},
    stdio::{stdin, stdout},
    sys,
};

fn main() {
    let args = env::args();

    if args.len() < 2 {
        cat(stdin()).unwrap();
        return;
    }

    for arg in args.skip(1) {
        let file = File::open(arg).unwrap();
        cat(file).unwrap();
    }
}

fn cat(mut reader: impl Read) -> sys::Result<()> {
    let mut buf = [0u8; 1024];

    loop {
        let n = match reader.read(&mut buf) {
            Ok(n) if n == 0 => return Ok(()),
            Ok(n) => n,
            Err(e) => return Err(e),
        };
        stdout().write(&buf[..n])?;
    }
}

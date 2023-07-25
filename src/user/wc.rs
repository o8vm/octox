#![no_std]
use ulib::{env, fs::File, io::Read, print, println, stdio::stdin, sys};

fn main() {
    let mut args = env::args().skip(1).peekable();

    if args.peek().is_none() {
        wc(stdin()).unwrap();
    }
    for arg in args {
        let file = File::open(arg).unwrap();
        wc(file).unwrap();
    }
}

fn wc(mut fd: impl Read) -> sys::Result<()> {
    let mut buf = [0u8; 512];
    let mut l = 0;
    let mut w = 0;
    let mut c = 0;
    let mut inword = false;
    loop {
        let n = fd.read(&mut buf)?;
        if n == 0 {
            break;
        }
        for b in &buf[..n] {
            c += 1;
            match b {
                b'\n' => {
                    l += 1;
                    inword = false
                }
                b' ' | b'\r' | b'\t' => inword = false,
                _ if !inword => {
                    w += 1;
                    inword = true
                }
                _ => {}
            }
        }
    }
    println!("l={}, w={}, c={}", l, w, c);
    Ok(())
}

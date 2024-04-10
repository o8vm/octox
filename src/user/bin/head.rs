#![no_std]
extern crate alloc;

use alloc::{string::String, vec};
use ulib::{
    env,
    fs::File,
    io::{BufReader, Read, Write},
    print,
    stdio::{stdin, stdout},
    sys,
};

fn main() {
    let mut args = env::args().skip(1).peekable();
    let mut config = (Some(10), None);

    while let Some(&arg) = args.peek() {
        match arg {
            "-n" => {
                let _ = args.next();
                config = (args.next().map(|s| s.parse().unwrap()), None);
            }
            "-c" => {
                let _ = args.next();
                config = (None, args.next().map(|s| s.parse().unwrap()));
            }
            s if s.contains('-') => panic!("invalid argument"),
            _ => break,
        }
    }

    if let Some(file) = args.next() {
        let buf = BufReader::new(File::open(file).unwrap());
        head(buf, config).unwrap();
    } else {
        let buf = BufReader::new(stdin());
        head(buf, config).unwrap();
    }
}

fn head<R: Read>(
    mut reader: BufReader<R>,
    config: (Option<usize>, Option<usize>),
) -> sys::Result<()> {
    match config {
        (Some(n), None) => {
            let mut buf = String::new();
            for _ in 0..n {
                reader.read_line(&mut buf)?;
            }
            print!("{}", buf);
            Ok(())
        }
        (None, Some(c)) => {
            let mut buf = vec![0u8; c];
            reader.read(&mut buf)?;
            stdout().write(&buf)?;
            Ok(())
        }
        _ => unreachable!(),
    }
}

#![no_std]
use ulib::{env, fs::File, io::Read, print, println, stdio::stdin, sys};

fn main() {
        let mut args = env::args().skip(1).peekable();
        let mut gNum: &str = args.next().unwrap();
        let initial_sleep_time: &str = args.next().unwrap();
        sys::sleep(initial_sleep_time.parse().unwrap());
        let mut gNumInt: i32 = gNum.parse().unwrap();
        wc(stdin(),gNumInt).unwrap();    
}

fn wc(mut fd: impl Read, mut gNum: i32) -> sys::Result<()> {
    let startTime = sys::uptime().unwrap();
    let mut buf = [0u8; 512];
    let mut c = 0;
    let mut inword = false;
    loop {
        let n = fd.read(&mut buf)?;
        if n == 0 {
            break;
        }
        for b in &buf[..n] {
            c += 1;
        }
    }
    //println!("c={}",c);
    let endTime = sys::uptime().unwrap();
    println!("Group {} : Time taken {}",gNum, endTime - startTime);
    Ok(())
}

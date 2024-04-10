#![no_std]
extern crate alloc;
use ulib::{
    fs::{File, OpenOptions},
    print, println,
    process::Command,
    stdio,
    sys::{self, Major},
};

fn main() -> sys::Result<()> {
    loop {
        match OpenOptions::new().read(true).write(true).open("console") {
            Err(_) => sys::mknod("console", Major::Console as usize, 0)?, // Major をそのまま指定できるように自動生成のところの定義を変更すべき
            Ok(stdin) => {
                stdio::stdout().set(stdin.try_clone()?)?;
                stdio::stderr().set(stdin.try_clone()?)?;
                stdio::stdin().set(stdin)?;
                break;
            }
        }
    }
    if File::open("null").is_err() {
        sys::mknod("null", Major::Null as usize, 0).unwrap();
    }

    loop {
        println!("init: starting sh");
        let mut child = Command::new("sh").spawn()?;
        child.wait().unwrap();
    }
}

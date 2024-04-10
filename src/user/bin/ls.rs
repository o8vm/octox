#![no_std]
use alloc::format;
use ulib::{
    env,
    fs::{self, File},
    path::Path,
    print, println, sys,
};
extern crate alloc;

fn main() {
    let args = env::args();
    if args.len() < 2 {
        ls(".").unwrap();
        return;
    }
    for arg in args.skip(1) {
        ls(arg).unwrap();
    }
}

fn ls(path: &str) -> sys::Result<()> {
    let path = Path::new(path);
    match fs::read_dir(path) {
        Err(_) => {
            let attr = File::open(path)?.metadata()?;
            println!(
                "{:14} {:6} {:3} {}",
                path.file_name().unwrap(),
                format!("{:?}", attr.file_type()),
                attr.inum(),
                attr.len()
            );
        }
        Ok(entries) => {
            for entry in entries {
                let entry = entry.unwrap();
                let attr = entry.metadata()?;
                println!(
                    "{:14} {:6} {:3} {}",
                    entry.file_name(),
                    format!("{:?}", attr.file_type()),
                    attr.inum(),
                    attr.len()
                );
            }
        }
    }
    Ok(())
}

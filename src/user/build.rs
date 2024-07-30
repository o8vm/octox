use kernel::syscall::*;
use std::{
    fs::{self, File},
    io::{self, Write},
    path::{Path, PathBuf},
};

fn main() {
    let root_out_dir = PathBuf::from(std::env::var("ROOT_OUT_DIR").unwrap());

    // copy etc/_* to root_out_dir/etc
    let src_dir = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap()).join("etc");
    let dst_dir = root_out_dir.join("etc");
    copy_files(&src_dir, &dst_dir, Some("_")).expect("failed to copy user etc");

    // copy lib/_* to root_out_dir/lib
    let src_dir = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap()).join("lib");
    let dst_dir = root_out_dir.join("lib");
    copy_files(&src_dir, &dst_dir, Some("_")).expect("failed to copy user etc");

    // build syscall interface file usys.rs
    let out_dir = PathBuf::from(std::env::var("OUT_DIR").unwrap());
    let mut usys_rs =
        File::create(out_dir.join("usys.rs")).expect("cloudn't create OUT_DIR/usys.rs");
    usys_rs
        .write_all("// Created by build.rs\n\n".as_bytes())
        .expect("OUT_DIR/usys.rs: write error");
    for syscall_id in SysCalls::into_enum_iter().skip(1) {
        usys_rs
            .write_all(syscall_id.gen_usys().as_bytes())
            .expect("usys write error");
    }

    // set linker script
    let local_path = Path::new(env!("CARGO_MANIFEST_DIR"));
    println!(
        "cargo:rustc-link-arg=-T{}",
        local_path.join("user.ld").display()
    );
}

fn copy_files(src_dir: &Path, dst_dir: &Path, prefix: Option<&str>) -> io::Result<()> {
    if !src_dir.exists() {
        // nothing to do
        return Ok(());
    }
    if !dst_dir.exists() {
        fs::create_dir_all(dst_dir)?;
    }
    for entry in fs::read_dir(src_dir)? {
        let entry = entry?;
        let entry_path = entry.path();
        let dst_path = dst_dir.join(entry.file_name());
        if entry_path.is_dir() {
            todo!()
        } else {
            let should_copy = match (prefix, entry_path.file_name().and_then(|s| s.to_str())) {
                (Some(prefix), Some(name)) if name.starts_with(prefix) => true,
                (None, Some(_)) => true,
                _ => false,
            };
            if should_copy {
                fs::copy(&entry_path, &dst_path)?;
            }
        }
    }
    Ok(())
}

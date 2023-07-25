use kernel::syscall::*;
use std::{
    fs::File,
    io::Write,
    path::{Path, PathBuf},
};

fn main() {
    let out_dir = PathBuf::from(std::env::var("OUT_DIR").unwrap());
    let mut usys_rs =
        File::create(out_dir.join("usys.rs")).expect("cloudn't create src/user/usys.rs");
    usys_rs
        .write_all("// Created by build.rs\n\n".as_bytes())
        .expect("src/user/usys.rs: write error");
    for syscall_id in SysCalls::into_enum_iter().skip(1) {
        usys_rs
            .write_all(syscall_id.gen_usys().as_bytes())
            .expect("usys write error");
    }

    let local_path = Path::new(env!("CARGO_MANIFEST_DIR"));
    println!(
        "cargo:rustc-link-arg=-T{}",
        local_path.join("user.ld").display()
    )
}

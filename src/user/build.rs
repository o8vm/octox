use std::{
    fs,
    io,
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

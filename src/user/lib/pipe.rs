use crate::{fs::File, sys};

pub fn pipe() -> sys::Result<(File, File)> {
    let mut fds = [0; 2];
    sys::pipe(&mut fds)?;
    let mut file0;
    let mut file1;
    unsafe {
        file0 = File::from_raw_fd(fds[0]);
        file1 = File::from_raw_fd(fds[1]);
    }
    file0.set_cloexec()?;
    file1.set_cloexec()?;
    Ok((file0, file1))
}

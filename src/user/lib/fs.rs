use alloc::string::{String, ToString};
use alloc::sync::Arc;

use crate::io::{Read, Write};
use crate::path::{Path, PathBuf};
use crate::sys::{
    self,
    defs::AsBytes,
    fcntl::{omode, FcntlCmd},
    fs::DirEnt,
    stat::FileType,
    stat::Stat,
    Error::*,
};
pub type Fd = usize;

#[derive(Debug, PartialEq, Eq)]
pub struct File(Fd);

impl File {
    pub fn open<P: AsRef<Path>>(path: P) -> sys::Result<File> {
        OpenOptions::new().read(true).open(path)
    }

    pub fn create<P: AsRef<Path>>(path: P) -> sys::Result<File> {
        OpenOptions::new()
            .write(true)
            .create(true)
            .truncate(true)
            .open(path)
    }

    pub fn options() -> OpenOptions {
        OpenOptions::new()
    }

    pub fn stat(&self) -> sys::Result<Stat> {
        let mut stat: Stat = Default::default();
        sys::fstat(self.0, &mut stat)?;
        Ok(stat)
    }

    pub fn try_clone(&self) -> sys::Result<File> {
        sys::dup(self.0).map(File)
    }

    pub fn dup2(src: &File, dst: &mut File) -> sys::Result<()> {
        sys::dup2(src.0, dst.0)?;
        Ok(())
    }

    pub unsafe fn from_raw_fd(raw_fd: Fd) -> Self {
        Self(raw_fd)
    }

    pub fn get_fd(&self) -> Fd {
        self.0
    }

    pub fn metadata(&self) -> sys::Result<Metadata> {
        let mut stat: Stat = Default::default();
        sys::fstat(self.0, &mut stat)?;
        Ok(Metadata(stat))
    }

    pub fn set_cloexec(&mut self) -> sys::Result<usize> {
        sys::fcntl(self.0, FcntlCmd::SetCloexec)
    }
}

impl Drop for File {
    fn drop(&mut self) {
        let _ = sys::close(self.0);
    }
}

impl Read for File {
    fn read(&mut self, buf: &mut [u8]) -> sys::Result<usize> {
        sys::read(self.0, buf)
    }
}

impl Write for File {
    fn write(&mut self, buf: &[u8]) -> sys::Result<usize> {
        sys::write(self.0, buf)
    }
}

#[derive(Clone, Debug)]
pub struct OpenOptions {
    read: bool,
    write: bool,
    truncate: bool,
    append: bool,
    create: bool,
}

impl Default for OpenOptions {
    fn default() -> Self {
        Self::new()
    }
}

impl OpenOptions {
    pub fn new() -> Self {
        Self {
            read: false,
            write: false,
            truncate: false,
            append: false,
            create: false,
        }
    }
    pub fn read(&mut self, read: bool) -> &mut Self {
        self.read = read;
        self
    }
    pub fn write(&mut self, write: bool) -> &mut Self {
        self.write = write;
        self
    }
    pub fn truncate(&mut self, truncate: bool) -> &mut Self {
        self.truncate = truncate;
        self
    }
    pub fn append(&mut self, append: bool) -> &mut Self {
        self.append = append;
        self
    }
    pub fn create(&mut self, create: bool) -> &mut Self {
        self.create = create;
        self
    }

    pub fn open<P: AsRef<Path>>(&self, path: P) -> sys::Result<File> {
        sys::open(
            path.as_ref().to_str(),
            self.get_access_mode()? | self.get_creation_mode()?,
        )
        .map(File)
    }

    fn get_access_mode(&self) -> sys::Result<usize> {
        match (self.read, self.write, self.append) {
            (true, false, false) => Ok(omode::RDONLY),
            (false, true, false) => Ok(omode::WRONLY),
            (true, true, false) => Ok(omode::RDWR),
            (false, _, true) => Ok(omode::WRONLY | omode::APPEND),
            (true, _, true) => Ok(omode::RDWR | omode::APPEND),
            (false, false, false) => Err(InvalidArgument),
        }
    }

    fn get_creation_mode(&self) -> sys::Result<usize> {
        match (self.write, self.append) {
            (true, false) => {}
            (false, false) => {
                if self.truncate || self.create {
                    return Err(InvalidArgument);
                };
            }
            (_, true) => {
                if self.truncate || !self.create {
                    return Err(InvalidArgument); // 要検討
                }
            }
        }

        Ok(match (self.create, self.truncate) {
            (false, false) => 0,
            (true, false) => omode::CREATE,
            (false, true) => omode::TRUNC,
            (true, true) => omode::CREATE | omode::TRUNC,
        })
    }
}

#[derive(Debug)]
pub struct Metadata(Stat);

pub fn metadata<P: AsRef<Path>>(path: P) -> sys::Result<Metadata> {
    File::open(path)?.metadata()
}

impl Metadata {
    pub fn file_type(&self) -> FileType {
        self.0.ftype
    }

    pub fn is_dir(&self) -> bool {
        self.file_type() == FileType::Dir
    }

    pub fn is_file(&self) -> bool {
        self.file_type() == FileType::File
    }

    #[allow(clippy::len_without_is_empty)]
    pub fn len(&self) -> usize {
        self.0.size
    }
    pub fn inum(&self) -> u32 {
        self.0.ino
    }
}

pub struct ReadDir {
    fd: File,
    root: Arc<PathBuf>,
    end_of_stream: bool,
}

pub struct DirEntry {
    dir: Arc<PathBuf>,
    name: String,
}

pub fn read_dir<P: AsRef<Path>>(path: P) -> sys::Result<ReadDir> {
    let root = Arc::new(path.as_ref().to_path_buf());
    let fd = File::open(path)?;
    if fd.metadata()?.is_dir() {
        Ok(ReadDir {
            fd,
            root,
            end_of_stream: false,
        })
    } else {
        Err(NotADirectory)
    }
}

impl Iterator for ReadDir {
    type Item = sys::Result<DirEntry>;
    fn next(&mut self) -> Option<Self::Item> {
        let mut de: DirEnt = Default::default();
        if self.end_of_stream {
            return None;
        }
        loop {
            if let Ok(0) = self.fd.read(de.as_bytes_mut()) {
                self.end_of_stream = true;
                break None;
            }

            if de.inum == 0 {
                continue;
            }
            let name = core::str::from_utf8(&de.name)
                .unwrap()
                .trim_end_matches(char::from(0))
                .to_string();
            if name == "." || name == ".." {
                continue;
            }
            break Some(Ok(DirEntry {
                dir: Arc::clone(&self.root),
                name,
            }));
        }
    }
}

impl DirEntry {
    pub fn path(&self) -> PathBuf {
        self.dir.join(self.name.as_str())
    }
    pub fn file_name(&self) -> String {
        self.name.clone()
    }
    pub fn metadata(&self) -> sys::Result<Metadata> {
        File::open(self.path())?.metadata()
    }
    pub fn file_type(&self) -> sys::Result<FileType> {
        self.metadata().map(|m| m.file_type())
    }
}

#[derive(Debug, Default)]
pub struct DirBuilder {
    recursive: bool,
}

impl DirBuilder {
    pub fn new() -> Self {
        DirBuilder { recursive: false }
    }

    pub fn recursive(&mut self, recursive: bool) -> &mut Self {
        self.recursive = recursive;
        self
    }

    pub fn create<P: AsRef<Path>>(&self, path: P) -> sys::Result<()> {
        self._create(path.as_ref())
    }

    fn _create(&self, path: &Path) -> sys::Result<()> {
        if self.recursive {
            self.create_dir_all(path)
        } else {
            sys::mkdir(path.to_str())
        }
    }

    #[allow(clippy::only_used_in_recursion)]
    fn create_dir_all(&self, path: &Path) -> sys::Result<()> {
        if path == Path::new("") {
            return Ok(());
        }

        match sys::mkdir(path.to_str()) {
            Ok(()) => return Ok(()),
            Err(NotFound) => {}
            Err(_) if path.is_dir() => return Ok(()),
            Err(e) => return Err(e),
        }
        match path.parent() {
            Some(p) => self.create_dir_all(p)?,
            None => return Err(Uncategorized),
        }
        match sys::mkdir(path.to_str()) {
            Ok(()) => Ok(()),
            Err(_) if path.is_dir() => Ok(()),
            Err(e) => Err(e),
        }
    }
}

pub fn create_dir_all<P: AsRef<Path>>(path: P) -> sys::Result<()> {
    DirBuilder::new().recursive(true).create(path)
}

pub fn create_dir<P: AsRef<Path>>(path: P) -> sys::Result<()> {
    DirBuilder::new().create(path)
}

pub fn hard_link<P: AsRef<Path>, Q: AsRef<Path>>(original: P, link: Q) -> sys::Result<()> {
    sys::link(original.as_ref().to_str(), link.as_ref().to_str())
}

pub fn remove_file<P: AsRef<Path>>(path: P) -> sys::Result<()> {
    sys::unlink(path.as_ref().to_str())
}

pub fn read_to_string<P: AsRef<Path>>(path: P) -> sys::Result<String> {
    let mut file = File::open(path)?;
    let mut string = String::new();
    file.read_to_string(&mut string)?;
    Ok(string)
}

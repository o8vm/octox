use crate::{
    error::{Error::*, Result},
    fcntl::OMode,
    file::{FType, File, FTABLE},
    mpmc::*,
    proc::{either_copyin, either_copyout},
    vm::VirtAddr,
};

#[derive(Debug)]
pub struct Pipe {
    rx: Option<Receiver<u8>>,
    tx: Option<SyncSender<u8>>,
}

impl Pipe {
    const PIPESIZE: isize = 512;

    pub fn new(rx: Option<Receiver<u8>>, tx: Option<SyncSender<u8>>) -> Self {
        Self { rx, tx }
    }

    pub fn get_mode(&self) -> OMode {
        let mut omode = OMode::new();
        omode.read(self.rx.is_some()).write(self.tx.is_some());
        omode
    }

    pub fn alloc() -> Result<(File, File)> {
        let (tx, rx) = sync_channel::<u8>(Self::PIPESIZE, "pipe");

        let p0 = Self::new(Some(rx), None);
        let p1 = Self::new(None, Some(tx));
        let f0 = FTABLE.alloc(p0.get_mode(), FType::Pipe(p0))?;
        let f1 = FTABLE.alloc(p1.get_mode(), FType::Pipe(p1))?;

        Ok((f0, f1))
    }

    pub fn write(&self, mut src: VirtAddr, n: usize) -> Result<usize> {
        let tx = self.tx.as_ref().ok_or(BrokenPipe)?;

        let mut i = 0;
        while i < n {
            let mut ch: u8 = 0;
            either_copyin(&mut ch, src)?;
            let Ok(_) = tx.send(ch) else {
                break;
            };
            src += 1;
            i += 1;
        }
        Ok(i)
    }

    pub fn read(&self, mut dst: VirtAddr, n: usize) -> Result<usize> {
        let rx = self.rx.as_ref().ok_or(BrokenPipe)?;

        let mut i = 0;
        while i < n {
            let Ok(ch) = rx.recv() else {
                break;
            };
            either_copyout(dst, &ch)?;
            dst += 1;
            i += 1;
        }
        Ok(i)
    }
}

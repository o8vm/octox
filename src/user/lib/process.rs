use core::fmt::Debug;

use alloc::{
    string::{String, ToString},
    vec,
    vec::Vec,
};

use crate::{
    fs::{File, OpenOptions},
    io::{Read, Write},
    path::Path,
    pipe, sys,
};

pub struct Command<'a> {
    program: &'a str,
    argv: Vec<&'a str>,
    cwd: Option<String>,
    stdin: Option<Stdio>,
    stdout: Option<Stdio>,
    stderr: Option<Stdio>,
}

pub enum ChildStdio {
    Inherit,
    Fd(File),
}

#[derive(Debug)]
pub enum Stdio {
    Inherit,
    Null,
    MakePipe,
    Fd(File),
}

impl Stdio {
    fn to_child_stdio(&self, readable: bool) -> sys::Result<(ChildStdio, Option<File>)> {
        match self {
            Stdio::Inherit => Ok((ChildStdio::Inherit, None)),
            Stdio::Fd(file) => Ok((ChildStdio::Fd(file.try_clone()?), None)),
            Stdio::MakePipe => {
                let (reader, writer) = pipe::pipe()?;
                let (ours, theirs) = if readable {
                    (writer, reader)
                } else {
                    (reader, writer)
                };
                Ok((ChildStdio::Fd(theirs), Some(ours)))
            }
            Stdio::Null => {
                let file = OpenOptions::new()
                    .read(readable)
                    .write(!readable)
                    .open("null")?;
                Ok((ChildStdio::Fd(file), None))
            }
        }
    }
}

// our pipe connected to child
pub struct StdioPipes {
    pub stdin: Option<File>,
    pub stdout: Option<File>,
    pub stderr: Option<File>,
}

// child stdio look like,
pub struct ChildPipes {
    pub stdin: ChildStdio,
    pub stdout: ChildStdio,
    pub stderr: ChildStdio,
}

impl<'a> Command<'a> {
    pub fn new(program: &'a str) -> Self {
        Self {
            program,
            argv: vec![program],
            cwd: None,
            stdin: None,
            stdout: None,
            stderr: None,
        }
    }

    pub fn arg(&mut self, arg: &'a str) -> &mut Self {
        self.argv.push(arg);
        self
    }

    pub fn args<I, S>(&mut self, args: I) -> &mut Self
    where
        I: IntoIterator<Item = &'a S>,
        S: AsRef<str> + 'a + ?Sized + Debug,
    {
        for arg in args {
            self.arg(arg.as_ref());
        }
        self
    }

    pub fn current_dir<P: AsRef<Path>>(&mut self, dir: P) -> &mut Self {
        self.cwd = Some(<Path as AsRef<str>>::as_ref(dir.as_ref()).to_string());
        self
    }

    pub fn stdin(&mut self, stdin: Stdio) -> &mut Self {
        self.stdin = Some(stdin);
        self
    }

    pub fn stdout(&mut self, stdout: Stdio) -> &mut Self {
        self.stdout = Some(stdout);
        self
    }

    pub fn stderr(&mut self, stderr: Stdio) -> &mut Self {
        self.stderr = Some(stderr);
        self
    }

    pub fn get_current_dir(&self) -> Option<&Path> {
        self.cwd.as_ref().map(|s| Path::new(s))
    }

    pub fn get_args(&self) -> &[&str] {
        &self.argv[1..]
    }

    pub fn get_program(&self) -> &str {
        self.program
    }

    fn setup_io(&self, default: Stdio, needs_stdin: bool) -> sys::Result<(StdioPipes, ChildPipes)> {
        let null = Stdio::Null;
        let default_stdin = if needs_stdin { &default } else { &null };
        let stdin = self.stdin.as_ref().unwrap_or(default_stdin);
        let stdout = self.stdout.as_ref().unwrap_or(&default);
        let stderr = self.stderr.as_ref().unwrap_or(&default);
        let (their_stdin, our_stdin) = stdin.to_child_stdio(true)?;
        let (their_stdout, our_stdout) = stdout.to_child_stdio(false)?;
        let (their_stderr, our_stderr) = stderr.to_child_stdio(false)?;
        let ours = StdioPipes {
            stdin: our_stdin,
            stdout: our_stdout,
            stderr: our_stderr,
        };
        let theirs = ChildPipes {
            stdin: their_stdin,
            stdout: their_stdout,
            stderr: their_stderr,
        };
        Ok((ours, theirs))
    }

    fn spawnp(&mut self, default: Stdio, needs_stdin: bool) -> sys::Result<Child> {
        let (ours, theirs) = self.setup_io(default, needs_stdin)?;
        let (mut input, mut output) = pipe::pipe()?;
        let pid = self.do_fork()?;
        if pid == 0 {
            drop(input);
            let Err(err) = self.do_exec(theirs) else {
                unreachable!()
            };
            let err = (err as isize).to_be_bytes();
            output.write(&err).unwrap();
            sys::exit(1);
        }

        drop(output);
        let mut p = Process::new(pid);
        let mut bytes = [0; 8];

        loop {
            match input.read(&mut bytes) {
                Ok(0) => {
                    return Ok(Child::from_inner((p, ours)));
                }
                Ok(8) => {
                    let err = sys::Error::from_isize(isize::from_be_bytes(bytes));
                    return Err(err);
                }
                Err(e) if e == sys::Error::Interrupted => {}
                Err(e) => {
                    assert!(p.wait().is_ok(), "wait() should either return Ok or panic");
                    panic!("THE CLOEXEC pipe failed {e:?}");
                }
                Ok(..) => {
                    assert!(p.wait().is_ok(), "wait() should either return Ok or panic");
                    panic!("short read on the CLOEXEC pipe");
                }
            }
        }
    }

    // If successful, returns Ok(0) in the child, and Ok(child_pid) in the parent.
    fn do_fork(&mut self) -> sys::Result<usize> {
        sys::fork()
    }

    fn do_exec(&mut self, stdio: ChildPipes) -> sys::Result<!> {
        if let ChildStdio::Fd(ref src) = stdio.stdin {
            crate::stdio::stdin().replace(src)?;
        }
        if let ChildStdio::Fd(ref src) = stdio.stdout {
            crate::stdio::stdout().replace(src)?;
        }
        if let ChildStdio::Fd(ref src) = stdio.stderr {
            crate::stdio::stderr().replace(src)?;
        }

        if let Some(cwd) = self.get_current_dir() {
            sys::chdir(cwd.to_str())?;
        }

        match sys::exec(self.program, &self.argv) {
            Ok(_) => Err(sys::Error::Uncategorized), // unreachable
            Err(err) => Err(err),
        }
    }

    pub fn spawn(&mut self) -> sys::Result<Child> {
        self.spawnp(Stdio::Inherit, true)
    }

    pub fn status(&mut self) -> sys::Result<ExitStatus> {
        self.spawnp(Stdio::Inherit, true)
            .and_then(|mut p| p.handle.wait())
    }

    pub fn output(&mut self) -> sys::Result<Output> {
        let mut child = self.spawnp(Stdio::MakePipe, false)?;
        drop(child.stdin.take());

        let (mut stdout, mut stderr) = (Vec::new(), Vec::new());
        match (child.stdout.take(), child.stderr.take()) {
            (None, None) => {}
            (Some(mut out), None) => {
                let res = out.0.read_to_end(&mut stdout);
                res.unwrap();
            }
            (None, Some(mut err)) => {
                let res = err.0.read_to_end(&mut stderr);
                res.unwrap();
            }
            (Some(mut _out), Some(mut _err)) => {
                // need to implement EAGAIN or EWULDBLOCK in pipe.
                // let res1 = out.0.read_to_end(&mut stdout);
                // let res2 = err.0.read_to_end(&mut stderr);
                unimplemented!();
            }
        }
        let status = child.handle.wait()?;
        Ok(Output {
            status,
            stdout,
            stderr,
        })
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub struct ExitStatus(pub i32);
pub struct Process {
    pid: usize,
    status: Option<ExitStatus>,
}

impl Process {
    fn new(pid: usize) -> Self {
        Self { pid, status: None }
    }
    pub fn kill(&mut self) -> sys::Result<()> {
        if self.status.is_some() {
            Err(sys::Error::InvalidArgument)
        } else {
            sys::kill(self.pid)
        }
    }
    pub fn wait(&mut self) -> sys::Result<ExitStatus> {
        if let Some(status) = self.status {
            return Ok(status);
        }
        let mut status: i32 = 0;
        loop {
            if self.pid == sys::wait(&mut status)? {
                self.status = Some(ExitStatus(status));
                break Ok(ExitStatus(status));
            }
        }
    }
}

pub struct Child {
    handle: Process,
    pub stdin: Option<ChildStdin>,
    pub stdout: Option<ChildStdout>,
    pub stderr: Option<ChildStderr>,
}

impl Child {
    pub fn from_inner((handle, io): (Process, StdioPipes)) -> Self {
        Self {
            handle,
            stdin: io.stdin.map(ChildStdin),
            stdout: io.stdout.map(ChildStdout),
            stderr: io.stderr.map(ChildStderr),
        }
    }
    pub fn wait(&mut self) -> sys::Result<ExitStatus> {
        drop(self.stdin.take());
        self.handle.wait()
    }
}

pub struct ChildStdin(File);

pub struct ChildStdout(File);

impl From<ChildStdout> for Stdio {
    fn from(value: ChildStdout) -> Self {
        Stdio::Fd(value.0)
    }
}

pub struct ChildStderr(File);

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Output {
    pub status: ExitStatus,
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
}

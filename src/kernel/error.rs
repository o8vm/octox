use core::fmt;

pub type Result<T> = core::result::Result<T, Error>;

#[repr(isize)]
#[derive(PartialEq, Debug)]
pub enum Error {
    Uncategorized,
    ResourceBusy = -2,
    NotFound = -3,
    OutOfMemory = -4,
    BadVirtAddr = -5,
    StorageFull = -6,
    TooManyLinks = -7,
    NoSuchProcess = -8,
    WouldBlock = -9,
    NoBufferSpace = -10,
    NoChildProcesses = -11,
    Interrupted = -12,
    BadFileDescriptor = -13,
    FileDescriptorTooLarge = -14,
    FileTooLarge = -15,
    AlreadyExists = -16,
    IsADirectory = -17,
    NotADirectory = -18,
    CrossesDevices = -19,
    PermissionDenied = -20,
    DirectoryNotEmpty = -21,
    FileTableOverflow = -22,
    InvalidArgument = -23,
    NoSuchNode = -24,
    BrokenPipe = -25,
    ExecFileFormatError = -26,
    ArgumentListTooLong = -27,
    Utf8Error = -28,
    WriteZero = -29,
    NotConnected = -30,
}

impl Error {
    pub fn as_str(&self) -> &'static str {
        use Error::*;
        match *self {
            ResourceBusy => "resource busy",
            NotFound => "entry not found",
            OutOfMemory => "out of memory",
            StorageFull => "no storage space",
            TooManyLinks => "too many links",
            BadVirtAddr => "bad virtual address",
            NoSuchProcess => "no such process",
            WouldBlock => "operation would block",
            NoBufferSpace => "no buffer space available",
            NoChildProcesses => "no child processes",
            Interrupted => "operation interrupted",
            BadFileDescriptor => "bad file descriptor",
            FileDescriptorTooLarge => "file descriptor value too large",
            FileTooLarge => "file too large",
            AlreadyExists => "entity already exists",
            IsADirectory => "is a directory",
            NotADirectory => "not a directory",
            CrossesDevices => "cross-device link or rename",
            PermissionDenied => "permission denied",
            DirectoryNotEmpty => "directory not empty",
            FileTableOverflow => "inode or file table overflow in system",
            InvalidArgument => "invalid argument",
            NoSuchNode => "no such node or address",
            BrokenPipe => "broken pipe",
            ExecFileFormatError => "executable file format error",
            ArgumentListTooLong => "argument list too long",
            Utf8Error => "slice is not utf8",
            WriteZero => "write zero",
            NotConnected => "not connected",
            Uncategorized => "uncategorized error",
        }
    }
    pub fn from_isize(code: isize) -> Self {
        use Error::*;
        match code {
            -2 => ResourceBusy,
            -3 => NotFound,
            -4 => OutOfMemory,
            -5 => BadVirtAddr,
            -6 => StorageFull,
            -7 => TooManyLinks,
            -8 => NoSuchProcess,
            -9 => WouldBlock,
            -10 => NoBufferSpace,
            -11 => NoChildProcesses,
            -12 => Interrupted,
            -13 => BadFileDescriptor,
            -14 => FileDescriptorTooLarge,
            -15 => FileTooLarge,
            -16 => AlreadyExists,
            -17 => IsADirectory,
            -18 => NotADirectory,
            -19 => CrossesDevices,
            -20 => PermissionDenied,
            -21 => DirectoryNotEmpty,
            -22 => FileTableOverflow,
            -23 => InvalidArgument,
            -24 => NoSuchNode,
            -25 => BrokenPipe,
            -26 => ExecFileFormatError,
            -27 => ArgumentListTooLong,
            -28 => Utf8Error,
            -29 => WriteZero,
            -30 => NotConnected,
            _ => Uncategorized,
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

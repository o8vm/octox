use alloc::string::{String, ToString};
use core::{fmt, todo};

use crate::{fs, sys};

#[repr(C)]
pub struct Path {
    inner: str,
}

impl Path {
    pub fn new(s: &str) -> &Path {
        unsafe { &*(s as *const str as *const Path) }
    }
    pub fn to_str(&self) -> &str {
        self.inner.as_ref()
    }

    fn from_inner_mut(inner: &mut str) -> &mut Path {
        unsafe { &mut *(inner as *mut str as *mut Path) }
    }

    pub fn components(&self) -> Components<'_> {
        Components {
            path: &self.inner,
            has_root: !self.inner.is_empty() && self.inner.starts_with('/'),
            front: State::StartDir,
            back: State::Body,
        }
    }

    pub fn has_root(&self) -> bool {
        self.components().has_root
    }
    pub fn is_absolute(&self) -> bool {
        self.has_root()
    }
    pub fn is_relative(&self) -> bool {
        !self.is_absolute()
    }

    pub fn parent(&self) -> Option<&Path> {
        let mut comps = self.components();
        let comp = comps.next_back();
        comp.and_then(|p| match p {
            Component::Normal(_) | Component::CurDir | Component::ParentDir => {
                Some(comps.as_path())
            }
            _ => None,
        })
    }

    pub fn ancestors(&self) -> Ancestors<'_> {
        Ancestors { next: Some(self) }
    }

    pub fn file_name(&self) -> Option<&str> {
        self.components().next_back().and_then(|p| match p {
            Component::Normal(p) => Some(p),
            _ => None,
        })
    }

    pub fn starts_with<P: AsRef<Path>>(&self, base: P) -> bool {
        iter_after(self.components(), base.as_ref().components()).is_some()
    }

    pub fn ends_with<P: AsRef<Path>>(&self, child: P) -> bool {
        iter_after(self.components().rev(), child.as_ref().components().rev()).is_some()
    }

    pub fn file_stem(&self) -> Option<&str> {
        self.file_name()
            .and_then(|s| s.rsplit_once('.'))
            .map(|(before, _)| before)
    }

    pub fn file_prefix(&self) -> Option<&str> {
        self.file_name()
            .and_then(|s| s.split_once('.'))
            .map(|(before, _)| before)
    }

    pub fn to_path_buf(&self) -> PathBuf {
        PathBuf::from(self.inner.to_string())
    }

    pub fn join<P: AsRef<Path>>(&self, path: P) -> PathBuf {
        let mut buf = self.to_path_buf();
        buf.push(path);
        buf
    }

    pub fn is_dir(&self) -> bool {
        fs::metadata(self).map(|m| m.is_dir()).unwrap_or(false)
    }

    pub fn try_exists(&self) -> sys::Result<bool> {
        todo!()
    }

    pub fn exists(&self) -> bool {
        fs::metadata(self).is_ok()
    }
}

impl fmt::Debug for Path {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.inner, f)
    }
}

impl AsRef<str> for Path {
    fn as_ref(&self) -> &str {
        &self.inner
    }
}

impl AsRef<Path> for str {
    fn as_ref(&self) -> &Path {
        Path::new(self)
    }
}

impl AsRef<Path> for Path {
    fn as_ref(&self) -> &Path {
        self
    }
}

impl PartialEq for Path {
    fn eq(&self, other: &Self) -> bool {
        self.components().path == other.components().path
    }
}

// the core iterators
#[derive(Copy, Clone, PartialEq, PartialOrd, Debug)]
enum State {
    StartDir = 0, // / or . or nothing
    Body = 1,     // foo/bar/baz
    Done = 2,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Component<'a> {
    RootDir,
    CurDir,
    ParentDir,
    Normal(&'a str),
}

impl<'a> Component<'a> {
    pub fn to_str(self) -> &'a str {
        match self {
            Self::RootDir => "/",
            Self::CurDir => ".",
            Self::ParentDir => "..",
            Self::Normal(path) => path,
        }
    }
}

#[derive(Clone)]
pub struct Components<'a> {
    path: &'a str,
    has_root: bool, // !path.is_empty() && path[0] == b'/'
    front: State,
    back: State,
}

pub struct Iter<'a> {
    inner: Components<'a>,
}

impl<'a> Iter<'a> {
    pub fn as_path(&self) -> &'a Path {
        self.inner.as_path()
    }
}

impl<'a> Iterator for Iter<'a> {
    type Item = &'a str;
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(Component::to_str)
    }
}

impl<'a> DoubleEndedIterator for Iter<'a> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back().map(Component::to_str)
    }
}

impl<'a> Components<'a> {
    fn len_before_body(&self) -> usize {
        let root = if self.front <= State::StartDir && self.has_root {
            1
        } else {
            0
        };
        let cur_dir = if self.front <= State::StartDir && self.include_cur_dir() {
            1
        } else {
            0
        };
        root + cur_dir
    }
    fn finished(&self) -> bool {
        self.front == State::Done || self.back == State::Done || self.front > self.back
    }

    pub fn as_path(&self) -> &'a Path {
        let mut comps = self.clone();
        if comps.front == State::Body {
            comps.trim_left();
        }
        if comps.back == State::Body {
            comps.trim_right();
        }
        Path::new(comps.path)
    }

    // should the normalized path include a leading . ?
    fn include_cur_dir(&self) -> bool {
        if self.has_root {
            return false;
        }
        let mut chars = self.path.chars();
        match (chars.next(), chars.next()) {
            (Some('.'), None) => true,
            (Some('.'), Some(b)) => b == '/',
            _ => false,
        }
    }
    fn parse_single_component(comp: &str) -> Option<Component<'_>> {
        match comp {
            "." => None, // .components are normalized, which is treated via include_cur_dir
            ".." => Some(Component::ParentDir),
            "" => None,
            _ => Some(Component::Normal(comp)),
        }
    }
    fn parse_next_component(&self) -> (&'a str, Option<Component<'a>>) {
        match self.path.split_once('/') {
            Some((comp, extra)) => (extra, Self::parse_single_component(comp)),
            None => ("", Self::parse_single_component(self.path)),
        }
    }
    fn parse_next_component_back(&self) -> (&'a str, Option<Component<'a>>) {
        match self.path.rsplit_once('/') {
            Some((extra, comp)) => (extra, Self::parse_single_component(comp)),
            None => ("", Self::parse_single_component(self.path)),
        }
    }
    // trim away repeated separators (i.e., empty components) on the left
    fn trim_left(&mut self) {
        while !self.path.is_empty() {
            let (extra, comp) = self.parse_next_component();
            if comp.is_some() {
                return;
            } else {
                self.path = extra;
            }
        }
    }
    // trim away repeated separators (i.e., empty components) on the right
    fn trim_right(&mut self) {
        while !self.path.is_empty() {
            let (extra, comp) = self.parse_next_component_back();
            if comp.is_some() {
                return;
            } else {
                self.path = extra;
            }
        }
    }
}

impl<'a> Iterator for Components<'a> {
    type Item = Component<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        while !self.finished() {
            match self.front {
                State::StartDir => {
                    self.front = State::Body;
                    if self.has_root {
                        self.path = self.path.get(1..).unwrap();
                        return Some(Component::RootDir);
                    } else if self.include_cur_dir() {
                        self.path = self.path.get(1..).unwrap();
                        return Some(Component::CurDir);
                    }
                }
                State::Body if !self.path.is_empty() => {
                    let (extra, comp) = self.parse_next_component();
                    self.path = extra;
                    if comp.is_some() {
                        return comp;
                    }
                }
                State::Body => {
                    self.front = State::Done;
                }
                State::Done => unreachable!(),
            }
        }
        None
    }
}

impl<'a> DoubleEndedIterator for Components<'a> {
    fn next_back(&mut self) -> Option<Self::Item> {
        while !self.finished() {
            match self.back {
                State::Body if self.path.len() > self.len_before_body() => {
                    let (extra, comp) = self.parse_next_component_back();
                    self.path = extra;
                    if comp.is_some() {
                        return comp;
                    }
                }
                State::Body => {
                    self.back = State::StartDir;
                }
                State::StartDir => {
                    self.back = State::Done;
                    if self.has_root {
                        return Some(Component::RootDir);
                    } else if self.include_cur_dir() {
                        return Some(Component::CurDir);
                    }
                }
                State::Done => unreachable!(),
            }
        }
        None
    }
}

#[derive(Debug, Copy, Clone)]
pub struct Ancestors<'a> {
    next: Option<&'a Path>,
}

impl<'a> Iterator for Ancestors<'a> {
    type Item = &'a Path;
    fn next(&mut self) -> Option<Self::Item> {
        let next = self.next;
        self.next = next.and_then(Path::parent);
        next
    }
}

// Iterate through `iter` while it matches `prefix`; return `None` if `prefix`
// is not a prefix of `iter`, otherwise return `Some(iter_after_prefix)` giving
// `iter` after having exhausted `prefix`
fn iter_after<'a, 'b, I, J>(mut iter: I, mut prefix: J) -> Option<I>
where
    I: Iterator<Item = Component<'a>> + Clone,
    J: Iterator<Item = Component<'b>>,
{
    loop {
        let mut iter_next = iter.clone();
        match (iter_next.next(), prefix.next()) {
            (Some(ref x), Some(ref y)) if x == y => (),
            (Some(_), Some(_)) => return None,
            (Some(_), None) => return Some(iter),
            (None, None) => return Some(iter),
            (None, Some(_)) => return None,
        }
        iter = iter_next;
    }
}

#[derive(Debug, Default)]
#[repr(transparent)]
pub struct PathBuf {
    inner: String,
}

impl PathBuf {
    pub fn new() -> Self {
        PathBuf {
            inner: String::new(),
        }
    }
    pub fn as_path(&self) -> &Path {
        self
    }
    pub fn push<P: AsRef<Path>>(&mut self, path: P) {
        let path = path.as_ref();
        let need_sep = self.inner.chars().last().map(|c| c != '/').unwrap_or(false);

        // absolute `path` replaces `self`
        if path.is_absolute() {
            self.inner.truncate(0);
        } else if need_sep {
            // `path` is a pure relative path
            self.inner.push('/');
        }
        self.inner.push_str(path.to_str());
    }
}

impl core::ops::Deref for PathBuf {
    type Target = Path;
    #[inline]
    fn deref(&self) -> &Path {
        Path::new(&self.inner)
    }
}

impl core::ops::DerefMut for PathBuf {
    #[inline]
    fn deref_mut(&mut self) -> &mut Path {
        Path::from_inner_mut(&mut self.inner)
    }
}

impl From<String> for PathBuf {
    fn from(value: String) -> Self {
        PathBuf { inner: value }
    }
}

impl AsRef<Path> for PathBuf {
    fn as_ref(&self) -> &Path {
        self
    }
}

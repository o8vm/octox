#![no_std]

use ulib::{io::Write, stdio::stdout};

fn main() {
    // clear the screen
    stdout().write(b"\x1b[2J\x1b[H").unwrap();
}

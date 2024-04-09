
#![no_std]

use ulib::{
    io::Write,
    stdio::{stdout}
};


fn main() {

    // clear the screen
    stdout().write_fmt(format_args!("\x1b[2J\x1b[H")).unwrap();
}
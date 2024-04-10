#![no_std]
use ulib::sys;

static INIT: &str = "/init";
static ARGV: [&str; 2] = ["init", "0"];

fn main() -> sys::Result<()> {
    sys::exec(INIT, &ARGV)?;
    //   loop {
    sys::exit(0)
    // }
}

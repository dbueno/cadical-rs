//! Shared helpers for the ported API tests (`tests/api_*.rs`,
//! `tests/contrib_*.rs`).
//!
//! The C++ tests print with `std::cout` (synchronized with C `stdio`) while
//! the library prints through the C `stdout` stream.  To get the same
//! interleaving of test and library output the Rust tests print through the
//! C `stdout` stream too ([`out!`], [`outln!`]).

#![allow(dead_code, unused_macros, unused_imports)]

pub mod craigtracer;

use std::path::PathBuf;

/// `printf`-like output on the C `stdout` stream (no flush).
macro_rules! out {
    ($($arg:tt)*) => {
        cadical::cprintf!($($arg)*)
    };
}

/// `std::cout << ... << std::endl` (prints a new-line and flushes).
macro_rules! outln {
    () => {{
        cadical::cprintf!("\n");
        $crate::common::flush();
    }};
    ($($arg:tt)*) => {{
        cadical::cprintf!($($arg)*);
        cadical::cprintf!("\n");
        $crate::common::flush();
    }};
}

pub(crate) use out;
pub(crate) use outln;

/// Flush the C `stdout` stream.
pub fn flush() {
    cadical::message::fflush(cadical::message::c_stdout());
}

/// Directory for files written by the tests.  This plays the role of
/// `$CADICALBUILD` in the C++ tests (and of `/tmp` for the tests which
/// write there): `CADICALBUILD` if set, otherwise
/// `/Volumes/Shampoo/cadical-rs/apitests/rust` if `/Volumes/Shampoo`
/// exists, otherwise `<tmp>/cadical-rs-apitests`.  The directory is
/// created if necessary.
pub fn build_dir() -> String {
    let dir = if let Ok(dir) = std::env::var("CADICALBUILD") {
        PathBuf::from(dir)
    } else if std::path::Path::new("/Volumes/Shampoo").is_dir() {
        PathBuf::from("/Volumes/Shampoo/cadical-rs/apitests/rust")
    } else {
        std::env::temp_dir().join("cadical-rs-apitests")
    };
    std::fs::create_dir_all(&dir).expect("can not create test output directory");
    dir.to_str().unwrap().to_string()
}

/// `getpid ()`.
pub fn pid() -> u32 {
    std::process::id()
}

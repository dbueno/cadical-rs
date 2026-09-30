//! Port of `terminal.hpp` and `terminal.cpp`: colored terminal output on
//! `stdout` (`tout`) and `stderr` (`terr`).
//!
//! The two global terminals are statics with atomic state (so they can be
//! used from anywhere, including signal handlers, without locking).  All
//! output goes through the C library `FILE` streams (see
//! [`crate::message::c_stdout`]) as in C++.

use std::sync::atomic::{AtomicBool, AtomicU8, Ordering::Relaxed};

use crate::message::{c_stderr, c_stdout, fflush, fputc, fputs};

pub struct Terminal {
    /// 1 = 'stdout', 2 = 'stderr'.
    fd: i32,
    /// 0 = not initialized, 1 = initialized.
    init: AtomicU8,
    /// Connected to terminal.
    connected: AtomicBool,
    /// Use colors.
    use_colors: AtomicBool,
    /// Reset on exit.
    reset_on_exit: AtomicBool,
}

impl Terminal {
    const fn new(fd: i32) -> Terminal {
        Terminal {
            fd,
            init: AtomicU8::new(0),
            connected: AtomicBool::new(false),
            use_colors: AtomicBool::new(false),
            reset_on_exit: AtomicBool::new(false),
        }
    }

    /// Lazy version of the C++ constructor `Terminal (FILE *)`.
    #[inline]
    fn ensure(&self) {
        if self.init.load(Relaxed) == 0 {
            // SAFETY: 'isatty' on a standard file descriptor.
            let tty = unsafe { libc::isatty(self.fd) } != 0;
            self.use_colors.store(tty, Relaxed);
            self.connected.store(tty, Relaxed);
            self.init.store(1, Relaxed);
        }
    }

    #[inline]
    fn file(&self) -> *mut libc::FILE {
        if self.fd == 1 {
            c_stdout()
        } else {
            c_stderr()
        }
    }

    #[inline]
    fn is_connected(&self) -> bool {
        self.ensure();
        self.connected.load(Relaxed)
    }

    fn escape(&self) {
        debug_assert!(self.is_connected());
        fputs("\x1b[", self.file());
    }

    fn color(&self, color: i32, bright: bool) {
        if !self.colors() {
            return;
        }
        debug_assert!(self.is_connected());
        self.escape();
        fputc(if bright { b'1' } else { b'0' } as i32, self.file());
        fputs(&format!(";{}m", color), self.file());
        fflush(self.file());
    }

    fn code(&self, str: &str) {
        if !self.is_connected() {
            return;
        }
        self.escape();
        fputs(str, self.file());
        fflush(self.file());
    }

    /// Assume disconnected in any case.
    pub fn disable(&self) {
        self.reset();
        self.connected.store(false, Relaxed);
        self.use_colors.store(false, Relaxed);
    }

    pub fn force_colors(&self) {
        self.ensure();
        self.use_colors.store(true, Relaxed);
        self.connected.store(true, Relaxed);
    }

    pub fn force_no_colors(&self) {
        self.ensure();
        self.use_colors.store(false, Relaxed);
    }

    pub fn force_reset_on_exit(&self) {
        self.ensure();
        self.reset_on_exit.store(true, Relaxed);
    }

    #[inline]
    pub fn colors(&self) -> bool {
        self.ensure();
        self.use_colors.load(Relaxed)
    }

    /// `operator bool ()`: connected to a terminal.
    #[inline]
    pub fn connected(&self) -> bool {
        self.is_connected()
    }

    pub fn red(&self, bright: bool) {
        self.color(31, bright)
    }
    pub fn green(&self, bright: bool) {
        self.color(32, bright)
    }
    pub fn yellow(&self, bright: bool) {
        self.color(33, bright)
    }
    pub fn blue(&self, bright: bool) {
        self.color(34, bright)
    }
    pub fn magenta(&self, bright: bool) {
        self.color(35, bright)
    }
    pub fn black(&self, bright: bool) {
        self.color(90, bright)
    }
    pub fn cyan(&self, bright: bool) {
        self.color(96, bright)
    }

    pub fn bold(&self) {
        self.code("1m")
    }
    pub fn normal(&self) {
        self.code("0m")
    }
    pub fn inverse(&self) {
        self.code("7m")
    }
    pub fn underline(&self) {
        self.code("4m")
    }

    #[inline]
    fn modify(&self, code: &'static str) -> &'static str {
        if self.colors() {
            code
        } else {
            ""
        }
    }

    pub fn bright_magenta_code(&self) -> &'static str {
        self.modify("\x1b[1;35m")
    }
    pub fn magenta_code(&self) -> &'static str {
        self.modify("\x1b[0;35m")
    }
    pub fn blue_code(&self) -> &'static str {
        self.modify("\x1b[0;34m")
    }
    pub fn bright_blue_code(&self) -> &'static str {
        self.modify("\x1b[1;34m")
    }
    pub fn yellow_code(&self) -> &'static str {
        self.modify("\x1b[0;33m")
    }
    pub fn bright_yellow_code(&self) -> &'static str {
        self.modify("\x1b[1;33m")
    }
    pub fn green_code(&self) -> &'static str {
        self.modify("\x1b[0;32m")
    }
    pub fn red_code(&self) -> &'static str {
        self.modify("\x1b[0;31m")
    }
    pub fn cyan_code(&self) -> &'static str {
        self.modify("\x1b[0;96m")
    }
    pub fn bright_red_code(&self) -> &'static str {
        self.modify("\x1b[1;31m")
    }
    pub fn normal_code(&self) -> &'static str {
        self.modify("\x1b[0m")
    }
    pub fn bold_code(&self) -> &'static str {
        self.modify("\x1b[1m")
    }

    pub fn cursor(&self, on: bool) {
        self.code(if on { "?25h" } else { "?25l" })
    }
    pub fn erase_until_end_of_line(&self) {
        self.code("K")
    }
    pub fn erase_line_if_connected_otherwise_new_line(&self) {
        if self.is_connected() {
            self.code("1G");
        } else {
            fputc(b'\n' as i32, self.file());
            fflush(self.file());
        }
    }

    pub fn reset(&self) {
        if !self.is_connected() {
            return;
        }
        self.erase_until_end_of_line();
        self.cursor(true);
        self.normal();
        fflush(self.file());
    }

    /// The C++ destructor resets the terminal if `force_reset_on_exit` was
    /// called.  Rust statics are not dropped, so the application calls
    /// this at exit.
    pub fn reset_if_forced_on_exit(&self) {
        if self.reset_on_exit.load(Relaxed) {
            self.reset();
        }
    }
}

/// Terminal of 'stdout' (file descriptor '1').
pub static TOUT: Terminal = Terminal::new(1);
/// Terminal of 'stderr' (file descriptor '2').
pub static TERR: Terminal = Terminal::new(2);

/// `tout`.
#[inline(always)]
pub fn tout() -> &'static Terminal {
    &TOUT
}

/// `terr`.
#[inline(always)]
pub fn terr() -> &'static Terminal {
    &TERR
}

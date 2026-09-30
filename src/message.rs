//! Port of `message.hpp` and `message.cpp`: messages, warnings, errors and
//! fatal errors, plus the C `stdio` helpers used for all output.
//!
//! All output of the solver goes through the C library `FILE` streams
//! (`stdout` / `stderr`) exactly as in C++, so that buffering, flushing and
//! interleaving with other `FILE` based output (proof files, DIMACS output
//! written to `stdout`, ...) is identical.
//!
//! Macros (the first argument gives access to the `Internal`: anything
//! implementing [`crate::internal::InternalRef`], i.e., `self` in
//! `Internal` or `External` methods or a `*mut Internal` back pointer;
//! `section!` needs `&mut Internal`):
//!
//! * `msg!(internal, "fmt", args...)` and `msg!(internal)` (empty line,
//!   C++ `LINE ()`),
//! * `verbose!(internal, level, "fmt", args...)`,
//! * `phase!(internal, "phase", "fmt", args...)` and
//!   `phase!(internal, "phase", count, "fmt", args...)`,
//! * `section!(internal, "title")`,
//! * `warning!(internal, "fmt", args...)`,
//! * `fatal!("fmt", args...)` (no internal, aborts),
//! * `cprintf!("fmt", args...)` (C `printf` to `stdout`),
//!   `cfprintf!(file, "fmt", args...)`.
//!
//! Format strings are Rust `format!` strings; C `printf` conversions
//! without Rust equivalent use the helpers in [`crate::format`].

use std::fmt;

use crate::internal::Internal;
use crate::terminal::{terr, tout};

/*------------------------------------------------------------------------*/

extern "C" {
    #[cfg_attr(any(target_os = "macos", target_os = "ios", target_os = "freebsd"), link_name = "__stdoutp")]
    #[cfg_attr(not(any(target_os = "macos", target_os = "ios", target_os = "freebsd")), link_name = "stdout")]
    static mut C_STDOUT: *mut libc::FILE;
    #[cfg_attr(any(target_os = "macos", target_os = "ios", target_os = "freebsd"), link_name = "__stderrp")]
    #[cfg_attr(not(any(target_os = "macos", target_os = "ios", target_os = "freebsd")), link_name = "stderr")]
    static mut C_STDERR: *mut libc::FILE;
    #[cfg_attr(any(target_os = "macos", target_os = "ios", target_os = "freebsd"), link_name = "__stdinp")]
    #[cfg_attr(not(any(target_os = "macos", target_os = "ios", target_os = "freebsd")), link_name = "stdin")]
    static mut C_STDIN: *mut libc::FILE;
}

/// The C library `stdout` stream.
#[inline(always)]
pub fn c_stdout() -> *mut libc::FILE {
    // SAFETY: reading the libc global stream pointer.
    unsafe { C_STDOUT }
}

/// The C library `stderr` stream.
#[inline(always)]
pub fn c_stderr() -> *mut libc::FILE {
    // SAFETY: reading the libc global stream pointer.
    unsafe { C_STDERR }
}

/// The C library `stdin` stream.
#[inline(always)]
pub fn c_stdin() -> *mut libc::FILE {
    // SAFETY: reading the libc global stream pointer.
    unsafe { C_STDIN }
}

/// `fputs (s, file)` (writes all bytes of `s`, including embedded zeros).
#[inline]
pub fn fputs(s: &str, file: *mut libc::FILE) {
    if s.is_empty() {
        return;
    }
    // SAFETY: 'file' is a valid stream, 's' a valid buffer.
    unsafe {
        libc::fwrite(s.as_ptr() as *const libc::c_void, 1, s.len(), file);
    }
}

/// `fputc (ch, file)`.
#[inline]
pub fn fputc(ch: i32, file: *mut libc::FILE) -> i32 {
    // SAFETY: 'file' is a valid stream.
    unsafe { libc::fputc(ch, file) }
}

/// `fflush (file)`.
#[inline]
pub fn fflush(file: *mut libc::FILE) {
    // SAFETY: 'file' is a valid stream (or null which flushes all).
    unsafe {
        libc::fflush(file);
    }
}

/// `fprintf (file, ...)` with Rust formatting.
pub fn cfprint(file: *mut libc::FILE, args: fmt::Arguments<'_>) {
    match args.as_str() {
        Some(s) => fputs(s, file),
        None => fputs(&fmt::format(args), file),
    }
}

/// `printf (...)` with Rust formatting.
#[inline]
pub fn cprint(args: fmt::Arguments<'_>) {
    cfprint(c_stdout(), args)
}

/// `printf` replacement writing to the C `stdout` stream.
#[macro_export]
macro_rules! cprintf {
    ($($arg:tt)*) => {
        $crate::message::cprint(format_args!($($arg)*))
    };
}

/// `fprintf` replacement writing to a C `FILE *`.
#[macro_export]
macro_rules! cfprintf {
    ($file:expr, $($arg:tt)*) => {
        $crate::message::cfprint($file, format_args!($($arg)*))
    };
}

/*------------------------------------------------------------------------*/

/// `MSG (...)` and `LINE ()`.
#[macro_export]
macro_rules! msg {
    ($internal:expr) => {{
        #[allow(unused_imports)]
        use $crate::internal::InternalRef as _;
        ($internal).internal_ref().message_empty()
    }};
    ($internal:expr, $($arg:tt)+) => {{
        #[allow(unused_imports)]
        use $crate::internal::InternalRef as _;
        ($internal).internal_ref().message(format_args!($($arg)+))
    }};
}

/// `VERBOSE (level, ...)`.
#[macro_export]
macro_rules! verbose {
    ($internal:expr, $level:expr) => {{
        #[allow(unused_imports)]
        use $crate::internal::InternalRef as _;
        ($internal).internal_ref().verbose_empty($level)
    }};
    ($internal:expr, $level:expr, $($arg:tt)+) => {{
        #[allow(unused_imports)]
        use $crate::internal::InternalRef as _;
        ($internal).internal_ref().verbose($level, format_args!($($arg)+))
    }};
}

/// `PHASE (phase, fmt, ...)` and `PHASE (phase, count, fmt, ...)`.
#[macro_export]
macro_rules! phase {
    ($internal:expr, $phase:expr, $fmt:literal $(, $arg:expr)* $(,)?) => {{
        #[allow(unused_imports)]
        use $crate::internal::InternalRef as _;
        ($internal).internal_ref().phase_message($phase, format_args!($fmt $(, $arg)*))
    }};
    ($internal:expr, $phase:expr, $count:expr, $fmt:literal $(, $arg:expr)* $(,)?) => {{
        #[allow(unused_imports)]
        use $crate::internal::InternalRef as _;
        ($internal)
            .internal_ref()
            .phase_message_count($phase, ($count) as i64, format_args!($fmt $(, $arg)*))
    }};
}

/// `SECTION (title)`.
#[macro_export]
macro_rules! section {
    ($internal:expr, $title:expr) => {
        $internal.section($title)
    };
}

/// `WARNING (...)`.
#[macro_export]
macro_rules! warning {
    ($internal:expr, $($arg:tt)+) => {{
        #[allow(unused_imports)]
        use $crate::internal::InternalRef as _;
        ($internal).internal_ref().warning(format_args!($($arg)+))
    }};
}

/// `FATAL (...)` / `fatal (...)`: print a fatal error message and abort.
#[macro_export]
macro_rules! fatal {
    ($($arg:tt)+) => {
        $crate::message::fatal(format_args!($($arg)+))
    };
}

/*------------------------------------------------------------------------*/

// Port of 'message.cpp' (the 'QUIET' configuration is not supported).

impl Internal {
    pub fn print_prefix(&self) {
        fputs(&self.prefix, c_stdout());
    }

    #[inline]
    fn quiet_suppressed(&self) -> bool {
        #[cfg(feature = "logging")]
        if self.opts.log != 0 {
            return false;
        }
        self.opts.quiet != 0
    }

    /// `message (fmt, ...)` (and `vmessage`).
    pub fn message(&self, args: fmt::Arguments<'_>) {
        if self.quiet_suppressed() {
            return;
        }
        self.print_prefix();
        cprint(args);
        fputc(b'\n' as i32, c_stdout());
        fflush(c_stdout());
    }

    /// `message ()`: empty line (only prefix).
    pub fn message_empty(&self) {
        if self.quiet_suppressed() {
            return;
        }
        self.print_prefix();
        fputc(b'\n' as i32, c_stdout());
        fflush(c_stdout());
    }

    #[inline]
    fn verbose_suppressed(&self, level: i32) -> bool {
        #[cfg(feature = "logging")]
        if self.opts.log != 0 {
            return false;
        }
        self.opts.quiet != 0 || level > self.opts.verbose
    }

    /// `verbose (level, fmt, ...)` (and `vverbose`).
    pub fn verbose(&self, level: i32, args: fmt::Arguments<'_>) {
        if self.verbose_suppressed(level) {
            return;
        }
        self.print_prefix();
        cprint(args);
        fputc(b'\n' as i32, c_stdout());
        fflush(c_stdout());
    }

    /// `verbose (level)`: empty verbose line.
    pub fn verbose_empty(&self, level: i32) {
        if self.verbose_suppressed(level) {
            return;
        }
        self.print_prefix();
        fputc(b'\n' as i32, c_stdout());
        fflush(c_stdout());
    }

    /// Print section headers in the form `c ---- [ <title> ] -----`.
    pub fn section(&mut self, title: &str) {
        if self.quiet_suppressed() {
            return;
        }
        let sections = self.stats.sections;
        self.stats.sections += 1;
        if sections != 0 {
            self.message_empty();
        }
        self.print_prefix();
        tout().blue(false);
        fputs("--- [ ", c_stdout());
        tout().blue(true);
        fputs(title, c_stdout());
        tout().blue(false);
        fputs(" ] ", c_stdout());
        let mut i = title.len() + self.prefix.len() + 9;
        while i < 78 {
            fputc(b'-' as i32, c_stdout());
            i += 1;
        }
        tout().normal();
        fputc(b'\n' as i32, c_stdout());
        self.message_empty();
    }

    #[inline]
    fn phase_suppressed(&self) -> bool {
        #[cfg(feature = "logging")]
        if self.opts.log != 0 {
            return false;
        }
        self.opts.quiet != 0 || (!self.force_phase_messages && self.opts.verbose < 2)
    }

    /// `phase (phase, fmt, ...)`: `c [<phase>] ...`.
    pub fn phase_message(&self, phase: &str, args: fmt::Arguments<'_>) {
        if self.phase_suppressed() {
            return;
        }
        self.print_prefix();
        cprint(format_args!("[{}] ", phase));
        cprint(args);
        fputc(b'\n' as i32, c_stdout());
        fflush(c_stdout());
    }

    /// `phase (phase, count, fmt, ...)`: `c [<phase>-<count>] ...`.
    pub fn phase_message_count(&self, phase: &str, count: i64, args: fmt::Arguments<'_>) {
        if self.phase_suppressed() {
            return;
        }
        self.print_prefix();
        cprint(format_args!("[{}-{}] ", phase, count));
        cprint(args);
        fputc(b'\n' as i32, c_stdout());
        fflush(c_stdout());
    }

    /*--------------------------------------------------------------------*/

    pub fn warning(&self, args: fmt::Arguments<'_>) {
        fflush(c_stdout());
        terr().bold();
        fputs("cadical: ", c_stderr());
        terr().red(true);
        fputs("warning:", c_stderr());
        terr().normal();
        fputc(b' ' as i32, c_stderr());
        cfprint(c_stderr(), args);
        fputc(b'\n' as i32, c_stderr());
        fflush(c_stderr());
    }

    /*--------------------------------------------------------------------*/

    pub fn error_message_start(&self) {
        fflush(c_stdout());
        terr().bold();
        fputs("cadical: ", c_stderr());
        terr().red(true);
        fputs("error:", c_stderr());
        terr().normal();
        fputc(b' ' as i32, c_stderr());
    }

    pub fn error_message_end(&self) -> ! {
        fputc(b'\n' as i32, c_stderr());
        fflush(c_stderr());
        // TODO add possibility to use call back instead.
        std::process::exit(1);
    }

    /// `error (fmt, ...)` (and `verror`): print error message and exit
    /// with status '1'.
    pub fn error(&self, args: fmt::Arguments<'_>) -> ! {
        self.error_message_start();
        cfprint(c_stderr(), args);
        self.error_message_end();
    }
}

/*------------------------------------------------------------------------*/

pub fn fatal_message_start() {
    fflush(c_stdout());
    terr().bold();
    fputs("cadical: ", c_stderr());
    terr().red(true);
    fputs("fatal error:", c_stderr());
    terr().normal();
    fputc(b' ' as i32, c_stderr());
}

pub fn fatal_message_end() -> ! {
    fputc(b'\n' as i32, c_stderr());
    fflush(c_stderr());
    std::process::abort();
}

/// Fatal internal error which leads to abort.
pub fn fatal(args: fmt::Arguments<'_>) -> ! {
    fatal_message_start();
    cfprint(c_stderr(), args);
    fatal_message_end();
}

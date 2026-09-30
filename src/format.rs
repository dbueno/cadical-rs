//! Port of `format.hpp` and `format.cpp` (the `Format` class capturing a
//! persistent error message), plus helpers producing exactly the output
//! of C `printf` conversions which have no exact Rust equivalent.

use std::ffi::CString;

/// `printf` style formatting utility capturing an error message.  In the
/// Rust port the format arguments are already rendered by `format!`, so
/// `init` and `append` take the finished text.
#[derive(Clone, Debug, Default)]
pub struct Format {
    buffer: String,
    /// Mirrors 'count != 0' of the C++ code ('operator const char *').
    set: bool,
}

impl Format {
    pub fn new() -> Format {
        Format { buffer: String::new(), set: false }
    }

    /// `init (fmt, ...)`: start a new message.
    pub fn init(&mut self, args: std::fmt::Arguments<'_>) -> &str {
        self.buffer.clear();
        self.set = true;
        std::fmt::Write::write_fmt(&mut self.buffer, args).unwrap();
        &self.buffer
    }

    /// `append (fmt, ...)`: append to the current message.
    pub fn append(&mut self, args: std::fmt::Arguments<'_>) -> &str {
        self.set = true;
        std::fmt::Write::write_fmt(&mut self.buffer, args).unwrap();
        &self.buffer
    }

    /// `operator const char * ()`: the message or `None` if empty.
    pub fn get(&self) -> Option<&str> {
        if self.set && !self.buffer.is_empty() {
            Some(&self.buffer)
        } else if self.set {
            // An empty but initialized message ('count == 0') is null too.
            None
        } else {
            None
        }
    }
}

/*------------------------------------------------------------------------*/

/// Format a single `double` with a C `printf` conversion specification
/// (e.g. `"%.2f"`, `"%g"`, `"%7.2f%%"`) using the C library, which
/// guarantees byte identical output to the C++ code.
pub fn cfmt_f64(spec: &str, x: f64) -> String {
    let fmt = CString::new(spec).unwrap();
    let mut buf = vec![0u8; 64];
    loop {
        // SAFETY: 'buf' is large enough for 'n' bytes plus terminator.
        let n = unsafe {
            libc::snprintf(buf.as_mut_ptr() as *mut libc::c_char, buf.len(), fmt.as_ptr(), x)
        };
        if n < 0 {
            return String::new();
        }
        let n = n as usize;
        if n < buf.len() {
            buf.truncate(n);
            return String::from_utf8(buf).unwrap_or_default();
        }
        buf.resize(n + 1, 0);
    }
}

/// `%g`.
#[inline]
pub fn fmt_g(x: f64) -> String {
    cfmt_f64("%g", x)
}

/// `%.<prec>f`.
#[inline]
pub fn fmt_f(x: f64, prec: usize) -> String {
    cfmt_f64(&format!("%.{}f", prec), x)
}

/// `%<width>.<prec>f`.
#[inline]
pub fn fmt_wf(x: f64, width: usize, prec: usize) -> String {
    cfmt_f64(&format!("%{}.{}f", width, prec), x)
}

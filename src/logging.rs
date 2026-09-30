//! Port of `logging.hpp` and `logging.cpp`.
//!
//! Logging code is only compiled with the `logging` feature (C++
//! `-DLOGGING`, `./configure -l`).  It still has to be enabled at run-time
//! with the `log` option (`-l` in the stand-alone solver).  The printed
//! text is identical to C++.
//!
//! Usage (the first argument is anything implementing
//! [`crate::internal::InternalRef`]: `self` in `Internal` or `External`
//! methods, or a `*mut Internal` back pointer):
//!
//! ```text
//!   log!(self, "fmt", args...);            // Logger::log (internal, fmt)
//!   log!(self, c, "fmt", args...);         // clause 'c: CRef' (may be null)
//!   log!(self, &self.clause, "fmt", ...);  // literals (&Vec<i32> / &[i32])
//!   log!(self, &chain, "fmt", ...);        // LRAT chain (&Vec<i64> / &[i64])
//!   log!(self, g, "fmt", ...);             // gate (*const Gate / *mut Gate)
//!   log_empty_line!(self);
//!   loglit!(self, lit)                     // -> String
//! ```
//!
//! Without the `logging` feature the macros expand to nothing (their
//! arguments are not evaluated nor type checked).

#[cfg(feature = "logging")]
use crate::clause::{clause_lit_less_than, CRef};
#[cfg(feature = "logging")]
use crate::congruence::{special_gate_str, string_of_gate, Gate};
#[cfg(feature = "logging")]
use crate::internal::Internal;
#[cfg(feature = "logging")]
use crate::message::{c_stdout, cprint, fflush, fputc, fputs};
#[cfg(feature = "logging")]
use crate::terminal::tout;

/// `LOG (...)`.
#[macro_export]
macro_rules! log {
    ($internal:expr, $fmt:literal $(, $arg:expr)* $(,)?) => {
        #[cfg(feature = "logging")]
        {
            #[allow(unused_imports)]
            use $crate::internal::InternalRef as _;
            let __internal: &$crate::internal::Internal = ($internal).internal_ref();
            if __internal.opts.log != 0 {
                $crate::logging::Logger::log(__internal, format_args!($fmt $(, $arg)*));
            }
        }
    };
    ($internal:expr, $item:expr, $fmt:literal $(, $arg:expr)* $(,)?) => {
        #[cfg(feature = "logging")]
        {
            #[allow(unused_imports)]
            use $crate::internal::InternalRef as _;
            let __internal: &$crate::internal::Internal = ($internal).internal_ref();
            if __internal.opts.log != 0 {
                $crate::logging::Loggable::log_item(
                    $item,
                    __internal,
                    format_args!($fmt $(, $arg)*),
                );
            }
        }
    };
}

/// `Logger::log_empty_line (internal)` guarded by `opts.log`.
#[macro_export]
macro_rules! log_empty_line {
    ($internal:expr) => {
        #[cfg(feature = "logging")]
        {
            #[allow(unused_imports)]
            use $crate::internal::InternalRef as _;
            let __internal: &$crate::internal::Internal = ($internal).internal_ref();
            if __internal.opts.log != 0 {
                $crate::logging::Logger::log_empty_line(__internal);
            }
        }
    };
}

/// `LOGLIT (lit)`: returns a `String` (only available with `logging`).
#[macro_export]
macro_rules! loglit {
    ($internal:expr, $lit:expr) => {
        {
            #[allow(unused_imports)]
            use $crate::internal::InternalRef as _;
            $crate::logging::Logger::loglit(($internal).internal_ref(), $lit)
        }
    };
}

/// Things that can be logged after the message (`Logger::log` overloads).
#[cfg(feature = "logging")]
pub trait Loggable {
    fn log_item(self, internal: &Internal, args: std::fmt::Arguments<'_>);
}

#[cfg(feature = "logging")]
impl Loggable for CRef {
    fn log_item(self, internal: &Internal, args: std::fmt::Arguments<'_>) {
        Logger::log_clause(internal, self, args)
    }
}

#[cfg(feature = "logging")]
impl Loggable for &Vec<i32> {
    fn log_item(self, internal: &Internal, args: std::fmt::Arguments<'_>) {
        Logger::log_lits(internal, self, args)
    }
}

#[cfg(feature = "logging")]
impl Loggable for &[i32] {
    fn log_item(self, internal: &Internal, args: std::fmt::Arguments<'_>) {
        Logger::log_lits(internal, self, args)
    }
}

#[cfg(feature = "logging")]
impl Loggable for &Vec<i64> {
    fn log_item(self, internal: &Internal, args: std::fmt::Arguments<'_>) {
        Logger::log_ids(internal, self, args)
    }
}

#[cfg(feature = "logging")]
impl Loggable for &[i64] {
    fn log_item(self, internal: &Internal, args: std::fmt::Arguments<'_>) {
        Logger::log_ids(internal, self, args)
    }
}

#[cfg(feature = "logging")]
impl Loggable for *const Gate {
    fn log_item(self, internal: &Internal, args: std::fmt::Arguments<'_>) {
        Logger::log_gate(internal, self, args)
    }
}

#[cfg(feature = "logging")]
impl Loggable for *mut Gate {
    fn log_item(self, internal: &Internal, args: std::fmt::Arguments<'_>) {
        Logger::log_gate(internal, self as *const Gate, args)
    }
}

#[cfg(feature = "logging")]
impl Loggable for &Gate {
    fn log_item(self, internal: &Internal, args: std::fmt::Arguments<'_>) {
        Logger::log_gate(internal, self as *const Gate, args)
    }
}

/// `struct Logger` (all static member functions).
pub struct Logger;

#[cfg(feature = "logging")]
impl Logger {
    pub fn print_log_prefix(internal: &Internal) {
        internal.print_prefix();
        tout().magenta(false);
        fputs("LOG ", c_stdout());
        tout().magenta(true);
        cprint(format_args!("{} ", internal.level));
        tout().normal();
    }

    pub fn log_empty_line(internal: &Internal) {
        internal.print_prefix();
        tout().magenta(false);
        let len = internal.prefix.len() as i32;
        let max = 78 - len;
        for _ in 0..max {
            fputc(b'-' as i32, c_stdout());
        }
        fputc(b'\n' as i32, c_stdout());
        tout().normal();
        fflush(c_stdout());
    }

    /// Simple logging of a format string.
    pub fn log(internal: &Internal, args: std::fmt::Arguments<'_>) {
        Logger::print_log_prefix(internal);
        tout().magenta(false);
        cprint(args);
        fputc(b'\n' as i32, c_stdout());
        tout().normal();
        fflush(c_stdout());
    }

    /// Prints the message and then the clause.  The clause can also be a
    /// null reference and then is interpreted as a decision (current
    /// decision level > 0) or unit clause (zero decision level).
    /// (C++ overload `Logger::log (Internal *, const Clause *, ...)`.)
    pub fn log_clause(internal: &Internal, c: CRef, args: std::fmt::Arguments<'_>) {
        Logger::print_log_prefix(internal);
        tout().magenta(false);
        cprint(args);
        if !c.is_null() {
            if c.redundant() {
                cprint(format_args!(" glue {} redundant", c.glue()));
            } else {
                cprint(format_args!(" irredundant"));
            }
            cprint(format_args!(" size {} clause[{}]", c.size(), c.id()));
            if c.moved() {
                cprint(format_args!(" ... (moved)"));
            } else if internal.opts.logsort != 0 {
                let mut s: Vec<i32> = c.lits().to_vec();
                crate::sort::std_sort(&mut s, clause_lit_less_than);
                for lit in s {
                    cprint(format_args!(" {}", lit));
                }
            } else {
                for &lit in c.lits() {
                    cprint(format_args!(" {}", Logger::loglit(internal, lit)));
                }
            }
        } else if internal.level != 0 {
            cprint(format_args!(" decision"));
        } else {
            cprint(format_args!(" unit"));
        }
        fputc(b'\n' as i32, c_stdout());
        tout().normal();
        fflush(c_stdout());
    }

    /// (C++ overload `Logger::log (Internal *, const Gate *, ...)`.)
    pub fn log_gate(internal: &Internal, g: *const Gate, args: std::fmt::Arguments<'_>) {
        Logger::print_log_prefix(internal);
        tout().magenta(false);
        cprint(args);
        if !g.is_null() {
            // SAFETY: non-null gate pointers point to live gates.
            let g = unsafe { &*g };
            cprint(format_args!(
                "{}{} gate[{}] (arity: {}) {} := {}",
                special_gate_str(g.degenerated_gate),
                if g.garbage { " garbage" } else { "" },
                g.id,
                g.arity(),
                Logger::loglit(internal, g.lhs),
                string_of_gate(g.tag)
            ));
            for &lit in g.rhs.iter() {
                cprint(format_args!(" {}", Logger::loglit(internal, lit)));
            }
        } else {
            cprint(format_args!(" null gate"));
        }
        fputc(b'\n' as i32, c_stdout());
        tout().normal();
        fflush(c_stdout());
    }

    /// Same as above, but for the global clause (or any literal vector).
    /// Covers the C++ overloads for `const vector<int> &`, the
    /// `(begin, end)` iterator pair and `(const int *, unsigned)`.
    pub fn log_lits(internal: &Internal, c: &[i32], args: std::fmt::Arguments<'_>) {
        Logger::print_log_prefix(internal);
        tout().magenta(false);
        cprint(args);
        if internal.opts.logsort != 0 {
            let mut s: Vec<i32> = c.to_vec();
            crate::sort::std_sort(&mut s, clause_lit_less_than);
            for lit in s {
                cprint(format_args!(" {}", lit));
            }
        } else {
            for &lit in c {
                cprint(format_args!(" {}", lit));
            }
        }
        fputc(b'\n' as i32, c_stdout());
        tout().normal();
        fflush(c_stdout());
    }

    /// For LRAT proof chains (C++ overload for `const vector<int64_t> &`).
    pub fn log_ids(internal: &Internal, c: &[i64], args: std::fmt::Arguments<'_>) {
        Logger::print_log_prefix(internal);
        tout().magenta(false);
        cprint(args);
        for &id in c {
            cprint(format_args!(" {}", id));
        }
        fputc(b'\n' as i32, c_stdout());
        tout().normal();
        fflush(c_stdout());
    }

    /// For LRAT proof clauses (C++ overload `(const int *, unsigned)`,
    /// which never sorts even with `logsort`).
    pub fn log_int_array(internal: &Internal, literals: &[i32], args: std::fmt::Arguments<'_>) {
        Logger::print_log_prefix(internal);
        tout().magenta(false);
        cprint(args);
        for &lit in literals {
            cprint(format_args!(" {}", lit));
        }
        fputc(b'\n' as i32, c_stdout());
        tout().normal();
        fflush(c_stdout());
    }

    pub fn loglit(internal: &Internal, lit: i32) -> String {
        let mut v = lit.to_string();
        if lit != 0 && -internal.max_var <= lit && internal.max_var >= lit {
            let va = internal.val(lit);
            if va != 0 {
                v = v + "@" + &internal.var(lit).level.to_string();
                if internal.var(lit).reason.is_null() {
                    v += "+";
                }
            }
            if va > 0 {
                v += "=1";
            } else if va < 0 {
                v += "=-1";
            }
        }
        v
    }
}

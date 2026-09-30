//! Port of `contract.hpp` and `contract.cpp`: API contract checking.
//!
//! Macros (used in `solver.rs`):
//!
//! * `require!(cond, "fmt", args...)` (`REQUIRE`),
//! * `cb_require!(cond, name, value, "fmt", args...)` (`CB_REQUIRE`),
//! * `contract_violated!(function, "fmt", args...)`,
//! * `callback_violated!(name, value, "fmt", args...)`.
//!
//! The C++ messages contain `__PRETTY_FUNCTION__` and `__FILE__`; the Rust
//! port passes the C++ function signature string explicitly (see
//! `solver.rs`) so that the messages stay identical, e.g.
//! `"int CaDiCaL::Solver::solve()"` and file `"solver.cpp"`.

use crate::message::{c_stderr, fatal_message_start, fflush};

/// `CONTRACT_VIOLATED (...)`.
pub fn contract_violated(function: &str, file: &str, args: std::fmt::Arguments<'_>) -> ! {
    fatal_message_start();
    crate::message::cfprint(
        c_stderr(),
        format_args!("invalid API usage of '{}' in '{}': ", function, file),
    );
    crate::message::cfprint(c_stderr(), args);
    crate::message::fputc(b'\n' as i32, c_stderr());
    fflush(c_stderr());
    std::process::abort();
}

/// `CALLBACK_VIOLATED (NAME, VALUE, ...)`.
pub fn callback_violated(name: &str, value: i32, args: std::fmt::Arguments<'_>) -> ! {
    fatal_message_start();
    crate::message::cfprint(
        c_stderr(),
        format_args!("invalid return value {} to callback '{}': ", value, name),
    );
    crate::message::cfprint(c_stderr(), args);
    crate::message::fputc(b'\n' as i32, c_stderr());
    fflush(c_stderr());
    std::process::abort();
}

/// See comments in 'contract.hpp'.  In Rust a null `self` is impossible,
/// kept for completeness (used with raw pointers only).
pub fn require_solver_pointer_to_be_non_zero(ptr: *const (), function_name: &str, file_name: &str) {
    if !ptr.is_null() {
        return;
    }
    fatal_message_start();
    crate::message::cfprint(
        c_stderr(),
        format_args!(
            "invalid API usage of '{}' in '{}': solver 'this' pointer zero (not initialized)\n",
            function_name, file_name
        ),
    );
    fflush(c_stderr());
    std::process::abort();
}

/// `REQUIRE (COND, ...)` with explicit function signature and file name:
/// `require!(func, file, cond, "fmt", args...)`.
#[macro_export]
macro_rules! require {
    ($func:expr, $file:expr, $cond:expr, $($arg:tt)+) => {
        if !($cond) {
            $crate::contract::contract_violated($func, $file, format_args!($($arg)+));
        }
    };
}

/// `CB_REQUIRE (COND, NAME, VALUE, ...)`.
#[macro_export]
macro_rules! cb_require {
    ($cond:expr, $name:expr, $value:expr, $($arg:tt)+) => {
        if !($cond) {
            $crate::contract::callback_violated($name, $value, format_args!($($arg)+));
        }
    };
}

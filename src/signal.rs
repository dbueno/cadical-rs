//! Port of `signal.hpp` and `signal.cpp`: helper class for handling
//! signals in applications.

/// `class Handler`.
pub trait Handler {
    fn catch_signal(&mut self, sig: i32);
    /// Defined in 'signal.cpp' as `catch_signal (SIGALRM)`.
    fn catch_alarm(&mut self) {
        self.catch_signal(libc::SIGALRM);
    }
}

/// `class Signal` (only static member functions).
pub struct Signal;

/*------------------------------------------------------------------------*/

// Signal handlers for printing statistics even if solver is interrupted.
//
// The state is kept in (process global) statics exactly as in C++.  All
// of them are only accessed through plain loads and stores (C++ uses
// 'volatile'), which we mirror with relaxed atomics where possible.

use std::sync::atomic::{AtomicBool, AtomicI32, Ordering::Relaxed};

use crate::resources::absolute_real_time;

static SIGNAL_VALUE: AtomicI32 = AtomicI32::new(0);
static CAUGHT_SIGNAL: AtomicBool = AtomicBool::new(false);

/// `static Handler *signal_handler` (a fat pointer, thus not atomic).
static mut SIGNAL_HANDLER: Option<*mut dyn Handler> = None;

static CAUGHT_ALARM: AtomicBool = AtomicBool::new(false);
static ALARM_SET: AtomicBool = AtomicBool::new(false);
static ALARM_TIME: AtomicI32 = AtomicI32::new(-1);

/// Previous handlers ('SIGABRT_handler', 'SIGINT_handler', ...).
static SIGABRT_HANDLER: AtomicUsize = AtomicUsize::new(0);
static SIGINT_HANDLER: AtomicUsize = AtomicUsize::new(0);
static SIGSEGV_HANDLER: AtomicUsize = AtomicUsize::new(0);
static SIGTERM_HANDLER: AtomicUsize = AtomicUsize::new(0);
static SIGALRM_HANDLER: AtomicUsize = AtomicUsize::new(0);

use std::sync::atomic::AtomicUsize;

#[inline]
fn get_handler() -> Option<*mut dyn Handler> {
    // SAFETY: plain read of a pointer sized value (as in C++).
    unsafe { *std::ptr::addr_of!(SIGNAL_HANDLER) }
}

#[inline]
fn set_handler(h: Option<*mut dyn Handler>) {
    // SAFETY: plain write (as in C++).
    unsafe {
        *std::ptr::addr_of_mut!(SIGNAL_HANDLER) = h;
    }
}

#[inline]
fn install(sig: i32, handler: libc::sighandler_t) -> libc::sighandler_t {
    // SAFETY: installing a signal handler with 'signal' as in C++.
    unsafe { libc::signal(sig, handler) }
}

/// The table of 'SIGNALS' in C++ order.
fn signals() -> [(i32, &'static AtomicUsize, &'static str); 4] {
    [
        (libc::SIGABRT, &SIGABRT_HANDLER, "SIGABRT"),
        (libc::SIGINT, &SIGINT_HANDLER, "SIGINT"),
        (libc::SIGSEGV, &SIGSEGV_HANDLER, "SIGSEGV"),
        (libc::SIGTERM, &SIGTERM_HANDLER, "SIGTERM"),
    ]
}

extern "C" fn catch_signal(sig: libc::c_int) {
    if sig == libc::SIGALRM && absolute_real_time() >= ALARM_TIME.load(Relaxed) as f64 {
        if !CAUGHT_ALARM.load(Relaxed) {
            CAUGHT_ALARM.store(true, Relaxed);
            if let Some(h) = get_handler() {
                // SAFETY: the handler is alive while connected (C++ same).
                unsafe { (*h).catch_alarm() };
            }
        }
        Signal::reset_alarm();
    } else {
        // Reraising should happen in solver control for SIGINT and SIGTERM.
        // For SIGABRT and SIGSEGV we reraise immediately.
        if sig == libc::SIGABRT || sig == libc::SIGSEGV {
            Signal::reset();
            // SAFETY: 'raise'.
            unsafe {
                libc::raise(sig);
            }
        }
        if !CAUGHT_SIGNAL.load(Relaxed) {
            CAUGHT_SIGNAL.store(true, Relaxed);
            if let Some(h) = get_handler() {
                // SAFETY: the handler is alive while connected (C++ same).
                unsafe { (*h).catch_signal(sig) };
            }
        }
    }
}

#[inline]
fn catch_signal_handler() -> libc::sighandler_t {
    catch_signal as extern "C" fn(libc::c_int) as libc::sighandler_t
}

impl Signal {
    pub fn reset_alarm() {
        if !ALARM_SET.load(Relaxed) {
            return;
        }
        let _ = install(libc::SIGALRM, SIGALRM_HANDLER.load(Relaxed));
        SIGALRM_HANDLER.store(0, Relaxed);
        CAUGHT_ALARM.store(false, Relaxed);
        ALARM_SET.store(false, Relaxed);
        ALARM_TIME.store(-1, Relaxed);
    }

    pub fn reset() {
        set_handler(None);
        for (sig, prev, _) in signals() {
            let _ = install(sig, prev.load(Relaxed));
            prev.store(0, Relaxed);
        }
        Signal::reset_alarm();
        CAUGHT_SIGNAL.store(false, Relaxed);
        SIGNAL_VALUE.store(0, Relaxed);
    }

    pub fn name(sig: i32) -> &'static str {
        for (s, _, name) in signals() {
            if sig == s {
                return name;
            }
        }
        if sig == libc::SIGALRM {
            return "SIGALRM";
        }
        "UNKNOWN"
    }

    pub fn set(handler: *mut dyn Handler) {
        set_handler(Some(handler));
        for (sig, prev, _) in signals() {
            prev.store(install(sig, catch_signal_handler()), Relaxed);
        }
    }

    pub fn alarm(seconds: i32) {
        debug_assert!(seconds >= 0);
        debug_assert!(!ALARM_SET.load(Relaxed));
        debug_assert!(ALARM_TIME.load(Relaxed) < 0);
        SIGALRM_HANDLER.store(install(libc::SIGALRM, catch_signal_handler()), Relaxed);
        ALARM_SET.store(true, Relaxed);
        // 'alarm_time' is an 'int' in C++ (truncating conversion).
        ALARM_TIME.store((absolute_real_time() + seconds as f64) as i32, Relaxed);
        // SAFETY: 'alarm'.
        unsafe {
            libc::alarm(seconds as libc::c_uint);
        }
    }

    pub fn set_received(sig: i32) {
        SIGNAL_VALUE.store(sig, Relaxed);
    }

    pub fn received() -> i32 {
        SIGNAL_VALUE.load(Relaxed)
    }

    /// Signals for which returning control is sensible.
    pub fn interrupted() -> bool {
        let sig = Signal::received();
        sig == libc::SIGINT || sig == libc::SIGTERM
    }
}

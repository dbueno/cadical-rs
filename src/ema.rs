//! Port of `ema.hpp` and `ema.cpp`: exponential moving averages with
//! ADAM style bias correction.

use crate::internal::Internal;

#[derive(Clone, Copy, Debug, Default)]
pub struct EMA {
    #[cfg(feature = "logging")]
    pub updated: u64,
    /// Unbiased (corrected) moving average.
    pub value: f64,
    /// Biased initialized moving average.
    pub biased: f64,
    /// Input scaling with 'alpha = 1 - beta'.
    pub alpha: f64,
    /// Decay of 'biased' with 'beta = 1 - alpha'.
    pub beta: f64,
    /// 'exp = pow (beta, updated)'.
    pub exp: f64,
}

impl EMA {
    /// `EMA (double a)`.
    pub fn new(a: f64) -> EMA {
        let beta = 1.0 - a;
        let e = EMA {
            #[cfg(feature = "logging")]
            updated: 0,
            value: 0.0,
            biased: 0.0,
            alpha: a,
            beta,
            exp: if beta != 0.0 { 1.0 } else { 0.0 },
        };
        debug_assert!(e.beta >= 0.0);
        e
    }

    /// `operator double ()`.
    #[inline(always)]
    pub fn value(&self) -> f64 {
        self.value
    }

    /// Updating an exponential moving average.  `internal` is only used
    /// for logging (a raw pointer since the average usually is a field of
    /// the same `Internal`).
    pub fn update(&mut self, internal: *const Internal, y: f64, name: &str) {
        #[cfg(feature = "logging")]
        let old_value;
        #[cfg(feature = "logging")]
        {
            self.updated += 1;
            old_value = self.value;
        }
        let old_biased = self.biased;
        let delta = y - old_biased;
        let scaled_delta = self.alpha * delta;
        let new_biased = old_biased + scaled_delta;
        #[cfg(feature = "logging")]
        {
            // SAFETY: 'internal' outlives this call.
            let internal = unsafe { &*internal };
            log!(
                internal,
                "update {} of biased {} EMA {} with {} (delta {}) yields {} (scaled delta {})",
                self.updated,
                name,
                crate::format::fmt_g(old_biased),
                crate::format::fmt_g(y),
                crate::format::fmt_g(delta),
                crate::format::fmt_g(new_biased),
                crate::format::fmt_g(scaled_delta)
            );
        }
        self.biased = new_biased;
        let old_exp = self.exp;
        let new_exp: f64;
        let div: f64;
        let new_value: f64;
        if old_exp != 0.0 {
            new_exp = old_exp * self.beta;
            debug_assert!(new_exp < 1.0);
            self.exp = new_exp;
            div = 1.0 - new_exp;
            debug_assert!(div > 0.0);
            new_value = new_biased / div;
        } else {
            new_value = new_biased;
            new_exp = 0.0;
            div = 1.0;
        }
        self.value = new_value;
        #[cfg(feature = "logging")]
        {
            // SAFETY: 'internal' outlives this call.
            let internal = unsafe { &*internal };
            log!(
                internal,
                "update {} of corrected {} EMA {} with {} (delta {}) yields {} (exponent {}, divisor {})",
                self.updated,
                name,
                crate::format::fmt_g(old_value),
                crate::format::fmt_g(y),
                crate::format::fmt_g(delta),
                crate::format::fmt_g(new_value),
                crate::format::fmt_g(new_exp),
                crate::format::fmt_g(div)
            );
        }
        let _ = (internal, name, new_exp, div);
    }
}

/// `UPDATE_AVERAGE (A, Y)`: `update_average!(self, averages.current.glue.fast, glue)`.
#[macro_export]
macro_rules! update_average {
    ($internal:expr, $($field:ident).+, $y:expr) => {{
        let __y = ($y) as f64;
        let __i: *const $crate::internal::Internal = &*$internal;
        $internal.$($field).+.update(__i, __y, stringify!($($field).+));
    }};
}

/// `INIT_EMA (E, WINDOW)`: `init_ema!(self, averages.current.jump, self.opts.emajump)`.
#[macro_export]
macro_rules! init_ema {
    ($internal:expr, $($field:ident).+, $window:expr) => {{
        let __w = $window;
        debug_assert!(__w >= 1);
        let __alpha = 1.0 / (__w as f64);
        $internal.$($field).+ = $crate::ema::EMA::new(__alpha);
        log!(
            $internal,
            "init {} EMA target alpha {} window {}",
            stringify!($($field).+),
            $crate::format::fmt_g(__alpha),
            __w as i32
        );
    }};
}

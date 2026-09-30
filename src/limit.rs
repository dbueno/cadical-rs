//! Port of `limit.hpp` and `limit.cpp`: search and inprocessing limits.

use crate::internal::Internal;

#[derive(Clone, Copy, Debug, Default)]
pub struct LimitTerminate {
    /// Countdown to next terminator call.
    pub check: i32,
    /// Forced termination for testing.
    pub forced: i32,
}

/// `Limit` (zero initialized as in C++ `memset`).
#[derive(Clone, Copy, Debug, Default)]
pub struct Limit {
    pub initialized: bool,
    /// Conflict limit if non-negative.
    pub conflicts: i64,
    /// Decision limit if non-negative.
    pub decisions: i64,
    /// Limit on preprocessing rounds.
    pub preprocessing: i64,
    /// Limit on local search rounds.
    pub localsearch: i64,
    /// Ticks limit if non-negative.
    pub ticks: i64,
    /// Conflict limit for next 'compact'.
    pub compact: i64,
    /// Conflict limit for next 'condition'.
    pub condition: i64,
    /// Conflict limit for next 'elim'.
    pub elim: i64,
    /// Conflict limit for next 'flush'.
    pub flush: i64,
    /// Conflict limit for next 'inprobe'.
    pub inprobe: i64,
    /// Conflict limit for next 'reduce'.
    pub reduce: i64,
    /// Conflict limit for next 'rephase'.
    pub rephase: i64,
    /// Report limit for header.
    pub report: i64,
    /// Conflict limit for next 'restart'.
    pub restart: i64,
    /// Conflict/ticks limit for next 'stabilize'.
    pub stabilize: i64,
    /// Conflict/ticks limit for next clause 'decay' for incremental clauses.
    pub incremental_decay: i64,
    /// Randomized decision limit for conflicts.
    pub random_decision: i64,
    /// Maximum kept size in 'reduce'.
    pub keptsize: i32,
    /// Maximum kept glue in 'reduce'.
    pub keptglue: i32,
    /// Conflict limit for next tier recomputation.
    pub recompute_tier: i64,
    /// How often rephased during (1) or out (0) of stabilization.
    pub rephased: [i64; 2],
    /// Current elimination bound per eliminated variable.
    pub elimbound: i64,
    pub terminate: LimitTerminate,
}

impl Limit {
    pub fn new() -> Limit {
        Limit::default()
    }
}

/// The `bumpreasons` member of `Delay` (an anonymous struct in C++).
#[derive(Clone, Copy, Debug, Default)]
pub struct DelayBumpReasons {
    pub interval: i64,
    pub limit: i64,
    pub bypass: bool,
}

impl DelayBumpReasons {
    #[inline]
    pub fn delay(&mut self) -> bool {
        if self.bypass {
            return false;
        }
        if self.limit != 0 {
            self.limit -= 1;
            true
        } else {
            false
        }
    }
    #[inline]
    pub fn bump_delay(&mut self) {
        self.interval += (self.interval < i64::MAX) as i64;
        self.limit = self.interval;
    }
    #[inline]
    pub fn reduce_delay(&mut self) {
        if self.interval == 0 {
            return;
        }
        self.interval /= 2;
        self.limit = self.interval;
    }
    #[inline]
    pub fn bypass_delay(&mut self) {
        self.bypass = true;
    }
    #[inline]
    pub fn unbypass_delay(&mut self) {
        self.bypass = false;
    }
}

/// `Delay` as declared in `limit.hpp` (not the one in `delay.hpp`).
#[derive(Clone, Copy, Debug, Default)]
pub struct Delay {
    pub bumpreasons: DelayBumpReasons,
}

#[derive(Clone, Copy, Debug, Default)]
pub struct LastPropagations {
    pub propagations: i64,
}
#[derive(Clone, Copy, Debug, Default)]
pub struct LastTicks {
    pub ticks: i64,
}
#[derive(Clone, Copy, Debug, Default)]
pub struct LastElim {
    pub fixed: i64,
    pub subsumephases: i64,
    pub marked: i64,
}
#[derive(Clone, Copy, Debug, Default)]
pub struct LastReductions {
    pub reductions: i64,
}
#[derive(Clone, Copy, Debug, Default)]
pub struct LastConflicts {
    pub conflicts: i64,
}
#[derive(Clone, Copy, Debug, Default)]
pub struct LastTernary {
    pub ticks: i64,
    pub marked: i64,
}
#[derive(Clone, Copy, Debug, Default)]
pub struct LastFixed {
    pub fixed: i64,
}
#[derive(Clone, Copy, Debug, Default)]
pub struct LastFactor {
    pub marked: i64,
    pub ticks: i64,
}
#[derive(Clone, Copy, Debug, Default)]
pub struct LastStabilize {
    pub conflicts: i64,
    pub ticks: i64,
    pub rephased: i64,
}
#[derive(Clone, Copy, Debug, Default)]
pub struct LastIncrementalDecay {
    pub last_id: i64,
}

/// `Last`: statistics at last occurrence (zero initialized).
#[derive(Clone, Copy, Debug, Default)]
pub struct Last {
    pub transred: LastPropagations,
    pub backbone: LastTicks,
    pub probe: LastTicks,
    pub sweep: LastTicks,
    pub vivify: LastTicks,
    pub walk: LastTicks,
    pub elim: LastElim,
    pub inprobe: LastReductions,
    pub reduce: LastConflicts,
    pub rephase: LastConflicts,
    pub ternary: LastTernary,
    pub collect: LastFixed,
    pub factor: LastFactor,
    pub stabilize: LastStabilize,
    pub incremental_decay: LastIncrementalDecay,
}

impl Last {
    pub fn new() -> Last {
        Last::default()
    }
}

/// `Inc`: increments on limits.
#[derive(Clone, Copy, Debug)]
pub struct Inc {
    /// Flushing interval in terms of conflicts.
    pub flush: i64,
    /// Base ticks limit after first mode switch.
    pub stabilize: i64,
    /// Next conflict limit if non-negative.
    pub conflicts: i64,
    /// Next decision limit if non-negative.
    pub decisions: i64,
    /// Next ticks limit if non-negative.
    pub ticks: i64,
    /// Next preprocessing limit if non-negative.
    pub preprocessing: i64,
    /// Next local search limit if non-negative.
    pub localsearch: i64,
}

impl Inc {
    pub fn new() -> Inc {
        Inc {
            flush: 0,
            stabilize: 0,
            conflicts: -1, // unlimited
            decisions: -1,
            ticks: -1,
            preprocessing: 0,
            localsearch: 0,
        }
    }
}

impl Default for Inc {
    fn default() -> Self {
        Inc::new()
    }
}

/// `SET_EFFORT_LIMIT (LIMIT, NAME, THRESHHOLD)`.  Expands to a statement
/// declaring `let $limit: i64` in the caller.  Returns `false` from the
/// enclosing function if the threshold check fails (as the C++ macro).
///
/// Usage: `set_effort_limit!(self, limit, probe, true);`  The threshold
/// argument must be a `bool` expression (C++ passes `stats.factor` in one
/// place, write `self.stats.factor != 0`).
#[macro_export]
macro_rules! set_effort_limit {
    ($internal:expr, $limit:ident, $name:ident, $threshhold:expr) => {
        let $limit: i64;
        {
            let old_limit: i64 = $internal.stats.ticks.$name;
            let ticks: i64 = $internal.stats.ticks.search[0] + $internal.stats.ticks.search[1];
            let last: i64 = $internal.last.$name.ticks;
            let mut reference: i64 = ticks - last;
            if reference == 0 || $internal.stats.conflicts == 0 {
                verbose!($internal, 2, "last {} current {} delta {}", last, ticks, reference);
                reference = $internal.opts.preprocessinit as i64;
            }
            let (__effort_opt, __thresh_opt) = $crate::__effort_thresh!($internal, $name);
            let effort: f64 = __effort_opt as f64 * 1e-3;
            let delta: i64 = (effort * reference as f64) as i64;
            let thresh: i64 = __thresh_opt as i64 * $internal.clauses.len() as i64;
            if $threshhold && delta < thresh {
                verbose!(
                    $internal,
                    2,
                    "delaying {} with ticklimit {} and threshhold {}",
                    stringify!($name),
                    delta,
                    thresh
                );
                return false;
            }
            $internal.last.$name.ticks = ticks;
            let new_limit: i64 = old_limit + delta;
            $limit = new_limit;
            verbose!(
                $internal,
                2,
                "new ticks limit {}= {} + {} * {}",
                new_limit,
                old_limit,
                $crate::format::fmt_f(effort, 6),
                reference
            );
        }
    };
}

/// Maps `NAME` to `(opts.NAME##effort, opts.NAME##thresh)` (no token
/// pasting in `macro_rules`).
#[doc(hidden)]
#[macro_export]
macro_rules! __effort_thresh {
    ($i:expr, backbone) => {
        ($i.opts.backboneeffort, $i.opts.backbonethresh)
    };
    ($i:expr, factor) => {
        ($i.opts.factoreffort, $i.opts.factorthresh)
    };
    ($i:expr, sweep) => {
        ($i.opts.sweepeffort, $i.opts.sweepthresh)
    };
    ($i:expr, probe) => {
        ($i.opts.probeeffort, $i.opts.probethresh)
    };
    ($i:expr, ternary) => {
        ($i.opts.ternaryeffort, $i.opts.ternarythresh)
    };
    ($i:expr, vivify) => {
        ($i.opts.vivifyeffort, $i.opts.vivifythresh)
    };
}

/*------------------------------------------------------------------------*/

// Port of 'limit.cpp'.

impl Internal {
    pub fn scale(&self, v: f64) -> f64 {
        let ratio = self.clause_variable_ratio();
        let factor = if ratio <= 2.0 { 1.0 } else { ratio.ln() / 2f64.ln() };
        let mut res = factor * v;
        if res < 1.0 {
            res = 1.0;
        }
        res
    }

    pub fn limit_terminate(&mut self, l: i32) {
        if l <= 0 && self.lim.terminate.forced == 0 {
            log!(self, "keeping unbounded terminate limit");
        } else if l <= 0 {
            log!(self, "reset terminate limit to be unbounded");
            self.lim.terminate.forced = 0;
        } else {
            self.lim.terminate.forced = l;
            log!(self, "new terminate limit of {} calls", l);
        }
    }

    pub fn limit_conflicts(&mut self, l: i32) {
        if l < 0 && self.inc.conflicts < 0 {
            log!(self, "keeping unbounded conflict limit");
        } else if l < 0 {
            log!(self, "reset conflict limit to be unbounded");
            self.inc.conflicts = -1;
        } else {
            self.inc.conflicts = l as i64;
            log!(self, "new conflict limit of {} conflicts", l);
        }
    }

    pub fn limit_decisions(&mut self, l: i32) {
        if l < 0 && self.inc.decisions < 0 {
            log!(self, "keeping unbounded decision limit");
        } else if l < 0 {
            log!(self, "reset decision limit to be unbounded");
            self.inc.decisions = -1;
        } else {
            self.inc.decisions = l as i64;
            log!(self, "new decision limit of {} decisions", l);
        }
    }

    pub fn limit_ticks(&mut self, l: i64) {
        if l < 0 && self.inc.ticks < 0 {
            log!(self, "keeping unbounded ticks limit");
        } else if l < 0 {
            log!(self, "reset ticks limit to be unbounded");
            self.inc.ticks = -1;
        } else {
            self.inc.ticks = l;
            log!(self, "new ticks limit of {} ticks", l);
        }
    }

    pub fn limit_preprocessing(&mut self, l: i32) {
        if l < 0 {
            log!(self, "ignoring invalid preprocessing limit {}", l);
        } else if l == 0 {
            log!(self, "reset preprocessing limit to no preprocessing");
            self.inc.preprocessing = 0;
        } else {
            self.inc.preprocessing = l as i64;
            log!(self, "new preprocessing limit of {} preprocessing rounds", l);
        }
    }

    pub fn limit_local_search(&mut self, l: i32) {
        if l < 0 {
            log!(self, "ignoring invalid local search limit {}", l);
        } else if l == 0 {
            log!(self, "reset local search limit to no local search");
            self.inc.localsearch = 0;
        } else {
            self.inc.localsearch = l as i64;
            log!(self, "new local search limit of {} local search rounds", l);
        }
    }

    pub fn is_valid_limit(name: &str) -> bool {
        matches!(
            name,
            "terminate" | "conflicts" | "decisions" | "preprocessing" | "localsearch" | "ticks"
        )
    }

    pub fn limit(&mut self, name: &str, l: i32) -> bool {
        let mut res = true;
        match name {
            "terminate" => self.limit_terminate(l),
            "conflicts" => self.limit_conflicts(l),
            "decisions" => self.limit_decisions(l),
            "preprocessing" => self.limit_preprocessing(l),
            "localsearch" => self.limit_local_search(l),
            "ticks" => self.limit_ticks(l as i64),
            _ => res = false,
        }
        res
    }

    pub fn reset_limits(&mut self) {
        log!(self, "reset limits");
        self.limit_terminate(0);
        self.limit_conflicts(-1);
        self.limit_decisions(-1);
        self.limit_preprocessing(0);
        self.limit_local_search(0);
        self.limit_ticks(-1);
    }
}

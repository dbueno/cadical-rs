//! Port of `restart.cpp`.

#[allow(unused_imports)]
use crate::prelude::*;

impl Internal {
    // As observed by Chanseok Oh and implemented in MapleSAT solvers too,
    // various mostly satisfiable instances benefit from long quiet phases
    // with less or almost no restarts.  We implement this idea by
    // prohibiting the Glucose style restart scheme in a geometric fashion,
    // which is very similar to how originally restarts were scheduled in
    // MiniSAT and earlier solvers.  We start with say 1e3 = 1000
    // (opts.stabilizeinit) conflicts of Glucose restarts.  Then in a
    // "stabilizing" phase we disable these until 1e4 = 2000 conflicts (if
    // 'opts.stabilizefactor' is '200' percent) have passed. After that we
    // switch back to regular Glucose style restarts until again 2 times
    // more conflicts than the previous limit are reached.  Actually, in the
    // latest version we still restarts during stabilization but only in a
    // reluctant doubling scheme with a rather high interval.

    pub fn stabilizing(&mut self) -> bool {
        if self.opts.stabilize == 0 {
            return false;
        }
        if self.stable && self.opts.stabilizeonly != 0 {
            return true;
        }
        if self.inc.stabilize == 0 {
            debug_assert!(!self.stable);
            if self.stats.conflicts <= self.lim.stabilize {
                return false;
            }
        } else if self.stats.ticks.search[self.stable as usize] <= self.lim.stabilize {
            return self.stable;
        }
        self.report(if self.stable { b']' } else { b'}' }, 0);
        if self.stable {
            stop!(self, stable);
        } else {
            stop!(self, unstable);
        }

        let stable = self.stable as usize;
        debug_assert!(self.last.stabilize.ticks >= 0);
        debug_assert!(
            self.last.stabilize.conflicts >= 0 && self.last.stabilize.conflicts <= self.stats.conflicts
        );
        debug_assert!(self.last.stabilize.ticks <= self.stats.ticks.search[stable]);
        let delta_ticks = self.stats.ticks.search[stable] - self.last.stabilize.ticks;
        let delta_conflicts = self.stats.conflicts - self.last.stabilize.conflicts;
        let current_mode = if self.stable { "stable" } else { "unstable" };
        let next_mode = if self.stable { "unstable" } else { "stable" };
        phase!(
            self,
            "stabilizing",
            self.stats.stabphases,
            "reached {} stabilization limit {} after {} conflicts and {} ticks at {} conflicts and {} ticks",
            current_mode,
            self.lim.stabilize,
            delta_conflicts,
            delta_ticks,
            self.stats.conflicts,
            self.stats.ticks.search[stable]
        );
        if self.inc.stabilize == 0 {
            self.inc.stabilize = delta_ticks;
        }
        if self.inc.stabilize == 0 {
            // rare occurence in incremental calls requiring no ticks
            self.inc.stabilize = 1;
        }

        let mut next_delta_ticks = self.inc.stabilize;
        let stabphases = self.stats.stabphases + 1;
        next_delta_ticks *= stabphases * stabphases;

        let next_stable = (!self.stable) as usize;
        self.lim.stabilize = self.stats.ticks.search[next_stable] + next_delta_ticks;
        self.last.stabilize.ticks = self.stats.ticks.search[next_stable];
        if self.lim.stabilize <= self.stats.ticks.search[next_stable] {
            self.lim.stabilize = self.stats.ticks.search[next_stable] + 1;
        }
        phase!(
            self,
            "stabilizing",
            self.stats.stabphases,
            "next {} stabilization limit {} at ticks interval {}",
            next_mode,
            self.lim.stabilize,
            next_delta_ticks
        );

        self.stable = !self.stable; // Switch!!!!!

        if self.stable {
            self.stats.stabphases += 1;
        }

        self.swap_averages();
        self.report(if self.stable { b'[' } else { b'{' }, 0);
        if self.stable {
            start!(self, stable);
        } else {
            start!(self, unstable);
        }
        self.stable
    }

    // Restarts are scheduled by a variant of the Glucose scheme as
    // presented in our POS'15 paper using exponential moving averages.
    // There is a slow moving average of the average recent glucose level
    // of learned clauses as well as a fast moving average of those glues.
    // If the end of a base restart conflict interval has passed and the
    // fast moving average is above a certain margin over the slow moving
    // average then we restart.

    pub fn restarting(&mut self) -> bool {
        if self.opts.restart == 0 {
            return false;
        }
        if (self.level as usize) < self.assumptions.len() + 2 {
            return false;
        }
        if self.stabilizing() && self.opts.reluctant != 0 {
            return self.reluctant.triggered();
        }
        if self.stats.conflicts <= self.lim.restart {
            return false;
        }
        let f = self.averages.current.glue.fast.value();
        let p = if self.stable { self.opts.restartmarginstable } else { self.opts.restartmarginfocused };
        let m = (100.0 + p as f64) / 100.0;
        let s = self.averages.current.glue.slow.value();
        let l = m * s;

        let c = if l > f {
            '>'
        } else if l < f {
            '<'
        } else {
            '='
        };
        verbose!(
            self,
            3,
            "restart glue limit {} = {} * {} (slow glue) {} {} (fast glue)",
            crate::format::fmt_g(l),
            crate::format::fmt_f(m, 2),
            crate::format::fmt_g(s),
            c,
            crate::format::fmt_g(f)
        );

        l <= f
    }

    // This is Marijn's reuse trail idea.  Instead of always backtracking
    // to the top we figure out which decisions will be made again anyhow
    // and only backtrack to the level of the last such decision or to the
    // top if no such decision exists top (in which case we do not reuse
    // any level).

    pub fn reuse_trail(&mut self) -> i32 {
        let asize = self.assumptions.len();
        let trivial_decisions: i32 = asize as i32
            // Plus 1 if the constraint is satisfied via implications of
            // assumptions and a pseudo-decision level was introduced.
            + (self.control[asize + 1].decision == 0) as i32;
        if self.opts.restartreusetrail == 0 {
            return trivial_decisions;
        }
        let next_decision = self.next_decision_variable();
        debug_assert!(1 <= next_decision);
        let mut res = trivial_decisions;
        if self.use_scores() {
            let less = self.scores.less;
            while res < self.level {
                let decision = self.control[(res + 1) as usize].decision;
                if decision != 0 && less.less(decision.unsigned_abs(), next_decision as u32) {
                    break;
                }
                res += 1;
            }
        } else {
            let limit = self.bumped(next_decision);
            while res < self.level {
                let decision = self.control[(res + 1) as usize].decision;
                if decision != 0 && self.bumped(decision) < limit {
                    break;
                }
                res += 1;
            }
        }
        let reused = res - trivial_decisions;
        if reused > 0 {
            self.stats.reused += 1;
            self.stats.reusedlevels += reused as i64;
            if self.stable {
                self.stats.reusedstable += 1;
            }
        }
        res
    }

    pub fn restart(&mut self) {
        start!(self, restart);
        self.stats.restarts += 1;
        self.stats.restartlevels += self.level as i64;
        if self.stable {
            self.stats.restartstable += 1;
        }
        log!(self, "restart {}", self.stats.restarts);
        let l = self.reuse_trail();
        self.backtrack(l);

        self.lim.restart = self.stats.conflicts + self.opts.restartint as i64;
        log!(self, "new restart limit at {} conflicts", self.lim.restart);

        self.report(b'R', 2);
        stop!(self, restart);
    }
}

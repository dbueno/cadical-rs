//! Port of `reduce.cpp`.

#[allow(unused_imports)]
use crate::prelude::*;

use std::cmp::Ordering;

/*------------------------------------------------------------------------*/

// Clauses of larger glue or larger size are considered less useful.
//
// We also follow the observations made by the Glucose team in their
// IJCAI'09 paper and keep all low glue clauses limited by
// 'options.keepglue' (typically '2').
//
// In earlier versions we pre-computed a 64-bit sort key per clause and
// wrapped a pointer to the clause and the 64-bit sort key into a separate
// data structure for sorting.  This was probably faster but awkward and
// so we moved back to a simpler scheme which also uses 'stable_sort'
// instead of 'rsort' below.  Sorting here is not a hot-spot anyhow.

#[inline]
fn reduce_less_useful(c: &CRef, d: &CRef) -> bool {
    if c.glue() > d.glue() {
        return true;
    }
    if c.glue() < d.glue() {
        return false;
    }
    c.size() > d.size()
}

impl Internal {
    // Once in a while we reduce, e.g., we remove learned clauses which are
    // supposed to be less useful in the future.  This is done in
    // increasing intervals, which has the effect of allowing more and more
    // learned clause to be kept for a longer period.  The number of learned
    // clauses kept in memory corresponds to an upper bound on the 'space'
    // of a resolution proof needed to refute a formula in proof complexity
    // sense.

    pub fn reducing(&mut self) -> bool {
        if self.opts.reduce == 0 {
            return false;
        }
        if self.stats.current.redundant == 0 {
            return false;
        }
        self.stats.conflicts >= self.lim.reduce
    }

    /*--------------------------------------------------------------------*/

    // Even less regularly we are flushing all redundant clauses.

    pub fn flushing(&mut self) -> bool {
        if self.opts.flush == 0 {
            return false;
        }
        self.stats.conflicts >= self.lim.flush
    }

    /*--------------------------------------------------------------------*/

    pub fn mark_clauses_to_be_flushed(&mut self) {
        let tier1limit = self.tier1[0];
        let tier2limit = std::cmp::max(tier1limit, self.tier2[0]);
        for i in 0..self.clauses.len() {
            let c = self.clauses[i];
            if !c.redundant() {
                continue; // keep irredundant
            }
            if c.garbage() {
                continue; // already marked as garbage
            }
            if c.reason() {
                continue; // need to keep reasons
            }
            let used = c.used();
            if used != 0 {
                c.set_used(used - 1);
            }
            if c.glue() <= tier1limit && used != 0 {
                continue;
            }
            if c.glue() <= tier2limit && used >= Internal::MAX_USED - 1 {
                continue;
            }
            self.mark_garbage(c); // flush unused clauses
            if c.hyper() {
                self.stats.flush.hyper += 1;
            } else {
                self.stats.flush.learned += 1;
            }
        }
        // No change to 'lim.kept{size,glue}'.
    }

    /*--------------------------------------------------------------------*/

    // This function implements the important reduction policy. It
    // determines which redundant clauses are considered not useful and
    // thus will be collected in a subsequent garbage collection phase.

    pub fn mark_useless_redundant_clauses_as_garbage(&mut self) {
        // We use a separate stack for sorting candidates for removal.  This
        // uses (slightly) more memory but has the advantage to keep the
        // relative order in 'clauses' intact, which actually due to using
        // stable sorting goes into the candidate selection (more recently
        // learned clauses are kept if they otherwise have the same glue and
        // size).

        let mut stack: Vec<CRef> = Vec::new();
        let tier1limit = self.tier1[0];
        let tier2limit = std::cmp::max(tier1limit, self.tier2[0]);

        stack.reserve(self.stats.current.redundant as usize);

        for i in 0..self.clauses.len() {
            let c = self.clauses[i];
            if !c.redundant() {
                continue; // Keep irredundant.
            }
            if c.garbage() {
                continue; // Skip already marked.
            }
            if c.reason() {
                continue; // Need to keep reasons.
            }
            let used = c.used();
            if used != 0 {
                c.set_used(used - 1);
            }
            if c.glue() <= tier1limit && used != 0 {
                continue;
            }
            if c.glue() <= tier2limit && used >= Internal::MAX_USED - 1 {
                continue;
            }
            if c.hyper() {
                // Hyper binary and ternary resolvents
                debug_assert!(c.size() <= 3); // are only kept for one reduce round
                if used == 0 {
                    self.mark_garbage(c); // unless
                }
                continue; //  used recently.
            }
            stack.push(c);
        }

        // 'std::stable_sort' (the result of a stable sort is unique).
        stack.sort_by(|a, b| {
            if reduce_less_useful(a, b) {
                Ordering::Less
            } else if reduce_less_useful(b, a) {
                Ordering::Greater
            } else {
                Ordering::Equal
            }
        });
        let mut target = (1e-2 * self.opts.reducetarget as f64 * stack.len() as f64) as usize;

        // This is defensive code, which I usually consider a bug, but here I
        // am just not sure that using floating points in the line above is
        // precise in all situations and instead of figuring that out, I just
        // use this.
        //
        if target > stack.len() {
            target = stack.len();
        }

        phase!(
            self,
            "reduce",
            self.stats.reductions,
            "reducing {} clauses {}%",
            target,
            crate::format::fmt_f(percent(target as f64, self.stats.current.redundant as f64), 0)
        );

        let t = target;
        for i in 0..t {
            let c = stack[i];
            log!(self, c, "marking useless to be collected");
            self.mark_garbage(c);
            self.stats.reduced += 1;
        }

        self.lim.keptglue = 0;
        self.lim.keptsize = 0;

        for i in t..stack.len() {
            let c = stack[i];
            log!(self, c, "keeping");
            if c.size() > self.lim.keptsize {
                self.lim.keptsize = c.size();
            }
            if c.glue() > self.lim.keptglue {
                self.lim.keptglue = c.glue();
            }
        }

        erase_vector(&mut stack);

        phase!(
            self,
            "reduce",
            self.stats.reductions,
            "maximum kept size {} glue {}",
            self.lim.keptsize,
            self.lim.keptglue
        );
    }

    /*--------------------------------------------------------------------*/

    // If chronological backtracking produces out-of-order assigned units,
    // then it is necessary to completely propagate them at the root level
    // in order to derive all implied units.  Otherwise the blocking
    // literals in 'flush_watches' are messed up and assertion 'FW1' fails.

    pub fn propagate_out_of_order_units(&mut self) -> bool {
        if self.level == 0 {
            return true;
        }
        let mut oou = 0;
        let mut i = self.control[1].trail as usize;
        while oou == 0 && i < self.trail.len() {
            let lit = self.trail[i];
            debug_assert!(self.val(lit) > 0);
            if self.var(lit).level != 0 {
                i += 1;
                continue;
            }
            log!(self, "found out-of-order assigned unit {}", oou);
            oou = lit;
            i += 1;
        }
        if oou == 0 {
            return true;
        }
        self.backtrack(0);
        if self.propagate() {
            return true;
        }
        self.learn_empty_clause();
        false
    }

    /*--------------------------------------------------------------------*/

    // reduction is scheduled with reduceint, reducetarget and reduceopt.
    // with reduceopt=1 the number of learnt clauses scale with sqrt of
    // conflicts times reduceint the scaling is the same as with
    // reduceopt=0 (the classical default) however, the constants are
    // different. To avoid this (and get roughly the same behaviour with
    // reduceopt=0 and reduceopt=1) we need to scale the interval, namely
    // (reduceint^2/2) Lastly, reduceopt=2 just replaces sqrt conflicts with
    // log conflicts.  The learnt clauses should not be bigger than
    // 1/reducetarget * reduceint * function (conflicts) for function being
    // log if reduceint=2 an sqrt otherwise.  This is however only the
    // theoretical target and second chance for tier2 clauses and very long
    // lifespan of tier1 clauses (through used flag) make this behave
    // differently.  reduceinit shifts the curve to the right, increasing
    // the number of clauses in the solver. This impact will decrease over
    // time.

    pub fn reduce(&mut self) {
        start!(self, reduce);

        self.stats.reductions += 1;
        self.report(b'.', 1);

        let flush = self.flushing();
        if flush {
            self.stats.flush.count += 1;
        }

        'done: {
            if !self.propagate_out_of_order_units() {
                break 'done;
            }

            self.mark_satisfied_clauses_as_garbage();
            self.protect_reasons();
            if flush {
                self.mark_clauses_to_be_flushed();
            } else {
                self.mark_useless_redundant_clauses_as_garbage();
            }
            self.garbage_collection();

            {
                let mut delta: i64 = self.opts.reduceint as i64;
                let mut factor: f64 = (self.stats.reductions + 1) as f64;
                if self.opts.reduceopt == 0 {
                    // adjust delta such this is the same as reduceopt=1
                    delta = delta * delta / 2;
                } else if self.opts.reduceopt == 1 {
                    // this is the same as reduceopt=0 if reduceint = sqrt
                    // (reduceint) = 17
                    factor = (self.stats.conflicts as f64).sqrt();
                } else if self.opts.reduceopt == 2 {
                    // log scaling instead
                    factor = (self.stats.conflicts as f64).ln();
                }
                if factor < 1.0 {
                    factor = 1.0;
                }
                delta = (delta as f64 * factor) as i64;
                if self.irredundant() as f64 > 1e5 {
                    delta = (delta as f64 * ((self.irredundant() as f64 / 1e4).ln() / (10f64).ln())) as i64;
                }
                if delta < 1 {
                    delta = 1;
                }
                self.lim.reduce = self.stats.conflicts + delta;
                phase!(
                    self,
                    "reduce",
                    self.stats.reductions,
                    "new reduce limit {} after {} conflicts",
                    self.lim.reduce,
                    delta
                );
            }

            if flush {
                phase!(self, "flush", self.stats.flush.count, "new flush increment {}", self.inc.flush);
                self.inc.flush *= self.opts.flushfactor as i64;
                self.lim.flush = self.stats.conflicts + self.inc.flush;
                phase!(self, "flush", self.stats.flush.count, "new flush limit {}", self.lim.flush);
            }

            self.last.reduce.conflicts = self.stats.conflicts;
        }

        // DONE:

        self.report(if flush { b'f' } else { b'-' }, 0);
        stop!(self, reduce);
    }
}

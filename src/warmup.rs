//! Port of `warmup.cpp`.
//!
//! The idea of warmup is to reuse the strength of CDCL, namely
//! propagating, before calling random walk that is not good at
//! propagating long chains. Therefore, we propagate (ignoring all
//! conflicts) discovered along the way.  The assignment is the same as the
//! normal assignment however, it updates the target phases so that local
//! search can pick them up later.

#[allow(unused_imports)]
use crate::prelude::*;
use crate::util::sign;

impl Internal {
    /// Specific warmup version with saving of the target.
    #[inline]
    pub fn warmup_assign(&mut self, lit: i32, reason: CRef) {
        debug_assert!(self.level != 0); // no need to learn unit clauses here
        self.require_mode(Mode::SEARCH);

        let idx = self.vidx(lit);
        debug_assert!(reason != self.external_reason);
        debug_assert!(self.val(idx) == 0);
        debug_assert!(!self.flags(idx).eliminated() || reason == Internal::decision_reason());
        debug_assert!(!self.searching_lucky_phases);
        debug_assert!(self.lrat_chain.is_empty());
        debug_assert!(
            !(reason == self.external_reason
                && ((self.level as usize)
                    <= self.assumptions.len() + (!self.constraint.is_empty()) as usize))
        );
        debug_assert!(!reason.is_null());
        debug_assert!(self.level != 0 || reason == Internal::decision_reason());
        // we  purely assign in order here
        let lit_level = self.level;

        let trail_size = self.trail.len() as i32;
        {
            let v = self.var_mut(idx);
            v.level = lit_level;
            v.trail = trail_size;
            v.reason = reason;
        }
        debug_assert!((self.num_assigned as i32) < self.max_var);
        debug_assert!(self.num_assigned == self.trail.len());
        self.num_assigned += 1;
        let tmp = sign(lit) as i8;
        self.phases.saved[idx as usize] = tmp;
        self.set_val(idx, tmp);
        debug_assert!(self.val(lit) > 0);
        debug_assert!(self.val(-lit) < 0);

        self.trail.push(lit);
        #[cfg(feature = "logging")]
        {
            if lit_level == 0 {
                log!(self, "root-level unit assign {} @ 0", lit);
            } else {
                log!(self, reason, "search assign {} @ {}", lit, lit_level);
            }
        }

        debug_assert!(self.watching());
        // (C++ prefetches the first watch of '-lit' here.)
    }

    pub fn warmup_propagate_beyond_conflict(&mut self) {
        debug_assert!(!self.unsat);

        start!(self, propagate);
        debug_assert!(self.ignore.is_null());

        let before = self.propagated as i64;

        while self.propagated != self.trail.len() {
            let lit = -self.trail[self.propagated];
            self.propagated += 1;
            log!(self, "propagating {}", -lit);

            // The watch list of 'lit' is only modified through the 'j' and
            // 'i' positions below ('watch_literal' adds watches to other
            // literals and 'warmup_assign' does not touch watches), thus
            // re-indexing is equivalent to keeping the C++ reference.
            let eow = self.watches(lit).len();
            let mut j = 0usize;
            let mut i = 0usize;

            while i != eow {
                let w = self.watches(lit)[i];
                self.watches_mut(lit)[j] = w;
                i += 1;
                j += 1;
                let b = self.val(w.blit);

                if b > 0 {
                    continue; // blocking literal satisfied
                }

                if w.binary() {
                    // Binary clauses are treated separately since they do
                    // not require to access the clause at all (see
                    // 'propagate.cpp' for the discussion of garbage binary
                    // clauses).

                    if b < 0 {
                        // ignoring conflict
                        self.stats.warmup.conflicts += 1;
                    } else {
                        self.warmup_assign(w.blit, w.clause);
                    }
                } else {
                    let c = w.clause;
                    debug_assert!(c.size() > 2);

                    // The cache line with the clause data is forced to be
                    // loaded here and thus this first memory access below is
                    // the real hot-spot of the solver.

                    if c.garbage() {
                        j -= 1;
                        continue;
                    }
                    let other = c.lit(0) ^ c.lit(1) ^ lit;
                    let u = self.val(other);
                    if u > 0 {
                        self.watches_mut(lit)[j - 1].blit = other;
                    } else {
                        let size = c.size() as usize;
                        let end = size;
                        let middle = c.pos() as usize;
                        let mut k = middle;
                        let mut v: i8 = -1;
                        let mut r: i32 = 0;
                        while k != end && {
                            r = c.lit(k);
                            v = self.val(r);
                            v < 0
                        } {
                            k += 1;
                        }
                        if v < 0 {
                            k = 2;
                            debug_assert!(c.pos() as usize <= size);
                            while k != middle && {
                                r = c.lit(k);
                                v = self.val(r);
                                v < 0
                            } {
                                k += 1;
                            }
                        }

                        c.set_pos(k as i32); // always save position

                        debug_assert!(2 <= k);
                        debug_assert!(k <= size);

                        if v > 0 {
                            // Replacement satisfied, so just replace 'blit'.

                            self.watches_mut(lit)[j - 1].blit = r;
                        } else if v == 0 {
                            // Found new unassigned replacement literal to be
                            // watched.

                            log!(self, c, "unwatch {} in", lit);

                            c.set_lit(0, other);
                            c.set_lit(1, r);
                            c.set_lit(k, lit);

                            self.watch_literal(r, lit, c);

                            j -= 1; // Drop this watch from the watch list of 'lit'.
                        } else if u == 0 {
                            debug_assert!(v < 0);

                            // The other watch is unassigned ('!u') and all
                            // other literals assigned to false (still 'v <
                            // 0'), thus we found a unit.
                            //
                            self.build_chain_for_units(other, c, false);
                            self.warmup_assign(other, c);
                        } else {
                            debug_assert!(u < 0);
                            debug_assert!(v < 0);

                            // ignoring conflict
                            self.stats.warmup.conflicts += 1;
                        }
                    }
                }
            }

            if j != i {
                self.watches_mut(lit).truncate(j);
            }
        }

        debug_assert!(self.propagated == self.trail.len());

        self.stats.warmup.propagated += self.trail.len() as i64 - before;
        stop!(self, propagate);
    }

    pub fn warmup_decide(&mut self) -> i32 {
        debug_assert!(!self.satisfied());
        start!(self, decide);
        let mut res = 0;
        if (self.level as usize) < self.assumptions.len() {
            let lit = self.assumptions[self.level as usize];
            debug_assert!(self.assumed(lit));
            let tmp = self.val(lit);
            if tmp < 0 {
                log!(self, "assumption {} falsified", lit);
                res = 20;
            } else if tmp > 0 {
                log!(self, "assumption {} already satisfied", lit);
                self.new_trail_level(0);
                log!(self, "added pseudo decision level");
                self.notify_decision();
            } else {
                log!(self, "deciding assumption {}", lit);
                self.search_assume_decision(lit);
            }
        } else if (self.level as usize) == self.assumptions.len() && !self.constraint.is_empty() {
            let mut satisfied_lit = 0; // The literal satisfying the constrain.
            let mut unassigned_lit = 0; // Highest score unassigned literal.
            let mut previous_lit = 0; // Move satisfied literals to the front.

            let size_constraint = self.constraint.len();

            #[cfg(debug_assertions)]
            let mut sum: u32 = 0;
            #[cfg(debug_assertions)]
            for &lit in self.constraint.iter() {
                sum = sum.wrapping_add(lit as u32);
            }
            for i in 0..size_constraint {
                // Get literal and move 'constraint[i] = constraint[i-1]'.

                let lit = self.constraint[i];
                self.constraint[i] = previous_lit;
                previous_lit = lit;

                let tmp = self.val(lit);
                if tmp < 0 {
                    log!(self, "constraint literal {} falsified", lit);
                    continue;
                }

                if tmp > 0 {
                    log!(self, "constraint literal {} satisfied", lit);
                    satisfied_lit = lit;
                    break;
                }

                debug_assert!(tmp == 0);
                log!(self, "constraint literal {} unassigned", lit);

                if unassigned_lit == 0 || self.better_decision(lit, unassigned_lit) {
                    unassigned_lit = lit;
                }
            }

            if satisfied_lit != 0 {
                self.constraint[0] = satisfied_lit; // Move satisfied to the front.

                log!(
                    self,
                    "literal {} satisfies constraint and is implied by assumptions",
                    satisfied_lit
                );

                self.new_trail_level(0);
                log!(self, "added pseudo decision level for constraint");
                self.notify_decision();
            } else {
                // Just move all the literals back.  If we found an
                // unsatisfied literal then it will be satisfied (most likely)
                // at the next decision and moved then to the first position.

                if size_constraint != 0 {
                    let mut i = 0;
                    while i + 1 != size_constraint {
                        self.constraint[i] = self.constraint[i + 1];
                        i += 1;
                    }

                    self.constraint[size_constraint - 1] = previous_lit;
                }

                if unassigned_lit != 0 {
                    log!(self, "deciding {} to satisfy constraint", unassigned_lit);
                    self.search_assume_decision(unassigned_lit);
                } else {
                    log!(self, "failing constraint");
                    self.unsat_constraint = true;
                    res = 20;
                }
            }

            #[cfg(debug_assertions)]
            {
                for &lit in self.constraint.iter() {
                    sum = sum.wrapping_sub(lit as u32);
                }
                debug_assert!(sum == 0); // Checksum of literal should not change!
            }
        } else {
            let target = self.stable || self.opts.target == 2;
            self.stats.warmup.decision += 1;
            let idx = self.next_decision_variable();
            if self.flags(idx).eliminated() {
                self.stats.warmup.dummydecision += 1;
            }
            let decision = self.decide_phase(idx, target);
            self.new_trail_level(decision);
            self.warmup_assign(decision, Internal::decision_reason());
            self.notify_decision();
        }
        if res != 0 {
            self.marked_failed = false;
        }
        stop!(self, decide);
        res
    }

    pub fn warmup(&mut self) -> i32 {
        debug_assert!(!self.unsat);
        debug_assert!(self.level == 0);
        if self.opts.warmup == 0 {
            return 0;
        }
        self.require_mode(Mode::WALK);
        start!(self, warmup);
        self.stats.warmup.count += 1;
        let mut res = 0;

        let warmup_propagated = self.stats.warmup.propagated;
        let decision = self.stats.warmup.decision;
        let dummydecision = self.stats.warmup.dummydecision;
        // first propagate assumptions in case we find a conflict. One subtle
        // thing, if we find a conflict in the assumption, then we actually
        // do need the notifications. Otherwise, we there should be no
        // notification at all (not even the `backtrack ()` at the end).
        // Also, we cannot not ignore conflicts at all, meaning that we cannot
        // use our special propagation function, even if it could counts
        // ticks.
        let assms_contraint_level =
            self.assumptions.len() + (!self.constraint.is_empty()) as usize;
        while res == 0
            && (self.level as usize) < assms_contraint_level
            && self.num_assigned < self.max_var as usize
        {
            debug_assert!(self.num_assigned < self.max_var as usize);
            res = self.warmup_decide();
            if !self.propagate() {
                res = 20;
                self.marked_failed = false;
                break;
            }
        }
        let no_backtrack_notification = self.level == 0;

        // now we do not need any notification and can simply propagate
        debug_assert!(res != 0 || self.propagated == self.trail.len());
        debug_assert!(!self.private_steps);
        self.private_steps = true;

        log!(self, "propagating beyond conflicts to warm-up walk");
        while res == 0 && self.num_assigned < self.max_var as usize {
            debug_assert!(self.propagated == self.trail.len());
            res = self.warmup_decide();
            self.warmup_propagate_beyond_conflict();
            log!(self, &self.lrat_chain, "during warmup with lrat chain:");
        }
        debug_assert!(res != 0 || self.num_assigned == self.max_var as usize);
        // constrains with empty levels break this
        // assert (res || stats.warmup.propagated - warmup_propagated ==
        // (int64_t)num_assigned);
        verbose!(
            self,
            3,
            "warming-up needed {} propagations including {} decisions (with {} dummy ones)",
            (self.stats.warmup.propagated - warmup_propagated) as u64,
            (self.stats.warmup.decision - decision) as u64,
            (self.stats.warmup.dummydecision - dummydecision) as u64
        );

        // now we backtrack, notifying only if there was something to
        // notify.
        self.private_steps = no_backtrack_notification;
        if res == 0 {
            self.backtrack_without_updating_phases(0);
        }
        self.private_steps = false;
        stop!(self, warmup);
        self.require_mode(Mode::WALK);
        res
    }
}

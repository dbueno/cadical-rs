//! Port of `subsume.cpp`: global forward subsumption (see the long
//! explanation at the top of `subsume.cpp`).

#[allow(unused_imports)]
use crate::prelude::*;

use crate::congruence::smaller_clause_size_rank;
use crate::format::fmt_f;
use crate::radix::rsort;
use crate::sort::std_sort;
use crate::util::{erase_vector, percent, shrink_vector};

impl Internal {
    // This is the actual subsumption and strengthening check.  We assume
    // that all the literals of the candidate clause to be subsumed or
    // strengthened are marked, so we only have to check that all the
    // literals of the argument clause 'subsuming', which is checked for
    // subsuming the candidate clause 'subsumed', has all its literals marked
    // (in the correct phase).  If exactly one is in the opposite phase we can
    // still strengthen the candidate clause by this single literal which
    // occurs in opposite phase.
    //
    // The result is INT_MIN if all literals are marked and thus the
    // candidate clause can be subsumed.  It is zero if neither subsumption
    // nor strengthening is possible.  Otherwise the candidate clause can be
    // strengthened and as a result the negation of the literal which can be
    // removed is returned.

    #[inline]
    pub fn subsume_check(&mut self, subsuming: CRef, subsumed: CRef) -> i32 {
        // Only use 'subsumed' for these following assertion checks.
        // Otherwise we only require that 'subsumed' has all its literals
        // marked.
        //
        debug_assert!(!subsumed.garbage());
        debug_assert!(!subsuming.garbage());
        debug_assert!(subsuming != subsumed);
        debug_assert!(subsuming.size() <= subsumed.size());
        let _ = subsumed;

        self.stats.subchecks += 1;
        if subsuming.size() == 2 {
            self.stats.subchecks2 += 1;
        }

        let mut flipped = 0;
        let mut prev = 0;
        let mut failed = false;
        let eoc = subsuming.size() as usize;
        let mut i = 0usize;
        while !failed && i != eoc {
            let lit = subsuming.lit(i);
            subsuming.set_lit(i, prev);
            prev = lit;
            let tmp = self.marked(lit);
            if tmp == 0 {
                failed = true;
            } else if tmp > 0 {
                i += 1;
                continue;
            } else if flipped != 0 {
                failed = true;
            } else {
                flipped = lit;
            }
            i += 1;
        }
        debug_assert!(prev != 0);
        debug_assert!(subsuming.lit(0) == 0);
        subsuming.set_lit(0, prev);
        if failed {
            return 0;
        }

        if flipped == 0 {
            i32::MIN // subsumed!!
        } else if self.opts.subsumestr == 0 {
            0
        } else {
            flipped // strengthen!!
        }
    }

    /*------------------------------------------------------------------------*/

    // Candidate clause 'subsumed' is subsumed by 'subsuming'.

    #[inline]
    pub fn subsume_clause(&mut self, subsuming: CRef, subsumed: CRef) {
        self.stats.subsumed += 1;
        debug_assert!(subsuming.size() <= subsumed.size());
        log!(self, subsumed, "subsumed");
        if subsumed.redundant() {
            self.stats.subred += 1;
        } else {
            self.stats.subirr += 1;
        }
        if subsumed.redundant() || !subsuming.redundant() {
            self.mark_garbage(subsumed);
            return;
        }
        log!(self, "turning redundant subsuming clause into irredundant clause");
        subsuming.set_redundant(false);
        if let Some(proof) = self.proof.as_mut() {
            proof.strengthen(subsuming.id());
        }
        self.mark_garbage(subsumed);
        self.stats.current.irredundant += 1;
        self.stats.added.irredundant += 1;
        self.stats.irrlits += subsuming.size() as i64;
        debug_assert!(self.stats.current.redundant > 0);
        self.stats.current.redundant -= 1;
        debug_assert!(self.stats.added.redundant > 0);
        self.stats.added.redundant -= 1;
        // ... and keep 'stats.added.total'.
    }

    /*------------------------------------------------------------------------*/

    // Candidate clause 'c' is strengthened by removing 'lit'.

    pub fn strengthen_clause(&mut self, c: CRef, lit: i32) {
        if self.opts.check != 0 && self.is_external_forgettable(c.id()) {
            self.mark_garbage_external_forgettable(c.id());
        }
        self.stats.strengthened += 1;
        debug_assert!(c.size() > 2);
        log!(self, c, "removing {} in", lit);
        if self.proof.is_some() {
            log!(self, &self.lrat_chain, "strengthening clause with chain");
            let chain = &self.lrat_chain;
            self.proof.as_mut().unwrap().strengthen_clause(c, lit, chain);
        }
        if !c.redundant() {
            self.mark_removed_lit(lit);
        }
        // 'std::remove (c->begin (), c->end (), lit)'.
        let size = c.size() as usize;
        let mut j = 0usize;
        for i in 0..size {
            let other = c.lit(i);
            if other == lit {
                continue;
            }
            c.set_lit(j, other);
            j += 1;
        }
        debug_assert!(j + 1 == size);
        let _ = j;
        let _ = self.shrink_clause(c, c.size() - 1);
        // bump_clause2 (c);
        log!(self, c, "strengthened");
        self.external().check_shrunken_clause(c);
    }

    /*------------------------------------------------------------------------*/

    // Find clauses connected in the occurrence lists 'occs' which subsume the
    // candidate clause 'c' given as first argument.  If this is the case the
    // clause is subsumed and the result is positive.   If the clause was
    // strengthened the result is negative.  Otherwise the candidate clause
    // can not be subsumed nor strengthened and zero is returned.

    #[inline]
    pub fn try_to_subsume_clause(&mut self, c: CRef, shrunken: &mut Vec<CRef>) -> i32 {
        self.stats.subtried += 1;
        debug_assert!(self.level == 0);
        log!(self, c, "trying to subsume");

        self.mark_clause_literals(c); // signed!

        let mut d = CRef::NULL;
        let mut flipped = 0;

        let csize = c.size() as usize;
        for ci in 0..csize {
            let lit = c.lit(ci);

            // Only clauses which have a variable which has recently been
            // added are checked for being subsumed.  The idea is that all
            // these newly added clauses are candidates for subsuming the
            // clause.  Then we also only need to check occurrences of these
            // variables.  The occurrence lists of other literal do not have
            // to be checked.
            //
            if !self.flags(lit).subsume {
                continue;
            }

            let mut sign = -1;
            while d.is_null() && sign <= 1 {
                // First we check against all binary clauses.  The other
                // literals of all binary clauses of 'sign*lit' are stored in
                // one consecutive array, which is way faster than storing
                // clause pointers and dereferencing them.  Since this binary
                // clause array is also not shrunken, we also can bail out
                // earlier if subsumption or strengthening is determined.

                // In both cases the (self-)subsuming clause is stored in 'd',
                // which makes it nonzero and forces aborting both the outer
                // and inner loop.  If the binary clause can strengthen the
                // candidate clause 'c' (through self-subsuming resolution),
                // then 'filled' is set to the literal which can be removed in
                // 'c', otherwise to 'INT_MIN' which is a non-valid literal.

                let bi = self.vlit(sign * lit) as usize;
                let nbins = self.big[bi].len();
                for k in 0..nbins {
                    let bin = self.big[bi][k];
                    let other = bin.lit;
                    let tmp = self.marked(other);
                    if tmp == 0 {
                        continue;
                    }
                    if tmp < 0 && sign < 0 {
                        continue;
                    }
                    let dummy = self.dummy_binary;
                    if tmp < 0 {
                        if sign < 0 {
                            continue; // tautological resolvent
                        }
                        dummy.set_lit(0, lit);
                        dummy.set_lit(1, other);
                        flipped = other;
                    } else {
                        dummy.set_lit(0, sign * lit);
                        dummy.set_lit(1, other);
                        flipped = if sign < 0 { -lit } else { i32::MIN };
                    }

                    // This dummy binary clauses is initialized in
                    // 'Internal::Internal' and only changes it literals in
                    // the lines above.   By using such a faked binary clause
                    // we can simply reuse 'subsume_clause' as well as the
                    // code around 'strengthen_clause' uniform for both real
                    // clauses and this special case for binary clauses

                    dummy.set_id(bin.id);
                    d = dummy;

                    break;
                }

                if !d.is_null() {
                    break;
                }

                // In this second loop we check for larger than binary clauses
                // to subsume or strengthen the candidate clause.   This is
                // more costly, and needs a call to 'subsume_check'.
                // Otherwise the same contract as above for communicating
                // 'subsumption' or 'strengthening' to the code after the loop
                // is used.
                //
                let oi = self.vlit(sign * lit) as usize;
                let nos = self.otab[oi].len();
                for k in 0..nos {
                    let e = self.otab[oi][k];
                    debug_assert!(!e.garbage()); // sanity check
                    if e.garbage() {
                        continue; // defensive: not needed
                    }
                    flipped = self.subsume_check(e, c);
                    if flipped == 0 {
                        continue;
                    }
                    d = e; // leave also outer loop
                    break;
                }

                sign += 2;
            }

            if !d.is_null() {
                break;
            }
        }

        self.unmark_clause_literals(c);

        if flipped == i32::MIN {
            log!(self, d, "subsuming");
            self.subsume_clause(d, c);
            return 1;
        }

        if flipped != 0 {
            log!(self, d, "strengthening");
            if self.lrat {
                debug_assert!(self.lrat_chain.is_empty());
                self.lrat_chain.push(c.id());
                self.lrat_chain.push(d.id());
            }
            if d.used() > c.used() {
                c.set_used(d.used());
            }
            self.strengthen_clause(c, -flipped);
            self.lrat_chain.clear();
            debug_assert!(self.likely_to_be_kept_clause(c));
            shrunken.push(c);
            return -1;
        }

        0
    }

    /*------------------------------------------------------------------------*/

    // Usually called from 'subsume' below if 'subsuming' triggered it.  Then
    // the idea is to subsume both redundant and irredundant clauses. It is
    // also called in the elimination loop in 'elim' in which case we focus
    // on irredundant clauses only to help bounded variable elimination.  The
    // function returns true of an irredundant clause was removed or
    // strengthened, which might then in the second usage scenario trigger
    // new variable eliminations.

    pub fn subsume_round(&mut self) -> bool {
        if self.opts.subsume == 0 {
            return false;
        }
        if self.unsat {
            return false;
        }
        if self.terminated_asynchronously(1) {
            return false;
        }
        if self.stats.current.redundant == 0 && self.stats.current.irredundant == 0 {
            return false;
        }

        start_simplifier!(self, subsume, SUBSUME);
        self.stats.subsumerounds += 1;

        let check_limit: i64;
        if self.opts.subsumelimited != 0 {
            let mut delta: i64 = self.stats.propagations.search;
            delta = (delta as f64 * (1e-3 * self.opts.subsumeeffort as f64)) as i64;
            if delta < self.opts.subsumemineff as i64 {
                delta = self.opts.subsumemineff as i64;
            }
            if delta > self.opts.subsumemaxeff as i64 {
                delta = self.opts.subsumemaxeff as i64;
            }
            delta = std::cmp::max(delta, 2i64 * self.active_count() as i64);

            phase!(
                self,
                "subsume-round",
                self.stats.subsumerounds,
                "limit of {} subsumption checks",
                delta
            );

            check_limit = self.stats.subchecks + delta;
        } else {
            phase!(
                self,
                "subsume-round",
                self.stats.subsumerounds,
                "unlimited subsumption checks"
            );
            check_limit = i64::MAX;
        }

        let old_marked_candidate_variables_for_elimination = self.stats.mark.elim as i32;

        debug_assert!(self.level == 0);

        // Allocate schedule and occurrence lists.
        //
        let mut schedule: Vec<ClauseSize> = Vec::new();
        self.init_noccs();

        // Determine candidate clauses and sort them by size.
        //
        let mut left_over_from_last_subsumption_round: i64 = 0;

        for ci in 0..self.clauses.len() {
            let c = self.clauses[ci];
            if self.terminated_asynchronously(1) {
                break;
            }
            if c.garbage() {
                continue;
            }
            if c.size() > self.opts.subsumeclslim {
                continue;
            }
            if !self.likely_to_be_kept_clause(c) {
                continue;
            }

            let mut fixed = false;
            let mut subsume = 0;
            for &lit in c.lits() {
                if self.val(lit) != 0 {
                    fixed = true;
                } else if self.flags(lit).subsume {
                    subsume += 1;
                }
            }

            // If the clause contains a root level assigned (fixed) literal we
            // will not work on it.  This simplifies the code substantially
            // since we do not have to care about assignments at all.
            // Strengthening becomes much simpler too.
            //
            if fixed {
                log!(self, c, "skipping (fixed literal)");
                continue;
            }

            // Further, if less than two variables in the clause were added
            // since the last subsumption round, the clause is ignored too.
            //
            if subsume < 2 {
                log!(self, c, "skipping (only {} added literals)", subsume);
                continue;
            }

            if c.subsume() {
                left_over_from_last_subsumption_round += 1;
            }
            schedule.push(ClauseSize::new(c.size(), c));
            for &lit in c.lits() {
                *self.noccs_mut(lit) += 1;
            }
        }
        shrink_vector(&mut schedule);

        // Smaller clauses are checked and connected first.
        //
        rsort(&mut schedule, smaller_clause_size_rank);

        if left_over_from_last_subsumption_round == 0 {
            for cs in schedule.iter() {
                if cs.clause.size() > 2 {
                    cs.clause.set_subsume(true);
                }
            }
        }

        let scheduled = schedule.len() as i64;
        let total = self.stats.current.irredundant + self.stats.current.redundant;
        phase!(
            self,
            "subsume-round",
            self.stats.subsumerounds,
            "scheduled {} clauses {}% out of {} clauses",
            scheduled,
            fmt_f(percent(scheduled as f64, total as f64), 0),
            total
        );

        // Now go over the scheduled clauses in the order of increasing size
        // and try to forward subsume and strengthen them. Forward subsumption
        // tries to find smaller or same size clauses which subsume or might
        // strengthen the candidate.  After the candidate has been processed
        // connect one of its literals (with smallest number of occurrences at
        // this point) in a one-watched scheme.

        let mut subsumed: i64 = 0;
        let mut strengthened: i64 = 0;
        let mut checked: i64 = 0;

        let mut shrunken: Vec<CRef> = Vec::new();
        self.init_occs();
        self.init_bins();

        for si in 0..schedule.len() {
            let s = schedule[si];
            if self.terminated_asynchronously(1) {
                break;
            }
            if self.stats.subchecks >= check_limit {
                break;
            }

            let c = s.clause;
            debug_assert!(!c.garbage());

            checked += 1;

            // First try to subsume or strengthen this candidate clause.  For
            // binary clauses this could be done much faster by hashing and is
            // costly due to a usually large number of binary clauses.  There
            // is further the issue, that strengthening binary clauses
            // (through double self-subsuming resolution) would produce
            // units, which needs much more care. In the same (lazy) spirit we
            // also ignore clauses with fixed literals (false or true).
            //
            if c.size() > 2 && c.subsume() {
                c.set_subsume(false);
                let tmp = self.try_to_subsume_clause(c, &mut shrunken);
                if tmp > 0 {
                    subsumed += 1;
                    continue;
                }
                if tmp < 0 {
                    strengthened += 1;
                }
            }

            // If not subsumed connect smallest occurring literal, where
            // occurring means the number of times it was used to connect (as
            // a one-watch) a previous smaller or equal sized clause.  This
            // minimizes the length of the occurrence lists traversed during
            // 'try_to_subsume_clause'. Also note that this number is usually
            // way smaller than the number of occurrences computed before and
            // stored in 'noccs'.
            //
            let mut minlit = 0;
            let mut minoccs: i64 = 0;
            let mut minsize: usize = 0;
            let mut subsume = true;
            let binary = c.size() == 2 && !c.redundant();

            for &lit in c.lits() {
                if !self.flags(lit).subsume {
                    subsume = false;
                }
                let size = if binary { self.bins(lit).len() } else { self.occs(lit).len() };
                if minlit != 0 && minsize <= size {
                    continue;
                }
                let tmp = self.noccs(lit);
                if minlit != 0 && minsize == size && tmp <= minoccs {
                    continue;
                }
                minlit = lit;
                minsize = size;
                minoccs = tmp;
            }

            // If there is a variable in a clause different from is not
            // 'subsume' (has been added since the last subsumption round),
            // then this clause can not serve to strengthen or subsume another
            // clause, since all shrunken or added clauses mark all their
            // variables as 'subsume'.
            //
            if !subsume {
                continue;
            }

            if !binary {
                // If smallest occurring literal occurs too often do not
                // connect.
                //
                if minsize > self.opts.subsumeocclim as usize {
                    continue;
                }

                log!(
                    self,
                    c,
                    "watching {} with {} current and total {} occurrences",
                    minlit,
                    minsize,
                    minoccs
                );

                self.occs_mut(minlit).push(c);

                // This sorting should give faster failures for assumption
                // checks since the less occurring variables are put first in
                // a clause and thus will make it more likely to be found as
                // witness for a clause not to be subsuming.  One could in
                // principle (see also the discussion on 'subsumption' in our
                // 'Splatz' solver) replace marking by a kind of merge sort, as
                // also suggested by Bayardo.  It would avoid 'marked' calls
                // and thus might be slightly faster but could not take benefit
                // of this sorting optimization.
                //
                let this: &Internal = self;
                std_sort(c.lits_mut(), |&a: &i32, &b: &i32| subsume_less_noccs(this, a, b));
            } else {
                // If smallest occurring literal occurs too often do not
                // connect.
                //
                if minsize > self.opts.subsumebinlim as usize {
                    continue;
                }

                log!(
                    self,
                    c,
                    "watching {} with {} current binary and total {} occurrences",
                    minlit,
                    minsize,
                    minoccs
                );

                let minlit_pos = (c.lit(1) == minlit) as usize;
                let other = c.lit(1 - minlit_pos);
                let id = c.id();
                self.bins_mut(minlit).push(Bin { lit: other, id });
            }
        }

        phase!(
            self,
            "subsume-round",
            self.stats.subsumerounds,
            "subsumed {} and strengthened {} out of {} clauses {}%",
            subsumed,
            strengthened,
            scheduled,
            fmt_f(percent((subsumed + strengthened) as f64, scheduled as f64), 0)
        );

        let remain = schedule.len() as i64 - checked;
        let completed = remain == 0;

        if completed {
            phase!(
                self,
                "subsume-round",
                self.stats.subsumerounds,
                "checked all {} scheduled clauses",
                checked
            );
        } else {
            phase!(
                self,
                "subsume-round",
                self.stats.subsumerounds,
                "checked {} clauses {}% of scheduled ({} remain)",
                checked,
                fmt_f(percent(checked as f64, scheduled as f64), 0),
                remain
            );
        }

        // Release occurrence lists and schedule.
        //
        erase_vector(&mut schedule);
        self.reset_noccs();
        self.reset_occs();
        self.reset_bins();

        // Reset all old 'added' flags and mark variables in shrunken
        // clauses as 'added' for the next subsumption round.
        //
        if completed {
            self.reset_subsume_bits();
        }

        for &c in shrunken.iter() {
            self.mark_added(c);
        }
        erase_vector(&mut shrunken);

        let quiet = self.opts.reportall == 0 && (subsumed + strengthened) == 0;
        self.report(b's', quiet as i32);

        stop_simplifier!(self, subsume, SUBSUME);

        (old_marked_candidate_variables_for_elimination as i64) < self.stats.mark.elim
    }

    /*------------------------------------------------------------------------*/

    pub fn subsume(&mut self) {
        if self.stats.current.redundant == 0 && self.stats.current.irredundant == 0 {
            return;
        }

        if self.unsat {
            return;
        }

        self.backtrack(0);
        if !self.propagate() {
            self.learn_empty_clause();
            return;
        }

        self.stats.subsumephases += 1;

        if self.external_prop {
            debug_assert!(self.level == 0);
            self.private_steps = true;
        }

        if self.opts.subsume != 0 {
            self.reset_watches();
            self.subsume_round();
            self.init_watches();
            self.connect_watches(false);
            if !self.unsat && !self.propagate() {
                log!(self, "propagation after subsume rounds results in inconsistency");
                self.learn_empty_clause();
            }
        }

        self.transred();
        if self.external_prop {
            debug_assert!(self.level == 0);
            self.private_steps = false;
        }
    }
}

/// `subsume_less_noccs` comparator.
#[inline]
fn subsume_less_noccs(internal: &Internal, a: i32, b: i32) -> bool {
    let u = internal.val(a);
    let v = internal.val(b);
    if u == 0 && v != 0 {
        return true;
    }
    if u != 0 && v == 0 {
        return false;
    }
    let m = internal.noccs(a);
    let n = internal.noccs(b);
    if m < n {
        return true;
    }
    if m > n {
        return false;
    }
    a.abs() < b.abs()
}

#[cfg(test)]
mod tests {
    use crate::prelude::*;

    #[test]
    fn subsume_check_results_and_rotates_literals() {
        let mut internal = Internal::new();
        let ip: *mut Internal = &mut *internal;
        let _external = External::new(ip);
        internal.enlarge_vals(8);
        internal.vsize = 8;
        internal.max_var = 6;
        internal.marks = vec![0; 8];
        let mk = |lits: &[i32]| {
            let c = CRef::alloc(lits.len() as i32);
            c.set_size(lits.len() as i32);
            for (i, &l) in lits.iter().enumerate() {
                c.set_lit(i, l);
            }
            c
        };
        // Candidate 'subsumed' = 1 -2 3 4 (marked).
        let subsumed = mk(&[1, -2, 3, 4]);
        for &l in &[1, -2, 3, 4] {
            internal.mark(l);
        }
        let a = mk(&[3, 1, -2]);
        assert_eq!(internal.subsume_check(a, subsumed), i32::MIN);
        // C++ rotates the literals of 'subsuming' (moving the last visited
        // literal to the front).
        assert_eq!(a.lits(), &[-2, 3, 1]);
        let b = mk(&[1, 2, 4]);
        internal.opts.subsumestr = 1;
        assert_eq!(internal.subsume_check(b, subsumed), 2);
        assert_eq!(b.lits(), &[4, 1, 2]);
        internal.opts.subsumestr = 0;
        assert_eq!(internal.subsume_check(b, subsumed), 0);
        assert_eq!(b.lits(), &[2, 4, 1]);
        let d = mk(&[1, 5, 4]);
        assert_eq!(internal.subsume_check(d, subsumed), 0);
        assert_eq!(d.lits(), &[5, 1, 4]);
        let e = mk(&[-1, 2, 4]);
        internal.opts.subsumestr = 1;
        assert_eq!(internal.subsume_check(e, subsumed), 0);
        assert_eq!(e.lits(), &[2, -1, 4]);
        assert_eq!(internal.stats.subchecks, 5);
        for c in [subsumed, a, b, d, e] {
            unsafe { c.dealloc() };
        }
        std::mem::forget(internal);
    }
}

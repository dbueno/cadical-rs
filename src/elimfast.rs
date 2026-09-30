//! Port of `elimfast.cpp`.

#[allow(unused_imports)]
use crate::prelude::*;

use crate::format::fmt_f;
use crate::occs::shrink_occs;

/*------------------------------------------------------------------------*/

// Implements a variant of elimination with a much lower limit to be run as
// preprocessing. See elim for comments

impl Internal {
    /*--------------------------------------------------------------------*/

    // Flush garbage clause, check fast elimination limits and return number
    // of remaining occurrences (or 'fastelimbound + 1' if some limit was
    // hit).

    pub fn flush_elimfast_occs(&mut self, lit: i32) -> i64 {
        let occslim = self.opts.fastelimocclim as i64;
        let clslim = self.opts.fastelimclslim as i64;
        let failed = occslim + 1;
        #[cfg(debug_assertions)]
        let fastelimbound = self.opts.fastelimbound;
        let os = self.occs_mut(lit);
        let end = os.len();
        let mut j = 0usize;
        let mut i = 0usize;
        let mut res: i64 = 0;
        while i != end {
            let c = os[i];
            i += 1;
            if c.collect() {
                continue;
            }
            os[j] = c;
            j += 1;
            if c.size() as i64 > clslim {
                res = failed;
                break;
            }
            res += 1;
            if res > occslim {
                #[cfg(debug_assertions)]
                debug_assert!(fastelimbound < 0 || res == failed);
                break;
            }
        }
        if i != j {
            while i != end {
                os[j] = os[i];
                j += 1;
                i += 1;
            }
            os.truncate(j);
            shrink_occs(os);
        }
        res
    }

    /*--------------------------------------------------------------------*/

    // Check whether the number of non-tautological resolvents on 'pivot' is
    // smaller or equal to the number of clauses with 'pivot' or '-pivot'.
    // This is the main criteria of bounded variable elimination.  As a side
    // effect it flushes garbage clauses with that variable, sorts its
    // occurrence lists (smallest clauses first) and also negates pivot if
    // it has more positive than negative occurrences.

    pub fn elimfast_resolvents_are_bounded(&mut self, eliminator: &mut Eliminator, pivot: i32) -> bool {
        debug_assert!(eliminator.gates.is_empty());
        debug_assert!(eliminator.definition_unit == 0);

        self.stats.elimtried += 1;

        debug_assert!(!self.unsat);
        debug_assert!(self.active(pivot));

        let pos = self.occs(pivot).len() as i64;
        let neg = self.occs(-pivot).len() as i64;

        let mut bound = self.opts.fastelimbound as i64;

        if pos == 0 || neg == 0 {
            return bound >= 0;
        }

        let sum = pos + neg;
        let product = pos * neg;
        if bound > sum {
            bound = sum;
        }

        log!(
            self,
            "checking number resolvents on {} bounded by {} = {} + {} + {}",
            pivot,
            bound,
            pos,
            neg,
            self.opts.fastelimbound
        );

        if product <= bound {
            log!(self, "fast elimination occurrence limits sufficiently small enough");
            return true;
        }

        // Try all resolutions between a positive occurrence (outer loop) of
        // 'pivot' and a negative occurrence of 'pivot' (inner loop) as long
        // the bound on non-tautological resolvents is not hit and the size
        // of the generated resolvents does not exceed the resolvent clause
        // size limit.

        let mut resolvents: i64 = 0; // Non-tautological resolvents.

        let ps_size = self.occs(pivot).len();
        for i in 0..ps_size {
            let c = self.occs(pivot)[i];
            if self.terminated_asynchronously(1) {
                return false;
            }
            debug_assert!(!c.redundant());
            if c.garbage() {
                continue;
            }
            let ns_size = self.occs(-pivot).len();
            for j in 0..ns_size {
                let d = self.occs(-pivot)[j];
                debug_assert!(!d.redundant());
                if d.garbage() {
                    continue;
                }
                if self.resolve_clauses(eliminator, c, pivot, d, true) {
                    resolvents += 1;
                    let size = self.clause.len() as i32;
                    self.clause.clear();
                    log!(self, "now at least {} non-tautological resolvents on pivot {}", resolvents, pivot);
                    if size > self.opts.fastelimclslim {
                        log!(self, "resolvent size {} too big after {} resolvents on {}", size, resolvents, pivot);
                        return false;
                    }
                    if resolvents > bound {
                        log!(self, "too many non-tautological resolvents on {}", pivot);
                        return false;
                    }
                } else if self.unsat {
                    return false;
                } else if self.val(pivot) != 0 {
                    return false;
                } else if self.terminated_asynchronously(1) {
                    return false;
                }
            }
        }

        log!(self, "need {} <= {} non-tautological resolvents", resolvents, bound);

        true
    }

    /*--------------------------------------------------------------------*/
    // Add all resolvents on 'pivot' and connect them.

    #[inline]
    pub fn elimfast_add_resolvents(&mut self, eliminator: &mut Eliminator, pivot: i32) {
        debug_assert!(eliminator.gates.is_empty());
        debug_assert!(eliminator.definition_unit == 0);

        log!(self, "adding all resolvents on {}", pivot);

        debug_assert!(self.val(pivot) == 0);
        debug_assert!(!self.flags(pivot).eliminated());

        #[cfg(feature = "logging")]
        let mut resolvents: i64 = 0;
        let ps_size = self.occs(pivot).len();
        for i in 0..ps_size {
            let c = self.occs(pivot)[i];
            if self.unsat {
                break;
            }
            if c.garbage() {
                continue;
            }
            let ns_size = self.occs(-pivot).len();
            for j in 0..ns_size {
                let d = self.occs(-pivot)[j];
                if self.unsat {
                    break;
                }
                if d.garbage() {
                    continue;
                }
                if !self.resolve_clauses(eliminator, c, pivot, d, false) {
                    continue;
                }
                debug_assert!(!self.lrat || !self.lrat_chain.is_empty());
                let r = self.new_resolved_irredundant_clause();
                self.elim_update_added_clause(eliminator, r);
                eliminator.enqueue(r);
                self.lrat_chain.clear();
                self.clause.clear();
                #[cfg(feature = "logging")]
                {
                    resolvents += 1;
                }
            }
        }

        log!(self, "added {} resolvents to eliminate {}", resolvents, pivot);
    }

    /*--------------------------------------------------------------------*/

    // Try to eliminate 'pivot' by bounded variable elimination.
    pub fn try_to_fasteliminate_variable(
        &mut self,
        eliminator: &mut Eliminator,
        pivot: i32,
        deleted_binary_clause: &mut bool,
    ) {
        let mut pivot = pivot;
        if !self.active(pivot) {
            return;
        }
        debug_assert!(!self.frozen(pivot));

        // First flush garbage clauses and check limits.

        let occ_bound = self.opts.fastelimocclim as i64;
        let mut bound = self.opts.fastelimbound as i64;

        let mut pos = self.flush_elimfast_occs(pivot);
        let mut neg = self.flush_elimfast_occs(-pivot);
        if neg != 0 && pos > occ_bound {
            log!(self, "too many occurrences thus not eliminated {}", pivot);
            debug_assert!(!eliminator.schedule.contains(pivot.unsigned_abs()));
            return;
        }

        if pos != 0 && neg > occ_bound {
            log!(self, "too many occurrences thus not eliminated {}", -pivot);
            debug_assert!(!eliminator.schedule.contains(pivot.unsigned_abs()));
            return;
        }

        let product = pos * neg;
        let sum = pos + neg;
        if bound > sum {
            bound = sum;
        }

        if pos > neg {
            pivot = -pivot;
            std::mem::swap(&mut pos, &mut neg);
        }

        log!(self, "pivot {} occurs positively {} times and negatively {} times", pivot, pos, neg);

        debug_assert!(!eliminator.schedule.contains(pivot.unsigned_abs()));
        debug_assert!(pos <= neg);

        log!(self, "trying to eliminate {}", pivot);
        debug_assert!(!self.flags(pivot).eliminated());

        // Sort occurrence lists, such that shorter clauses come first.
        self.occs_mut(pivot).sort_by_key(|c| c.size());
        self.occs_mut(-pivot).sort_by_key(|c| c.size());

        if !self.unsat && self.val(pivot) == 0 {
            if product <= bound || self.elimfast_resolvents_are_bounded(eliminator, pivot) {
                log!(self, "number of resolvents on {} are bounded", pivot);
                self.elimfast_add_resolvents(eliminator, pivot);
                if !self.unsat {
                    self.mark_eliminated_clauses_as_garbage(eliminator, pivot, deleted_binary_clause);
                }
                if self.active(pivot) {
                    self.mark_eliminated(pivot);
                }
            } else {
                log!(self, "too many resolvents on {} so not eliminated", pivot);
            }
        }

        self.unmark_gate_clauses(eliminator);
        self.elim_backward_clauses(eliminator);
    }

    /*--------------------------------------------------------------------*/

    // This function performs one round of bounded variable elimination and
    // returns the number of eliminated variables. The additional result
    // 'completed' is true if this elimination round ran to completion (all
    // variables have been tried).  Otherwise it was asynchronously
    // terminated or the resolution limit was hit.

    pub fn elimfast_round(&mut self, completed: &mut bool, deleted_binary_clause: &mut bool) -> i32 {
        debug_assert!(self.opts.fastelim != 0);
        debug_assert!(!self.unsat);
        if self.terminated_asynchronously(1) {
            return 0;
        }

        start_simplifier!(self, fastelim, ELIM);

        self.stats.elimfastrounds += 1;

        debug_assert!(self.level == 0);

        let resolution_limit: i64;

        if self.opts.elimlimited != 0 {
            let mut delta: i64 = self.stats.propagations.search;
            delta = (delta as f64 * (1e-3 * self.opts.elimeffort as f64)) as i64;
            if delta < self.opts.elimmineff as i64 {
                delta = self.opts.elimmineff as i64;
            }
            if delta > self.opts.elimmaxeff as i64 {
                delta = self.opts.elimmaxeff as i64;
            }

            phase!(self, "fastelim-round", self.stats.elimfastrounds, "limit of {} resolutions", delta);

            resolution_limit = self.stats.elimres + delta;
        } else {
            phase!(self, "fastelim-round", self.stats.elimfastrounds, "resolutions unlimited");
            resolution_limit = i64::MAX;
        }

        self.init_noccs();

        // First compute the number of occurrences of each literal and at the
        // same time mark satisfied clauses and update 'elim' flags of
        // variables in clauses with root level assigned literals (both false
        // and true).
        //
        for k in 0..self.clauses.len() {
            if self.terminated_asynchronously(1) {
                break;
            }
            let c = self.clauses[k];
            if c.garbage() || c.redundant() {
                continue;
            }
            let mut satisfied = false;
            let mut falsified = false;
            for &lit in c.lits() {
                let tmp = self.val(lit);
                if tmp > 0 {
                    satisfied = true;
                } else if tmp < 0 {
                    falsified = true;
                } else {
                    debug_assert!(self.active(lit));
                }
            }
            if satisfied {
                self.mark_garbage(c); // forces more precise counts
            } else {
                for &lit in c.lits() {
                    if !self.active(lit) {
                        continue;
                    }
                    if falsified {
                        self.mark_elim(lit); // simulate unit propagation
                    }
                    *self.noccs_mut(lit) += 1;
                }
            }
        }

        self.init_occs();

        let mut eliminator = Eliminator::new(self as *mut Internal);
        debug_assert!(eliminator.schedule.empty());

        // Now find elimination candidates which occurred in clauses removed
        // since the last time we ran bounded variable elimination, which in
        // turned triggered their 'elim' bit to be set.
        //
        for idx in self.vars() {
            if !self.active(idx) {
                continue;
            }
            if self.frozen(idx) {
                continue;
            }
            if !self.flags(idx).elim {
                continue;
            }
            log!(self, "scheduling {} for elimination initially", idx);
            eliminator.schedule.push_back(idx as u32);
        }

        eliminator.schedule.shrink();

        let scheduled = eliminator.schedule.size() as i64;

        phase!(
            self,
            "fastelim-round",
            self.stats.elimfastrounds,
            "scheduled {} variables {}% for elimination",
            scheduled,
            fmt_f(percent(scheduled as f64, self.active_count() as f64), 0)
        );

        // Connect irredundant clauses.
        //
        for k in 0..self.clauses.len() {
            if self.terminated_asynchronously(1) {
                break;
            }
            let c = self.clauses[k];
            if !c.garbage() && !c.redundant() {
                for &lit in c.lits() {
                    if self.active(lit) {
                        self.occs_mut(lit).push(c);
                    }
                }
            }
        }

        let old_resolutions = self.stats.elimres;
        let old_eliminated = self.stats.all.eliminated as i32;
        let old_fixed = self.stats.all.fixed as i32;

        // Limit on garbage literals during variable elimination. If the
        // limit is hit a garbage collection is performed.
        //
        let garbage_limit: i64 = (2 * self.stats.irrlits / 3) + (1 << 20);

        // Main loops tries to eliminate variables according to the schedule.
        // The schedule is updated dynamically and variables are potentially
        // rescheduled to be tried again if they occur in a removed clause.
        //
        let mut tried: i64 = 0;
        while !self.unsat
            && !self.terminated_asynchronously(1)
            && self.stats.elimres <= resolution_limit
            && !eliminator.schedule.empty()
        {
            let idx = eliminator.schedule.front() as i32;
            eliminator.schedule.pop_front();
            self.flags_mut(idx).elim = false;
            self.try_to_fasteliminate_variable(&mut eliminator, idx, deleted_binary_clause);
            tried += 1;
            if self.stats.garbage.literals <= garbage_limit {
                continue;
            }
            self.mark_redundant_clauses_with_eliminated_variables_as_garbage();
            self.garbage_collection();
        }

        // If the schedule is empty all variables have been tried (even
        // rescheduled ones).  Otherwise asynchronous termination happened or
        // we ran into the resolution limit (or derived unsatisfiability).
        //
        *completed = eliminator.schedule.size() == 0;

        phase!(
            self,
            "fastelim-round",
            self.stats.elimfastrounds,
            "tried to eliminate {} variables {}% ({} remain)",
            tried,
            fmt_f(percent(tried as f64, scheduled as f64), 0),
            eliminator.schedule.size()
        );

        eliminator.schedule.erase();

        self.reset_occs();
        self.reset_noccs();

        // Mark all redundant clauses with eliminated variables as garbage.
        //
        if !self.unsat {
            self.mark_redundant_clauses_with_eliminated_variables_as_garbage();
        }

        let eliminated = self.stats.all.eliminated as i32 - old_eliminated;
        self.stats.all.fasteliminated += eliminated as i64;
        let resolutions = self.stats.elimres - old_resolutions;
        phase!(
            self,
            "fastelim-round",
            self.stats.elimfastrounds,
            "eliminated {} variables {}% in {} resolutions",
            eliminated,
            fmt_f(percent(eliminated as f64, scheduled as f64), 0),
            resolutions
        );

        let units = self.stats.all.fixed as i32 - old_fixed;
        let quiet = self.opts.reportall == 0 && (eliminated + units) == 0;
        self.report(b'e', quiet as i32);
        stop_simplifier!(self, fastelim, ELIM);

        drop(eliminator);

        eliminated // non-zero if successful
    }

    /*--------------------------------------------------------------------*/

    pub fn elimfast(&mut self) {
        if self.unsat {
            return;
        }
        if self.terminated_asynchronously(1) {
            return;
        }
        if self.level != 0 {
            self.backtrack(0);
        }
        if !self.propagate() {
            self.learn_empty_clause();
            return;
        }

        self.stats.elimfastphases += 1;
        phase!(
            self,
            "fastelim-phase",
            self.stats.elimfastphases,
            "starting at most {} elimination rounds",
            self.opts.fastelimrounds
        );

        if self.external_prop {
            debug_assert!(self.level == 0);
            self.private_steps = true;
        }

        let old_active_variables = self.active_count();
        let old_eliminated = self.stats.all.eliminated as i32;

        self.reset_watches(); // saves lots of memory

        // Alternate one round of bounded variable elimination ('elim_round')
        // and subsumption ('subsume_round'), blocked ('block') and covered
        // clause elimination ('cover') until nothing changes, or the round
        // limit is hit.  The loop also aborts early if no variable could be
        // eliminated, the empty clause is resolved, it is asynchronously
        // terminated or a resolution limit is hit.

        // This variable determines whether the whole loop of this bounded
        // variable elimination phase ('elim') ran until completion.  This
        // potentially triggers an incremental increase of the elimination
        // bound.
        //
        let mut phase_complete = false;
        let mut deleted_binary_clause = false;

        let mut round = 1;

        let mut round_complete = false;
        while !self.unsat && !phase_complete && !self.terminated_asynchronously(1) {
            let eliminated = self.elimfast_round(&mut round_complete, &mut deleted_binary_clause);

            if !round_complete {
                phase!(
                    self,
                    "fastelim-phase",
                    self.stats.elimphases,
                    "last round {} incomplete {}",
                    round,
                    if eliminated != 0 { "but successful" } else { "and unsuccessful" }
                );
                debug_assert!(!phase_complete);
                break;
            }

            let r = round;
            round += 1;
            if r >= self.opts.fastelimrounds {
                phase!(
                    self,
                    "fastelim-phase",
                    self.stats.elimphases,
                    "round limit {} hit ({})",
                    round - 1,
                    if eliminated != 0 {
                        "though last round successful"
                    } else {
                        "last round unsuccessful anyhow"
                    }
                );
                debug_assert!(!phase_complete);
                break;
            }

            // Prioritize 'subsumption' over blocked and covered clause
            // elimination.

            if self.subsume_round() {
                continue;
            }

            // Was not able to generate new variable elimination candidates
            // after variable elimination round, neither through subsumption,
            // nor blocked, nor covered clause elimination.
            //
            phase!(self, "fastelim-phase", self.stats.elimphases, "no new variable elimination candidates");

            debug_assert!(round_complete);
            phase_complete = true;
        }

        for idx in self.vars() {
            if self.active(idx) {
                self.flags_mut(idx).elim = true;
            }
        }

        if phase_complete {
            self.stats.elimcompleted += 1;
            phase!(
                self,
                "fastelim-phase",
                self.stats.elimphases,
                "fully completed elimination {} at elimination bound {}",
                self.stats.elimcompleted,
                self.lim.elimbound
            );
        } else {
            phase!(
                self,
                "fastelim-phase",
                self.stats.elimphases,
                "incomplete elimination {} at elimination bound {}",
                self.stats.elimcompleted + 1,
                self.lim.elimbound
            );
        }

        if deleted_binary_clause {
            self.delete_garbage_clauses();
        }
        self.init_watches();
        self.connect_watches(false);

        if self.unsat {
            log!(self, "elimination derived empty clause");
        } else if self.propagated < self.trail.len() {
            log!(self, "elimination produced {} units", self.trail.len() - self.propagated);
            if !self.propagate() {
                log!(self, "propagating units after elimination results in empty clause");
                self.learn_empty_clause();
            }
        }

        let eliminated = self.stats.all.eliminated as i32 - old_eliminated;
        phase!(
            self,
            "fastelim-phase",
            self.stats.elimphases,
            "eliminated {} variables {}%",
            eliminated,
            fmt_f(percent(eliminated as f64, old_active_variables as f64), 2)
        );

        if self.external_prop {
            debug_assert!(self.level == 0);
            self.private_steps = false;
        }
    }
}

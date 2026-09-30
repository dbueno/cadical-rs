//! Port of `block.hpp` and `block.cpp`: blocked clause elimination.

use crate::clause::CRef;
use crate::heap::{Heap, HeapLess};
use crate::internal::Internal;
use crate::util::erase_vector;

/// Comparator of the blocking schedule (`block_more_occs_size`).
#[derive(Clone, Copy, Debug)]
pub struct block_more_occs_size {
    pub internal: *mut Internal,
}

impl block_more_occs_size {
    pub fn new(i: *mut Internal) -> Self {
        block_more_occs_size { internal: i }
    }
}

pub type BlockSchedule = Heap<block_more_occs_size>;

pub struct Blocker {
    pub candidates: Vec<CRef>,
    pub reschedule: Vec<CRef>,
    pub schedule: BlockSchedule,
}

impl Blocker {
    pub fn new(i: *mut Internal) -> Blocker {
        Blocker {
            candidates: Vec::new(),
            reschedule: Vec::new(),
            schedule: BlockSchedule::new(block_more_occs_size::new(i)),
        }
    }
    pub fn erase(&mut self) {
        erase_vector(&mut self.candidates);
        erase_vector(&mut self.reschedule);
        self.schedule.erase();
    }
}

/*------------------------------------------------------------------------*/

// This implements an inprocessing version of blocked clause elimination and
// is assumed to be triggered just before bounded variable elimination.  It
// has a separate 'block' flag while variable elimination uses 'elim'.
// Thus it only tries to block clauses on a literal which was removed in an
// irredundant clause in negated form before and has not been tried to use
// as blocking literal since then.

#[allow(unused_imports)]
use crate::prelude::*;

use crate::format::fmt_f;

impl HeapLess for block_more_occs_size {
    #[inline]
    fn less(&self, a: u32, b: u32) -> bool {
        // SAFETY: the back pointer to the owning 'Internal' is valid while
        // the schedule is alive (only read access to 'ntab').
        let internal = unsafe { &*self.internal };
        let mut s = internal.noccs(-internal.u2i(a)) as usize;
        let mut t = internal.noccs(-internal.u2i(b)) as usize;
        if s > t {
            return true;
        }
        if s < t {
            return false;
        }
        s = internal.noccs(internal.u2i(a)) as usize;
        t = internal.noccs(internal.u2i(b)) as usize;
        if s > t {
            return true;
        }
        if s < t {
            return false;
        }
        a > b
    }
}

impl Internal {
    /*--------------------------------------------------------------------*/

    // Determine whether 'c' is blocked on 'lit', by first marking all its
    // literals and then checking all resolvents with negative clauses (with
    // '-lit') are tautological.  We use a move-to-front scheme for both the
    // occurrence list of negative clauses (with '-lit') and then for
    // literals within each such clause.  The clause move-to-front scheme
    // has the goal to find non-tautological clauses faster in the future,
    // while the literal move-to-front scheme has the goal to faster find
    // the matching literal, which makes the resolvent tautological (again
    // in the future).

    pub fn is_blocked_clause(&mut self, c: CRef, lit: i32) -> bool {
        log!(self, c, "trying to block on {}", lit);

        debug_assert!(c.size() >= self.opts.blockminclslim);
        debug_assert!(c.size() <= self.opts.blockmaxclslim);
        debug_assert!(self.active(lit));
        debug_assert!(self.val(lit) == 0);
        debug_assert!(!c.garbage());
        debug_assert!(!c.redundant());
        debug_assert!(self.level == 0);

        self.mark_clause_literals(c); // First mark all literals in 'c'.

        let end_of_os = self.occs(-lit).len();
        log!(self, "resolving against at most {} clauses with {}", end_of_os, -lit);

        let mut res = true; // Result is true if all resolvents tautological.

        // Can not use 'auto' here since we update 'os' during traversal.
        //
        let mut i = 0usize;

        let mut prev_d = CRef::NULL; // Previous non-tautological clause.

        while i != end_of_os {
            // Move the first clause with non-tautological resolvent to the
            // front of the occurrence list to improve finding it faster
            // later.
            //
            let d = self.occs(-lit)[i];

            debug_assert!(!d.garbage());
            debug_assert!(!d.redundant());
            debug_assert!(d.size() <= self.opts.blockmaxclslim);

            self.occs_mut(-lit)[i] = prev_d; // Move previous non-tautological clause
            prev_d = d; // backwards but remember clause at this position.

            log!(self, d, "resolving on {} against", lit);
            self.stats.blockres += 1;

            let mut prev_other = 0; // Previous non-tautological literal.

            // No 'auto' since we update literals of 'd' during traversal.
            //
            let end_of_d = d.size() as usize;
            let mut l = 0usize;

            while l != end_of_d {
                // Same move-to-front mechanism for literals within a clause.
                // It moves the first negatively marked literal to the front
                // to find it faster in the future.
                //
                let other = d.lit(l);
                d.set_lit(l, prev_other);
                prev_other = other;
                if other == -lit {
                    l += 1;
                    continue;
                }
                debug_assert!(other != lit);
                debug_assert!(self.active(other));
                debug_assert!(self.val(other) == 0);
                if self.marked(other) < 0 {
                    log!(self, "found tautological literal {}", other);
                    d.set_lit(0, other); // Move to front of 'd'.
                    break;
                }
                l += 1;
            }

            if l == end_of_d {
                log!(self, "no tautological literal found");
                //
                // Since we did not find a tautological literal we restore
                // the old order of literals in the clause.
                //
                while l != 0 {
                    l -= 1;
                    let other = d.lit(l);
                    d.set_lit(l, prev_other);
                    prev_other = other;
                }
                res = false; // Now 'd' is a witness that 'c' is not blocked.
                self.occs_mut(-lit)[0] = d; // Move it to the front of the occurrence list.
                break;
            }
            i += 1;
        }
        self.unmark_clause_literals(c); // ... all literals of the candidate clause.

        // If all resolvents are tautological and thus the clause is blocked
        // we restore the old order of clauses in the occurrence list of
        // '-lit'.
        //
        if res {
            debug_assert!(i == end_of_os);
            while i != 0 {
                i -= 1;
                let d = self.occs(-lit)[i];
                self.occs_mut(-lit)[i] = prev_d;
                prev_d = d;
            }
        }

        res
    }

    /*--------------------------------------------------------------------*/

    pub fn block_schedule(&mut self, blocker: &mut Blocker) {
        // Set skip flags for all literals in too large clauses.
        //
        for k in 0..self.clauses.len() {
            let c = self.clauses[k];

            if c.garbage() {
                continue;
            }
            if c.redundant() {
                continue;
            }
            if c.size() <= self.opts.blockmaxclslim {
                continue;
            }

            for &lit in c.lits() {
                self.mark_skip(-lit);
            }
        }

        // Connect all literal occurrences in irredundant clauses.
        //
        for k in 0..self.clauses.len() {
            let c = self.clauses[k];

            if c.garbage() {
                continue;
            }
            if c.redundant() {
                continue;
            }

            for &lit in c.lits() {
                debug_assert!(self.active(lit));
                debug_assert!(self.val(lit) == 0);
                self.occs_mut(lit).push(c);
            }
        }

        // We establish the invariant that 'noccs' gives the number of actual
        // occurrences of 'lit' in non-garbage clauses,  while 'occs' might
        // still refer to garbage clauses, thus 'noccs (lit) <= occs
        // (lit).size ()'.  It is expensive to remove references to garbage
        // clauses from 'occs' during blocked clause elimination, but
        // decrementing 'noccs' is cheap.

        for lit in self.lits() {
            if !self.active(lit) {
                continue;
            }
            debug_assert!(self.val(lit) == 0);
            let n = self.occs(lit).len() as i64;
            *self.noccs_mut(lit) = n;
        }

        // Now we fill the schedule (priority queue) of candidate literals to
        // be tried as blocking literals.  It is probably slightly faster to
        // do this in one go after all occurrences have been determined,
        // instead of filling the priority queue during pushing occurrences.
        // Filling the schedule can not be fused with the previous loop
        // (easily) since we first have to initialize 'noccs' for both 'lit'
        // and '-lit'.

        let mut skipped: i32 = 0;

        for idx in self.vars() {
            if !self.active(idx) {
                continue;
            }
            if self.frozen(idx) {
                skipped += 2;
                continue;
            }
            debug_assert!(self.val(idx) == 0);
            let mut sign = -1;
            while sign <= 1 {
                let lit = sign * idx;
                sign += 2;
                if self.marked_skip(lit) {
                    skipped += 1;
                    continue;
                }
                if !self.marked_block(lit) {
                    continue;
                }
                self.unmark_block(lit);
                log!(
                    self,
                    "scheduling {} with {} positive and {} negative occurrences",
                    lit,
                    self.noccs(lit),
                    self.noccs(-lit)
                );
                blocker.schedule.push_back(self.vlit(lit));
            }
        }

        phase!(
            self,
            "block",
            self.stats.blockings,
            "scheduled {} candidate literals {}% ({} skipped {}%)",
            blocker.schedule.size(),
            fmt_f(percent(blocker.schedule.size() as f64, 2.0 * self.active_count() as f64), 2),
            skipped,
            fmt_f(percent(skipped as f64, 2.0 * self.active_count() as f64), 2)
        );
    }

    /*--------------------------------------------------------------------*/

    // A literal is pure if it only occurs positive.  Then all clauses in
    // which it occurs are blocked on it. This special case can be
    // implemented faster than trying to block literals with at least one
    // negative occurrence and is thus handled separately.  It also allows to
    // avoid pushing blocked clauses onto the extension stack.

    pub fn block_pure_literal(&mut self, blocker: &mut Blocker, lit: i32) {
        if self.frozen(lit) {
            return;
        }
        debug_assert!(self.active(lit));

        debug_assert!(self.noccs(-lit) == 0);
        #[cfg(debug_assertions)]
        for &c in self.occs(-lit).iter() {
            debug_assert!(c.garbage());
        }
        self.stats.blockpurelits += 1;
        log!(self, "found pure literal {}", lit);
        #[cfg(feature = "logging")]
        let mut pured: i64 = 0;
        let n = self.occs(lit).len();
        for k in 0..n {
            let c = self.occs(lit)[k];
            if c.garbage() {
                continue;
            }
            debug_assert!(!c.redundant());
            log!(self, c, "pure literal {} in", lit);
            blocker.reschedule.push(c);
            if let Some(proof) = self.proof.as_mut() {
                proof.weaken_minus(c);
            }
            self.external().push_clause_on_extension_stack_with_witness(c, lit);
            self.stats.blockpured += 1;
            self.mark_garbage(c);
            #[cfg(feature = "logging")]
            {
                pured += 1;
            }
        }

        erase_vector(self.occs_mut(lit));
        erase_vector(self.occs_mut(-lit));

        self.mark_pure(lit);
        self.stats.blockpured += 1;
        log!(self, "blocking {} clauses on pure literal {}", pured, lit);
    }

    /*--------------------------------------------------------------------*/

    // If there is only one negative clause with '-lit' it is faster to mark
    // it instead of marking all the positive clauses with 'lit' one after
    // the other and then resolving against the negative clause.

    pub fn block_literal_with_one_negative_occ(&mut self, blocker: &mut Blocker, lit: i32) {
        debug_assert!(self.active(lit));
        debug_assert!(!self.frozen(lit));
        debug_assert!(self.noccs(lit) > 0);
        debug_assert!(self.noccs(-lit) == 1);

        debug_assert!(!self.occs(-lit).is_empty());

        let mut d = CRef::NULL;
        for &c in self.occs(-lit).iter() {
            if c.garbage() {
                continue;
            }
            debug_assert!(d.is_null());
            d = c;
            if cfg!(debug_assertions) {
                break;
            }
        }
        debug_assert!(!d.is_null());
        {
            let nos = self.occs_mut(-lit);
            nos.resize(1, CRef::NULL);
            nos[0] = d;
        }

        if !d.is_null() && d.size() > self.opts.blockmaxclslim {
            log!(self, d, "skipped common antecedent");
            return;
        }

        debug_assert!(!d.garbage());
        debug_assert!(!d.redundant());
        debug_assert!(d.size() <= self.opts.blockmaxclslim);

        log!(self, d, "common {} antecedent", lit);
        self.mark_clause_literals(d);
        let mut blocked: i64 = 0;
        #[cfg(feature = "logging")]
        let mut skipped: i64 = 0;

        // Again no 'auto' since 'pos' is update during traversal.
        //
        let eop = self.occs(lit).len();
        let mut j = 0usize;

        for i in 0..eop {
            let c = self.occs(lit)[i];
            self.occs_mut(lit)[j] = c;
            j += 1;

            if c.garbage() {
                j -= 1;
                continue;
            }
            if c.size() > self.opts.blockmaxclslim {
                #[cfg(feature = "logging")]
                {
                    skipped += 1;
                }
                continue;
            }
            if c.size() < self.opts.blockminclslim {
                #[cfg(feature = "logging")]
                {
                    skipped += 1;
                }
                continue;
            }

            log!(self, c, "trying to block on {}", lit);

            // We use the same literal move-to-front strategy as in
            // 'is_blocked_clause'.  See there for more explanations.

            let mut prev_other = 0; // Previous non-tautological literal.

            // No 'auto' since literals of 'c' are updated during traversal.
            //
            let end_of_c = c.size() as usize;
            let mut l = 0usize;

            while l != end_of_c {
                let other = c.lit(l);
                c.set_lit(l, prev_other);
                prev_other = other;
                if other == lit {
                    l += 1;
                    continue;
                }
                debug_assert!(other != -lit);
                debug_assert!(self.active(other));
                debug_assert!(self.val(other) == 0);
                if self.marked(other) < 0 {
                    log!(self, "found tautological literal {}", other);
                    c.set_lit(0, other); // Move to front of 'c'.
                    break;
                }
                l += 1;
            }

            if l == end_of_c {
                log!(self, "no tautological literal found");

                // Restore old literal order in the clause because.

                while l != 0 {
                    l -= 1;
                    let other = c.lit(l);
                    c.set_lit(l, prev_other);
                    prev_other = other;
                }

                continue; // ... with next candidate 'c' in 'pos'.
            }

            blocked += 1;
            log!(self, c, "blocked");
            if let Some(proof) = self.proof.as_mut() {
                proof.weaken_minus(c);
            }
            self.external().push_clause_on_extension_stack_with_witness(c, lit);
            blocker.reschedule.push(c);
            self.mark_garbage(c);
            j -= 1;
        }
        if j == 0 {
            erase_vector(self.occs_mut(lit));
        } else {
            self.occs_mut(lit).truncate(j);
        }

        self.stats.blocked += blocked;
        log!(self, "blocked {} clauses on {} (skipped {})", blocked, lit, skipped);

        self.unmark_clause_literals(d);
    }

    /*--------------------------------------------------------------------*/

    // Determine the set of candidate clauses with 'lit', which are checked
    // to be blocked by 'lit'.  Filter out too large and small clauses and
    // which do not have any negated other literal in any of the clauses
    // with '-lit'.

    pub fn block_candidates(&mut self, blocker: &mut Blocker, lit: i32) -> usize {
        debug_assert!(blocker.candidates.is_empty());

        debug_assert!(self.noccs(lit) as usize <= self.occs(lit).len());
        debug_assert!(self.noccs(-lit) as usize == self.occs(-lit).len()); // Already flushed.

        // Mark all literals in clauses with '-lit'.  Note that 'mark2' uses
        // separate bits for 'lit' and '-lit'.
        //
        let nos_size = self.occs(-lit).len();
        for k in 0..nos_size {
            let c = self.occs(-lit)[k];
            self.mark2_clause_literals(c);
        }

        let eop = self.occs(lit).len();
        let mut j = 0usize;

        for i in 0..eop {
            let c = self.occs(lit)[i];
            self.occs_mut(lit)[j] = c;
            j += 1;
            if c.garbage() {
                j -= 1;
                continue;
            }
            debug_assert!(!c.redundant());
            if c.size() > self.opts.blockmaxclslim {
                continue;
            }
            if c.size() < self.opts.blockminclslim {
                continue;
            }
            let lits = c.lits();
            let eoc = lits.len();
            let mut l = 0usize;
            while l != eoc {
                let other = lits[l];
                if other == lit {
                    l += 1;
                    continue;
                }
                debug_assert!(other != -lit);
                debug_assert!(self.active(other));
                debug_assert!(self.val(other) == 0);
                if self.marked2(-other) {
                    break;
                }
                l += 1;
            }
            if l != eoc {
                blocker.candidates.push(c);
            }
        }
        if j == 0 {
            erase_vector(self.occs_mut(lit));
        } else {
            self.occs_mut(lit).truncate(j);
        }

        debug_assert!(self.occs(lit).len() == self.noccs(lit) as usize); // Now also flushed.

        for k in 0..nos_size {
            let c = self.occs(-lit)[k];
            self.unmark_clause_literals(c);
        }

        blocker.candidates.len()
    }

    /*--------------------------------------------------------------------*/

    // Try to find a clause with '-lit' which does not have any literal in
    // clauses with 'lit'.  If such a clause exists no candidate clause can
    // be blocked on 'lit' since all candidates would produce a
    // non-tautological resolvent with that clause.

    pub fn block_impossible(&mut self, blocker: &mut Blocker, lit: i32) -> CRef {
        debug_assert!(self.noccs(-lit) > 1);
        debug_assert!(blocker.candidates.len() > 1);

        for &c in blocker.candidates.iter() {
            self.mark2_clause_literals(c);
        }

        let mut res = CRef::NULL;

        for &c in self.occs(-lit).iter() {
            debug_assert!(!c.garbage());
            debug_assert!(!c.redundant());
            debug_assert!(c.size() <= self.opts.blockmaxclslim);
            let lits = c.lits();
            let eoc = lits.len();
            let mut l = 0usize;
            while l != eoc {
                let other = lits[l];
                if other == -lit {
                    l += 1;
                    continue;
                }
                debug_assert!(other != lit);
                debug_assert!(self.active(other));
                debug_assert!(self.val(other) == 0);
                if self.marked2(-other) {
                    break;
                }
                l += 1;
            }
            if l == eoc {
                res = c;
            }
        }

        for &c in blocker.candidates.iter() {
            self.unmark_clause_literals(c);
        }

        if !res.is_null() {
            log!(self, res, "common non-tautological resolvent producing");
            blocker.candidates.clear();
        }

        res
    }

    /*--------------------------------------------------------------------*/

    // In the general case we have at least two negative occurrences.

    pub fn block_literal_with_at_least_two_negative_occs(&mut self, blocker: &mut Blocker, lit: i32) {
        debug_assert!(self.active(lit));
        debug_assert!(!self.frozen(lit));
        debug_assert!(self.noccs(lit) > 0);
        debug_assert!(self.noccs(-lit) > 1);

        debug_assert!(self.noccs(-lit) as usize <= self.occs(-lit).len());

        let mut max_size = 0;

        // Flush all garbage clauses in occurrence list 'nos' of '-lit' and
        // determine the maximum size of negative clauses (with '-lit').
        //
        {
            let nos = self.occs_mut(-lit);
            let eon = nos.len();
            let mut j = 0usize;
            for i in 0..eon {
                let c = nos[i];
                nos[j] = c;
                j += 1;
                if c.garbage() {
                    j -= 1;
                } else if c.size() > max_size {
                    max_size = c.size();
                }
            }
            if j == 0 {
                erase_vector(nos);
            } else {
                nos.truncate(j);
            }
        }

        debug_assert!(self.occs(-lit).len() == self.noccs(-lit) as usize);
        debug_assert!(self.occs(-lit).len() > 1);

        // If the maximum size of a negative clause (with '-lit') exceeds the
        // maximum clause size limit ignore this candidate literal.
        //
        if max_size > self.opts.blockmaxclslim {
            log!(
                self,
                "maximum size {} of clauses with {} exceeds clause size limit {}",
                max_size,
                -lit,
                self.opts.blockmaxclslim
            );
            return;
        }

        log!(self, "maximum size {} of clauses with {}", max_size, -lit);

        // We filter candidate clauses with positive occurrence of 'lit' in
        // 'blocker.candidates' and return if no candidate clause remains.
        // Candidates should be small enough and should have at least one
        // literal which occurs negated in one of the clauses with '-lit'.
        //
        let candidates = self.block_candidates(blocker, lit);
        if candidates == 0 {
            log!(self, "no candidate clauses found");
            return;
        }

        log!(self, "found {} candidate clauses", candidates);

        // We further search for a clause with '-lit' that has no literal
        // negated in any of the candidate clauses (except 'lit').  If such a
        // clause exists, we know that none of the candidates is blocked.
        //
        if candidates > 1 && !self.block_impossible(blocker, lit).is_null() {
            log!(self, "impossible to block any candidate clause on {}", lit);
            debug_assert!(blocker.candidates.is_empty());
            return;
        }

        log!(
            self,
            "trying to block {} clauses out of {} with literal {}",
            candidates,
            self.noccs(lit),
            lit
        );

        let mut blocked: i64 = 0;

        // Go over all remaining candidates and try to block them on 'lit'.
        //
        for k in 0..blocker.candidates.len() {
            let c = blocker.candidates[k];
            debug_assert!(!c.garbage());
            debug_assert!(!c.redundant());
            if !self.is_blocked_clause(c, lit) {
                continue;
            }
            blocked += 1;
            log!(self, c, "blocked");
            if let Some(proof) = self.proof.as_mut() {
                proof.weaken_minus(c);
            }
            self.external().push_clause_on_extension_stack_with_witness(c, lit);
            blocker.reschedule.push(c);
            self.mark_garbage(c);
        }

        log!(
            self,
            "blocked {} clauses on {} out of {} candidates in {} occurrences",
            blocked,
            lit,
            blocker.candidates.len(),
            self.occs(lit).len()
        );

        blocker.candidates.clear();
        self.stats.blocked += blocked;
        if blocked != 0 {
            self.flush_occs(lit);
        }
    }

    /*--------------------------------------------------------------------*/

    // Reschedule literals in a clause (except 'lit') which was blocked.

    pub fn block_reschedule_clause(&mut self, blocker: &mut Blocker, lit: i32, c: CRef) {
        let _ = lit;
        debug_assert!(c.garbage());

        for &other in c.lits() {
            {
                let n = self.noccs_mut(other);
                debug_assert!(*n > 0);
                *n -= 1;
            }

            log!(
                self,
                "updating {} with {} positive and {} negative occurrences",
                other,
                self.noccs(other),
                self.noccs(-other)
            );

            if blocker.schedule.contains(self.vlit(-other)) {
                blocker.schedule.update(self.vlit(-other));
            } else if self.active(other) && !self.frozen(other) && !self.marked_skip(-other) {
                log!(self, "rescheduling to block clauses on {}", -other);
                blocker.schedule.push_back(self.vlit(-other));
            }

            if blocker.schedule.contains(self.vlit(other)) {
                debug_assert!(other != lit);
                blocker.schedule.update(self.vlit(other));
            }
        }
    }

    // Reschedule all literals in clauses blocked by 'lit' (except 'lit').

    pub fn block_reschedule(&mut self, blocker: &mut Blocker, lit: i32) {
        while let Some(c) = blocker.reschedule.pop() {
            self.block_reschedule_clause(blocker, lit, c);
        }
    }

    /*--------------------------------------------------------------------*/

    pub fn block_literal(&mut self, blocker: &mut Blocker, lit: i32) {
        debug_assert!(!self.marked_skip(lit));

        if !self.active(lit) {
            return; // Pure literal '-lit'.
        }
        if self.frozen(lit) {
            return;
        }

        debug_assert!(self.val(lit) == 0);

        // If the maximum number of a negative clauses (with '-lit') exceeds
        // the occurrence limit ignore this candidate literal.
        //
        if self.noccs(-lit) > self.opts.blockocclim as i64 {
            return;
        }

        log!(
            self,
            "blocking literal candidate {} with {} positive and {} negative occurrences",
            lit,
            self.noccs(lit),
            self.noccs(-lit)
        );

        self.stats.blockcands += 1;

        debug_assert!(blocker.reschedule.is_empty());
        debug_assert!(blocker.candidates.is_empty());

        if self.noccs(-lit) == 0 {
            self.block_pure_literal(blocker, lit);
        } else if self.noccs(lit) == 0 {
            // Rare situation, where the clause length limit was hit for
            // 'lit' and '-lit' is skipped and then it becomes pure.  Can be
            // ignored.  We also so it once happening for a 'elimboundmin=-1'
            // and zero positive and one negative occurrence.
        } else if self.noccs(-lit) == 1 {
            self.block_literal_with_one_negative_occ(blocker, lit);
        } else {
            self.block_literal_with_at_least_two_negative_occs(blocker, lit);
        }

        // Done with blocked clause elimination on this literal and we do not
        // have to try blocked clause elimination on it again until
        // irredundant clauses with its negation are removed.
        //
        debug_assert!(!self.frozen(lit)); // just to be sure ...
        self.unmark_block(lit);
    }

    /*--------------------------------------------------------------------*/

    pub fn block(&mut self) -> bool {
        if self.opts.block == 0 {
            return false;
        }
        if self.unsat {
            return false;
        }
        if self.stats.current.irredundant == 0 {
            return false;
        }
        if self.terminated_asynchronously(1) {
            return false;
        }

        if self.propagated < self.trail.len() {
            log!(self, "need to propagate {} units first", self.trail.len() - self.propagated);
            self.init_watches();
            self.connect_watches(false);
            if !self.propagate() {
                log!(self, "propagating units results in empty clause");
                self.learn_empty_clause();
                debug_assert!(self.unsat);
            }
            self.clear_watches();
            self.reset_watches();
            if self.unsat {
                return false;
            }
        }

        start_simplifier!(self, block, BLOCK);

        self.stats.blockings += 1;

        log!(self, "block-{}", self.stats.blockings);

        debug_assert!(self.level == 0);
        debug_assert!(!self.watching());
        debug_assert!(!self.occurring());

        self.mark_satisfied_clauses_as_garbage();

        self.init_occs(); // Occurrence lists for all literals.
        self.init_noccs(); // Number of occurrences to avoid flushing garbage clauses.

        let mut blocker = Blocker::new(self as *mut Internal);
        self.block_schedule(&mut blocker);

        let mut blocked = self.stats.blocked;
        let mut resolutions = self.stats.blockres;
        let mut purelits = self.stats.blockpurelits;
        let mut pured = self.stats.blockpured;

        while !self.terminated_asynchronously(1) && !blocker.schedule.empty() {
            let lit = self.u2i(blocker.schedule.front());
            blocker.schedule.pop_front();
            self.block_literal(&mut blocker, lit);
            self.block_reschedule(&mut blocker, lit);
        }

        blocker.erase();
        self.reset_noccs();
        self.reset_occs();

        resolutions = self.stats.blockres - resolutions;
        blocked = self.stats.blocked - blocked;

        phase!(
            self,
            "block",
            self.stats.blockings,
            "blocked {} clauses in {} resolutions",
            blocked,
            resolutions
        );

        pured = self.stats.blockpured - pured;
        purelits = self.stats.blockpurelits - purelits;

        if pured != 0 {
            self.mark_redundant_clauses_with_eliminated_variables_as_garbage();
        }

        if purelits != 0 {
            phase!(
                self,
                "block",
                self.stats.blockings,
                "found {} pure literals in {} clauses",
                purelits,
                pured
            );
        } else {
            phase!(self, "block", self.stats.blockings, "no pure literals found");
        }

        let quiet = self.opts.reportall == 0 && blocked == 0;
        self.report(b'b', quiet as i32);

        stop_simplifier!(self, block, BLOCK);

        blocked != 0
    }
}

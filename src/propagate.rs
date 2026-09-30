//! Port of `propagate.cpp`.

#[allow(unused_imports)]
use crate::prelude::*;

/*------------------------------------------------------------------------*/

// We are using the address of 'decision_reason' as pseudo reason for
// decisions to distinguish assignment decisions from other assignments.
// Before we added chronological backtracking all learned units were
// assigned at decision level zero ('Solver.level == 0') and we just used a
// zero pointer as reason.  After allowing chronological backtracking units
// were also assigned at higher decision level (but with assignment level
// zero), and it was not possible anymore to just distinguish the case
// 'unit' versus 'decision' by just looking at the current level.  Both had
// a zero pointer as reason.  Now only units have a zero reason and
// decisions need to use the pseudo reason 'decision_reason'.
//
// (The static 'decision_reason_clause' lives in 'clause.rs', see
// 'Internal::decision_reason ()'.)

// External propagation steps use the pseudo reason 'external_reason'.
// The corresponding actual reason clauses are learned only when they are
// relevant in conflict analysis or in root-level fixing steps.

impl Internal {
    // If chronological backtracking is used the actual assignment level
    // might be lower than the current decision level. In this case the
    // assignment level is defined as the maximum level of the literals in
    // the reason clause except the literal for which the clause is a
    // reason.  This function determines this assignment level. For
    // non-chronological backtracking as in classical CDCL this function
    // always returns the current decision level, the concept of assignment
    // level does not make sense, and accordingly this function can be
    // skipped.

    // In case of external propagation, it is implicitly assumed that the
    // assignment level is the level of the literal (since the reason
    // clause, i.e., the set of other literals, is unknown).

    #[inline(always)]
    pub fn assignment_level(&mut self, lit: i32, reason: CRef) -> i32 {
        if reason.is_null() || reason == self.external_reason {
            return self.level;
        }

        let mut res = 0;

        let size = reason.size() as usize;
        for i in 0..size {
            let other = reason.lit(i);
            if other == lit {
                continue;
            }
            debug_assert!(self.val(other) != 0);
            let tmp = self.var(other).level;
            if tmp > res {
                res = tmp;
            }
        }

        res
    }

    // calculate lrat_chain
    //
    pub fn build_chain_for_units(&mut self, lit: i32, reason: CRef, forced: bool) {
        if !self.lrat {
            return;
        }
        if self.assignment_level(lit, reason) != 0 && !forced {
            return;
        }
        debug_assert!(self.lrat_chain.is_empty());
        let size = reason.size() as usize;
        for i in 0..size {
            let reason_lit = reason.lit(i);
            if lit == reason_lit {
                continue;
            }
            debug_assert!(self.val(reason_lit) != 0);
            if self.val(reason_lit) == 0 {
                continue;
            }
            let signed_reason_lit = self.val(reason_lit) as i32 * reason_lit;
            let id = self.unit_id(signed_reason_lit);
            self.lrat_chain.push(id);
        }
        self.lrat_chain.push(reason.id());
    }

    // same code as above but reason is assumed to be conflict and lit is
    // not needed
    //
    pub fn build_chain_for_empty(&mut self) {
        if !self.lrat || !self.lrat_chain.is_empty() {
            return;
        }
        debug_assert!(self.level == 0 || self.in_mode(Mode::BACKBONE));
        debug_assert!(self.lrat_chain.is_empty());
        debug_assert!(!self.conflict.is_null());
        log!(self, self.conflict, "lrat for global empty clause with conflict");
        let conflict = self.conflict;
        let size = conflict.size() as usize;
        for i in 0..size {
            let lit = conflict.lit(i);
            debug_assert!(self.val(lit) < 0);
            let id = self.unit_id(-lit);
            self.lrat_chain.push(id);
        }
        self.lrat_chain.push(conflict.id());
    }

    /*--------------------------------------------------------------------*/

    #[inline(always)]
    pub fn search_assign(&mut self, lit: i32, mut reason: CRef) {
        if self.level != 0 {
            self.require_mode(Mode::SEARCH);
        }

        let idx = self.vidx(lit);
        let from_external = reason == self.external_reason;
        debug_assert!(self.val(idx) == 0);
        debug_assert!(
            !self.flags(idx).eliminated()
                || reason == Internal::decision_reason()
                || reason == self.external_reason
        );
        let lit_level: i32;
        debug_assert!(
            !self.lrat
                || self.level != 0
                || reason == self.external_reason
                || reason == Internal::decision_reason()
                || !self.lrat_chain.is_empty()
        );
        // The following cases are explained in the two comments above
        // before 'decision_reason' and 'assignment_level'.
        //
        // External decision reason means that the propagation was done by
        // an external propagation and the reason clause not known (yet).
        // In that case it is assumed that the propagation is NOT out of
        // order (i.e. lit_level = level), because due to lazy explanation,
        // we can not calculate the real assignment level.
        // The function assignment_level () will also assign the current
        // level to literals with external reason.
        if reason.is_null() {
            lit_level = 0; // unit
        } else if reason == Internal::decision_reason() {
            lit_level = self.level;
            reason = CRef::NULL;
        } else {
            lit_level = self.assignment_level(lit, reason);
        }
        if lit_level == 0 {
            reason = CRef::NULL;
        }

        let trail_size = self.trail.len() as i32;
        {
            let v = &mut self.vtab[idx as usize];
            v.level = lit_level;
            v.trail = trail_size;
            v.reason = reason;
        }
        debug_assert!((self.num_assigned as i32) < self.max_var);
        debug_assert!(self.num_assigned == self.trail.len());
        self.num_assigned += 1;
        if lit_level == 0 && !from_external {
            self.learn_unit_clause(lit); // increases 'stats.fixed'
        }
        debug_assert!(lit_level != 0 || !from_external);
        let tmp = sign(lit) as i8;
        self.set_val(idx, tmp);
        debug_assert!(self.val(lit) > 0); // Just a bit paranoid but useful.
        debug_assert!(self.val(-lit) < 0); // Ditto.
        if !self.searching_lucky_phases {
            self.phases.saved[idx as usize] = tmp; // phase saving during search
        }
        self.trail.push(lit);
        #[cfg(feature = "logging")]
        {
            if lit_level == 0 {
                log!(self, "root-level unit assign {} @ 0", lit);
            } else {
                log!(self, reason, "search assign {} @ {}", lit, lit_level);
            }
        }

        // The C++ code prefetches the first watch of '-lit' here (no
        // semantic effect, not ported).

        self.lrat_chain.clear();
    }

    /*--------------------------------------------------------------------*/

    // External versions of 'search_assign' which are not inlined.  They
    // either are used to assign unit clauses on the root-level, in
    // 'decide' to assign a decision or in 'analyze' to assign the literal
    // 'driven' by a learned clause.  This happens far less frequently than
    // the 'search_assign' above, which is called directly in 'propagate'
    // below and thus is inlined.

    #[inline(never)]
    pub fn assign_unit(&mut self, lit: i32) {
        debug_assert!(self.level == 0);
        self.search_assign(lit, CRef::NULL);
    }

    // Just assume the given literal as decision (increase decision level
    // and assign it).  This is used below in 'decide'.

    #[inline(never)]
    pub fn search_assume_decision(&mut self, lit: i32) {
        self.require_mode(Mode::SEARCH);
        debug_assert!(self.propagated == self.trail.len());
        self.new_trail_level(lit);
        self.notify_decision();
        log!(self, "search decide {}", lit);
        self.search_assign(lit, Internal::decision_reason());
    }

    #[inline(never)]
    pub fn search_assign_driving(&mut self, lit: i32, c: CRef) {
        self.require_mode(Mode::SEARCH);
        self.search_assign(lit, c);
        self.notify_assignments();
    }

    #[inline(never)]
    pub fn search_assign_external(&mut self, lit: i32) {
        self.require_mode(Mode::SEARCH);
        let r = self.external_reason;
        self.search_assign(lit, r);
        self.notify_assignments();
    }

    /*--------------------------------------------------------------------*/

    // The 'propagate' function is usually the hot-spot of a CDCL SAT
    // solver.  The 'trail' stack saves assigned variables and is used here
    // as BFS queue for checking clauses with the negation of assigned
    // variables for being in conflict or whether they produce additional
    // assignments.

    // This version of 'propagate' uses lazy watches and keeps two watched
    // literals at the beginning of the clause.  We also use 'blocking
    // literals' to reduce the number of times clauses have to be visited
    // (2008 JSAT paper by Chu, Harwood and Stuckey).  The watches know if a
    // watched clause is binary, in which case it never has to be visited.
    // If a binary clause is falsified we continue propagating.

    // Finally, for long clauses we save the position of the last watch
    // replacement in 'pos', which in turn reduces certain quadratic
    // accumulated propagation costs (2013 JAIR article by Ian Gent) at the
    // expense of four more bytes for each clause.

    pub fn propagate(&mut self) -> bool {
        if self.level != 0 {
            self.require_mode(Mode::SEARCH);
        }
        debug_assert!(!self.unsat);
        log!(self, "starting propagate");
        start!(self, propagate);

        // Updating statistics counter in the propagation loops is costly so
        // we delay until propagation ran to completion.
        //
        let before = self.propagated as i64;
        let mut ticks: i64 = 0;

        while self.conflict.is_null() && self.propagated != self.trail.len() {
            let lit = -self.trail[self.propagated];
            self.propagated += 1;
            log!(self, "propagating {}", -lit);
            let widx = self.vlit(lit) as usize;

            // We keep a raw pointer to the watch list elements of 'lit'
            // while calling 'search_assign' and 'watch_literal'.
            //
            // SAFETY (for all dereferences of 'ws' below): 'search_assign'
            // never touches any watch list, and 'watch_literal' only pushes
            // to the watches of a literal 'r' (or 's') different from 'lit'
            // (a clause does not contain duplicated literals and 'lit' is
            // one of the two watched literals while 'r' / 's' are taken from
            // positions '>= 2').  Thus the buffer of this watch list is
            // neither reallocated nor accessed through any other path until
            // we truncate it at the end (by re-indexing 'wtab').  The indices
            // 'i' and 'j' always satisfy 'j <= i <= eow == len'.
            let ws: *mut Watch = self.wtab[widx].as_mut_ptr();
            let eow: usize = self.wtab[widx].len();
            let mut j: usize = 0;
            let mut i: usize = 0;
            ticks += 1 + self.cache_lines_n(eow, std::mem::size_of::<Watch>());

            while i != eow {
                // SAFETY: see above ('j <= i < eow').
                let w = unsafe {
                    let w = *ws.add(i);
                    *ws.add(j) = w;
                    w
                };
                i += 1;
                j += 1;
                let b = self.val(w.blit);
                log!(self, w.clause, "checking");

                if b > 0 {
                    continue; // blocking literal satisfied
                }

                if w.binary() {
                    // Binary clauses are treated separately since they do
                    // not require to access the clause at all (only during
                    // conflict analysis, and there also only to simplify
                    // the code).  See the C++ source for the (long)
                    // explanation why garbage binary clauses are not
                    // skipped here.

                    if b < 0 {
                        self.conflict = w.clause; // but continue ...
                    } else {
                        self.build_chain_for_units(w.blit, w.clause, false);
                        self.search_assign(w.blit, w.clause);
                        // lrat_chain.clear (); done in search_assign
                        ticks += 1;
                    }
                } else {
                    debug_assert!(w.clause.size() > 2);

                    if !self.conflict.is_null() {
                        break; // Stop if there was a binary conflict already.
                    }

                    // The cache line with the clause data is forced to be
                    // loaded here and thus this first memory access below
                    // is the real hot-spot of the solver.  Note, that this
                    // check is positive very rarely and thus branch
                    // prediction should be almost perfect here.

                    ticks += 1;

                    let c = w.clause;
                    if c.garbage() {
                        j -= 1;
                        continue;
                    }

                    let lits = c.literals_ptr();
                    // SAFETY: 'lits' points to the 'size >= 3' literals of
                    // the live clause 'c', all accesses below are at
                    // positions '< size'.
                    let (l0, l1) = unsafe { (*lits, *lits.add(1)) };
                    debug_assert!(l0 == lit || l1 == lit);

                    // Simplify code by forcing 'lit' to be the second
                    // literal in the clause.  This goes back to MiniSAT.
                    // We use a branch-less version for conditionally
                    // swapping the first two literals.
                    //
                    let other = l0 ^ l1 ^ lit;
                    let u = self.val(other); // value of the other watch

                    if u > 0 {
                        // satisfied, just replace blit
                        // SAFETY: 'j >= 1' after the copy above.
                        unsafe { (*ws.add(j - 1)).blit = other };
                    } else {
                        // This follows Ian Gent's (JAIR'13) idea of saving
                        // the position of the last watch replacement.  In
                        // essence it needs two copies of the default search
                        // for a watch replacement (in essence the code in
                        // the 'if (v < 0) { ... }' block below), one
                        // starting at the saved position until the end of
                        // the clause and then if that one failed to find a
                        // replacement another one starting at the first
                        // non-watched literal until the saved position.

                        let size = c.size() as usize;
                        let middle = c.pos() as usize;
                        let end = size;
                        let mut k = middle;

                        // Find replacement watch 'r' at position 'k' with
                        // value 'v'.
                        debug_assert!(2 <= k);
                        log!(self, c, "search starting at {}", c.pos());
                        let mut r: i32 = 0;
                        let mut v: i8 = -1;

                        while k != end {
                            // SAFETY: 'k < size'.
                            r = unsafe { *lits.add(k) };
                            v = self.val(r);
                            if v >= 0 {
                                break;
                            }
                            k += 1;
                        }

                        if v < 0 {
                            // need second search starting at the head?

                            k = 2;
                            debug_assert!(c.pos() as usize <= size);
                            while k != middle {
                                // SAFETY: 'k < middle <= size'.
                                r = unsafe { *lits.add(k) };
                                v = self.val(r);
                                if v >= 0 {
                                    break;
                                }
                                k += 1;
                            }
                        }

                        c.set_pos(k as i32); // always save position

                        debug_assert!(2 <= k);
                        debug_assert!(k <= size);

                        if v > 0 {
                            // Replacement satisfied, so just replace 'blit'.

                            // SAFETY: 'j >= 1'.
                            unsafe { (*ws.add(j - 1)).blit = r };
                        } else if v == 0 {
                            // Found new unassigned replacement literal to be
                            // watched.

                            log!(self, c, "unwatch {} in", lit);

                            // SAFETY: '0, 1, k < size'.
                            unsafe {
                                *lits = other;
                                *lits.add(1) = r;
                                *lits.add(k) = lit;
                            }

                            debug_assert!(r != lit);
                            self.watch_literal(r, lit, c);

                            j -= 1; // Drop this watch from the watch list of 'lit'.

                            ticks += 1;
                        } else if u == 0 {
                            debug_assert!(v < 0);

                            // The other watch is unassigned ('!u') and all
                            // other literals assigned to false (still 'v <
                            // 0'), thus we found a unit.
                            //
                            self.build_chain_for_units(other, c, false);
                            self.search_assign(other, c);
                            // lrat_chain.clear (); done in search_assign
                            ticks += 1;

                            // Similar code is in the implementation of the
                            // SAT'18 paper on chronological backtracking but
                            // in our experience, this code first does not
                            // really seem to be necessary for correctness,
                            // and further does not improve running time
                            // either.
                            //
                            if self.opts.chrono > 1 {
                                let other_level = self.var(other).level;

                                if other_level > self.var(lit).level {
                                    // The assignment level of the new unit
                                    // 'other' is larger than the assignment
                                    // level of 'lit'.  Thus we should find
                                    // another literal in the clause at that
                                    // higher assignment level and watch that
                                    // instead of 'lit'.

                                    debug_assert!(size > 2);

                                    let mut pos = 2usize;
                                    let mut s = 0;

                                    while pos < size {
                                        // SAFETY: 'pos < size'.
                                        s = unsafe { *lits.add(pos) };
                                        if self.var(s).level == other_level {
                                            break;
                                        }
                                        pos += 1;
                                    }

                                    debug_assert!(s != 0);
                                    debug_assert!(pos < size);

                                    log!(self, c, "unwatch {} in", lit);
                                    // SAFETY: '0, 1, pos < size'.
                                    unsafe {
                                        *lits.add(pos) = lit;
                                        *lits = other;
                                        *lits.add(1) = s;
                                    }
                                    debug_assert!(s != lit);
                                    self.watch_literal(s, lit, c);

                                    j -= 1; // Drop this watch from the watch list of 'lit'.
                                }
                            }
                        } else {
                            debug_assert!(u < 0);
                            debug_assert!(v < 0);

                            // The other watch is assigned false ('u < 0')
                            // and all other literals as well (still 'v <
                            // 0'), thus we found a conflict.

                            self.conflict = c;
                            break;
                        }
                    }
                }
            }

            if j != i {
                while i != eow {
                    // SAFETY: 'j < i < eow'.
                    unsafe { *ws.add(j) = *ws.add(i) };
                    j += 1;
                    i += 1;
                }

                debug_assert!(self.wtab[widx].len() == eow);
                self.wtab[widx].truncate(j);
            }
        }

        if self.searching_lucky_phases {
            if !self.conflict.is_null() {
                log!(self, self.conflict, "ignoring lucky conflict");
            }
        } else {
            // Avoid updating stats eagerly in the hot-spot of the solver.
            //
            self.stats.propagations.search += self.propagated as i64 - before;
            self.stats.ticks.search[self.stable as usize] += ticks;

            if self.conflict.is_null() {
                self.no_conflict_until = self.propagated;
            } else {
                if self.stable {
                    self.stats.stabconflicts += 1;
                }
                self.stats.conflicts += 1;

                log!(self, self.conflict, "conflict");

                // The trail before the current decision level was conflict
                // free.
                //
                self.no_conflict_until = self.control[self.level as usize].trail as usize;
            }
        }

        if !self.conflict.is_null() && self.randomized_deciding != 0 {
            self.randomized_deciding -= 1;
            if self.randomized_deciding == 0 {
                verbose!(self, 3, "last random decision conflict");
            }
        }
        stop!(self, propagate);

        self.conflict.is_null()
    }

    /*--------------------------------------------------------------------*/

    pub fn propergate(&mut self) {
        debug_assert!(self.conflict.is_null());
        debug_assert!(self.propagated == self.trail.len());

        while self.propergated != self.trail.len() {
            let lit = -self.trail[self.propergated];
            self.propergated += 1;
            log!(self, "propergating {}", -lit);
            let widx = self.vlit(lit) as usize;

            // SAFETY (for all dereferences of 'ws' below): as in
            // 'propagate', 'watch_literal' only pushes to the watches of a
            // literal 'r' different from 'lit', so the buffer of this watch
            // list is neither reallocated nor otherwise accessed until it is
            // truncated below.  Always 'j <= i <= eow == len'.
            let ws: *mut Watch = self.wtab[widx].as_mut_ptr();
            let eow: usize = self.wtab[widx].len();
            let mut j: usize = 0;
            let mut i: usize = 0;

            while i != eow {
                // SAFETY: 'j <= i < eow'.
                let w = unsafe {
                    let w = *ws.add(i);
                    *ws.add(j) = w;
                    w
                };
                i += 1;
                j += 1;
                log!(self, w.clause, "propergate");
                if w.binary() {
                    debug_assert!(self.val(w.blit) > 0);
                    continue;
                }
                let c = w.clause;
                if c.garbage() {
                    j -= 1;
                    continue;
                }

                let lits = c.literals_ptr();

                // SAFETY: clause has 'size >= 3' literals.
                let other = unsafe { *lits ^ *lits.add(1) } ^ lit;
                let u = self.val(other);

                // TODO: check if u == 0 can happen.
                if u > 0 {
                    continue;
                }
                debug_assert!(u < 0);

                let size = c.size() as usize;
                let middle = c.pos() as usize;
                let end = size;
                let mut k = middle;

                let mut r: i32 = 0;
                let mut v: i8 = -1;

                while k != end {
                    // SAFETY: 'k < size'.
                    r = unsafe { *lits.add(k) };
                    v = self.val(r);
                    if v >= 0 {
                        break;
                    }
                    k += 1;
                }

                if v < 0 {
                    k = 2;
                    debug_assert!(c.pos() as usize <= size);
                    while k != middle {
                        // SAFETY: 'k < middle <= size'.
                        r = unsafe { *lits.add(k) };
                        v = self.val(r);
                        if v >= 0 {
                            break;
                        }
                        k += 1;
                    }
                }

                debug_assert!(2 <= k);
                debug_assert!(k <= size);
                c.set_pos(k as i32);

                debug_assert!(v > 0);

                log!(self, c, "unwatch {} in", lit);

                // SAFETY: '0, 1, k < size'.
                unsafe {
                    *lits = other;
                    *lits.add(1) = r;
                    *lits.add(k) = lit;
                }

                debug_assert!(r != lit);
                self.watch_literal(r, lit, c);

                j -= 1;
            }

            if j != i {
                while i != eow {
                    // SAFETY: 'j < i < eow'.
                    unsafe { *ws.add(j) = *ws.add(i) };
                    j += 1;
                    i += 1;
                }

                debug_assert!(self.wtab[widx].len() == eow);
                self.wtab[widx].truncate(j);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct Lcg(u64);
    impl Lcg {
        fn next(&mut self) -> u64 {
            self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            self.0 >> 33
        }
        fn below(&mut self, n: u64) -> u64 {
            self.next() % n
        }
    }

    fn lit_val(internal: &Internal, lit: i32) -> i8 {
        internal.val(lit)
    }

    /// Random formulas with binary and ternary / larger clauses: decide
    /// random literals and check after each 'propagate' that either a
    /// falsified clause was reported, or no clause is falsified or unit
    /// (i.e., propagation reached the fixpoint), and that the two watch
    /// invariant holds.
    #[test]
    fn propagate_reaches_fixpoint_and_keeps_watches() {
        let mut rng = Lcg(12345);
        let mut conflicts = 0;
        for trial in 0..300 {
            let n: i32 = 8 + rng.below(40) as i32;
            let m: usize = (n as usize) * (2 + rng.below(4) as usize);
            let mut internal = Internal::new();
            let ip: *mut Internal = &mut *internal;
            let external = External::new(ip);
            let vsize = (n + 1) as usize;
            internal.enlarge_vals(vsize);
            internal.vsize = vsize;
            internal.max_var = n;
            internal.vtab = vec![Var::default(); vsize];
            internal.ftab = vec![Flags::new(); vsize];
            internal.phases.saved = vec![0; vsize];
            internal.wtab = vec![Vec::new(); 2 * vsize];
            let mut clauses: Vec<CRef> = Vec::new();
            for _ in 0..m {
                let size = if rng.below(4) == 0 { 2 } else { 3 + rng.below(3) as i32 };
                let mut lits: Vec<i32> = Vec::new();
                while (lits.len() as i32) < size {
                    let v = 1 + rng.below(n as u64) as i32;
                    if lits.iter().any(|&l| l.abs() == v) {
                        continue;
                    }
                    lits.push(if rng.below(2) == 0 { v } else { -v });
                }
                let c = CRef::alloc(size);
                c.set_size(size);
                c.set_pos(2);
                c.set_id(clauses.len() as i64 + 1);
                for (i, &l) in lits.iter().enumerate() {
                    c.set_lit(i, l);
                }
                if size == 2 {
                    internal.watch_binary_literal(lits[0], lits[1], c);
                    internal.watch_binary_literal(lits[1], lits[0], c);
                } else {
                    internal.watch_clause(c);
                }
                clauses.push(c);
            }
            loop {
                // decide
                let unassigned: Vec<i32> = (1..=n).filter(|&v| lit_val(&internal, v) == 0).collect();
                if unassigned.is_empty() {
                    break;
                }
                let v = unassigned[rng.below(unassigned.len() as u64) as usize];
                let lit = if rng.below(2) == 0 { v } else { -v };
                internal.new_trail_level(lit);
                internal.search_assign(lit, Internal::decision_reason());
                let ok = internal.propagate();
                assert!(!ok || internal.propagated == internal.trail.len());
                // watch invariant
                for &c in &clauses {
                    let l0 = c.lit(0);
                    let l1 = c.lit(1);
                    for &l in &[l0, l1] {
                        let cnt = internal.watches(l).iter().filter(|w| w.clause == c).count();
                        assert_eq!(cnt, 1, "trial {} clause watched once by {}", trial, l);
                    }
                    for i in 2..c.size() as usize {
                        let l = c.lit(i);
                        assert!(internal.watches(l).iter().all(|w| w.clause != c));
                    }
                }
                if !ok {
                    let conflict = internal.conflict;
                    assert!(conflict.lits().iter().all(|&l| lit_val(&internal, l) < 0));
                    conflicts += 1;
                    break;
                }
                for &c in &clauses {
                    let vals: Vec<i8> = c.lits().iter().map(|&l| lit_val(&internal, l)).collect();
                    if vals.iter().any(|&x| x > 0) {
                        continue;
                    }
                    let unassigned = vals.iter().filter(|&&x| x == 0).count();
                    assert!(unassigned >= 2, "trial {} missed unit or conflict", trial);
                }
                // reasons are correct
                for &l in &internal.trail {
                    let r = internal.var(l).reason;
                    if r.is_null() {
                        continue;
                    }
                    assert!(r.lits().contains(&l));
                    for &o in r.lits() {
                        if o != l {
                            assert!(lit_val(&internal, o) < 0);
                        }
                    }
                }
            }
            internal.conflict = CRef::NULL;
            for c in clauses {
                // SAFETY: allocated with 'alloc' above and no longer used.
                unsafe { c.dealloc() };
            }
            internal.wtab.clear();
            drop(internal);
            drop(external);
        }
        assert!(conflicts > 0);
    }
}

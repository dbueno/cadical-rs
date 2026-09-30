//! Port of `ternary.cpp`.
//!
//! This procedure can be used to produce all possible hyper ternary
//! resolvents from ternary clauses.  In contrast to hyper binary resolution
//! we would only try to produce ternary clauses from ternary clauses, i.e.,
//! do not consider quaternary clauses as antecedents.  Of course if a binary
//! clause is generated we keep it too.  In any case we have to make sure
//! though that we do not add clauses which are already in the formula or
//! are subsumed by a binary clause in the formula.  This procedure
//! simulates structural hashing for multiplexer (if-then-else) and binary
//! XOR gates in combination with equivalent literal substitution
//! ('decompose') if run until to completion (which in the current
//! implementation is too costly though and would need to be interleaved
//! more eagerly with equivalent literal substitution).  For more
//! information see our CPAIOR'13 paper.

#[allow(unused_imports)]
use crate::prelude::*;

use crate::format::fmt_f;
use crate::util::percent;

impl Internal {
    // Check whether a binary clause consisting of the permutation of the
    // given literals already exists.

    pub fn ternary_find_binary_clause(&mut self, a: i32, b: i32) -> bool {
        debug_assert!(self.occurring());
        debug_assert!(self.active(a));
        debug_assert!(self.active(b));
        let s = self.occs(a).len();
        let t = self.occs(b).len();
        let lit = if s < t { a } else { b };
        if self.opts.ternaryocclim < self.occs(lit).len() as i32 {
            return true;
        }
        for &c in self.occs(lit).iter() {
            if c.size() != 2 {
                continue;
            }
            let l0 = c.lit(0);
            let l1 = c.lit(1);
            if l0 == a && l1 == b {
                return true;
            }
            if l0 == b && l1 == a {
                return true;
            }
        }
        false
    }

    /*------------------------------------------------------------------------*/

    // Check whether a ternary clause consisting of the permutation of the
    // given literals already exists or is subsumed by an existing binary
    // clause.

    pub fn ternary_find_ternary_clause(&mut self, a: i32, b: i32, c: i32) -> bool {
        debug_assert!(self.occurring());
        debug_assert!(self.active(a));
        debug_assert!(self.active(b));
        debug_assert!(self.active(c));
        let r = self.occs(a).len();
        let s = self.occs(b).len();
        let t = self.occs(c).len();
        let lit = if r < s {
            if t < r {
                c
            } else {
                a
            }
        } else if t < s {
            c
        } else {
            b
        };
        if self.opts.ternaryocclim < self.occs(lit).len() as i32 {
            return true;
        }
        for &d in self.occs(lit).iter() {
            if d.size() == 2 {
                let l0 = d.lit(0);
                let l1 = d.lit(1);
                if l0 == a && l1 == b {
                    return true;
                }
                if l0 == b && l1 == a {
                    return true;
                }
                if l0 == a && l1 == c {
                    return true;
                }
                if l0 == c && l1 == a {
                    return true;
                }
                if l0 == b && l1 == c {
                    return true;
                }
                if l0 == c && l1 == b {
                    return true;
                }
            } else {
                debug_assert!(d.size() == 3);
                let l0 = d.lit(0);
                let l1 = d.lit(1);
                let l2 = d.lit(2);
                if l0 == a && l1 == b && l2 == c {
                    return true;
                }
                if l0 == a && l1 == c && l2 == b {
                    return true;
                }
                if l0 == b && l1 == a && l2 == c {
                    return true;
                }
                if l0 == b && l1 == c && l2 == a {
                    return true;
                }
                if l0 == c && l1 == a && l2 == b {
                    return true;
                }
                if l0 == c && l1 == b && l2 == a {
                    return true;
                }
            }
        }
        false
    }

    /*------------------------------------------------------------------------*/

    // Try to resolve the two ternary clauses on the given pivot (assumed to
    // occur positively in the first clause, negatively in the second).  If
    // the resolvent has four literals, is tautological, already exists or in
    // the case of a ternary resolvent is subsumed by an existing binary
    // clause then 'false' is returned.  The global 'clause' contains the
    // resolvent and needs to be cleared in any case.

    pub fn hyper_ternary_resolve(&mut self, c: CRef, pivot: i32, d: CRef) -> bool {
        log!(self, "hyper binary resolving on pivot {}", pivot);
        log!(self, c, "1st antecedent");
        log!(self, d, "2nd antecedent");
        self.stats.ternres += 1;
        debug_assert!(c.size() == 3);
        debug_assert!(d.size() == 3);
        debug_assert!(self.clause.is_empty());
        for &lit in c.lits() {
            if lit != pivot {
                self.clause.push(lit);
            }
        }
        for &lit in d.lits() {
            if lit == -pivot {
                continue;
            }
            if lit == self.clause[0] {
                continue;
            }
            if lit == -self.clause[0] {
                return false;
            }
            if lit == self.clause[1] {
                continue;
            }
            if lit == -self.clause[1] {
                return false;
            }
            self.clause.push(lit);
        }
        let size = self.clause.len();
        if size > 3 {
            return false;
        }
        if size == 2 {
            let (a, b) = (self.clause[0], self.clause[1]);
            if self.ternary_find_binary_clause(a, b) {
                return false;
            }
        }
        if size == 3 {
            let (a, b, cc) = (self.clause[0], self.clause[1], self.clause[2]);
            if self.ternary_find_ternary_clause(a, b, cc) {
                return false;
            }
        }
        true
    }

    /*------------------------------------------------------------------------*/

    // Produce all ternary resolvents on literal 'pivot' and increment the
    // 'steps' counter by the number of clauses containing 'pivot' which are
    // used during this process.  The reason for choosing this metric to
    // measure the effort spent in 'ternary' is that it should be similar to
    // one propagation step during search.

    pub fn ternary_lit(&mut self, pivot: i32, steps: &mut i64, htrs: &mut i64) {
        log!(self, "starting hyper ternary resolutions on pivot {}", pivot);
        // 'sizeof (Clause *)' is 8.
        *steps -= 1 + self.cache_lines_n(self.occs(pivot).len(), 8);
        // Neither 'occs (pivot)' nor 'occs (-pivot)' are changed below (the
        // resolvents contain neither 'pivot' nor '-pivot'), thus iterating
        // with indices over a fixed size is the same as the C++ range based
        // for loops.
        let pi = self.vlit(pivot) as usize;
        let ni = self.vlit(-pivot) as usize;
        let pn = self.otab[pi].len();
        for ci in 0..pn {
            let c = self.otab[pi][ci];
            if *steps < 0 {
                break;
            }
            if *htrs < 0 {
                break;
            }
            if c.garbage() {
                continue;
            }
            if c.size() != 3 {
                debug_assert!(c.size() == 2);
                continue;
            }
            *steps -= 1;
            if *steps < 0 {
                break;
            }
            let mut assigned = false;
            for &lit in c.lits() {
                if self.val(lit) != 0 {
                    assigned = true;
                    break;
                }
            }
            if assigned {
                continue;
            }
            *steps -= 1 + self.cache_lines_n(self.otab[ni].len(), 8);
            let nn = self.otab[ni].len();
            for di in 0..nn {
                let d = self.otab[ni][di];
                if *htrs < 0 {
                    break;
                }
                *steps -= 1;
                if *steps < 0 {
                    break;
                }
                if d.garbage() {
                    continue;
                }
                if d.size() != 3 {
                    debug_assert!(d.size() == 2);
                    continue;
                }
                // Note that 'assigned' is not reset here (as in C++).
                for &lit in d.lits() {
                    if self.val(lit) != 0 {
                        assigned = true;
                        break;
                    }
                }
                if assigned {
                    continue;
                }
                debug_assert!(self.clause.is_empty());
                *htrs -= 1;
                if self.hyper_ternary_resolve(c, pivot, d) {
                    let size = self.clause.len();
                    let red = size == 3 || (c.redundant() && d.redundant());
                    if self.lrat {
                        debug_assert!(self.lrat_chain.is_empty());
                        self.lrat_chain.push(c.id());
                        self.lrat_chain.push(d.id());
                    }
                    let r = self.new_hyper_ternary_resolved_clause(red);
                    if red {
                        r.set_hyper(true);
                    }
                    self.lrat_chain.clear();
                    self.clause.clear();
                    log!(self, r, "hyper ternary resolved");
                    self.stats.htrs += 1;
                    for i in 0..r.size() as usize {
                        let lit = r.lit(i);
                        self.occs_mut(lit).push(r);
                    }
                    if size == 2 {
                        log!(self, "hyper ternary resolvent subsumes both antecedents");
                        self.mark_garbage(c);
                        self.mark_garbage(d);
                        self.stats.htrs2 += 1;
                        break;
                    } else {
                        debug_assert!(r.size() == 3);
                        self.stats.htrs3 += 1;
                    }
                } else {
                    log!(self, &self.clause, "ignoring size {} resolvent", self.clause.len());
                    self.clause.clear();
                }
            }
        }
    }

    /*------------------------------------------------------------------------*/

    // Same as 'ternary_lit' but pick the phase of the variable based on the
    // number of positive and negative occurrence.

    pub fn ternary_idx(&mut self, idx: i32, steps: &mut i64, htrs: &mut i64) {
        debug_assert!(0 < idx);
        debug_assert!(idx <= self.max_var);
        *steps -= 3;
        if !self.active(idx) {
            return;
        }
        if !self.flags(idx).ternary {
            return;
        }
        let pos = self.occs(idx).len() as i32;
        let neg = self.occs(-idx).len() as i32;
        if pos <= self.opts.ternaryocclim && neg <= self.opts.ternaryocclim {
            log!(
                self,
                "index {} has {} positive and {} negative occurrences",
                idx,
                self.occs(idx).len(),
                self.occs(-idx).len()
            );
            let pivot = if neg < pos { -idx } else { idx };
            self.ternary_lit(pivot, steps, htrs);
        }
        self.flags_mut(idx).ternary = false;
    }

    /*------------------------------------------------------------------------*/

    // One round of ternary resolution over all variables.  As in 'block' and
    // 'elim' we maintain a persistent global flag 'ternary' for each
    // variable, which records, whether a ternary clause containing it was
    // added.  Then we can focus on those variables for which we have not
    // tried ternary resolution before and nothing changed for them since
    // then.  This works across multiple calls to 'ternary' as well as
    // 'ternary_round' since this 'ternary' variable flag is updated during
    // adding (ternary) resolvents.  This function goes over each variable
    // just once.

    pub fn ternary_round(&mut self, steps_limit: &mut i64, htrs_limit: &mut i64) -> bool {
        debug_assert!(!self.unsat);

        let mut bincon: i64 = 0;
        let mut terncon: i64 = 0;

        self.init_occs();

        *steps_limit -= 1 + self.cache_lines_n(self.clauses.len(), 8);
        for ci in 0..self.clauses.len() {
            let c = self.clauses[ci];
            *steps_limit -= 1;
            if c.garbage() {
                continue;
            }
            if c.size() > 3 {
                continue;
            }
            if self.terminated_asynchronously(1) {
                break;
            }
            let mut assigned = false;
            let mut marked = false;
            for &lit in c.lits() {
                if self.val(lit) != 0 {
                    assigned = true;
                    break;
                }
                if self.flags(lit).ternary {
                    marked = true;
                }
            }
            if assigned {
                continue;
            }
            if c.size() == 2 {
                bincon += 1;
            } else {
                debug_assert!(c.size() == 3);
                if !marked {
                    continue;
                }
                terncon += 1;
            }

            for i in 0..c.size() as usize {
                let lit = c.lit(i);
                self.occs_mut(lit).push(c);
            }
        }

        phase!(
            self,
            "ternary",
            self.stats.ternary,
            "connected {} ternary {}% and {} binary clauses {}%",
            terncon,
            fmt_f(percent(terncon as f64, self.clauses.len() as f64), 0),
            bincon,
            fmt_f(percent(bincon as f64, self.clauses.len() as f64), 0)
        );

        // Try ternary resolution on all variables once.
        //
        for idx in self.vars() {
            if self.terminated_asynchronously(1) {
                break;
            }
            if *steps_limit < 0 {
                break;
            }
            if *htrs_limit < 0 {
                break;
            }
            self.ternary_idx(idx, steps_limit, htrs_limit);
        }

        // Gather some statistics for the verbose messages below and also
        // determine whether new variables have been marked and it would make
        // sense to run another round of ternary resolution over those
        // variables.
        //
        let mut remain = 0;
        for idx in self.vars() {
            if !self.active(idx) {
                continue;
            }
            if !self.flags(idx).ternary {
                continue;
            }
            remain += 1;
        }
        if remain != 0 {
            phase!(
                self,
                "ternary",
                self.stats.ternary,
                "{} variables remain {}%",
                remain,
                fmt_f(percent(remain as f64, self.max_var as f64), 0)
            );
        } else {
            phase!(self, "ternary", self.stats.ternary, "completed hyper ternary resolution");
        }

        self.reset_occs();
        debug_assert!(!self.unsat);

        remain != 0 // Are there variables that should be tried again?
    }

    /*------------------------------------------------------------------------*/

    pub fn ternary(&mut self) -> bool {
        if self.opts.ternary == 0 {
            return false;
        }
        if self.unsat {
            return false;
        }
        if self.terminated_asynchronously(1) {
            return false;
        }

        // No new ternary clauses added since last time?
        //
        if self.last.ternary.marked == self.stats.mark.ternary {
            return false;
        }

        set_effort_limit!(self, limit, ternary, true);

        start_simplifier!(self, ternary, TERNARY);
        self.stats.ternary += 1;

        debug_assert!(self.level == 0);

        debug_assert!(!self.unsat);
        if self.watching() {
            self.reset_watches();
        }

        // The number of clauses derived through ternary resolution can grow
        // substantially, particularly for random formulas.  Thus we limit the
        // number of added clauses too (actually the number of 'htrs').
        //
        let mut htrs_limit: i64 = self.stats.current.redundant + self.stats.current.irredundant;
        htrs_limit *= self.opts.ternarymaxadd as i64;
        htrs_limit /= 100;

        // approximation of ternary ticks.
        // TODO: count with ternary.ticks directly.
        let mut steps_limit: i64 = self.stats.ticks.ternary - limit;
        self.stats.ticks.ternary = limit;

        // With 'stats.ternary' we actually count the number of calls to
        // 'ternary_round' and not the number of calls to 'ternary'. But
        // before the first round we want to show the limit on the number of
        // steps and thus we increase counter for the first round here and
        // skip increasing it in the loop below.
        //
        phase!(
            self,
            "ternary",
            self.stats.ternary,
            "will run a maximum of {} rounds limited to {} steps and {} clauses",
            self.opts.ternaryrounds,
            steps_limit,
            htrs_limit
        );

        let mut resolved_binary_clause = false;
        let mut completed = false;

        let mut round = 0;
        while !self.terminated_asynchronously(1) && round < self.opts.ternaryrounds {
            if htrs_limit < 0 {
                break;
            }
            if steps_limit < 0 {
                break;
            }
            if round != 0 {
                self.stats.ternary += 1;
            }
            let old_htrs2 = self.stats.htrs2 as i32;
            let old_htrs3 = self.stats.htrs3 as i32;
            completed = self.ternary_round(&mut steps_limit, &mut htrs_limit);
            let delta_htrs2 = (self.stats.htrs2 as i32).wrapping_sub(old_htrs2);
            let delta_htrs3 = (self.stats.htrs3 as i32).wrapping_sub(old_htrs3);
            phase!(
                self,
                "ternary",
                self.stats.ternary,
                "derived {} ternary and {} binary resolvents",
                delta_htrs3,
                delta_htrs2
            );
            // Note: C++ checks 'delta_htrs2 + delta_htrs2' here.
            let quiet = self.opts.reportall == 0 && (delta_htrs2 + delta_htrs2) == 0;
            self.report(b'3', quiet as i32);
            if delta_htrs2 != 0 {
                resolved_binary_clause = true;
            }
            if delta_htrs3 == 0 {
                break;
            }
            round += 1;
        }

        debug_assert!(!self.occurring());
        debug_assert!(!self.unsat);
        self.init_watches();
        self.connect_watches(false);
        if !self.propagate() {
            log!(self, "propagation after connecting watches results in inconsistency");
            self.learn_empty_clause();
        }

        if completed {
            self.last.ternary.marked = self.stats.mark.ternary;
        }

        stop_simplifier!(self, ternary, TERNARY);

        resolved_binary_clause
    }
}

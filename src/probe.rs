//! Port of `probe.cpp`.
//!
//! Failed literal probing uses its own propagation and assignment
//! functions.  It further provides on-the-fly generation of hyper binary
//! resolvents but only probes on roots of the binary implication graph.  The
//! search for failed literals is limited, but untried roots are kept until
//! the next time 'probe' is called.  Left over probes from the last attempt
//! and new probes are tried until the limit is hit or all are tried.

#[allow(unused_imports)]
use crate::prelude::*;

use crate::format::fmt_f;
use crate::radix::rsort;
use crate::util::{erase_vector, percent, shrink_vector};

impl Internal {
    pub fn inprobing(&mut self) -> bool {
        if self.opts.inprobing == 0 {
            return false;
        }
        if !self.preprocessing && self.opts.inprocessing == 0 {
            return false;
        }
        if self.preprocessing {
            debug_assert!(self.lim.preprocessing != 0);
        }
        if self.stats.inprobingphases != 0 && self.last.inprobe.reductions == self.stats.reductions {
            return false;
        }
        self.lim.inprobe <= self.stats.conflicts
    }

    /*------------------------------------------------------------------------*/

    #[inline]
    pub fn get_parent_reason_literal(&mut self, lit: i32) -> i32 {
        let idx = self.vidx(lit);
        let mut res = self.parents[idx as usize];
        if lit < 0 {
            res = -res;
        }
        res
    }

    #[inline]
    pub fn set_parent_reason_literal(&mut self, lit: i32, reason: i32) {
        let idx = self.vidx(lit);
        let mut reason = reason;
        if lit < 0 {
            reason = -reason;
        }
        self.parents[idx as usize] = reason;
    }

    /*-----------------------------------------------------------------------*/

    // for opts.probehbr=false we need to do a lot of extra work to remember
    // the correct lrat_chains... This solution is also memory intensive I
    // think all corresponding functions are guarded to only work with the
    // right options so they can be called without checking for options
    //
    // call locally after failed_literal or backtracking
    //
    pub fn clean_probehbr_lrat(&mut self) {
        if !self.lrat || self.opts.probehbr != 0 {
            return;
        }
        for field in self.probehbr_chains.iter_mut() {
            for chain in field.iter_mut() {
                chain.clear();
            }
        }
    }

    // call globally before a probe round (or a lookahead round)
    //
    pub fn init_probehbr_lrat(&mut self) {
        if !self.lrat || self.opts.probehbr != 0 {
            return;
        }
        let size = 2 * (1 + self.max_var as usize);
        self.probehbr_chains.resize(size, Vec::new());
        for i in 0..size {
            self.probehbr_chains[i].resize(size, Vec::new());
        }
    }

    // sets lrat_chain to the stored chain in probehbr_chains.
    // this leads to conflict with unit reason uip
    //
    pub fn get_probehbr_lrat(&mut self, lit: i32, uip: i32) {
        if !self.lrat || self.opts.probehbr != 0 {
            return;
        }
        debug_assert!(lit != 0);
        debug_assert!(self.lrat_chain.is_empty());
        debug_assert!(self.val(uip) < 0);
        let a = self.vlit(lit) as usize;
        let b = self.vlit(uip) as usize;
        self.lrat_chain = self.probehbr_chains[a][b].clone();
        let id = self.unit_id(-uip);
        self.lrat_chain.push(id);
    }

    // sets the corresponding probehbr_chain to what is currently stored in
    // lrat_chain. also clears lrat_chain.
    //
    pub fn set_probehbr_lrat(&mut self, lit: i32, uip: i32) {
        if !self.lrat || self.opts.probehbr != 0 {
            return;
        }
        debug_assert!(lit != 0);
        debug_assert!(!self.lrat_chain.is_empty());
        let a = self.vlit(lit) as usize;
        let b = self.vlit(uip) as usize;
        debug_assert!(self.probehbr_chains[a][b].is_empty());
        self.probehbr_chains[a][b] = self.lrat_chain.clone();
        self.lrat_chain.clear();
    }

    // compute lrat_chain for the part of the tree from lit to dom
    // use mini_chain because it needs to be reversed
    //
    pub fn probe_dominator_lrat(&mut self, dom: i32, reason: CRef) {
        if !self.lrat || dom == 0 {
            return;
        }
        log!(self, reason, "probe dominator LRAT for {} from", dom);
        let size = reason.size() as usize;
        for i in 0..size {
            let lit = reason.lit(i);
            if self.val(lit) >= 0 {
                continue;
            }
            let other = -lit;
            if other == dom {
                continue;
            }
            if self.flags(other).seen {
                continue;
            }
            self.flags_mut(other).seen = true;
            self.analyzed.push(other);
            let u = *self.var(other);
            if u.level != 0 {
                if u.reason.is_null() {
                    log!(self, "this may be a problem {}", other);
                    continue;
                }
                self.probe_dominator_lrat(dom, u.reason);
                continue;
            }
            let id = self.unit_id(other);
            self.lrat_chain.push(id);
        }
        self.lrat_chain.push(reason.id());
    }

    /*------------------------------------------------------------------------*/

    // On-the-fly (dynamic) hyper binary resolution on decision level one can
    // make use of the fact that the implication graph is actually a tree.

    // Compute a dominator of two literals in the binary implication tree.

    pub fn probe_dominator(&mut self, a: i32, b: i32) -> i32 {
        self.require_mode(Mode::PROBE);
        let mut l = a;
        let mut k = b;
        debug_assert!(self.val(l) > 0);
        debug_assert!(self.val(k) > 0);
        debug_assert!(self.var(l).level == 1);
        debug_assert!(self.var(k).level == 1);
        while l != k {
            if self.var(l).trail > self.var(k).trail {
                std::mem::swap(&mut l, &mut k);
            }
            if self.get_parent_reason_literal(l) == 0 {
                return l;
            }
            let parent = self.get_parent_reason_literal(k);
            debug_assert!(parent != 0);
            debug_assert!(self.val(parent) > 0);
            k = parent;
            debug_assert!(self.var(k).level == 1);
        }
        log!(self, "dominator {} of {} and {}", l, a, b);
        debug_assert!(self.val(l) > 0);
        l
    }

    // The idea of dynamic on-the-fly hyper-binary resolution came up in the
    // PrecoSAT solver, where it originally was used on all decision levels.
    //
    // See 'probe.cpp' for the (long) explanation of the special cases (A)
    // and (B).

    #[inline]
    pub fn hyper_binary_resolve(&mut self, reason: CRef) -> i32 {
        self.require_mode(Mode::PROBE);
        debug_assert!(self.level == 1);
        debug_assert!(reason.size() > 2);
        let size = reason.size() as usize;
        #[cfg(debug_assertions)]
        {
            // First literal unassigned, all others false.
            debug_assert!(self.val(reason.lit(0)) == 0);
            for k in 1..size {
                debug_assert!(self.val(reason.lit(k)) < 0);
            }
            debug_assert!(self.var(reason.lit(1)).level == 1);
        }
        log!(self, reason, "hyper binary resolving");
        self.stats.hbrs += 1;
        self.stats.hbrsizes += reason.size() as i64;
        let lit = reason.lit(1);
        let mut dom = -lit;
        let mut non_root_level_literals = 0;
        for k in 2..size {
            let other = -reason.lit(k);
            debug_assert!(self.val(other) > 0);
            if self.var(other).level == 0 {
                continue;
            }
            dom = self.probe_dominator(dom, other);
            non_root_level_literals += 1;
        }
        self.probe_reason = reason;
        if non_root_level_literals != 0 && self.opts.probehbr != 0 {
            // !(A)
            let mut contained = false;
            let mut k = 1;
            while !contained && k != size {
                contained = reason.lit(k) == -dom;
                k += 1;
            }
            let red = !contained || reason.redundant();
            if red {
                self.stats.hbreds += 1;
            }
            log!(
                self,
                "new {} hyper binary resolvent {} {}",
                if red { "redundant" } else { "irredundant" },
                -dom,
                reason.lit(0)
            );
            debug_assert!(self.clause.is_empty());
            self.clause.push(-dom);
            self.clause.push(reason.lit(0));
            self.probe_dominator_lrat(dom, reason);
            if self.lrat {
                self.clear_analyzed_literals();
            }
            let c = self.new_hyper_binary_resolved_clause(red, 2);
            self.probe_reason = c;
            if red {
                c.set_hyper(true);
            }
            self.clause.clear();
            self.lrat_chain.clear();
            if contained {
                self.stats.hbrsubs += 1;
                log!(self, reason, "subsumed original");
                self.mark_garbage(reason);
            }
        } else if non_root_level_literals != 0 && self.lrat {
            // still calculate LRAT and remember for later
            debug_assert!(self.opts.probehbr == 0);
            self.probe_dominator_lrat(dom, reason);
            self.clear_analyzed_literals();
            let lit0 = reason.lit(0);
            self.set_probehbr_lrat(dom, lit0);
        }
        dom
    }

    /*------------------------------------------------------------------------*/

    // The following functions 'probe_assign' and 'probe_propagate' are used
    // for propagating during failed literal probing in simplification mode,
    // as replacement of the generic propagation routine 'propagate' and
    // 'search_assign'.

    #[inline]
    pub fn probe_assign(&mut self, lit: i32, parent: i32) {
        self.require_mode(Mode::PROBE);
        let idx = self.vidx(lit);
        debug_assert!(self.val(idx) == 0);
        debug_assert!(!self.flags(idx).eliminated() || parent == 0);
        debug_assert!(parent == 0 || self.val(parent) > 0);
        let level = self.level;
        let trail_size = self.trail.len() as i32;
        let reason = if level != 0 { self.probe_reason } else { CRef::NULL };
        {
            let v = self.var_mut(idx);
            v.level = level;
            v.trail = trail_size;
            v.reason = reason;
        }
        debug_assert!((self.num_assigned as i32) < self.max_var);
        self.num_assigned += 1;
        self.probe_reason = CRef::NULL;
        self.set_parent_reason_literal(lit, parent);
        if level == 0 {
            self.learn_unit_clause(lit);
        } else {
            debug_assert!(level == 1);
        }
        let tmp = sign(lit) as i8;
        self.set_val(idx, tmp);
        debug_assert!(self.val(lit) > 0);
        debug_assert!(self.val(-lit) < 0);
        self.trail.push(lit);

        // Do not save the current phase during inprocessing but remember the
        // number of units on the trail of the last time this literal was
        // assigned.  This allows us to avoid some redundant failed literal
        // probing attempts.  Search for 'propfixed' in 'probe.cpp' for
        // details.
        //
        if level != 0 {
            let fixed = self.stats.all.fixed as i32;
            *self.propfixed_mut(lit) = fixed;
        }

        if parent != 0 {
            log!(self, "probe assign {} parent {}", lit, parent);
        } else if level != 0 {
            log!(self, "probe assign {} probe", lit);
        } else {
            log!(self, "probe assign {} negated failed literal UIP", lit);
        }
    }

    pub fn probe_assign_decision(&mut self, lit: i32) {
        self.require_mode(Mode::PROBE);
        debug_assert!(self.level == 0);
        debug_assert!(self.propagated == self.trail.len());
        self.level += 1;
        let t = self.trail.len() as i32;
        self.control.push(Level::new(lit, t));
        self.probe_assign(lit, 0);
    }

    pub fn probe_assign_unit(&mut self, lit: i32) {
        self.require_mode(Mode::PROBE);
        debug_assert!(self.level == 0);
        debug_assert!(self.active(lit));
        self.probe_assign(lit, 0);
    }

    /*------------------------------------------------------------------------*/

    // same as in propagate but inlined here
    //
    #[inline]
    pub fn probe_lrat_for_units(&mut self, lit: i32) {
        if !self.lrat {
            return;
        }
        if self.level != 0 {
            return; // not decision level 0
        }
        log!(self, "building chain for units");
        debug_assert!(self.lrat_chain.is_empty());
        debug_assert!(!self.probe_reason.is_null());
        let probe_reason = self.probe_reason;
        let size = probe_reason.size() as usize;
        for i in 0..size {
            let reason_lit = probe_reason.lit(i);
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
        self.lrat_chain.push(probe_reason.id());
    }

    /*------------------------------------------------------------------------*/

    // This is essentially the same as 'propagate' except that we prioritize
    // and always propagate binary clauses first (see our CPAIOR'13 paper on
    // tree based look ahead), then immediately stop at a conflict and of
    // course use 'probe_assign' instead of 'search_assign'.  The binary
    // propagation part is factored out too.  If a new unit on decision level
    // one is found we perform hyper binary resolution and thus actually
    // build an implication tree instead of a DAG.  Statistics counters are
    // also different.

    #[inline]
    pub fn probe_propagate2(&mut self) {
        self.require_mode(Mode::PROBE);
        while self.propagated2 != self.trail.len() {
            let lit = -self.trail[self.propagated2];
            self.propagated2 += 1;
            log!(self, "probe propagating {} over binary clauses", -lit);
            let wi = self.vlit(lit) as usize;
            let n = self.wtab[wi].len();
            // 'sizeof (const_watch_iterator *)' is 8.
            self.stats.ticks.probe += 1 + self.cache_lines_n(n, 8);
            // The watch list of 'lit' is not changed by 'probe_assign' (range
            // based for loop in C++ evaluates 'end' once).
            for k in 0..n {
                let w = self.wtab[wi][k];
                if !w.binary() {
                    continue;
                }
                let b = self.val(w.blit);
                if b > 0 {
                    continue;
                }
                self.stats.ticks.probe += 1;
                if b < 0 {
                    self.conflict = w.clause; // but continue
                } else {
                    debug_assert!(self.lrat_chain.is_empty());
                    debug_assert!(self.probe_reason.is_null());
                    self.probe_reason = w.clause;
                    self.probe_lrat_for_units(w.blit);
                    self.probe_assign(w.blit, -lit);
                    self.lrat_chain.clear();
                }
            }
        }
    }

    pub fn probe_propagate(&mut self) -> bool {
        self.require_mode(Mode::PROBE);
        debug_assert!(!self.unsat);
        start!(self, propagate);
        self.propagated2 = self.propagated;
        let before = self.propagated2 as i64;
        while self.conflict.is_null() {
            if self.propagated2 != self.trail.len() {
                self.probe_propagate2();
            } else if self.propagated != self.trail.len() {
                let lit = -self.trail[self.propagated];
                self.propagated += 1;
                log!(self, "probe propagating {} over large clauses", -lit);
                // Hyper binary resolution might add a watch to this list and
                // thus we use indices and re-index the watch table (as C++).
                let wi = self.vlit(lit) as usize;
                let n = self.wtab[wi].len();
                self.stats.ticks.probe += 1 + self.cache_lines_n(n, 8);
                let mut i = 0usize;
                let mut j = 0usize;
                while i != self.wtab[wi].len() {
                    let w = self.wtab[wi][i];
                    self.wtab[wi][j] = w;
                    i += 1;
                    j += 1;
                    if w.binary() {
                        continue;
                    }
                    let b = self.val(w.blit);
                    if b > 0 {
                        continue;
                    }
                    self.stats.ticks.probe += 1;
                    if w.clause.garbage() {
                        continue;
                    }
                    let c = w.clause;
                    let other = c.lit(0) ^ c.lit(1) ^ lit;
                    // lits[0] = other, lits[1] = lit;
                    let u = self.val(other);
                    if u > 0 {
                        self.wtab[wi][j - 1].blit = other;
                    } else {
                        let size = c.size() as usize;
                        let middle = c.pos() as usize;
                        let mut k = middle;
                        let mut r = 0i32;
                        let mut v: i8 = -1;
                        while k != size && {
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
                        c.set_pos(k as i32);
                        debug_assert!(2 <= k);
                        debug_assert!(k <= size);
                        if v > 0 {
                            self.wtab[wi][j - 1].blit = r;
                        } else if v == 0 {
                            self.stats.ticks.probe += 1;
                            log!(self, c, "unwatch {} in", r);
                            c.set_lit(k, lit);
                            c.set_lit(0, other);
                            c.set_lit(1, r);
                            self.watch_literal(r, lit, c);
                            j -= 1;
                        } else if u == 0 {
                            self.stats.ticks.probe += 1;
                            if self.level == 1 {
                                c.set_lit(0, other);
                                c.set_lit(1, lit);
                                debug_assert!(self.lrat_chain.is_empty());
                                debug_assert!(self.probe_reason.is_null());
                                let dom = self.hyper_binary_resolve(c);
                                self.probe_assign(other, dom);
                            } else {
                                self.stats.ticks.probe += 1;
                                debug_assert!(self.lrat_chain.is_empty());
                                debug_assert!(self.probe_reason.is_null());
                                self.probe_reason = c;
                                self.probe_lrat_for_units(other);
                                self.probe_assign_unit(other);
                                self.lrat_chain.clear();
                            }
                            self.probe_propagate2();
                        } else {
                            self.conflict = c;
                        }
                    }
                }
                if j != i {
                    let ws = &mut self.wtab[wi];
                    while i != ws.len() {
                        ws[j] = ws[i];
                        j += 1;
                        i += 1;
                    }
                    ws.truncate(j);
                }
            } else {
                break;
            }
        }
        let delta = self.propagated2 as i64 - before;
        self.stats.propagations.probe += delta;
        if !self.conflict.is_null() {
            log!(self, self.conflict, "conflict");
        }
        stop!(self, propagate);
        self.conflict.is_null()
    }

    /*------------------------------------------------------------------------*/

    // This a specialized instance of 'analyze'.

    pub fn failed_literal(&mut self, failed: i32) {
        log!(self, "analyzing failed literal probe {}", failed);
        self.stats.failed += 1;
        self.stats.probefailed += 1;

        debug_assert!(!self.unsat);
        debug_assert!(!self.conflict.is_null());
        debug_assert!(self.level == 1);
        debug_assert!(self.analyzed.is_empty());
        debug_assert!(self.lrat_chain.is_empty());

        start!(self, analyze);

        log!(self, self.conflict, "analyzing failed literal conflict");

        let mut uip = 0;
        let conflict = self.conflict;
        let size = conflict.size() as usize;
        for i in 0..size {
            let other = -conflict.lit(i);
            if self.var(other).level == 0 {
                debug_assert!(self.val(other) > 0);
                continue;
            }
            uip = if uip != 0 { self.probe_dominator(uip, other) } else { other };
        }
        self.probe_dominator_lrat(uip, conflict);
        if self.lrat {
            self.clear_analyzed_literals();
        }

        log!(self, "found probing UIP {}", uip);
        debug_assert!(uip != 0);

        let mut work: Vec<i32> = Vec::new();

        let mut parent = uip;
        while parent != failed {
            let next = self.get_parent_reason_literal(parent);
            parent = next;
            debug_assert!(parent != 0);
            work.push(parent);
        }

        self.backtrack(0);
        self.conflict = CRef::NULL;

        debug_assert!(self.val(uip) == 0);
        self.probe_assign_unit(-uip);
        self.lrat_chain.clear();

        if !self.probe_propagate() {
            self.learn_empty_clause();
        }

        let mut j = 0usize;
        while !self.unsat && j < work.len() {
            // assert (!opts.probehbr);        assertion fails ...
            let parent = work[j];
            j += 1;
            let tmp = self.val(parent);
            if tmp > 0 {
                debug_assert!(self.opts.probehbr == 0); // ... assertion should hold here
                self.get_probehbr_lrat(parent, uip);
                log!(self, "clashing failed parent {}", parent);
                self.learn_empty_clause();
            } else if tmp == 0 {
                debug_assert!(self.opts.probehbr == 0); // ... and here
                log!(self, "found unassigned failed parent {}", parent);
                self.get_probehbr_lrat(parent, uip); // this is computed during
                self.probe_assign_unit(-parent); // propagation and can include
                self.lrat_chain.clear(); // multiple chains where only one
                if !self.probe_propagate() {
                    self.learn_empty_clause(); // is needed!
                }
            }
            uip = parent;
        }
        work.clear();
        erase_vector(&mut work);

        stop!(self, analyze);

        debug_assert!(self.unsat || self.val(failed) < 0);
    }

    /*------------------------------------------------------------------------*/

    pub fn is_binary_clause(&mut self, c: CRef, a: &mut i32, b: &mut i32) -> bool {
        debug_assert!(self.level == 0);
        if c.garbage() {
            return false;
        }
        let mut first = 0;
        let mut second = 0;
        for &lit in c.lits() {
            let tmp = self.val(lit);
            if tmp > 0 {
                return false;
            }
            if tmp < 0 {
                continue;
            }
            if second != 0 {
                return false;
            }
            if first != 0 {
                second = lit;
            } else {
                first = lit;
            }
        }
        if second == 0 {
            return false;
        }
        *a = first;
        *b = second;
        true
    }

    // We probe on literals first, which occur more often negated and thus we
    // sort the 'probes' stack in such a way that literals which occur
    // negated less frequently come first.  Probes are taken from the back of
    // the stack.

    fn sort_probes_by_negated_noccs(&mut self) {
        // 'probe_negated_noccs_rank': 'internal->noccs (-a)' as 'size_t'.
        let ntab = &self.ntab;
        let max_var = self.max_var;
        rsort(&mut self.probes, |&a: &i32| {
            let lit = -a;
            debug_assert!(lit != 0 && lit.abs() <= max_var);
            let _ = max_var;
            let vlit = (lit < 0) as usize + 2 * lit.unsigned_abs() as usize;
            ntab[vlit] as usize
        });
    }

    fn count_binary_clause_noccs(&mut self) {
        let n = self.clauses.len();
        self.stats.ticks.probe += 1 + self.cache_lines_n(n, 8);
        for i in 0..n {
            let c = self.clauses[i];
            let mut a = 0;
            let mut b = 0;
            self.stats.ticks.probe += 1;
            if !self.is_binary_clause(c, &mut a, &mut b) {
                continue;
            }
            *self.noccs_mut(a) += 1;
            *self.noccs_mut(b) += 1;
        }
    }

    // Fill the 'probes' schedule.

    pub fn generate_probes(&mut self) {
        debug_assert!(self.probes.is_empty());

        // First determine all the literals which occur in binary clauses. It
        // is way faster to go over the clauses once, instead of walking the
        // watch lists for each literal.
        //
        self.init_noccs();
        self.count_binary_clause_noccs();

        for idx in self.vars() {
            // Then focus on roots of the binary implication graph, which are
            // literals occurring negatively in a binary clause, but not
            // positively.  If neither 'idx' nor '-idx' is a root it makes
            // less sense to probe this variable.

            // This argument requires that equivalent literal substitution
            // through 'decompose' is performed, because otherwise there
            // might be 'cyclic roots' which are not tried, i.e., -1 2 0, 1 -2
            // 0, 1 2 3 0, 1 2 -3 0.

            self.stats.ticks.probe += 2;

            let have_pos_bin_occs = self.noccs(idx) > 0;
            let have_neg_bin_occs = self.noccs(-idx) > 0;

            if have_pos_bin_occs == have_neg_bin_occs {
                continue;
            }

            let probe = if have_neg_bin_occs { idx } else { -idx };

            // See the discussion where 'propfixed' is used below.
            //
            if self.propfixed(probe) as i64 >= self.stats.all.fixed {
                continue;
            }

            log!(self, "scheduling probe {} negated occs {}", probe, self.noccs(-probe));
            self.probes.push(probe);
        }

        self.sort_probes_by_negated_noccs();

        self.reset_noccs();
        shrink_vector(&mut self.probes);

        phase!(
            self,
            "probe-round",
            self.stats.probingrounds,
            "scheduled {} literals {}%",
            self.probes.len(),
            fmt_f(percent(self.probes.len() as f64, (2u32.wrapping_mul(self.max_var as u32)) as f64), 0)
        );
    }

    // Follow the ideas in 'generate_probes' but flush non root probes and
    // reorder remaining probes.

    pub fn flush_probes(&mut self) {
        debug_assert!(!self.probes.is_empty());

        self.init_noccs();
        self.count_binary_clause_noccs();

        let eop = self.probes.len();
        let mut j = 0usize;
        for i in 0..eop {
            let mut lit = self.probes[i];
            if !self.active(lit) {
                continue;
            }
            self.stats.ticks.probe += 2;
            let have_pos_bin_occs = self.noccs(lit) > 0;
            let have_neg_bin_occs = self.noccs(-lit) > 0;
            if have_pos_bin_occs == have_neg_bin_occs {
                continue;
            }
            if have_pos_bin_occs {
                lit = -lit;
            }
            debug_assert!(self.noccs(lit) == 0);
            debug_assert!(self.noccs(-lit) > 0);
            if self.propfixed(lit) as i64 >= self.stats.all.fixed {
                continue;
            }
            log!(self, "keeping probe {} negated occs {}", lit, self.noccs(-lit));
            self.probes[j] = lit;
            j += 1;
        }
        let remain = j;
        let flushed = self.probes.len() - remain;
        self.probes.truncate(remain);

        self.sort_probes_by_negated_noccs();

        self.reset_noccs();
        shrink_vector(&mut self.probes);

        phase!(
            self,
            "probe-round",
            self.stats.probingrounds,
            "flushed {} literals {}% remaining {}",
            flushed,
            fmt_f(percent(flushed as f64, (remain + flushed) as f64), 0),
            remain
        );
    }

    pub fn next_probe(&mut self) -> i32 {
        let mut generated = 0;

        loop {
            if self.probes.is_empty() {
                let g = generated;
                generated += 1;
                if g != 0 {
                    return 0;
                }
                self.generate_probes();
            }

            while let Some(probe) = self.probes.pop() {
                // Eliminated or assigned.
                //
                if !self.active(probe) {
                    continue;
                }

                // There is now new unit since the last time we propagated
                // this probe, thus we propagated it before without obtaining
                // a conflict and nothing changed since then.  Thus there is
                // no need to propagate it again.  This observation was
                // independently made by Partik Simons et.al. in the context
                // of implementing 'smodels' (see for instance Alg. 4 in his
                // JAIR article from 2002) and it has also been contributed to
                // the thesis work of Yacine Boufkhad.
                //
                if self.propfixed(probe) as i64 >= self.stats.all.fixed {
                    continue;
                }

                return probe;
            }
        }
    }

    pub fn probe(&mut self) -> bool {
        if self.opts.probe == 0 {
            return false;
        }
        if self.unsat {
            return false;
        }
        if self.terminated_asynchronously(1) {
            return false;
        }

        set_effort_limit!(self, limit, probe, true);

        start_simplifier!(self, probe, PROBE);
        self.stats.probingrounds += 1;

        // Probing is limited in terms of non-probing propagations
        // 'stats.propagations'. We allow a certain percentage
        // 'opts.probeeffort' (say %5) of probing propagations in each probing
        // with a lower bound of 'opts.probmineff'.
        //

        phase!(
            self,
            "probe-round",
            self.stats.probingrounds,
            "probing limit of {} propagations ",
            limit
        );

        let old_failed = self.stats.failed as i32;
        let old_probed = self.stats.probed;
        let old_hbrs = self.stats.hbrs;

        if !self.probes.is_empty() {
            self.flush_probes();
        }

        // We reset 'propfixed' since there was at least another conflict thus
        // a new learned clause, which might produce new propagations (and
        // hyper binary resolvents).  During 'generate_probes' we keep the old
        // value.
        //
        for idx in self.vars() {
            *self.propfixed_mut(-idx) = -1;
            *self.propfixed_mut(idx) = -1;
        }

        debug_assert!(self.unsat || self.propagated == self.trail.len());
        self.propagated = self.trail.len();
        self.propagated2 = self.trail.len();

        self.init_probehbr_lrat();
        while !self.unsat && !self.terminated_asynchronously(1) && self.stats.ticks.probe < limit {
            let probe = self.next_probe();
            if probe == 0 {
                break;
            }
            self.stats.probed += 1;
            log!(self, "probing {}", probe);
            self.probe_assign_decision(probe);
            if self.probe_propagate() {
                self.backtrack_without_updating_phases(0);
            } else {
                self.failed_literal(probe);
            }
            self.clean_probehbr_lrat();
        }

        if self.unsat {
            log!(self, "probing derived empty clause");
        } else if self.propagated < self.trail.len() {
            log!(self, "probing produced {} units", self.trail.len() - self.propagated);
            if !self.propagate() {
                log!(self, "propagating units after probing results in empty clause");
                self.learn_empty_clause();
            } else {
                self.sort_watches();
            }
        }

        let failed = (self.stats.failed as i32).wrapping_sub(old_failed);
        let probed = self.stats.probed - old_probed;
        let hbrs = self.stats.hbrs - old_hbrs;

        phase!(
            self,
            "probe-round",
            self.stats.probingrounds,
            "probed {} and found {} failed literals",
            probed,
            failed
        );

        if hbrs != 0 {
            phase!(
                self,
                "probe-round",
                self.stats.probingrounds,
                "found {} hyper binary resolvents",
                hbrs
            );
        }

        stop_simplifier!(self, probe, PROBE);

        let quiet = self.opts.reportall == 0 && (self.unsat as i64 + failed as i64 + hbrs) == 0;
        self.report(b'p', quiet as i32);

        !self.unsat && failed != 0
    }

    /*------------------------------------------------------------------------*/

    // This schedules a number of inprocessing techniques (see the long
    // comment in 'probe.cpp').

    /// `update_limits` defaults to `true` in C++
    pub fn inprobe(&mut self, update_limits: bool) {
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

        self.stats.inprobingphases += 1;
        if self.external_prop {
            debug_assert!(self.level == 0);
            self.private_steps = true;
        }
        let before = self.active_count();
        let before_extended = self.stats.variables_extension as i32;

        // schedule of inprobing techniques.
        //
        {
            self.mark_duplicated_binary_clauses_as_garbage();
            self.decompose();
            if self.ternary() {
                self.decompose(); // If we derived a binary clause
            }
            if self.probe() {
                self.decompose();
            }

            let preprocessing = self.preprocessing;
            if self.extract_gates(preprocessing) {
                self.decompose();
            }
            self.binary_clauses_backbone();
            self.mark_duplicated_binary_clauses_as_garbage();
            if self.sweep() {
                // full occurrence list
                self.decompose(); // ... and (ELS) afterwards.
            }
            let _ = self.vivify(); // resets watches
            self.transred(); // builds big.
            self.binary_clauses_backbone();
            self.factor(); // resets watches, partial occurrence list
        }

        if self.external_prop {
            debug_assert!(self.level == 0);
            self.private_steps = false;
        }

        if !update_limits {
            return;
        }

        let after = self.active_count();
        let after_extended = self.stats.variables_extension as i32;
        let diff_extended = after_extended - before_extended;
        debug_assert!(diff_extended >= 0);
        let removed = before - after + diff_extended;
        debug_assert!(removed >= 0);

        if removed != 0 {
            self.stats.inprobesuccess += 1;
            phase!(
                self,
                "probe-phase",
                self.stats.inprobingphases,
                "successfully removed {} active variables {}%",
                removed,
                fmt_f(percent(removed as f64, before as f64), 0)
            );
        } else {
            phase!(
                self,
                "probe-phase",
                self.stats.inprobingphases,
                "could not remove any active variable"
            );
        }

        let delta = ((25 * self.opts.inprobeint as i64) as f64
            * ((self.stats.inprobingphases + 9) as f64).log10()) as i64;
        self.lim.inprobe = self.stats.conflicts + delta;

        phase!(
            self,
            "probe-phase",
            self.stats.inprobingphases,
            "new limit at {} conflicts after {} conflicts",
            self.lim.inprobe,
            delta
        );

        self.last.inprobe.reductions = self.stats.reductions;
    }
}

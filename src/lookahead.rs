//! Port of `lookahead.cpp`.

#[allow(unused_imports)]
use crate::prelude::*;

use std::sync::atomic::Ordering::Relaxed;

#[derive(Clone, Copy, Debug, Default)]
struct literal_occ {
    lit: i32,
    count: i32,
}

impl literal_occ {
    /// `bool operator< (const literal_occ &locc) const`.
    #[inline]
    fn less(&self, locc: &literal_occ) -> bool {
        (self.count > locc.count) || (self.count == locc.count && self.lit < locc.lit)
    }
}

/// `bool non_tautological_cube (std::vector<int> cube)` (only used in an
/// assertion).
#[allow(dead_code)]
fn non_tautological_cube(mut cube: Vec<i32>) -> bool {
    crate::sort::std_sort(&mut cube, clause_lit_less_than);

    let mut i = 0usize;
    let mut j = 1usize;
    while j < cube.len() {
        if cube[i] == cube[j] {
            return false;
        } else if cube[i] == -cube[j] {
            return false;
        } else if cube[i] == 0 {
            return false;
        }
        i += 1;
        j += 1;
    }

    true
}

impl Internal {
    pub fn lookahead_populate_locc(&mut self) -> Vec<i32> {
        let mut loccs: Vec<literal_occ> = vec![literal_occ::default(); self.max_var as usize + 1];
        for (lit, l) in loccs.iter_mut().enumerate() {
            l.lit = lit as i32;
        }
        for &c in self.clauses.iter() {
            if !c.redundant() {
                for &lit in c.lits() {
                    if self.active(lit) {
                        loccs[lit.unsigned_abs() as usize].count += 1;
                    }
                }
            }
        }
        crate::sort::std_sort(&mut loccs, |a, b| a.less(b));
        let mut locc_map: Vec<i32> = Vec::with_capacity(self.max_var as usize);
        for locc in &loccs {
            locc_map.push(locc.lit);
        }
        locc_map
    }

    pub fn lookahead_locc(&mut self, loccs: &[i32]) -> i32 {
        for &lit in loccs {
            if self.active(lit.abs()) && !self.assumed(lit) && !self.assumed(-lit) && self.val(lit) == 0 {
                return lit;
            }
        }
        0
    }

    // This calculates the literal that appears the most often reusing the
    // available datastructures and iterating over the clause set. This is
    // too slow to be called iteratively. A faster (but inexact) version is
    // lookahead_populate_loc and lookahead_loc.
    pub fn most_occurring_literal(&mut self) -> i32 {
        self.init_noccs();
        for ci in 0..self.clauses.len() {
            let c = self.clauses[ci];
            if !c.redundant() {
                for &lit in c.lits() {
                    if self.active(lit) {
                        *self.noccs_mut(lit) += 1;
                    }
                }
            }
        }
        let mut max_noccs: i64 = 0;
        let mut res = 0;

        if self.unsat {
            return i32::MIN;
        }

        self.propagate();
        for idx in 1..=self.max_var {
            if !self.active(idx) || self.assumed(idx) || self.assumed(-idx) || self.val(idx) != 0 {
                continue;
            }
            let mut sign = -1;
            while sign <= 1 {
                let lit = sign * idx;
                sign += 2;
                if !self.active(lit) {
                    continue;
                }
                let tmp = self.noccs(lit);
                if tmp <= max_noccs {
                    continue;
                }
                max_noccs = tmp;
                res = lit;
            }
        }
        msg!(self, "maximum occurrence {} of literal {}", max_noccs, res);
        self.reset_noccs();
        res
    }

    // We probe on literals first, which occur more often negated and thus
    // we sort the 'probes' stack in such a way that literals which occur
    // negated less frequently come first.  Probes are taken from the back
    // of the stack.  ('probe_negated_noccs_rank' is the rank closure given
    // to 'rsort' below.)

    // Follow the ideas in 'generate_probes' but flush non root probes and
    // reorder remaining probes.

    pub fn lookahead_flush_probes(&mut self) {
        debug_assert!(!self.probes.is_empty());

        self.init_noccs();
        for ci in 0..self.clauses.len() {
            let c = self.clauses[ci];
            let mut a = 0;
            let mut b = 0;
            if !self.is_binary_clause(c, &mut a, &mut b) {
                continue;
            }
            *self.noccs_mut(a) += 1;
            *self.noccs_mut(b) += 1;
        }

        let eop = self.probes.len();
        let mut j = 0usize;
        for i in 0..eop {
            let mut lit = self.probes[i];
            if !self.active(lit) {
                continue;
            }
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
            msg!(self, "keeping probe {} negated occs {}", lit, self.noccs(-lit));
            self.probes[j] = lit;
            j += 1;
        }
        let remain = j;
        let flushed = self.probes.len() - remain;
        self.probes.truncate(remain);

        {
            let ntab = &self.ntab;
            let rank = |a: &i32| -> usize {
                let na = -*a;
                let u = (na < 0) as usize + 2 * na.unsigned_abs() as usize;
                ntab[u] as usize
            };
            crate::radix::rsort(&mut self.probes, rank);
        }

        self.reset_noccs();
        shrink_vector(&mut self.probes);

        phase!(
            self,
            "probe-round",
            self.stats.probingrounds,
            "flushed {} literals {}% remaining {}",
            flushed,
            crate::format::fmt_f(percent(flushed as f64, (remain + flushed) as f64), 0),
            remain
        );
    }

    pub fn lookahead_generate_probes(&mut self) {
        debug_assert!(self.probes.is_empty());

        // First determine all the literals which occur in binary clauses.
        // It is way faster to go over the clauses once, instead of walking
        // the watch lists for each literal.
        //
        self.init_noccs();
        for ci in 0..self.clauses.len() {
            let c = self.clauses[ci];
            let mut a = 0;
            let mut b = 0;
            if !self.is_binary_clause(c, &mut a, &mut b) {
                continue;
            }
            *self.noccs_mut(a) += 1;
            *self.noccs_mut(b) += 1;
        }

        for idx in 1..=self.max_var {
            // Then focus on roots of the binary implication graph, which
            // are literals occurring negatively in a binary clause, but not
            // positively.  If neither 'idx' nor '-idx' is a root it makes
            // less sense to probe this variable.

            // This argument requires that equivalent literal substitution
            // through 'decompose' is performed, because otherwise there
            // might be 'cyclic roots' which are not tried, i.e., -1 2 0, 1
            // -2 0, 1 2 3 0, 1 2 -3 0.

            let have_pos_bin_occs = self.noccs(idx) > 0;
            let have_neg_bin_occs = self.noccs(-idx) > 0;

            // if (have_pos_bin_occs == have_neg_bin_occs) continue;

            if have_pos_bin_occs {
                let probe = -idx;

                // See the discussion where 'propfixed' is used below.
                //
                if self.propfixed(probe) as i64 >= self.stats.all.fixed {
                    continue;
                }

                msg!(self, "scheduling probe {} negated occs {}", probe, self.noccs(-probe));
                self.probes.push(probe);
            }

            if have_neg_bin_occs {
                let probe = idx;

                // See the discussion where 'propfixed' is used below.
                //
                if self.propfixed(probe) as i64 >= self.stats.all.fixed {
                    continue;
                }

                msg!(self, "scheduling probe {} negated occs {}", probe, self.noccs(-probe));
                self.probes.push(probe);
            }
        }

        {
            let ntab = &self.ntab;
            let rank = |a: &i32| -> usize {
                let na = -*a;
                let u = (na < 0) as usize + 2 * na.unsigned_abs() as usize;
                ntab[u] as usize
            };
            crate::radix::rsort(&mut self.probes, rank);
        }

        self.reset_noccs();
        shrink_vector(&mut self.probes);

        phase!(
            self,
            "probe-round",
            self.stats.probingrounds,
            "scheduled {} literals {}%",
            self.probes.len(),
            crate::format::fmt_f(percent(self.probes.len() as f64, (2 * self.max_var) as f64), 0)
        );
    }

    pub fn lookahead_next_probe(&mut self) -> i32 {
        let mut generated = 0;

        loop {
            if self.probes.is_empty() {
                let g = generated;
                generated += 1;
                if g != 0 {
                    return 0;
                }
                self.lookahead_generate_probes();
            }

            while let Some(probe) = self.probes.pop() {
                // Eliminated or assigned.
                //
                if !self.active(probe) || self.assumed(probe) || self.assumed(-probe) {
                    continue;
                }

                // There is now new unit since the last time we propagated
                // this probe, thus we propagated it before without obtaining
                // a conflict and nothing changed since then.  Thus there is
                // no need to propagate it again.  This observation was
                // independently made by Partik Simons et.al. in the context
                // of implementing 'smodels' (see for instance Alg. 4 in his
                // JAIR article from 2002) and it has also been contributed
                // to the thesis work of Yacine Boufkhad.
                //
                if self.propfixed(probe) as i64 >= self.stats.all.fixed {
                    continue;
                }

                return probe;
            }
        }
    }

    pub fn terminating_asked(&mut self) -> bool {
        let terminate = match self.external().terminator.as_mut() {
            Some(t) => t.terminate(),
            None => false,
        };
        if terminate {
            msg!(self, "connected terminator forces termination");
            return true;
        }

        if self.termination_forced.load(Relaxed) {
            msg!(self, "termination forced");
            return true;
        }
        false
    }

    // We run probing on all literals with some differences:
    //
    // * no limit on the number of propagations. We rely on terminating to
    // stop()
    // * we run only one round
    //
    // The run can be expensive, so we actually first run the cheaper
    // occurrence version and only then run lookahead.
    //
    pub fn lookahead_probing(&mut self) -> i32 {
        if self.active_count() == 0 {
            return 0;
        }

        msg!(
            self,
            "lookahead-probe-round {} without propagations limit and {} assumptions",
            self.stats.probingrounds,
            self.assumptions.len()
        );

        self.termination_forced.store(false, Relaxed);

        let old_failed = self.stats.failed as i32;
        let old_probed = self.stats.probed;
        let old_hbrs = self.stats.hbrs;

        if self.unsat {
            return i32::MIN;
        }
        if self.level != 0 {
            self.backtrack(0);
        }
        if !self.propagate() {
            msg!(self, "empty clause before probing");
            self.learn_empty_clause();
            return i32::MIN;
        }

        if self.terminating_asked() {
            return self.most_occurring_literal();
        }

        self.decompose();

        if self.ternary() {
            // If we derived a binary clause
            self.decompose(); // then start another round of ELS.
        }

        // Remove duplicated binary clauses and perform in essence hyper
        // unary resolution, i.e., derive the unit '2' from '1 2' and '-1 2'.
        //
        self.mark_duplicated_binary_clauses_as_garbage();

        self.lim.conflicts = -1;

        if !self.probes.is_empty() {
            self.lookahead_flush_probes();
        }

        // We reset 'propfixed' since there was at least another conflict
        // thus a new learned clause, which might produce new propagations
        // (and hyper binary resolvents).  During 'generate_probes' we keep
        // the old value.
        //
        for idx in 1..=self.max_var {
            *self.propfixed_mut(-idx) = -1;
            *self.propfixed_mut(idx) = -1;
        }

        debug_assert!(self.unsat || self.propagated == self.trail.len());
        self.propagated = self.trail.len();
        self.propagated2 = self.trail.len();

        let mut probe;
        let mut res = self.most_occurring_literal();
        let mut max_hbrs: i32 = -1;

        self.set_mode(Mode::PROBE);

        {
            let unsat = self.unsat as i32;
            let asked = self.terminating_asked() as i32;
            msg!(self, "unsat = {}, terminating_asked () = {} ", unsat, asked);
        }
        self.init_probehbr_lrat();
        while !self.unsat && !self.terminating_asked() && {
            probe = self.lookahead_next_probe();
            probe != 0
        } {
            self.stats.probed += 1;
            let hbrs: i32;

            self.probe_assign_decision(probe);
            if self.probe_propagate() {
                hbrs = self.trail.len() as i32;
                self.backtrack(0);
            } else {
                hbrs = 0;
                self.failed_literal(probe);
            }
            self.clean_probehbr_lrat();
            if max_hbrs < hbrs || (max_hbrs == hbrs && self.bumped(probe) > self.bumped(res)) {
                res = probe;
                max_hbrs = hbrs;
            }
        }

        self.reset_mode(Mode::PROBE);

        if self.unsat {
            msg!(self, "probing derived empty clause");
            res = i32::MIN;
        } else if self.propagated < self.trail.len() {
            msg!(self, "probing produced {} units", self.trail.len() - self.propagated);
            if !self.propagate() {
                msg!(self, "propagating units after probing results in empty clause");
                self.learn_empty_clause();
                res = i32::MIN;
            } else {
                self.sort_watches();
            }
        }

        let failed = (self.stats.failed - old_failed as i64) as i32;
        let probed = self.stats.probed - old_probed;
        let hbrs = self.stats.hbrs - old_hbrs;

        msg!(
            self,
            "lookahead-probe-round {} probed {} and found {} failed literals",
            self.stats.probingrounds,
            probed,
            failed
        );

        if hbrs != 0 {
            phase!(
                self,
                "lookahead-probe-round",
                self.stats.probingrounds,
                "found {} hyper binary resolvents",
                hbrs
            );
        }

        msg!(self, "lookahead literal {} with {}\n", res, max_hbrs);

        res
    }

    pub fn generate_cubes(&mut self, depth: i32, min_depth: i32) -> CubesWithStatus {
        if self.active_count() == 0 || depth == 0 {
            let mut cubes = CubesWithStatus::default();
            cubes.status = 0;
            cubes.cubes.push(Vec::new());
            return cubes;
        }

        self.lookingahead = true;
        start!(self, lookahead);
        msg!(self, "Generating cubes of depth {}", depth);

        // presimplify required due to assumptions

        self.termination_forced.store(false, Relaxed);
        let mut res = self.already_solved();
        if res == 0 {
            res = self.restore_clauses();
        }
        if self.unsat {
            res = 10;
        }
        if res != 0 {
            res = self.solve(true);
        }
        if res != 0 {
            msg!(self, "Solved during preprocessing");
            let mut cubes = CubesWithStatus::default();
            cubes.status = res;
            self.lookingahead = false;
            stop!(self, lookahead);
            return cubes;
        }

        self.reset_limits();
        msg!(self, "generate cubes with {} assumptions\n", self.assumptions.len());

        debug_assert!(self.ntab.is_empty());
        let current_assumptions: Vec<i32> = self.assumptions.clone();
        let mut cubes: Vec<Vec<i32>> = vec![self.assumptions.clone()];
        let loccs = self.lookahead_populate_locc();
        log!(self, "loccs populated\n");
        debug_assert!(self.ntab.is_empty());

        for i in 0..depth {
            log!(self, "Probing at depth {}, currently {} have been generated", i, cubes.len());
            let mut cubes2: Vec<Vec<i32>> = std::mem::take(&mut cubes);
            cubes.clear();

            for j in 0..cubes2.len() {
                debug_assert!(self.ntab.is_empty());
                debug_assert!(!self.unsat);
                self.reset_assumptions();
                for k in 0..cubes2[j].len() {
                    let lit = cubes2[j][k];
                    self.assume(lit);
                }
                self.restore_clauses();
                self.propagate();
                // preprocess_round(0); //uncomment maybe

                if self.unsat {
                    log!(self, "current cube is unsat; skipping");
                    self.unsat = false;
                    continue;
                }

                let res = if self.terminating_asked() {
                    self.lookahead_locc(&loccs)
                } else {
                    self.lookahead_probing()
                };
                if self.unsat {
                    log!(self, "current cube is unsat; skipping");
                    self.unsat = false;
                    continue;
                }

                if res == 0 {
                    log!(self, "no lit to split {}", res);
                    cubes.push(cubes2[j].clone());
                    continue;
                }

                debug_assert!(res != 0);
                log!(self, "splitting on lit {}", res);
                let mut cube1: Vec<i32> = cubes2[j].clone();
                cube1.push(res);
                let mut cube2: Vec<i32> = std::mem::take(&mut cubes2[j]);
                cube2.push(-res);
                cubes.push(cube1);
                cubes.push(cube2);
            }

            if self.terminating_asked() && i >= min_depth {
                break;
            }
        }

        // The C++ assertion wraps 'std::for_each' whose result (the lambda)
        // is always true; the lambda is still evaluated on every cube.
        #[cfg(debug_assertions)]
        for cube in &cubes {
            let _ = non_tautological_cube(cube.clone());
        }
        self.reset_assumptions();

        for &lit in &current_assumptions {
            self.assume(lit);
        }

        stop!(self, lookahead);
        self.lookingahead = false;

        if self.unsat {
            log!(self, "Solved during preprocessing");
            let mut cubes = CubesWithStatus::default();
            cubes.status = 20;
            return cubes;
        }

        let mut rcubes = CubesWithStatus::default();
        rcubes.status = 0;
        rcubes.cubes = cubes;

        rcubes
    }
}

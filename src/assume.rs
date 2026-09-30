//! Port of `assume.cpp`: assumptions, failed assumption analysis
//! (MiniSAT's 'analyze_final'), incremental proof conclusion and
//! reusing the trail for assumptions ('ilb').

#[allow(unused_imports)]
use crate::prelude::*;

use crate::radix::msort;
use crate::util::{bign, percent};

impl Internal {
    /// Failed literal handling as pioneered by MiniSAT.  This first
    /// function adds an assumption literal onto the assumption stack.
    pub fn assume(&mut self, lit: i32) {
        if self.level != 0 && self.opts.ilb == 0 {
            self.backtrack(0);
        } else if self.val(lit) < 0 {
            let l = std::cmp::max(0, self.var(lit).level - 1);
            self.backtrack(l);
        }
        let bit = bign(lit) as u8;
        if self.flags(lit).assumed & bit != 0 {
            log!(self, "ignoring already assumed {}", lit);
            return;
        }
        log!(self, "assume {}", lit);
        self.flags_mut(lit).assumed |= bit;
        self.assumptions.push(lit);
        self.freeze(lit);
    }

    /// For LRAT we actually need to implement recursive DFS, for non-LRAT
    /// use BFS.  TODO: maybe derecursify to avoid stack overflow.
    pub fn assume_analyze_literal(&mut self, lit: i32) {
        debug_assert!(lit != 0);
        if self.flags(lit).seen {
            return;
        }
        self.flags_mut(lit).seen = true;
        self.analyzed.push(lit);
        debug_assert!(self.val(lit) < 0);
        if self.var(lit).reason == self.external_reason {
            let reason = self.wrapped_learn_external_reason_clause(-lit);
            self.var_mut(lit).reason = reason;
            debug_assert!(!self.var(lit).reason.is_null() || self.var(lit).level == 0);
        }
        debug_assert!(self.var(lit).reason != self.external_reason);
        if self.var(lit).level == 0 {
            let id = self.unit_id(-lit);
            self.lrat_chain.push(id);
            return;
        }
        let reason = self.var(lit).reason;
        if !reason.is_null() {
            debug_assert!(self.var(lit).level != 0);
            log!(self, reason, "analyze reason");
            let size = reason.size() as usize;
            for i in 0..size {
                let other = reason.lit(i);
                self.assume_analyze_literal(other);
            }
            let id = self.var(lit).reason.id();
            self.lrat_chain.push(id);
            return;
        }
        debug_assert!(self.assumed(-lit));
        log!(self, "failed assumption {}", -lit);
        self.clause.push(lit);
    }

    pub fn assume_analyze_reason(&mut self, lit: i32, reason: CRef) {
        debug_assert!(!reason.is_null());
        debug_assert!(self.lrat_chain.is_empty());
        debug_assert!(reason != self.external_reason);
        debug_assert!(self.lrat);
        let size = reason.size() as usize;
        for i in 0..size {
            let other = reason.lit(i);
            if other != lit {
                self.assume_analyze_literal(other);
            }
        }
        self.lrat_chain.push(reason.id());
    }

    /// Find all failing assumptions starting from the one on the
    /// assumption stack with the lowest decision level.  This goes back to
    /// MiniSAT and is called 'analyze_final' there.
    pub fn failing(&mut self) {
        start!(self, analyze);

        log!(self, "analyzing failing assumptions");

        debug_assert!(self.analyzed.is_empty());
        debug_assert!(self.clause.is_empty());
        debug_assert!(self.lrat_chain.is_empty());
        debug_assert!(!self.marked_failed);
        debug_assert!(self.conflict_id == 0);

        'done: {
            if !self.unsat_constraint {
                // Search for failing assumptions in the (internal)
                // assumption stack.

                // There are in essence three cases: (1) An assumption is
                // falsified on the root-level and then 'failed_unit' is set
                // to that assumption, (2) two clashing assumptions are
                // assumed and then 'failed_clashing' is set to the second
                // assumed one, or otherwise (3) there is a failing
                // assumption 'first_failed' with minimum (non-zero)
                // decision level 'failed_level'.

                let mut failed_unit = 0;
                let mut failed_clashing = 0;
                let mut first_failed = 0;
                let mut failed_level = i32::MAX;
                let mut efailed = 0;

                let n = self.external().assumptions.len();
                for k in 0..n {
                    let elit = self.external().assumptions[k];
                    let mut lit = self.external().e2i[elit.unsigned_abs() as usize];
                    if elit < 0 {
                        lit = -lit;
                    }
                    if self.val(lit) >= 0 {
                        continue;
                    }
                    if self.var(lit).level == 0 {
                        failed_unit = lit;
                        efailed = elit;
                        break;
                    }
                    if failed_clashing != 0 {
                        continue;
                    }
                    if self.var(lit).reason == self.external_reason {
                        let reason = self.learn_external_reason_clause(-lit, 0, false);
                        self.var_mut(lit).reason = reason;
                        if reason.is_null() {
                            self.var_mut(lit).level = 0;
                            failed_unit = lit;
                            efailed = elit;
                            break;
                        }
                        self.var_mut(lit).level = 0;
                        // Recalculate assignment level
                        let size = reason.size() as usize;
                        for i in 0..size {
                            let other = reason.lit(i);
                            if other == -lit {
                                continue;
                            }
                            debug_assert!(self.val(other) != 0);
                            let tmp = self.var(other).level;
                            if tmp > self.var(lit).level {
                                self.var_mut(lit).level = tmp;
                            }
                        }
                        if self.var(lit).level == 0 {
                            failed_unit = lit;
                            efailed = elit;
                            break;
                        }
                    }
                    debug_assert!(self.var(lit).reason != self.external_reason);
                    if self.var(lit).reason.is_null() {
                        failed_clashing = lit;
                        efailed = elit;
                    } else if first_failed == 0 || self.var(lit).level < failed_level {
                        first_failed = lit;
                        efailed = elit;
                        failed_level = self.var(lit).level;
                    }
                }

                debug_assert!(self.clause.is_empty());

                // Get the 'failed' assumption from one of the three cases.
                let failed = if failed_unit != 0 {
                    failed_unit
                } else if failed_clashing != 0 {
                    failed_clashing
                } else {
                    first_failed
                };
                debug_assert!(failed != 0);
                debug_assert!(efailed != 0);

                // In any case mark literal 'failed' as failed assumption.
                {
                    let bit = bign(failed) as u8;
                    debug_assert!(self.flags(failed).failed & bit == 0);
                    self.flags_mut(failed).failed |= bit;
                }

                // First case (1).
                if failed_unit != 0 {
                    debug_assert!(failed == failed_unit);
                    log!(self, "root-level falsified assumption {}", failed);
                    if self.proof.is_some() {
                        if self.lrat {
                            let eidx = (efailed > 0) as u32 + 2u32 * efailed.unsigned_abs();
                            debug_assert!((eidx as usize) < self.external().ext_units.len());
                            let id = self.external().ext_units[eidx as usize];
                            if id != 0 {
                                self.lrat_chain.push(id);
                            } else {
                                let id = self.unit_id(-failed_unit);
                                self.lrat_chain.push(id);
                            }
                        }
                        self.clause_id += 1;
                        let id = self.clause_id;
                        self.proof.as_mut().unwrap().add_assumption_clause_unit(
                            id,
                            -efailed,
                            &self.lrat_chain,
                        );
                        self.conclusion.push(self.clause_id);
                        self.lrat_chain.clear();
                    }
                    break 'done;
                }

                // Second case (2).
                if failed_clashing != 0 {
                    debug_assert!(failed == failed_clashing);
                    log!(self, "clashing assumptions {} and {}", failed, -failed);
                    let bit = bign(-failed) as u8;
                    debug_assert!(self.flags(-failed).failed & bit == 0);
                    self.flags_mut(-failed).failed |= bit;
                    if self.proof.is_some() {
                        let clash = vec![self.externalize(failed), self.externalize(-failed)];
                        self.clause_id += 1;
                        let id = self.clause_id;
                        self.proof.as_mut().unwrap().add_assumption_clause(
                            id,
                            &clash,
                            &self.lrat_chain,
                        );
                        self.conclusion.push(self.clause_id);
                    }
                    break 'done;
                }

                // Fall through to third case (3).
                log!(
                    self,
                    "starting with assumption {} falsified on minimum decision level {}",
                    first_failed,
                    failed_level
                );

                debug_assert!(first_failed != 0);
                debug_assert!(failed_level > 0);

                // The 'analyzed' stack serves as working stack for a BFS
                // through the implication graph until decisions, which are
                // all assumptions, or units are reached.  This is simpler
                // than corresponding code in 'analyze'.
                {
                    log!(self, "failed assumption {}", first_failed);
                    debug_assert!(!self.flags(first_failed).seen);
                    self.flags_mut(first_failed).seen = true;
                    debug_assert!(
                        self.flags(first_failed).failed & bign(first_failed) as u8 != 0
                    );
                    self.analyzed.push(-first_failed);
                    self.clause.push(-first_failed);
                }
            } else {
                // unsat_constraint
                // The assumptions necessary to fail each literal in the
                // constraint are collected.
                let n = self.constraint.len();
                for k in 0..n {
                    let mut lit = self.constraint[k];
                    lit *= -1;
                    debug_assert!(lit != i32::MIN);
                    self.flags_mut(lit).seen = true;
                    self.analyzed.push(lit);
                }
            }

            {
                // used for unsat_constraint lrat
                let mut constraint_chains: Vec<Vec<i64>> = Vec::new();
                let mut constraint_clauses: Vec<Vec<i32>> = Vec::new();
                let mut sum_constraints: Vec<i32> = Vec::new();
                let mut econstraints: Vec<i32> = Vec::new();
                let n = self.external().constraint.len();
                for k in 0..n {
                    let elit = self.external().constraint[k];
                    let mut lit = self.external().e2i[elit.unsigned_abs() as usize];
                    if elit < 0 {
                        lit = -lit;
                    }
                    if lit == 0 {
                        continue;
                    }
                    if self.flags(lit).seen {
                        continue;
                    }
                    if econstraints.contains(&elit) {
                        continue;
                    }
                    econstraints.push(elit);
                }

                // no LRAT do bfs as it was before
                if !self.lrat {
                    let mut next = 0usize;
                    while next < self.analyzed.len() {
                        let lit = self.analyzed[next];
                        next += 1;
                        debug_assert!(self.val(lit) > 0);
                        if self.var(lit).level == 0 {
                            continue;
                        }
                        if self.var(lit).reason == self.external_reason {
                            let reason = self.wrapped_learn_external_reason_clause(lit);
                            self.var_mut(lit).reason = reason;
                            if reason.is_null() {
                                self.var_mut(lit).level = 0;
                                continue;
                            }
                        }
                        debug_assert!(self.var(lit).reason != self.external_reason);
                        let reason = self.var(lit).reason;
                        if !reason.is_null() {
                            debug_assert!(self.var(lit).level != 0);
                            log!(self, reason, "analyze reason");
                            let size = reason.size() as usize;
                            for i in 0..size {
                                let other = reason.lit(i);
                                if self.flags(other).seen {
                                    continue;
                                }
                                self.flags_mut(other).seen = true;
                                debug_assert!(self.val(other) < 0);
                                self.analyzed.push(-other);
                            }
                        } else {
                            debug_assert!(self.assumed(lit));
                            log!(self, "failed assumption {}", lit);
                            self.clause.push(-lit);
                            let bit = bign(lit) as u8;
                            debug_assert!(self.flags(lit).failed & bit == 0);
                            self.flags_mut(lit).failed |= bit;
                        }
                    }
                    self.clear_analyzed_literals();
                } else if !self.unsat_constraint {
                    // LRAT for case (3)
                    debug_assert!(self.clause.len() == 1);
                    let lit = self.clause[0];
                    debug_assert!(!self.var(lit).reason.is_null());
                    if self.var(lit).reason == self.external_reason {
                        // does this even happen?
                        let reason = self.wrapped_learn_external_reason_clause(lit);
                        self.var_mut(lit).reason = reason;
                    }
                    debug_assert!(self.var(lit).reason != self.external_reason);
                    let reason = self.var(lit).reason;
                    if !reason.is_null() {
                        self.assume_analyze_reason(lit, reason);
                    } else {
                        let id = self.unit_id(lit);
                        self.lrat_chain.push(id);
                    }
                    let n = self.clause.len();
                    for k in 0..n {
                        let lit = self.clause[k];
                        let bit = bign(-lit) as u8;
                        if self.flags(lit).failed & bit == 0 {
                            self.flags_mut(lit).failed |= bit;
                        }
                    }
                    self.clear_analyzed_literals();
                } else {
                    // LRAT for unsat_constraint
                    debug_assert!(self.clause.is_empty());
                    self.clear_analyzed_literals();
                    let n = self.constraint.len();
                    for k in 0..n {
                        let lit = self.constraint[k];
                        // make sure nothing gets marked failed twice
                        // also might shortcut the case where
                        // lrat_chain is empty because clause is tautological
                        debug_assert!(lit != i32::MIN);
                        self.assume_analyze_literal(lit);
                        constraint_chains.push(Vec::new());
                        constraint_clauses.push(Vec::new());
                        let m = self.clause.len();
                        for j in 0..m {
                            let ign = self.clause[j];
                            constraint_clauses.last_mut().unwrap().push(ign);
                            let bit = bign(-ign) as u8;
                            if self.flags(ign).failed & bit == 0 {
                                sum_constraints.push(ign);
                                debug_assert!(self.flags(ign).failed & bit == 0);
                                self.flags_mut(ign).failed |= bit;
                            }
                        }
                        self.clause.clear();
                        self.clear_analyzed_literals();
                        for &p in self.lrat_chain.iter() {
                            constraint_chains.last_mut().unwrap().push(p);
                        }
                        self.lrat_chain.clear();
                    }
                    for &lit in sum_constraints.iter() {
                        self.clause.push(lit);
                    }
                }
                self.clear_analyzed_literals();

                // Doing clause minimization here does not do anything
                // because the clause already contains only one literal of
                // each level and minimization can never reduce the number
                // of levels

                verbose!(
                    self,
                    1,
                    "found {} failed assumptions {}%",
                    self.clause.len(),
                    crate::format::fmt_f(
                        percent(self.clause.len() as f64, self.assumptions.len() as f64),
                        0
                    )
                );

                // We do not actually need to learn this clause, since the
                // conflict is forced already by some other clauses.  There
                // is also no bumping of variables nor clauses necessary.
                // But we still want to check correctness of the claim that
                // the determined subset of failing assumptions are a
                // high-level core or equivalently their negations form a
                // unit-implied clause.
                //
                if !self.unsat_constraint {
                    self.external().check_learned_clause();
                    if self.proof.is_some() {
                        let mut eclause: Vec<i32> = Vec::new();
                        for &lit in self.clause.iter() {
                            eclause.push(self.externalize(lit));
                        }
                        self.clause_id += 1;
                        let id = self.clause_id;
                        self.proof.as_mut().unwrap().add_assumption_clause(
                            id,
                            &eclause,
                            &self.lrat_chain,
                        );
                        self.conclusion.push(self.clause_id);
                    }
                } else {
                    debug_assert!(
                        !self.lrat
                            || (self.constraint.len() == constraint_clauses.len()
                                && self.constraint.len() == constraint_chains.len())
                    );
                    let n = self.constraint.len();
                    for k in (0..n).rev() {
                        let lit = self.constraint[k];
                        if self.lrat {
                            self.clause.clear();
                            for &ign in constraint_clauses.last().unwrap().iter() {
                                self.clause.push(ign);
                            }
                            constraint_clauses.pop();
                        }
                        self.clause.push(-lit);
                        self.external().check_learned_clause();
                        if self.proof.is_some() {
                            if self.lrat {
                                for &p in constraint_chains.last().unwrap().iter() {
                                    self.lrat_chain.push(p);
                                }
                                constraint_chains.pop();
                                log!(self, &self.lrat_chain, "assume proof chain with constraints");
                            }
                            let mut eclause: Vec<i32> = Vec::new();
                            for &lit in self.clause.iter() {
                                eclause.push(self.externalize(lit));
                            }
                            self.clause_id += 1;
                            let id = self.clause_id;
                            self.proof.as_mut().unwrap().add_assumption_clause(
                                id,
                                &eclause,
                                &self.lrat_chain,
                            );
                            self.conclusion.push(self.clause_id);
                            self.lrat_chain.clear();
                        }
                        self.clause.pop();
                    }
                    if self.proof.is_some() {
                        for &elit in econstraints.iter() {
                            if self.lrat {
                                let eidx = (elit > 0) as u32 + 2u32 * elit.unsigned_abs();
                                debug_assert!((eidx as usize) < self.external().ext_units.len());
                                let id = self.external().ext_units[eidx as usize];
                                if id != 0 {
                                    self.lrat_chain.push(id);
                                } else {
                                    let mut lit = self.external().e2i[elit.unsigned_abs() as usize];
                                    if elit < 0 {
                                        lit = -lit;
                                    }
                                    let id = self.unit_id(-lit);
                                    self.lrat_chain.push(id);
                                }
                            }
                            self.clause_id += 1;
                            let id = self.clause_id;
                            self.proof.as_mut().unwrap().add_assumption_clause_unit(
                                id,
                                -elit,
                                &self.lrat_chain,
                            );
                            self.conclusion.push(self.clause_id);
                            self.lrat_chain.clear();
                        }
                    }
                }
                self.lrat_chain.clear();
                self.clause.clear();
            }
        }

        // DONE:
        stop!(self, analyze);
    }

    pub fn failed(&mut self, lit: i32) -> bool {
        if !self.marked_failed {
            if self.conflict_id == 0 {
                self.failing();
            }
            self.marked_failed = true;
        }
        self.conclude_unsat();
        let bit = bign(lit) as u8;
        (self.flags(lit).failed & bit) != 0
    }

    pub fn conclude_unsat(&mut self) {
        if self.proof.is_none() || self.concluded {
            return;
        }
        self.concluded = true;
        if !self.marked_failed {
            debug_assert!(self.conclusion.is_empty());
            if self.conflict_id == 0 {
                self.failing();
            }
            self.marked_failed = true;
        }
        let con = if self.conflict_id != 0 {
            ConclusionType::CONFLICT
        } else if self.unsat_constraint {
            ConclusionType::CONSTRAINT
        } else {
            ConclusionType::ASSUMPTIONS
        };
        self.proof.as_mut().unwrap().conclude_unsat(con, &self.conclusion);
    }

    pub fn reset_concluded(&mut self) {
        if let Some(proof) = self.proof.as_mut() {
            proof.reset_assumptions();
        }
        if self.concluded {
            log!(self, "reset concluded");
            self.concluded = false;
        }
        if self.conflict_id != 0 {
            debug_assert!(self.conclusion.len() == 1);
            return;
        }
        self.conclusion.clear();
    }

    /// Add the start of each incremental phase (leaving the state
    /// 'UNSATISFIABLE' actually) we reset all assumptions.
    pub fn reset_assumptions(&mut self) {
        let n = self.assumptions.len();
        for k in 0..n {
            let lit = self.assumptions[k];
            let bit = bign(lit) as u8;
            let f = self.flags_mut(lit);
            f.assumed &= !bit;
            f.failed &= !bit;
            self.melt(lit);
        }
        log!(self, "cleared {} assumptions", self.assumptions.len());
        self.assumptions.clear();
        self.marked_failed = true;
    }

    /// Sort the assumptions by the current position on the trail and
    /// backtrack to the first place where the assumptions and the current
    /// trail differ.
    pub fn sort_and_reuse_assumptions(&mut self) {
        debug_assert!(self.opts.ilb >= 1);
        if self.assumptions.is_empty() {
            if self.opts.ilb == 1 {
                log!(self, "no assumptions, reusing nothing (ilb == 1)");
                self.backtrack(0);
            } else {
                // reuse full trail
                log!(self, "no assumptions, reusing everything (ilb == 2)");
                return;
            }
        }
        {
            let mut assumptions = self.assumptions.clone();
            let this: &Internal = self;
            // Decision level could be 'INT_MAX' and thus 'level + 1' could
            // overflow.  Therefore we carefully have to use 'unsigned' for
            // levels below.
            let max_level: u32 = (this.level as u32).wrapping_add(1);
            // Set assumptions first, then sorted by position on the trail
            // unset literals are sorted by literal value.
            let rank = |a: &i32| -> u64 {
                let val = this.val(*a);
                let assigned = val != 0;
                let v = this.var(*a);
                let mut res: u64 = if assigned { v.level as u32 } else { max_level } as u64;
                res <<= 32;
                res |= (if assigned { v.trail } else { a.abs() }) as u64;
                res
            };
            let less = |a: &i32, b: &i32| -> bool { rank(a) < rank(b) };
            let limit = this.opts.radixsortlim as usize;
            msort(limit, &mut assumptions, rank, less);
            self.assumptions = assumptions;
        }

        let mut max_level: u32 = 0;
        // assumptions are sorted by level, with unset at the end
        for &lit in self.assumptions.iter() {
            if self.val(lit) != 0 {
                max_level = self.var(lit).level as u32;
            } else {
                break;
            }
        }

        let size: u32 = std::cmp::min((self.level as u32).wrapping_add(1), max_level.wrapping_add(1));
        debug_assert!(self.level as usize == self.control.len() - 1);
        log!(self, &self.assumptions, "sorted assumptions");
        let mut target: i32 = 0;
        let mut i: u32 = 1;
        let mut j: usize = 0;
        while i < size {
            let l = self.control[i as usize];
            let lit = l.decision;
            let alit = self.assumptions[j];
            let lev = i as i32;
            target = lev;
            if self.val(alit) > 0 && self.var(alit).level < lev {
                // we can ignore propagated assumptions
                log!(self, "ILB skipping propagation {}", alit);
                j += 1;
                continue;
            }
            if lit == 0 {
                // skip fake decisions
                target = lev - 1;
                break;
            }
            i += 1;
            j += 1;
            debug_assert!(
                self.var(lit).level == lev
                    || self.var(lit).level == 0
                    || !self.var(lit).reason.is_null()
            );
            if l.decision == alit {
                continue;
            }
            target = lev - 1;
            log!(
                self,
                "first different literal {} on the trail and {} from the assumptions",
                lit,
                alit
            );
            break;
        }
        if self.opts.ilb == 1 && target as usize > self.assumptions.len() {
            // reusing only assumptions
            target = self.assumptions.len() as i32;
        }
        if target < self.level {
            self.backtrack_without_updating_phases(target);
        }
        log!(self, "assumptions allow for reuse of trail up to level {}", self.level);
        if self.level as usize > self.assumptions.len() {
            self.stats.assumptionsreused += self.assumptions.len() as i64;
        } else {
            self.stats.assumptionsreused += self.level as i64;
        }
    }
}

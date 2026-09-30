//! Port of `minimize.cpp`.

#[allow(unused_imports)]
use crate::prelude::*;

// Functions for learned clause minimization. We only have the recursive
// version, which actually really is implemented recursively.  We also
// played with a derecursified version, which however was more complex and
// slower.  The trick to keep potential stack exhausting recursion under
// guards is to explicitly limit the recursion depth.

// Instead of signatures as in the original implementation in MiniSAT and
// our corresponding paper, we use the 'poison' idea of Allen Van Gelder to
// mark unsuccessful removal attempts, then Donald Knuth's idea to abort
// minimization if only one literal was seen on the level and a new idea of
// also aborting if the earliest seen literal was assigned afterwards.

impl Internal {
    /// `depth` defaults to `0` in C++
    pub fn minimize_literal(&mut self, lit: i32, depth: i32) -> bool {
        log!(self, "attempt to minimize lit {} at depth {}", lit, depth);
        debug_assert!(self.val(lit) > 0);
        let idx = self.vidx(lit) as usize;
        {
            let f = &self.ftab[idx];
            let v = &self.vtab[idx];
            if v.level == 0 || f.removable || f.keep {
                return true;
            }
            if v.reason.is_null() || f.poison || v.level == self.level {
                return false;
            }
            let l = &self.control[v.level as usize];
            if depth == 0 && l.seen.count < 2 {
                return false; // Don Knuth's idea
            }
            if v.trail <= l.seen.trail {
                return false; // new early abort
            }
            if depth > self.opts.minimizedepth {
                return false;
            }
        }
        let mut res = true;
        debug_assert!(!self.vtab[idx].reason.is_null());
        if self.opts.minimizeticks != 0 {
            self.stats.ticks.search[self.stable as usize] += 1;
        }
        if self.vtab[idx].reason == self.external_reason {
            debug_assert!(self.opts.exteagerreasons == 0);
            let r = self.learn_external_reason_clause(lit, 0, true);
            self.vtab[idx].reason = r;
            if r.is_null() {
                debug_assert!(self.vtab[idx].level == 0);
                return true;
            }
        }
        let reason = self.vtab[idx].reason;
        debug_assert!(reason != self.external_reason);
        let end = reason.size() as usize;
        let mut i = 0usize;
        while res && i != end {
            let other = reason.lit(i);
            i += 1;
            if other == lit {
                continue;
            }
            res = self.minimize_literal(-other, depth + 1);
        }
        {
            let f = &mut self.ftab[idx];
            if res {
                f.removable = true;
            } else {
                f.poison = true;
            }
        }
        self.minimized.push(lit);
        if depth == 0 {
            log!(self, "minimizing {} {}", lit, if res { "succeeded" } else { "failed" });
        }
        res
    }

    // Sorting the clause before minimization with respect to the trail
    // order (literals with smaller trail height first) is necessary but
    // natural and might help to minimize the required recursion depth too.
    //
    // ('minimize_trail_level_positive_rank' and
    // 'minimize_trail_level_smaller' are defined but unused in C++.)

    pub fn minimize_clause(&mut self) {
        start!(self, minimize);
        log!(self, &self.clause, "minimizing first UIP clause");

        self.external().check_learned_clause(); // check 1st UIP learned clause first
        self.minimize_sort_clause();

        debug_assert!(self.minimized.is_empty());
        debug_assert!(self.minimize_chain.is_empty());
        let end = self.clause.len();
        let mut j = 0usize;
        let mut i = 0usize;
        let mut stack: Vec<i32> = Vec::new();
        while i != end {
            let lit = self.clause[i];
            if self.minimize_literal(-lit, 0) {
                if self.lrat {
                    debug_assert!(self.mini_chain.is_empty());
                    self.calculate_minimize_chain(-lit, &mut stack);
                    for k in 0..self.mini_chain.len() {
                        let p = self.mini_chain[k];
                        self.minimize_chain.push(p);
                    }
                    self.mini_chain.clear();
                }
                self.stats.minimized += 1;
            } else {
                self.clause[j] = lit;
                j += 1;
                self.flags_mut(lit).keep = true;
            }
            i += 1;
        }
        log!(self, "minimized {} literals", self.clause.len() - j);
        if j != end {
            self.clause.truncate(j);
        }
        self.clear_minimized_literals();
        for k in (0..self.minimize_chain.len()).rev() {
            let p = self.minimize_chain[k];
            self.lrat_chain.push(p);
        }
        self.minimize_chain.clear();
        stop!(self, minimize);
    }

    // go backwards in reason graph and add ids mini_chain is in correct
    // order so we have to add it to minimize_chain and then reverse when we
    // put it on lrat_chain
    //
    // We have to use the non-recursive as we cannot limit the depth like
    // the minimize version. Unlike the minimize version, we have to keep
    // literals on the stack in order to push its reason later.
    pub fn calculate_minimize_chain(&mut self, lit: i32, stack: &mut Vec<i32>) {
        debug_assert!(stack.is_empty());
        stack.push(self.vidx(lit));
        let _ = lit;

        while let Some(&idx) = stack.last() {
            debug_assert!(idx != 0);
            stack.pop();
            if idx < 0 {
                let id = self.var(idx).reason.id();
                self.mini_chain.push(id);
                continue;
            }
            debug_assert!(idx != 0);
            let uidx = idx as usize;
            {
                let f = &self.ftab[uidx];
                if f.keep || f.added || f.poison {
                    continue;
                }
            }
            let v = self.vtab[uidx];
            if v.level == 0 {
                if self.ftab[uidx].seen {
                    continue;
                }
                self.ftab[uidx].seen = true;
                self.unit_analyzed.push(idx);
                let lit = if self.val(idx) > 0 { idx } else { -idx };
                let id = self.unit_id(lit);
                self.unit_chain.push(id);
                continue;
            }
            self.ftab[uidx].added = true;
            debug_assert!(!v.reason.is_null() && self.ftab[uidx].removable);
            let reason = v.reason;
            let end = reason.size() as usize;
            log!(
                self,
                reason,
                "LRAT chain for lit {} at depth {} by going over",
                lit,
                stack.len()
            );
            stack.push(-idx);
            for i in 0..end {
                let other = reason.lit(i);
                if other == idx {
                    continue;
                }
                stack.push(self.vidx(other));
            }
        }
        debug_assert!(stack.is_empty());
    }

    // Sort the literals in reverse assignment order (thus trail order) to
    // establish the base case of the recursive minimization algorithm in
    // the positive case (where a literal with 'keep' true is hit).
    //
    pub fn minimize_sort_clause(&mut self) {
        let limit = self.opts.radixsortlim as usize;
        let vtab = &self.vtab;
        #[cfg(debug_assertions)]
        let vals = self.vals;
        crate::radix::msort(
            limit,
            &mut self.clause,
            |a: &i32| {
                // SAFETY: 'vals' covers '[-max_var,max_var]'.
                #[cfg(debug_assertions)]
                debug_assert!(unsafe { *vals.offset(*a as isize) } != 0);
                vtab[a.unsigned_abs() as usize].trail as u32
            },
            |a: &i32, b: &i32| vtab[a.unsigned_abs() as usize].trail < vtab[b.unsigned_abs() as usize].trail,
        );
    }

    pub fn clear_minimized_literals(&mut self) {
        log!(self, "clearing {} minimized literals", self.minimized.len());
        for k in 0..self.minimized.len() {
            let lit = self.minimized[k];
            let idx = self.vidx(lit) as usize;
            let f = &mut self.ftab[idx];
            f.poison = false;
            f.removable = false;
            f.shrinkable = false;
            f.added = false;
        }
        for k in 0..self.clause.len() {
            let lit = self.clause[k];
            debug_assert!(!self.flags(lit).shrinkable);
            let idx = self.vidx(lit) as usize;
            let f = &mut self.ftab[idx];
            f.keep = false;
            f.shrinkable = false;
            f.added = false;
        }
        self.minimized.clear();
    }
}

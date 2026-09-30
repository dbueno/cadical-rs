//! Port of `lucky.cpp`.

#[allow(unused_imports)]
use crate::prelude::*;

// It turns out that even in the competition there are formulas which are
// easy to satisfy by either setting all variables to the same truth value
// or by assigning variables to the same value and propagating it.  In the
// latter situation this can be done either in the order of all variables
// (forward or backward) or in the order of all clauses.  These lucky
// assignments can be tested initially in a kind of pre-solving step.

impl Internal {
    // This function factors out clean up code common among the 'lucky'
    // functions for backtracking and resetting a potential conflict.  One
    // could also use exceptions here, but there are two different reasons
    // for aborting early.  The first kind of aborting is due to
    // asynchronous termination and the second kind due to a situation in
    // which it is clear that a particular function will not be successful
    // (for instance a completely negative clause is found).  The latter
    // situation returns zero and will just abort the particular lucky
    // function, while the former will abort all (by returning '-1').

    pub fn unlucky(&mut self, res: i32) -> i32 {
        if self.level > 0 {
            self.backtrack_without_updating_phases(0);
        }
        if self.conflict.is_some() {
            self.conflict = CRef::NULL;
        }
        res
    }

    pub fn trivially_false_satisfiable(&mut self) -> i32 {
        if self.terminated_asynchronously(1) {
            return -1;
        }
        log!(self, "checking that all clauses contain a negative literal");
        debug_assert!(self.level == 0);
        let res = self.lucky_decide_assumptions();
        if res != 0 {
            return res;
        }
        let n = self.clauses.len();
        for ci in 0..n {
            let c = self.clauses[ci];
            if self.terminated_asynchronously(100) {
                return self.unlucky(-1);
            }
            if c.garbage() {
                continue;
            }
            if c.redundant() {
                continue;
            }
            let mut satisfied = false;
            let mut found_negative_literal = false;
            for &lit in c.lits() {
                let tmp = self.val(lit);
                if tmp > 0 {
                    satisfied = true;
                    break;
                }
                if tmp < 0 {
                    continue;
                }
                if lit > 0 {
                    continue;
                }
                found_negative_literal = true;
                break;
            }
            if satisfied || found_negative_literal {
                continue;
            }
            log!(self, c, "found purely positively");
            return self.unlucky(0);
        }
        verbose!(self, 1, "all clauses contain a negative literal");
        for idx in self.vars() {
            if self.terminated_asynchronously(10) {
                return self.unlucky(-1);
            }
            if self.val(idx) != 0 {
                continue;
            }
            self.search_assume_decision(-idx);
            if self.propagate() {
                continue;
            }
            debug_assert!(self.level > 0);
            log!(self, "propagation failed including redundant clauses");
            return self.unlucky(0);
        }
        self.stats.lucky.constant.zero += 1;
        10
    }

    pub fn trivially_true_satisfiable(&mut self) -> i32 {
        if self.terminated_asynchronously(1) {
            return -1;
        }
        log!(self, "checking that all clauses contain a positive literal");
        debug_assert!(self.level == 0);
        let res = self.lucky_decide_assumptions();
        if res != 0 {
            return res;
        }
        let n = self.clauses.len();
        for ci in 0..n {
            let c = self.clauses[ci];
            if self.terminated_asynchronously(100) {
                return self.unlucky(-1);
            }
            if c.garbage() {
                continue;
            }
            if c.redundant() {
                continue;
            }
            let mut satisfied = false;
            let mut found_positive_literal = false;
            for &lit in c.lits() {
                let tmp = self.val(lit);
                if tmp > 0 {
                    satisfied = true;
                    break;
                }
                if tmp < 0 {
                    continue;
                }
                if lit < 0 {
                    continue;
                }
                found_positive_literal = true;
                break;
            }
            if satisfied || found_positive_literal {
                continue;
            }
            log!(self, c, "found purely negatively");
            return self.unlucky(0);
        }
        verbose!(self, 1, "all clauses contain a positive literal");
        for idx in self.vars() {
            if self.terminated_asynchronously(10) {
                return self.unlucky(-1);
            }
            if self.val(idx) != 0 {
                continue;
            }
            self.search_assume_decision(idx);
            if self.propagate() {
                continue;
            }
            debug_assert!(self.level > 0);
            log!(self, "propagation failed including redundant clauses");
            return self.unlucky(0);
        }
        self.stats.lucky.constant.one += 1;
        10
    }

    /*------------------------------------------------------------------------*/

    #[inline]
    pub fn lucky_propagate_discrepency(&mut self, dec: i32) -> bool {
        self.search_assume_decision(dec);
        let mut no_conflict = self.propagate();
        if no_conflict {
            return false;
        }
        if self.level > 1 {
            self.conflict = CRef::NULL;
            let new_level = self.level - 1;
            self.backtrack_without_updating_phases(new_level);
            self.search_assume_decision(-dec);
            no_conflict = self.propagate();
            if no_conflict {
                return false;
            }
            return true;
        } else {
            self.analyze();
            debug_assert!(self.level == 0);
            no_conflict = self.propagate();
            if !no_conflict {
                self.analyze();
                log!(self, "lucky inconsistency backward assigning to true");
                return true;
            }
        }
        false
    }

    /// Common body of the four forward / backward functions (the C++ code
    /// repeats it with 'goto START').  Returns 'Some (res)' if the caller
    /// should return 'res'.
    #[inline]
    fn lucky_discrepency_idx(&mut self, idx: i32, dec: i32, factor: i32) -> Option<i32> {
        loop {
            // START:
            if self.terminated_asynchronously(factor) {
                return Some(self.unlucky(-1));
            }
            if self.val(idx) != 0 {
                return None;
            }
            if self.lucky_propagate_discrepency(dec) {
                if self.unsat {
                    return Some(20);
                } else {
                    return Some(self.unlucky(0));
                }
            }
            // else goto START
        }
    }

    pub fn forward_false_satisfiable(&mut self) -> i32 {
        if self.terminated_asynchronously(1) {
            return -1;
        }
        log!(self, "checking increasing variable index false assignment");
        debug_assert!(!self.unsat);
        debug_assert!(self.level == 0);
        let res = self.lucky_decide_assumptions();
        if res != 0 {
            return res;
        }
        for idx in self.vars() {
            if let Some(res) = self.lucky_discrepency_idx(idx, -idx, 100) {
                return res;
            }
        }
        verbose!(self, 1, "forward assuming variables false satisfies formula");
        debug_assert!(self.satisfied());
        self.stats.lucky.forward.zero += 1;
        10
    }

    pub fn forward_true_satisfiable(&mut self) -> i32 {
        if self.terminated_asynchronously(1) {
            return -1;
        }
        log!(self, "checking increasing variable index true assignment");
        debug_assert!(!self.unsat);
        debug_assert!(self.level == 0);
        let res = self.lucky_decide_assumptions();
        if res != 0 {
            return res;
        }
        for idx in self.vars() {
            if let Some(res) = self.lucky_discrepency_idx(idx, idx, 10) {
                return res;
            }
        }
        verbose!(self, 1, "forward assuming variables true satisfies formula");
        debug_assert!(self.satisfied());
        self.stats.lucky.forward.one += 1;
        10
    }

    /*------------------------------------------------------------------------*/

    pub fn backward_false_satisfiable(&mut self) -> i32 {
        if self.terminated_asynchronously(1) {
            return -1;
        }
        log!(self, "checking decreasing variable index false assignment");
        debug_assert!(!self.unsat);
        debug_assert!(self.level == 0);
        let res = self.lucky_decide_assumptions();
        if res != 0 {
            return res;
        }
        for idx in crate::range::Range::reversed(self.max_var) {
            if let Some(res) = self.lucky_discrepency_idx(idx, -idx, 10) {
                return res;
            }
        }
        verbose!(self, 1, "backward assuming variables false satisfies formula");
        debug_assert!(self.satisfied());
        self.stats.lucky.backward.zero += 1;
        10
    }

    pub fn backward_true_satisfiable(&mut self) -> i32 {
        if self.terminated_asynchronously(1) {
            return -1;
        }
        log!(self, "checking decreasing variable index true assignment");
        debug_assert!(!self.unsat);
        debug_assert!(self.level == 0);
        let res = self.lucky_decide_assumptions();
        if res != 0 {
            return res;
        }
        for idx in crate::range::Range::reversed(self.max_var) {
            if let Some(res) = self.lucky_discrepency_idx(idx, idx, 10) {
                return res;
            }
        }
        verbose!(self, 1, "backward assuming variables true satisfies formula");
        debug_assert!(self.satisfied());
        self.stats.lucky.backward.one += 1;
        10
    }

    /*------------------------------------------------------------------------*/

    // The following two functions test if the formula is a satisfiable horn
    // formula.  Actually the test is slightly more general.  It goes over
    // all clauses and assigns the first positive literal to true and
    // propagates.  Already satisfied clauses are of course skipped.  A
    // reverse function is not implemented yet.

    pub fn positive_horn_satisfiable(&mut self) -> i32 {
        if self.terminated_asynchronously(1) {
            return -1;
        }
        log!(self, "checking that all clauses are positive horn satisfiable");
        debug_assert!(self.level == 0);
        let res = self.lucky_decide_assumptions();
        if res != 0 {
            return res;
        }
        let n = self.clauses.len();
        for ci in 0..n {
            let c = self.clauses[ci];
            if self.terminated_asynchronously(10) {
                return self.unlucky(-1);
            }
            if c.garbage() {
                continue;
            }
            if c.redundant() {
                continue;
            }
            let mut positive_literal = 0;
            let mut satisfied = false;
            for &lit in c.lits() {
                let tmp = self.val(lit);
                if tmp > 0 {
                    satisfied = true;
                    break;
                }
                if tmp < 0 {
                    continue;
                }
                if lit < 0 {
                    continue;
                }
                positive_literal = lit;
                break;
            }
            if satisfied {
                continue;
            }
            if positive_literal == 0 {
                log!(self, c, "no positive unassigned literal in");
                return self.unlucky(0);
            }
            debug_assert!(positive_literal > 0);
            log!(self, c, "found positive literal {} in", positive_literal);
            self.search_assume_decision(positive_literal);
            if self.propagate() {
                continue;
            }
            log!(self, "propagation of positive literal {} leads to conflict", positive_literal);
            return self.unlucky(0);
        }
        for idx in self.vars() {
            if self.terminated_asynchronously(10) {
                return self.unlucky(-1);
            }
            if self.val(idx) != 0 {
                continue;
            }
            self.search_assume_decision(-idx);
            if self.propagate() {
                continue;
            }
            log!(self, "propagation of remaining literal {} leads to conflict", -idx);
            return self.unlucky(0);
        }
        verbose!(self, 1, "clauses are positive horn satisfied");
        debug_assert!(self.conflict.is_null());
        debug_assert!(self.satisfied());
        self.stats.lucky.horn.positive += 1;
        10
    }

    pub fn lucky_decide_assumptions(&mut self) -> i32 {
        debug_assert!(self.level == 0);
        debug_assert!(self.constraint.is_empty());
        let mut res;
        while (self.level as usize) < self.assumptions.len() {
            res = self.decide();
            if res == 20 {
                self.marked_failed = false;
                return 20;
            }
            if !self.propagate() {
                break;
            }
        }

        if self.conflict.is_some() {
            // analyze and learn from the conflict.
            log!(self, self.conflict, "setting assumption lead to conflict");
            self.analyze_wrapper();
            self.backtrack(0);
            debug_assert!(self.conflict.is_null());
            res = 0;
            while res == 0 {
                debug_assert!((self.level as usize) <= self.assumptions.len());
                if self.unsat {
                    res = 20;
                } else if !self.propagate() {
                    self.analyze_wrapper();
                } else {
                    res = self.decide_wrapper();
                }
            }
            debug_assert!(res == 20);
            return 20;
        }
        0
    }

    pub fn negative_horn_satisfiable(&mut self) -> i32 {
        if self.terminated_asynchronously(1) {
            return -1;
        }
        debug_assert!(self.level == 0);
        log!(self, "checking that all clauses are negative horn satisfiable");
        let res = self.lucky_decide_assumptions();
        if res != 0 {
            return res;
        }
        let n = self.clauses.len();
        for ci in 0..n {
            let c = self.clauses[ci];
            if self.terminated_asynchronously(10) {
                return self.unlucky(-1);
            }
            if c.garbage() {
                continue;
            }
            if c.redundant() {
                continue;
            }
            let mut negative_literal = 0;
            let mut satisfied = false;
            for &lit in c.lits() {
                let tmp = self.val(lit);
                if tmp > 0 {
                    satisfied = true;
                    break;
                }
                if tmp < 0 {
                    continue;
                }
                if lit > 0 {
                    continue;
                }
                negative_literal = lit;
                break;
            }
            if satisfied {
                continue;
            }
            if negative_literal == 0 {
                if self.level > 0 {
                    self.backtrack_without_updating_phases(0);
                }
                log!(self, c, "no negative unassigned literal in");
                return self.unlucky(0);
            }
            debug_assert!(negative_literal < 0);
            log!(self, c, "found negative literal {} in", negative_literal);
            self.search_assume_decision(negative_literal);
            if self.propagate() {
                continue;
            }
            log!(self, "propagation of negative literal {} leads to conflict", negative_literal);
            return self.unlucky(0);
        }
        for idx in self.vars() {
            if self.terminated_asynchronously(10) {
                return self.unlucky(-1);
            }
            if self.val(idx) != 0 {
                continue;
            }
            self.search_assume_decision(idx);
            if self.propagate() {
                continue;
            }
            log!(self, "propagation of remaining literal {} leads to conflict", idx);
            return self.unlucky(0);
        }
        verbose!(self, 1, "clauses are negative horn satisfied");
        debug_assert!(self.conflict.is_null());
        debug_assert!(self.satisfied());
        self.stats.lucky.horn.negative += 1;
        10
    }

    /*------------------------------------------------------------------------*/

    pub fn lucky_phases(&mut self) -> i32 {
        debug_assert!(self.level == 0);
        self.require_mode(Mode::SEARCH);
        if self.opts.lucky == 0 {
            return 0;
        }
        if self.opts.luckyassumptions == 0 && !self.assumptions.is_empty() {
            return 0;
        }
        if self.terminated_asynchronously(1) {
            return 0;
        }
        // TODO: Some of the lucky assignments can also be found if there
        // are constraint.  External propagator assumes a CDCL loop, so lucky
        // is not tried here.
        if !self.constraint.is_empty() || self.external_prop {
            return 0;
        }
        if !self.propagate() {
            self.learn_empty_clause();
            return 20;
        }

        start!(self, search);
        start!(self, lucky);
        log!(self, "starting lucky");
        debug_assert!(!self.searching_lucky_phases);
        self.searching_lucky_phases = true;
        self.stats.lucky.tried += 1;
        let active_before = self.stats.active;
        let mut res = self.trivially_false_satisfiable();
        if res == 0 {
            res = self.trivially_true_satisfiable();
        }
        if res == 0 {
            res = self.forward_false_satisfiable();
        }
        if res == 0 {
            res = self.forward_true_satisfiable();
        }
        if res == 0 {
            res = self.backward_false_satisfiable();
        }
        if res == 0 {
            res = self.backward_true_satisfiable();
        }
        if res == 0 {
            res = self.negative_horn_satisfiable();
        }
        if res == 0 {
            res = self.positive_horn_satisfiable();
        }
        if res < 0 {
            debug_assert!(self.termination_forced.load(std::sync::atomic::Ordering::Relaxed));
            res = 0;
        }
        if res == 10 {
            self.stats.lucky.succeeded += 1;
        }
        self.report(b'l', (res == 0) as i32);
        debug_assert!(self.searching_lucky_phases);

        debug_assert!(res != 0 || self.level == 0);
        if res != 20 && !self.propagate() {
            log!(self, "propagating units after elimination results in empty clause");
            self.learn_empty_clause();
        }

        let units = active_before - self.stats.active;

        if res == 0 && units != 0 {
            log!(self, "lucky {} units", units);
        }
        let _ = units;
        self.searching_lucky_phases = false;

        // Here we should reset lim.terminate.check since in a lucky run this
        // may be set to up to 1000. This then may lead to a high latency for
        // external termination.
        self.lim.terminate.check = self.opts.terminateint;

        stop!(self, lucky);
        stop!(self, search);

        res
    }
}

//! Port of `constrain.cpp`: the constraint clause (same lifetime as the
//! assumptions, see `Solver::constrain`).

#[allow(unused_imports)]
use crate::prelude::*;

impl Internal {
    pub fn constrain(&mut self, lit: i32) {
        if lit != 0 {
            self.constraint.push(lit);
        } else {
            if self.level != 0 {
                self.backtrack(0);
            }
            log!(self, &self.constraint, "shrinking constraint");
            let mut satisfied_constraint = false;
            let end = self.constraint.len();
            let mut i = 0usize;
            let mut j = 0usize;
            while j != end {
                let lit_j = self.constraint[j];
                let mut tmp = self.marked(lit_j) as i32;
                if tmp > 0 {
                    log!(self, "removing duplicated literal {} from constraint", lit_j);
                } else if tmp < 0 {
                    log!(
                        self,
                        "tautological since both {} and {} occur in constraint",
                        -lit_j,
                        lit_j
                    );
                    satisfied_constraint = true;
                    break;
                } else {
                    tmp = self.val(lit_j) as i32;
                    if tmp < 0 {
                        log!(self, "removing falsified literal {} from constraint clause", lit_j);
                    } else if tmp > 0 {
                        log!(self, "satisfied constraint with literal {}", lit_j);
                        satisfied_constraint = true;
                        break;
                    } else {
                        self.constraint[i] = lit_j;
                        i += 1;
                        self.mark(lit_j);
                    }
                }
                j += 1;
            }
            self.constraint.truncate(i);
            let n = self.constraint.len();
            for k in 0..n {
                let lit = self.constraint[k];
                self.unmark(lit);
            }
            if satisfied_constraint {
                self.constraint.clear();
            } else if self.constraint.is_empty() {
                self.unsat_constraint = true;
                if self.conflict_id == 0 {
                    self.marked_failed = false; // allow to trigger failing ()
                }
            } else {
                let n = self.constraint.len();
                for k in 0..n {
                    let lit = self.constraint[k];
                    self.freeze(lit);
                }
            }
        }
    }

    pub fn failed_constraint(&mut self) -> bool {
        self.unsat_constraint
    }

    pub fn reset_constraint(&mut self) {
        let n = self.constraint.len();
        for k in 0..n {
            let lit = self.constraint[k];
            self.melt(lit);
        }
        log!(self, "cleared {} constraint literals", self.constraint.len());
        self.constraint.clear();
        self.unsat_constraint = false;
        self.marked_failed = true;
    }
}

//! Port of `solution.cpp`.

#[allow(unused_imports)]
use crate::prelude::*;

use crate::message::{c_stderr, fatal_message_end, fatal_message_start, fputc, fputs};

// Sam Buss suggested to debug the case where a solver incorrectly claims
// the formula to be unsatisfiable by checking every learned clause to be
// satisfied by a satisfying assignment.  Thus the first inconsistent
// learned clause will be immediately flagged without the need to generate
// proof traces and perform forward proof checking.  The incorrectly derived
// clause will raise an abort signal and thus allows to debug the issue with
// a symbolic debugger immediately.

impl External {
    pub fn check_solution_on_learned_clause(&mut self) {
        debug_assert!(self.solution.is_some());
        let internal = self.internal_unbound();
        for &lit in internal.clause.iter() {
            if self.sol(internal.externalize(lit)) == lit {
                return;
            }
        }
        fatal_message_start();
        fputs("learned clause unsatisfied by solution:\n", c_stderr());
        for &lit in internal.clause.iter() {
            cfprintf!(c_stderr(), "{} ", lit);
        }
        fputc(b'0' as i32, c_stderr());
        fatal_message_end();
    }

    pub fn check_solution_on_shrunken_clause(&mut self, c: CRef) {
        debug_assert!(self.solution.is_some());
        let internal = self.internal_unbound();
        for &lit in c.lits() {
            if self.sol(internal.externalize(lit)) == lit {
                return;
            }
        }
        fatal_message_start();
        for &lit in c.lits() {
            cfprintf!(c_stderr(), "{} ", lit);
        }
        fputc(b'0' as i32, c_stderr());
        fatal_message_end();
    }

    pub fn check_no_solution_after_learning_empty_clause(&mut self) {
        debug_assert!(self.solution.is_some());
        fatal!("learned empty clause but got solution");
    }

    pub fn check_solution_on_learned_unit_clause(&mut self, unit: i32) {
        debug_assert!(self.solution.is_some());
        if self.sol(self.internal().externalize(unit)) == unit {
            return;
        }
        fatal!("learned unit {} contradicts solution", unit);
    }
}

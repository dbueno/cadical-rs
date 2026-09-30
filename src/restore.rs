//! Port of `restore.cpp`.
//!
//! In incremental solving after a first call to 'solve' has finished and
//! before calling the internal 'solve' again incrementally we have to
//! restore clauses which have the negation of a literal as a witness
//! literal on the extension stack, which was added as original literal in
//! a new clause or in an assumption.  This procedure has to be applied
//! recursively, i.e., the literals of restored clauses are treated in the
//! same way as literals of a new original clause.
//!
//! See the long comment in 'restore.cpp' and our SAT'19 paper
//! [FazekasBiereScholl-SAT'19] for more details.

#[allow(unused_imports)]
use crate::prelude::*;

use crate::format::fmt_f;

impl External {
    /// The C++ iterators `begin` / `end` into `extension` are indices here.
    pub fn restore_clause(&mut self, begin: usize, end: usize, id: i64) {
        log!(self, &self.extension[begin..end], "restoring external clause[{}]", id);
        debug_assert!(self.eclause.is_empty());
        debug_assert!(id != 0);
        let internal = self.internal_unbound();
        for p in begin..end {
            let elit = self.extension[p];
            self.eclause.push(elit);
            if internal.proof.is_some() && internal.lrat {
                let eidx = (elit > 0) as u32 + 2u32 * elit.unsigned_abs();
                debug_assert!((eidx as usize) < self.ext_units.len());
                let id = self.ext_units[eidx as usize];
                let added = self.ext_flags[elit.unsigned_abs() as usize];
                if id != 0 && !added {
                    self.ext_flags[elit.unsigned_abs() as usize] = true;
                    internal.lrat_chain.push(id);
                }
            }
            let ilit = self.internalize(self.extension[p], false);
            internal.add_original_lit(ilit);
            internal.stats.restoredlits += 1;
        }
        if internal.proof.is_some() && internal.lrat {
            for k in 0..self.eclause.len() {
                let elit = self.eclause[k];
                self.ext_flags[elit.unsigned_abs() as usize] = false;
            }
        }
        internal.finish_added_clause_with_id(id, true);
        self.eclause.clear();
        internal.stats.restored += 1;
    }

    /*----------------------------------------------------------------------*/

    pub fn restore_clauses(&mut self) {
        let internal = self.internal_unbound();
        debug_assert!(internal.opts.restoreall == 2 || !self.tainted.is_empty());

        start!(internal, restore);
        internal.stats.restorations += 1;

        let mut clauses_weakened: i64 = 0;
        let mut clauses_satisfied: i64 = 0;
        let mut clauses_restored: i64 = 0;
        let mut clauses_removed: i64 = 0;

        if internal.opts.restoreall != 0 && self.tainted.is_empty() {
            phase!(self, "restore", internal.stats.restorations, "forced to restore all clauses");
        }

        {
            let mut numtainted: u32 = 0;
            for &b in self.tainted.iter() {
                if b {
                    numtainted += 1;
                }
            }

            phase!(
                self,
                "restore",
                internal.stats.restorations,
                "starting with {} tainted literals {}%",
                numtainted,
                fmt_f(percent(numtainted as f64, (2u32.wrapping_mul(self.max_var as u32)) as f64), 0)
            );
            let _ = numtainted;
        }

        let end_of_extension = self.extension.len();
        let mut p = 0usize;
        let mut q = 0usize;

        // Go over all witness labelled clauses on the extension stack,
        // restore those necessary, remove restored and flush satisfied
        // clauses.
        //
        while p != end_of_extension {
            clauses_weakened += 1;

            debug_assert!(self.extension[p] == 0);
            let saved = q; // Save old start.
            self.extension[q] = self.extension[p]; // Copy zero '0'.
            q += 1;
            p += 1;

            // Copy witness part and try to find a tainted witness literal in
            // it.
            //
            let mut tlit = 0; // Negation tainted.
            let mut elit;
            //
            debug_assert!(p != end_of_extension);
            //
            loop {
                elit = self.extension[p];
                self.extension[q] = elit;
                q += 1;
                p += 1;
                if elit == 0 {
                    break;
                }

                if self.marked(&self.tainted, -elit) {
                    tlit = elit;
                    log!(self, "negation of witness literal {} tainted", tlit);
                }

                debug_assert!(p != end_of_extension);
            }

            // now copy the id of the clause
            let id: i64 = ((self.extension[p] as i64) << 32) + self.extension[p + 1] as i64;
            log!(self, "id is {}", id);
            self.extension[q] = self.extension[p];
            q += 1;
            p += 1;
            self.extension[q] = self.extension[p];
            q += 1;
            p += 1;
            debug_assert!(id != 0);
            debug_assert!(self.extension[p] == 0);
            self.extension[q] = self.extension[p];
            q += 1;
            p += 1;

            // Now find 'end_of_clause' (clause starts at 'p') and at the same
            // time figure out whether the clause is actually root level
            // satisfied.
            //
            let mut satisfied = 0;
            let mut end_of_clause = p;
            while end_of_clause != end_of_extension {
                elit = self.extension[end_of_clause];
                if elit == 0 {
                    break;
                }
                if satisfied == 0 && self.fixed(elit) > 0 {
                    satisfied = elit;
                }
                end_of_clause += 1;
            }
            debug_assert!(id != 0);

            // Do not apply our 'FLUSH' rule to remove satisfied (implied)
            // clauses if the corresponding option is set simply by resetting
            // 'satisfied'.
            //
            if satisfied != 0 && internal.opts.restoreflush == 0 {
                log!(self, &self.extension[p..end_of_clause], "forced to not remove {} satisfied", satisfied);
                satisfied = 0;
            }

            if satisfied != 0 || tlit != 0 || internal.opts.restoreall != 0 {
                if satisfied != 0 {
                    log!(
                        self,
                        &self.extension[p..end_of_clause],
                        "flushing implied clause satisfied by {} from extension stack",
                        satisfied
                    );
                    clauses_satisfied += 1;
                } else {
                    self.restore_clause(p, end_of_clause, id); // Might taint literals.
                    clauses_restored += 1;
                }

                clauses_removed += 1;
                p = end_of_clause;
                q = saved;
            } else {
                log!(self, &self.extension[p..end_of_clause], "keeping clause on extension stack");

                while p != end_of_clause {
                    // Copy clause too.
                    self.extension[q] = self.extension[p];
                    q += 1;
                    p += 1;
                }
            }
        }

        self.extension.truncate(q);
        shrink_vector(&mut self.extension);

        if clauses_satisfied != 0 {
            phase!(
                self,
                "restore",
                internal.stats.restorations,
                "removed {} satisfied {}% of {} weakened clauses",
                clauses_satisfied,
                fmt_f(percent(clauses_satisfied as f64, clauses_weakened as f64), 0),
                clauses_weakened
            );
        } else {
            phase!(
                self,
                "restore",
                internal.stats.restorations,
                "no satisfied clause removed out of {} weakened clauses",
                clauses_weakened
            );
        }

        if clauses_restored != 0 {
            phase!(
                self,
                "restore",
                internal.stats.restorations,
                "restored {} clauses {}% out of {} weakened clauses",
                clauses_restored,
                fmt_f(percent(clauses_restored as f64, clauses_weakened as f64), 0),
                clauses_weakened
            );
        } else {
            phase!(
                self,
                "restore",
                internal.stats.restorations,
                "no clause restored out of {} weakened clauses",
                clauses_weakened
            );
        }
        {
            let mut numtainted: u32 = 0;
            for &b in self.tainted.iter() {
                if b {
                    numtainted += 1;
                }
            }

            phase!(
                self,
                "restore",
                internal.stats.restorations,
                "finishing with {} tainted literals {}%",
                numtainted,
                fmt_f(percent(numtainted as f64, (2u32.wrapping_mul(self.max_var as u32)) as f64), 0)
            );
            let _ = numtainted;
        }
        let _ = (clauses_removed, clauses_weakened, clauses_satisfied, clauses_restored);

        log!(self, "extension stack clean");
        self.tainted.clear();

        // Finally recompute the witness bits.
        //
        self.witness.clear();
        let begin_of_extension = 0usize;
        p = self.extension.len();
        while p != begin_of_extension {
            loop {
                p -= 1;
                if self.extension[p] == 0 {
                    break;
                }
                debug_assert!(p != begin_of_extension);
            }
            let mut elit;
            debug_assert!(p != begin_of_extension);
            p -= 1;
            debug_assert!(p != begin_of_extension);
            debug_assert!(self.extension[p] != 0 || self.extension[p - 1] != 0);
            p -= 1;
            debug_assert!(p != begin_of_extension);
            debug_assert!(self.extension[p] == 0);
            p -= 1;
            debug_assert!(p != begin_of_extension);
            loop {
                p -= 1;
                elit = self.extension[p];
                if elit == 0 {
                    break;
                }
                let mut witness = std::mem::take(&mut self.witness);
                self.mark(&mut witness, elit);
                self.witness = witness;
                debug_assert!(p != begin_of_extension);
            }
        }

        stop!(internal, restore);
    }
}

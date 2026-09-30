//! Port of `transred.cpp`.
//!
//! Implement transitive reduction in the binary implication graph.  This is
//! important for hyper binary resolution, which has the risk to produce too
//! many hyper binary resolvents otherwise.  This algorithm only works on
//! binary clauses and is usually pretty fast.  It will also find some
//! failed literals (in the binary implication graph).

#[allow(unused_imports)]
use crate::prelude::*;

use crate::util::erase_vector;

impl Internal {
    pub fn transred(&mut self) {
        if self.opts.transred == 0 {
            return;
        }
        if self.unsat {
            return;
        }
        if self.terminated_asynchronously(1) {
            return;
        }
        if self.stats.current.redundant == 0 && self.stats.current.irredundant == 0 {
            return;
        }

        debug_assert!(self.opts.transred != 0);
        debug_assert!(self.level == 0);

        start_simplifier!(self, transred, TRANSRED);
        self.stats.transreds += 1;

        // Transitive reduction can not be run to completion for larger
        // formulas with many binary clauses.  We bound it in the same way as
        // 'probe_core'.
        //
        let mut limit: i64 = self.stats.propagations.search;
        limit -= self.last.transred.propagations;
        limit = (limit as f64 * (1e-3 * self.opts.transredeffort as f64)) as i64;
        if limit < self.opts.transredmineff as i64 {
            limit = self.opts.transredmineff as i64;
        }
        if limit > self.opts.transredmaxeff as i64 {
            limit = self.opts.transredmaxeff as i64;
        }

        phase!(
            self,
            "transred",
            self.stats.transreds,
            "transitive reduction limit of {} propagations",
            limit
        );

        let end = self.clauses.len();
        let mut i = 0usize;

        // Find first clause not checked for being transitive yet.
        //
        while i != end {
            let c = self.clauses[i];
            if c.garbage() {
                i += 1;
                continue;
            }
            if c.size() != 2 {
                i += 1;
                continue;
            }
            if c.redundant() && c.hyper() {
                i += 1;
                continue;
            }
            if !c.transred() {
                break;
            }
            i += 1;
        }

        // If all candidate clauses have been checked reschedule all.
        //
        if i == end {
            phase!(
                self,
                "transred",
                self.stats.transreds,
                "rescheduling all clauses since no clauses to check left"
            );
            for k in 0..end {
                let c = self.clauses[k];
                if c.transred() {
                    c.set_transred(false);
                }
            }
            i = 0;
        }

        // Move watches of binary clauses to the front. Thus we can stop
        // iterating watches as soon a long clause is found during watch
        // traversal.
        //
        self.sort_watches();

        // This working stack plays the same role as the 'trail' during
        // standard propagation.
        //
        let mut work: Vec<i32> = Vec::new();

        let mut propagations: i64 = 0;
        let mut units: i64 = 0;
        let mut removed: i64 = 0;

        while !self.unsat && i != end && !self.terminated_asynchronously(1) && propagations < limit {
            let c = self.clauses[i];
            i += 1;

            // A clause is a candidate for being transitive if it is binary,
            // and not the result of hyper binary resolution.  The reason for
            // excluding those, is that they come in large numbers, most of
            // them are reduced away anyhow and further are non-transitive at
            // the point they are added (see the code in
            // 'hyper_binary_resolve' in 'prope.cpp' and also check out our
            // CPAIOR paper on tree-based look ahead).
            //
            if c.garbage() {
                continue;
            }
            if c.size() != 2 {
                continue;
            }
            if c.redundant() && c.hyper() {
                continue;
            }
            if c.transred() {
                continue; // checked before?
            }
            c.set_transred(true); // marked as checked

            log!(self, c, "checking transitive reduction of");

            // Find a different path from 'src' to 'dst' in the binary
            // implication graph, not using 'c'.  Since this is the same as
            // checking whether there is a path from '-dst' to '-src', we can
            // do the reverse search if the number of watches of '-dst' is
            // larger than those of 'src'.
            //
            let mut src = -c.lit(0);
            let mut dst = c.lit(1);
            if self.val(src) != 0 || self.val(dst) != 0 {
                continue;
            }
            if self.watches(-src).len() < self.watches(dst).len() {
                let tmp = dst;
                dst = -src;
                src = -tmp;
            }

            log!(self, "searching path from {} to {}", src, dst);

            // If the candidate clause is irredundant then we can not use
            // redundant binary clauses in the implication graph.  See our
            // inprocessing rules paper, why this restriction is required.
            //
            let irredundant = !c.redundant();

            debug_assert!(work.is_empty());
            self.mark(src);
            work.push(src);
            log!(self, "transred assign {}", src);

            let mut transitive = false; // found path from 'src' to 'dst'?
            let mut failed = false; // 'src' failed literal?

            let mut j = 0usize; // 'propagated' in BFS

            debug_assert!(self.lrat_chain.is_empty());
            debug_assert!(self.mini_chain.is_empty());
            let mut parents: Vec<i32> = Vec::new();

            while !transitive && !failed && j < work.len() {
                let lit = work[j];
                j += 1;
                debug_assert!(self.marked(lit) > 0);
                log!(self, "transred propagating {}", lit);
                propagations += 1;
                let wi = self.vlit(-lit) as usize;
                let eow = self.wtab[wi].len();
                let mut k = 0usize;
                while !transitive && !failed && k != eow {
                    let w = self.wtab[wi][k];
                    k += 1;
                    if !w.binary() {
                        break; // since we sorted watches above
                    }
                    let d = w.clause;
                    if d == c {
                        continue;
                    }
                    if irredundant && d.redundant() {
                        continue;
                    }
                    if d.garbage() {
                        continue;
                    }
                    let other = w.blit;
                    if other == dst {
                        transitive = true; // 'dst' reached
                    } else {
                        let tmp = self.marked(other);
                        if tmp > 0 {
                            continue;
                        } else if tmp < 0 {
                            if self.lrat {
                                parents.push(lit);
                                self.mini_chain.push(d.id());
                                work.push(other);
                            }
                            log!(self, "found both {} and {} reachable", -other, other);
                            failed = true;
                        } else {
                            if self.lrat {
                                parents.push(lit);
                                self.mini_chain.push(d.id());
                            }
                            self.mark(other);
                            work.push(other);
                            log!(self, "transred assign {}", other);
                        }
                    }
                }
            }

            let failed_lit = *work.last().unwrap();
            let mut next_pos = 0;
            let mut next_neg = 0;

            // Unassign all assigned literals (same as '[bp]acktrack').
            //
            while let Some(lit) = work.pop() {
                if self.lrat && failed && !work.is_empty() {
                    debug_assert!(!parents.is_empty() && !self.mini_chain.is_empty());
                    log!(
                        self,
                        "transred LRAT current lit {} next pos {} next neg {}",
                        lit,
                        next_pos,
                        next_neg
                    );
                    if lit == failed_lit || lit == next_pos {
                        let id = *self.mini_chain.last().unwrap();
                        self.lrat_chain.push(id);
                        next_pos = *parents.last().unwrap();
                    } else if lit == -failed_lit || lit == next_neg {
                        let id = *self.mini_chain.last().unwrap();
                        self.lrat_chain.push(id);
                        next_neg = *parents.last().unwrap();
                    }
                    parents.pop();
                    self.mini_chain.pop();
                }
                self.unmark(lit);
            }
            self.mini_chain.clear();
            debug_assert!(self.mini_chain.is_empty());
            if self.lrat && failed {
                self.lrat_chain.reverse();
            }

            if transitive {
                removed += 1;
                self.stats.transitive += 1;
                log!(self, c, "transitive redundant");
                self.mark_garbage(c);
            } else if failed {
                units += 1;
                log!(self, "found failed literal {} during transitive reduction", src);
                self.stats.failed += 1;
                self.stats.transredunits += 1;
                self.assign_unit(-src);
                if !self.propagate() {
                    verbose!(self, 1, "propagating new unit results in conflict");
                    self.learn_empty_clause();
                }
            }
            self.lrat_chain.clear();
        }

        self.last.transred.propagations = self.stats.propagations.search;
        self.stats.propagations.transred += propagations;
        erase_vector(&mut work);

        phase!(
            self,
            "transred",
            self.stats.transreds,
            "removed {} transitive clauses, found {} units",
            removed,
            units
        );

        stop_simplifier!(self, transred, TRANSRED);
        let quiet = self.opts.reportall == 0 && (removed + units) == 0;
        self.report(b't', quiet as i32);
    }
}

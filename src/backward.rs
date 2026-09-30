//! Port of `backward.cpp`.

#[allow(unused_imports)]
use crate::prelude::*;

use crate::occs::remove_occs;

/*------------------------------------------------------------------------*/

// Provide eager backward subsumption for resolved clauses.

// The eliminator maintains a queue of clauses that are new and have to be
// checked to subsume or strengthen other (longer or same size) clauses.

impl Eliminator {
    pub fn enqueue(&mut self, c: CRef) {
        // SAFETY: the back pointer to the owning 'Internal' is valid while
        // the eliminator is alive.
        let elimbackward = unsafe { (*self.internal).opts.elimbackward };
        if elimbackward == 0 {
            return;
        }
        if c.enqueued() {
            return;
        }
        log!(self.internal, c, "backward enqueue");
        self.backward.push_back(c);
        c.set_enqueued(true);
    }

    pub fn dequeue(&mut self) -> CRef {
        let res = match self.backward.pop_front() {
            None => return CRef::NULL,
            Some(res) => res,
        };
        debug_assert!(res.enqueued());
        res.set_enqueued(false);
        log!(self.internal, res, "backward dequeue");
        res
    }
}

impl Drop for Eliminator {
    fn drop(&mut self) {
        while !self.dequeue().is_null() {}
    }
}

/*------------------------------------------------------------------------*/

impl Internal {
    pub fn elim_backward_clause(&mut self, eliminator: &mut Eliminator, c: CRef) {
        debug_assert!(self.opts.elimbackward != 0);
        debug_assert!(!c.redundant());
        if c.garbage() {
            return;
        }
        log!(self, c, "attempting backward subsumption and strengthening with");
        let mut len: usize = u32::MAX as usize;
        let mut size: u32 = 0;
        let mut best = 0;
        let mut satisfied = false;
        debug_assert!(self.mini_chain.is_empty());
        for &lit in c.lits() {
            let tmp = self.val(lit);
            if tmp > 0 {
                satisfied = true;
                break;
            }
            if tmp < 0 {
                continue;
            }
            let l = self.occs(lit).len();
            log!(self, "literal {} occurs {} times", lit, l);
            if l < len {
                best = lit;
                len = l;
            }
            self.mark(lit);
            size += 1;
        }
        if satisfied {
            log!(self, "clause actually already satisfied");
            self.elim_update_removed_clause(eliminator, c, 0);
            self.mark_garbage(c);
        } else if len > self.opts.elimocclim as usize {
            log!(self, "skipping backward subsumption due to too many occurrences");
        } else {
            debug_assert!(len != 0);
            log!(self, "literal {} has smallest number of occurrences {}", best, len);
            log!(self, "marked {} literals in clause of size {}", size, c.size());
            let occs_size = self.occs(best).len();
            for k in 0..occs_size {
                let d = self.occs(best)[k];
                if d == c {
                    continue;
                }
                if d.garbage() {
                    continue;
                }
                if (d.size() as u32) < size {
                    continue;
                }
                let mut negated = 0;
                let mut found: u32 = 0;
                satisfied = false;
                for &lit in d.lits() {
                    let mut tmp = self.val(lit);
                    if tmp > 0 {
                        satisfied = true;
                        break;
                    }
                    if tmp < 0 {
                        continue;
                    }
                    tmp = self.marked(lit);
                    if tmp == 0 {
                        continue;
                    }
                    if tmp < 0 {
                        if negated != 0 {
                            size = u32::MAX;
                            break;
                        } else {
                            negated = lit;
                        }
                    }
                    found += 1;
                    if found == size {
                        break;
                    }
                }
                if satisfied {
                    log!(self, d, "found satisfied clause");
                    self.elim_update_removed_clause(eliminator, d, 0);
                    self.mark_garbage(d);
                } else if found == size {
                    if negated == 0 {
                        log!(self, d, "found subsumed clause");
                        self.elim_update_removed_clause(eliminator, d, 0);
                        self.mark_garbage(d);
                        self.stats.subsumed += 1;
                        self.stats.elimbwsub += 1;
                    } else {
                        let mut unit = 0;
                        debug_assert!(self.minimize_chain.is_empty());
                        debug_assert!(self.analyzed.is_empty());
                        debug_assert!(self.lrat_chain.is_empty());
                        // figure out wether we strengthen c or get a new unit
                        for &lit in d.lits() {
                            let tmp = self.val(lit);
                            if tmp < 0 {
                                if !self.lrat {
                                    continue;
                                }
                                debug_assert!(!self.flags(lit).seen);
                                if self.flags(lit).seen {
                                    continue;
                                }
                                self.flags_mut(lit).seen = true;
                                self.analyzed.push(lit);
                                continue;
                            }
                            if tmp > 0 {
                                satisfied = true;
                                break;
                            }
                            if lit == negated {
                                continue;
                            }
                            if unit != 0 {
                                unit = i32::MIN;
                                continue; // needed to guarantee d is not satsified
                            } else {
                                unit = lit;
                            }
                        }
                        if self.lrat && !satisfied {
                            // if we found a unit we need to add all unit ids
                            // from {c\d}U{d\c} otherwise just the unit ids
                            // from {c\d}
                            for &lit in c.lits() {
                                let tmp = self.val(lit);
                                debug_assert!(tmp <= 0);
                                if tmp >= 0 {
                                    continue;
                                }
                                let seen = self.flags(lit).seen;
                                if seen && unit != 0 && unit == i32::MIN {
                                    self.flags_mut(lit).seen = false;
                                    continue;
                                } else if !seen {
                                    self.flags_mut(lit).seen = true;
                                    self.analyzed.push(lit);
                                }
                            }
                            if unit == i32::MIN {
                                // we do not need units from {d\c}
                                for &lit in d.lits() {
                                    self.flags_mut(lit).seen = false;
                                }
                            }
                            for k2 in 0..self.analyzed.len() {
                                let lit = self.analyzed[k2];
                                if !self.flags(lit).seen {
                                    self.flags_mut(lit).seen = true;
                                    continue;
                                }
                                let id = self.unit_id(-lit);
                                self.lrat_chain.push(id);
                            }
                            self.clear_analyzed_literals();
                            self.lrat_chain.push(d.id());
                            self.lrat_chain.push(c.id());
                        } else if self.lrat {
                            self.clear_analyzed_literals();
                        }
                        if satisfied {
                            debug_assert!(self.lrat_chain.is_empty());
                            self.mark_garbage(d);
                            self.elim_update_removed_clause(eliminator, d, 0);
                        } else if unit != 0 && unit != i32::MIN {
                            debug_assert!(unit != 0);
                            log!(self, d, "unit {} through hyper unary resolution with", unit);
                            self.assign_unit(unit);
                            self.elim_propagate(eliminator, unit);
                            self.lrat_chain.clear();
                            break;
                        } else if self.occs(negated).len() <= self.opts.elimocclim as usize {
                            self.strengthen_clause(d, negated);
                            remove_occs(self.occs_mut(negated), d);
                            self.elim_update_removed_lit(eliminator, negated);
                            self.stats.elimbwstr += 1;
                            debug_assert!(negated != best);
                            eliminator.enqueue(d);
                        }
                        self.lrat_chain.clear();
                    }
                }
            }
        }
        self.mini_chain.clear();
        self.unmark_clause_literals(c);
    }

    /*--------------------------------------------------------------------*/

    pub fn elim_backward_clauses(&mut self, eliminator: &mut Eliminator) {
        if self.opts.elimbackward == 0 {
            debug_assert!(eliminator.backward.is_empty());
            return;
        }
        start!(self, backward);
        log!(
            self,
            "attempting backward subsumption and strengthening with {} clauses",
            eliminator.backward.len()
        );
        while !self.unsat {
            let c = eliminator.dequeue();
            if c.is_null() {
                break;
            }
            self.elim_backward_clause(eliminator, c);
        }
        stop!(self, backward);
    }
}

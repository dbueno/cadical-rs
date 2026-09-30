//! Port of `decide.cpp`.

#[allow(unused_imports)]
use crate::prelude::*;

impl Internal {
    // This function determines the next decision variable on the queue,
    // without actually removing it from the decision queue, e.g., calling
    // it multiple times without any assignment will return the same result.
    // This is of course used below in 'decide' but also in 'reuse_trail' to
    // determine the largest decision level to backtrack to during 'restart'
    // without changing the assigned variables (if 'opts.restartreusetrail'
    // is non-zero).

    pub fn next_decision_variable_on_queue(&mut self) -> i32 {
        let mut searched: i64 = 0;
        let mut res = self.queue.unassigned;
        while self.val(res) != 0 {
            res = self.links[res as usize].prev;
            searched += 1;
        }
        if searched != 0 {
            self.stats.searched += searched;
            self.update_queue_unassigned(res);
        }
        log!(self, "next queue decision variable {} bumped {}", res, self.bumped(res));
        res
    }

    // This function determines the best decision with respect to score.
    //
    pub fn next_decision_variable_with_best_score(&mut self) -> i32 {
        let mut res;
        loop {
            res = self.scores.front() as i32;
            if self.val(res) == 0 {
                break;
            }
            let _ = self.scores.pop_front();
        }
        log!(
            self,
            "next decision variable {} with score {}",
            res,
            crate::format::fmt_g(self.score(res))
        );
        res
    }

    pub fn start_random_sequence(&mut self) {
        if self.opts.randec == 0 {
            return;
        }

        debug_assert!(!self.stable || self.opts.randecstable != 0);
        debug_assert!(self.stable || self.opts.randecfocused != 0);
        debug_assert!(self.randomized_deciding == 0);

        self.stats.randec.random_decision_phases += 1;
        let count = self.stats.randec.random_decision_phases as u64;
        let length = (self.opts.randeclength as f64 * ((count + 10) as f64).ln()) as u32;
        verbose!(
            self,
            3,
            "starting random decision sequence at {} conflicts for {} conflicts",
            self.stats.conflicts,
            length
        );
        self.randomized_deciding = length as u64;

        let phases = self.stats.randec.random_decision_phases;
        let delta = phases as f64 * (phases as f64).ln();
        self.lim.random_decision =
            (self.stats.conflicts as f64 + delta * self.opts.randecint as f64) as i64;
        verbose!(
            self,
            3,
            "next random decision sequence at {} conflicts current conflict: {} conflicts",
            self.lim.random_decision,
            self.stats.conflicts
        );
    }

    pub fn next_random_decision(&mut self) -> i32 {
        debug_assert!(self.max_var != 0);
        if self.opts.randec == 0 {
            return 0;
        }
        if self.stable && self.opts.randecstable == 0 {
            return 0;
        }
        if !self.stable && self.opts.randecfocused == 0 {
            return 0;
        }
        if self.stats.conflicts < self.lim.random_decision {
            return 0;
        }
        if self.satisfied() {
            return 0;
        }

        if self.randomized_deciding == 0 {
            if self.level > self.assumptions.len() as i32 + (!self.constraint.is_empty()) as i32 {
                log!(self, "random decision delayed because too deep");
                return 0;
            }
            self.start_random_sequence();
        }
        log!(self, "searching for random decision");
        let mut random = Random::new(self.opts.seed as u64);
        random += self.stats.decisions as u64;
        self.stats.randec.random_decisions += 1;
        loop {
            let idx = (1 + (random.next() % self.max_var as u64)) as i32;
            log!(self, "trying lit {}", loglit!(self, idx));
            // Kissat filters out active literals but we cannot do that
            // because eliminated variables are not actively removed.
            if self.val(idx) != 0 {
                continue;
            }
            return idx;
        }
    }

    pub fn next_decision_variable(&mut self) -> i32 {
        let res = self.next_random_decision();
        if res != 0 {
            log!(self, "randomized decision {}", loglit!(self, res));
            return res;
        }
        if self.use_scores() {
            self.next_decision_variable_with_best_score()
        } else {
            self.next_decision_variable_on_queue()
        }
    }

    /*--------------------------------------------------------------------*/

    // Implements phase saving as well using a target phase during
    // stabilization unless decision phase is forced to the initial value
    // of a phase is forced through the 'phase' option.

    pub fn decide_phase(&mut self, idx: i32, target: bool) -> i32 {
        let initial_phase: i32 = if self.opts.phase != 0 { 1 } else { -1 };
        let mut phase: i32 = 0;
        if self.force_saved_phase {
            phase = self.phases.saved[idx as usize] as i32;
            log!(self, "trying force_saved_phase, i.e., {}", phase);
        }
        debug_assert!(self.force_saved_phase || phase == 0);
        if phase == 0 {
            phase = self.phases.forced[idx as usize] as i32; // swapped with opts.forcephase case!
            log!(self, "trying forced phase, i.e., {}", phase);
        }
        if phase == 0 && self.opts.forcephase != 0 {
            phase = initial_phase;
            log!(self, "trying initial phase, i.e., {}", phase);
        }
        if phase == 0 && target {
            phase = self.phases.target[idx as usize] as i32;
        }
        if phase == 0 {
            // ported from kissat where it does not seem very useful
            if self.opts.stubbornIOfocused != 0 && self.opts.rephase == 2 {
                match (self.stats.rephased.total >> 1) & 7 {
                    1 => phase = initial_phase,
                    5 => phase = -initial_phase, // kissat has 3 but 5 looks better
                    _ => phase = self.phases.saved[idx as usize] as i32,
                }
            } else {
                phase = self.phases.saved[idx as usize] as i32;
            }
        }

        // The following should not be necessary and in some version we had
        // even a hard 'COVER' assertion here to check for this.  See the
        // C++ source for the rationale of this 'defensive' code.
        //
        if phase == 0 {
            phase = initial_phase;
        }

        phase * idx
    }

    // The likely phase of an variable used in 'collect' for optimizing
    // co-location of clauses likely accessed together during search.

    pub fn likely_phase(&mut self, idx: i32) -> i32 {
        self.decide_phase(idx, false)
    }

    /*--------------------------------------------------------------------*/

    // adds new level to control and trail
    //
    pub fn new_trail_level(&mut self, lit: i32) {
        self.level += 1;
        let t = self.trail.len() as i32;
        self.control.push(Level::new(lit, t));
    }

    /*--------------------------------------------------------------------*/

    pub fn satisfied(&mut self) -> bool {
        if (self.level as usize) < self.assumptions.len() + (!self.constraint.is_empty()) as usize {
            return false;
        }
        if self.num_assigned < self.max_var as usize {
            return false;
        }
        debug_assert!(self.num_assigned == self.max_var as usize);
        if self.propagated < self.trail.len() {
            return false;
        }
        let assigned = self.num_assigned;
        assigned == self.max_var as usize
    }

    pub fn better_decision(&mut self, lit: i32, other: i32) -> bool {
        let lit_idx = lit.abs() as usize;
        let other_idx = other.abs() as usize;
        if self.stable {
            self.stab[lit_idx] > self.stab[other_idx]
        } else {
            self.btab[lit_idx] > self.btab[other_idx]
        }
    }

    // Search for the next decision and assign it to the saved phase.
    // Requires that not all variables are assigned.

    pub fn decide(&mut self) -> i32 {
        debug_assert!(!self.satisfied());
        start!(self, decide);
        let mut res = 0;
        if (self.level as usize) < self.assumptions.len() {
            let lit = self.assumptions[self.level as usize];
            debug_assert!(self.assumed(lit));
            let tmp = self.val(lit);
            if tmp < 0 {
                log!(self, "assumption {} falsified", lit);
                res = 20;
            } else if tmp > 0 {
                log!(self, "assumption {} already satisfied", lit);
                self.new_trail_level(0);
                log!(self, "added pseudo decision level");
                self.notify_decision();
            } else {
                log!(self, "deciding assumption {}", lit);
                self.search_assume_decision(lit);
            }
        } else if self.level as usize == self.assumptions.len() && !self.constraint.is_empty() {
            let mut satisfied_lit = 0; // The literal satisfying the constrain.
            let mut unassigned_lit = 0; // Highest score unassigned literal.
            let mut previous_lit = 0; // Move satisfied literals to the front.

            let size_constraint = self.constraint.len();

            #[cfg(debug_assertions)]
            let mut sum: u32 = 0;
            #[cfg(debug_assertions)]
            for &lit in &self.constraint {
                sum = sum.wrapping_add(lit as u32);
            }
            for i in 0..size_constraint {
                // Get literal and move 'constraint[i] = constraint[i-1]'.

                let lit = self.constraint[i];
                self.constraint[i] = previous_lit;
                previous_lit = lit;

                let tmp = self.val(lit);
                if tmp < 0 {
                    log!(self, "constraint literal {} falsified", lit);
                    continue;
                }

                if tmp > 0 {
                    log!(self, "constraint literal {} satisfied", lit);
                    satisfied_lit = lit;
                    break;
                }

                debug_assert!(tmp == 0);
                log!(self, "constraint literal {} unassigned", lit);

                if unassigned_lit == 0 || self.better_decision(lit, unassigned_lit) {
                    unassigned_lit = lit;
                }
            }

            if satisfied_lit != 0 {
                self.constraint[0] = satisfied_lit; // Move satisfied to the front.

                log!(
                    self,
                    "literal {} satisfies constraint and is implied by assumptions",
                    satisfied_lit
                );

                self.new_trail_level(0);
                log!(self, "added pseudo decision level for constraint");
                self.notify_decision();
            } else {
                // Just move all the literals back.  If we found an
                // unsatisfied literal then it will be satisfied (most
                // likely) at the next decision and moved then to the first
                // position.

                if size_constraint != 0 {
                    for i in 0..size_constraint - 1 {
                        self.constraint[i] = self.constraint[i + 1];
                    }

                    self.constraint[size_constraint - 1] = previous_lit;
                }

                if unassigned_lit != 0 {
                    log!(self, "deciding {} to satisfy constraint", unassigned_lit);
                    self.search_assume_decision(unassigned_lit);
                } else {
                    log!(self, "failing constraint");
                    self.unsat_constraint = true;
                    res = 20;
                }
            }

            #[cfg(debug_assertions)]
            {
                for &lit in &self.constraint {
                    sum = sum.wrapping_sub(lit as u32);
                }
                debug_assert!(sum == 0); // Checksum of literal should not change!
            }
        } else {
            let mut decision = self.ask_decision();
            if (self.level as usize) < self.assumptions.len()
                || (self.level as usize == self.assumptions.len() && !self.constraint.is_empty())
            {
                // Forced backtrack below pseudo decision levels.
                // So one of the two branches above will handle it.
                stop!(self, decide);
                res = self.decide(); // STARTS and STOPS profiling
                start!(self, decide);
            } else {
                self.stats.decisions += 1;
                if decision == 0 {
                    let idx = self.next_decision_variable();
                    let target = self.opts.target > 1 || (self.stable && self.opts.target != 0);
                    decision = self.decide_phase(idx, target);
                }
                self.search_assume_decision(decision);
            }
        }
        if res != 0 {
            self.marked_failed = false;
        }
        stop!(self, decide);
        res
    }
}

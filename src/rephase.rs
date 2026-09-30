//! Port of `rephase.cpp`.

#[allow(unused_imports)]
use crate::prelude::*;

/*------------------------------------------------------------------------*/

// We experimented with resetting and reinitializing the saved phase with
// many solvers. Actually RSAT had already such a scheme.  Our newest
// version seems to be quite beneficial for satisfiable instances.  In an
// arithmetic increasing interval in the number of conflicts we either use
// the original phase (set by the option 'phase'), its inverted value, flip
// the current phase, pick random phases, then pick the best since the last
// time a best phase was picked and finally also use local search to find
// phases which minimize the number of falsified clauses.  During
// stabilization (see 'stabilizing' in 'restart.cpp' when 'stable' is true)
// we execute a different rephasing schedule.  The same applies if local
// search is disabled.

impl Internal {
    pub fn rephasing(&mut self) -> bool {
        if self.opts.rephase == 0 {
            return false;
        }
        if self.opts.forcephase != 0 {
            return false;
        }
        if self.opts.rephase == 2 {
            if self.stable {
                return self.stats.stabconflicts > self.lim.rephase;
            } else {
                return false;
            }
        }
        self.stats.conflicts > self.lim.rephase
    }

    /*--------------------------------------------------------------------*/

    // Pick the original default phase.

    pub fn rephase_original(&mut self) -> u8 {
        self.stats.rephased.original += 1;
        let val: i8 = if self.opts.phase != 0 { 1 } else { -1 }; // original = initial
        phase!(self, "rephase", self.stats.rephased.total, "switching to original phase {}", val);
        for idx in self.vars() {
            self.phases.saved[idx as usize] = val;
        }
        b'O'
    }

    // Pick the inverted original default phase.

    pub fn rephase_inverted(&mut self) -> u8 {
        self.stats.rephased.inverted += 1;
        let val: i8 = if self.opts.phase != 0 { -1 } else { 1 }; // original = -initial
        phase!(
            self,
            "rephase",
            self.stats.rephased.total,
            "switching to inverted original phase {}",
            val
        );
        for idx in self.vars() {
            self.phases.saved[idx as usize] = val;
        }
        b'I'
    }

    // Flip the current phase.

    pub fn rephase_flipping(&mut self) -> u8 {
        self.stats.rephased.flipped += 1;
        phase!(self, "rephase", self.stats.rephased.total, "flipping all phases individually");
        for idx in self.vars() {
            let p = &mut self.phases.saved[idx as usize];
            *p = p.wrapping_mul(-1);
        }
        b'F'
    }

    // Complete random picking of phases.

    pub fn rephase_random(&mut self) -> u8 {
        self.stats.rephased.random += 1;
        phase!(self, "rephase", self.stats.rephased.total, "resetting all phases randomly");
        let mut random = Random::new(self.opts.seed as u64); // global seed
        random += self.stats.rephased.random as u64; // different every time
        for idx in self.vars() {
            self.phases.saved[idx as usize] = if random.generate_bool() { -1 } else { 1 };
        }
        b'#'
    }

    // Best phases are those saved at the largest trail height without
    // conflict.  See code and comments in 'update_target_and_best' in
    // 'backtrack.cpp'

    pub fn rephase_best(&mut self) -> u8 {
        self.stats.rephased.best += 1;
        phase!(self, "rephase", self.stats.rephased.total, "overwriting saved phases by best phases");
        for idx in self.vars() {
            let val = self.phases.best[idx as usize];
            if val != 0 {
                self.phases.saved[idx as usize] = val;
            }
        }
        b'B'
    }

    // Trigger local search 'walk' in 'walk.cpp'.

    pub fn rephase_walk(&mut self) -> u8 {
        self.stats.rephased.walk += 1;
        phase!(
            self,
            "rephase",
            self.stats.rephased.total,
            "starting local search to improve current phase"
        );
        if self.opts.walkfullocc != 0 {
            self.walk_full_occs();
        } else {
            self.walk();
        }
        b'W'
    }

    /*--------------------------------------------------------------------*/

    pub fn rephase(&mut self) {
        self.stats.rephased.total += 1;
        self.last.stabilize.rephased += 1;
        debug_assert!(self.last.stabilize.rephased <= self.stats.rephased.total);
        phase!(
            self,
            "rephase",
            self.stats.rephased.total,
            "reached rephase limit {} after {} conflicts",
            self.lim.rephase,
            if self.opts.rephase == 2 { self.stats.stabconflicts } else { self.stats.conflicts }
        );

        // Report current 'target' and 'best' and then set 'rephased' below,
        // which will trigger reporting the new 'target' and 'best' after
        // updating it in the next 'update_target_and_best' called from the
        // next 'backtrack'.
        //
        self.report(b'~', 1);

        self.backtrack(0);

        let s = self.stable as usize;
        let count = self.lim.rephased[s] as usize;
        self.lim.rephased[s] += 1;
        let single: bool;
        let type_: u8;

        if self.opts.stabilize != 0 && self.opts.stabilizeonly != 0 {
            single = true;
        } else {
            single = self.opts.stabilize == 0;
        }

        if single && self.opts.walk == 0 {
            // (inverted,best,flipping,best,random,best,original,best)^\omega
            type_ = match count % 8 {
                0 => self.rephase_inverted(),
                1 => self.rephase_best(),
                2 => self.rephase_flipping(),
                3 => self.rephase_best(),
                4 => self.rephase_random(),
                5 => self.rephase_best(),
                6 => self.rephase_original(),
                7 => self.rephase_best(),
                _ => 0,
            };
        } else if single && self.opts.walk != 0 {
            // (inverted,best,walk,
            //  flipping,best,walk,
            //    random,best,walk,
            //  original,best,walk)^\omega
            type_ = match count % 12 {
                0 => self.rephase_inverted(),
                1 => self.rephase_best(),
                2 => self.rephase_walk(),
                3 => self.rephase_flipping(),
                4 => self.rephase_best(),
                5 => self.rephase_walk(),
                6 => self.rephase_random(),
                7 => self.rephase_best(),
                8 => self.rephase_walk(),
                9 => self.rephase_original(),
                10 => self.rephase_best(),
                11 => self.rephase_walk(),
                _ => 0,
            };
        } else if self.opts.rephase == 2 && self.opts.walk != 0 {
            // (inverted,best,walk,
            //  flipping,best,walk,
            //    random,best,walk,
            //  original,best,walk)^\omega
            type_ = match count % 12 {
                0 => self.rephase_inverted(),
                1 => self.rephase_best(),
                2 => self.rephase_walk(),
                3 => self.rephase_flipping(),
                4 => self.rephase_best(),
                5 => self.rephase_walk(),
                6 => self.rephase_random(),
                7 => self.rephase_best(),
                8 => self.rephase_walk(),
                9 => self.rephase_original(),
                10 => self.rephase_best(),
                11 => self.rephase_walk(),
                _ => 0,
            };
        } else if self.stable && self.opts.walk == 0 {
            // original,inverted,(best,original,best,inverted)^\omega
            if count == 0 {
                type_ = self.rephase_original();
            } else if count == 1 {
                type_ = self.rephase_inverted();
            } else {
                type_ = match (count - 2) % 4 {
                    0 => self.rephase_best(),
                    1 => self.rephase_original(),
                    2 => self.rephase_best(),
                    3 => self.rephase_inverted(),
                    _ => 0,
                };
            }
        } else if self.stable && self.opts.walk != 0 {
            // original,inverted,(best,walk,original,best,walk,inverted)^\omega
            if count == 0 {
                type_ = self.rephase_original();
            } else if count == 1 {
                type_ = self.rephase_inverted();
            } else {
                type_ = match (count - 2) % 6 {
                    0 => self.rephase_best(),
                    1 => self.rephase_walk(),
                    2 => self.rephase_original(),
                    3 => self.rephase_best(),
                    4 => self.rephase_walk(),
                    5 => self.rephase_inverted(),
                    _ => 0,
                };
            }
        } else if !self.stable && (self.opts.walk == 0 || self.opts.walknonstable == 0) {
            // flipping,(random,best,flipping,best)^\omega
            if count == 0 {
                type_ = self.rephase_flipping();
            } else {
                type_ = match (count - 1) % 4 {
                    0 => self.rephase_random(),
                    1 => self.rephase_best(),
                    2 => self.rephase_flipping(),
                    3 => self.rephase_best(),
                    _ => 0,
                };
            }
        } else {
            debug_assert!(!self.stable && self.opts.walk != 0 && self.opts.walknonstable != 0);
            // flipping,(random,best,walk,flipping,best,walk)^\omega
            if count == 0 {
                type_ = self.rephase_original();
            } else {
                type_ = match (count - 1) % 6 {
                    0 => self.rephase_random(),
                    1 => self.rephase_best(),
                    2 => self.rephase_walk(),
                    3 => self.rephase_flipping(),
                    4 => self.rephase_best(),
                    5 => self.rephase_walk(),
                    _ => 0,
                };
            }
        }
        debug_assert!(type_ != 0);

        // clear after walk such that random walk can still access the
        // target by using the saved phases
        self.copy_phases(PhaseKind::Target);
        self.target_assigned = 0;

        let delta: i64 = self.opts.rephaseint as i64 * (self.stats.rephased.total + 1);
        self.lim.rephase =
            (if self.opts.rephase == 2 { self.stats.stabconflicts } else { self.stats.conflicts }) + delta;

        phase!(
            self,
            "rephase",
            self.stats.rephased.total,
            "new rephase limit {} after {} conflicts",
            self.lim.rephase,
            delta
        );

        // This will trigger to report the effect of this new set of phases
        // at the 'backtrack' (actually 'update_target_and_best') after the
        // next conflict, as well as resetting 'best_assigned' then to allow
        // to compute a new "best" assignment at that point.
        //
        self.last.rephase.conflicts = self.stats.conflicts;
        self.rephased = type_;

        if !self.marked_failed || self.unsat_constraint {
            debug_assert!(self.opts.warmup != 0);
            return;
        }
        if self.stable {
            self.shuffle_scores();
        } else {
            self.shuffle_queue();
        }
    }
}

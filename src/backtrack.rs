//! Port of `backtrack.cpp`.

#[allow(unused_imports)]
use crate::prelude::*;

impl Internal {
    // The global assignment stack can only be (partially) reset through
    // 'backtrack' which is the only function using 'unassign' (inlined and
    // thus local to this file).  It turns out that 'unassign' does not
    // need a specialization for 'probe' nor 'vivify' and thus it is shared.

    #[inline(always)]
    pub fn unassign(&mut self, lit: i32) {
        debug_assert!(self.val(lit) > 0);
        self.set_val(lit, 0);

        let idx = self.vidx(lit);
        log!(self, "unassign {} @ {}", lit, self.var(idx).level);
        self.num_assigned -= 1;

        // In the standard EVSIDS variable decision heuristic of MiniSAT, we
        // need to push variables which become unassigned back to the heap.
        //
        if !self.scores.contains(idx as u32) {
            self.scores.push_back(idx as u32);
        }

        // For VMTF we need to update the 'queue.unassigned' pointer in case
        // this variable sits after the variable to which 'queue.unassigned'
        // currently points.  See our SAT'15 paper for more details on this
        // aspect.
        //
        if self.queue.bumped < self.btab[idx as usize] {
            self.update_queue_unassigned(idx);
        }
    }

    /*--------------------------------------------------------------------*/

    // Update the current target maximum assignment and also the very best
    // assignment.  Whether a trail produces a conflict is determined
    // during propagation.  Thus that all functions in the 'search' loop
    // after propagation can assume that 'no_conflict_until' is valid.  If
    // a conflict is found then the trail before the last decision is used
    // (see the end of 'propagate').  During backtracking we can then save
    // this largest propagation conflict free assignment.  It is saved as
    // both 'target' assignment for picking decisions in 'stable' mode and
    // if it is the largest ever such assignment also as 'best' assignment.
    // This 'best' assignment can then be used in future stable decisions
    // after the next 'rephase_best' overwrites saved phases with it.

    pub fn update_target_and_best(&mut self) {
        if self.opts.rephase == 2 && !self.stable {
            return;
        }

        let reset = self.rephased != 0 && self.stats.conflicts > self.last.rephase.conflicts;

        if reset {
            self.target_assigned = 0;
            if self.rephased == b'B' {
                self.best_assigned = 0; // update it again
            }
        }

        if self.no_conflict_until > self.target_assigned {
            self.copy_phases(PhaseKind::Target);
            self.target_assigned = self.no_conflict_until;
            log!(self, "new target trail level {}", self.target_assigned);
        }

        if self.no_conflict_until > self.best_assigned {
            self.copy_phases(PhaseKind::Best);
            self.best_assigned = self.no_conflict_until;
            log!(self, "new best trail level {}", self.best_assigned);
        }

        if reset {
            let r = self.rephased;
            self.report(r, 0);
            self.rephased = 0;
        }
    }

    /*--------------------------------------------------------------------*/

    /// `new_level` defaults to `0` in C++
    pub fn backtrack(&mut self, new_level: i32) {
        debug_assert!(new_level <= self.level);
        if new_level == self.level {
            return;
        }

        self.update_target_and_best();
        self.backtrack_without_updating_phases(new_level);
    }

    /// `new_level` defaults to `0` in C++
    pub fn backtrack_without_updating_phases(&mut self, new_level: i32) {
        debug_assert!(new_level <= self.level);
        if new_level == self.level {
            return;
        }

        self.stats.backtracks += 1;

        debug_assert!(self.num_assigned == self.trail.len());

        let assigned = self.control[(new_level + 1) as usize].trail as usize;

        log!(
            self,
            "backtracking to decision level {} with decision {} and trail {}",
            new_level,
            self.control[new_level as usize].decision,
            assigned
        );

        let end_of_trail = self.trail.len();
        let mut i = assigned;
        let mut j = i;

        #[cfg(feature = "logging")]
        let mut unassigned: i32 = 0;
        let mut reassigned: i32 = 0;

        self.notify_backtrack(new_level as usize);
        if self.external_prop && !self.external_prop_is_lazy && !self.private_steps && self.notified > assigned {
            log!(
                self,
                "external propagator is notified about some unassignments (trail: {}, notified: {}).",
                self.trail.len(),
                self.notified
            );
            self.notified = assigned;
        }

        while i < end_of_trail {
            let lit = self.trail[i];
            i += 1;
            let v_level = self.var(lit).level;
            if v_level > new_level {
                self.unassign(lit);
                #[cfg(feature = "logging")]
                {
                    unassigned += 1;
                }
            } else {
                // This is the essence of the SAT'18 paper on chronological
                // backtracking.  It is possible to just keep out-of-order
                // assigned literals on the trail without breaking the
                // solver (after some modifications to 'analyze' - see
                // 'opts.chrono' guarded code there).
                #[cfg(feature = "logging")]
                {
                    if v_level == 0 {
                        log!(self, "reassign {} @ 0 unit clause {}", lit, lit);
                    } else {
                        log!(self, self.var(lit).reason, "reassign {} @ {}", lit, v_level);
                    }
                }
                self.trail[j] = lit;
                self.var_mut(lit).trail = j as i32;
                j += 1;
                reassigned += 1;
            }
        }
        self.trail.truncate(j);
        #[cfg(feature = "logging")]
        {
            log!(
                self,
                "unassigned {} literals {}%",
                unassigned,
                crate::format::fmt_f(percent(unassigned as f64, (unassigned + reassigned) as f64), 0)
            );
            log!(
                self,
                "reassigned {} literals {}%",
                reassigned,
                crate::format::fmt_f(percent(reassigned as f64, (unassigned + reassigned) as f64), 0)
            );
        }

        if self.propagated > assigned {
            self.propagated = assigned;
        }
        if self.propagated2 > assigned {
            self.propagated2 = assigned;
        }
        if self.no_conflict_until > assigned {
            self.no_conflict_until = assigned;
        }

        self.propergated = 0; // Always go back to root-level.

        debug_assert!(self.notified <= assigned + reassigned as usize);
        if reassigned != 0 {
            self.notify_assignments();
        }

        self.control.truncate((new_level + 1) as usize);
        self.level = new_level;
        if self.changed_val != 0 {
            debug_assert!(self.opts.ilb != 0);
            if self.val(self.changed_val) == 0 {
                self.changed_val = 0;
            }
        }
        debug_assert!(self.num_assigned == self.trail.len());
    }
}

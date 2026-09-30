//! Port of `external_propagate.cpp`: the IPASIR-UP external propagator
//! interaction of the internal solver (observed variables, external
//! propagation, lazy reason clauses, external clauses, final model check
//! and the notification of assignments, decisions and backtracks).

#[allow(unused_imports)]
use crate::prelude::*;

use crate::internal::Mode;

/// `__FILE__` in the C++ contract messages.
const FILE: &str = "../src/external_propagate.cpp";

/*------------------------------------------------------------------------*/

// The 'LOG_INTERACTION_*' macros of the C++ code (with tracing enabled,
// i.e., 'NTRACING' undefined, which is the default).  The call-back
// interactions are logged and, if 'opts.exttracecalls' is set and the
// external 'trace_api_file' is open, also traced.

/// Static `trace_api_call (FILE *, Internal *, const char *, int)`.
fn trace_api_call_1(trace_api_file: *mut libc::FILE, internal: &Internal, s0: &str, i1: i32) {
    debug_assert!(!trace_api_file.is_null());
    log!(internal, "TRACE {} {}", s0, i1);
    let _ = internal;
    crate::message::cfprint(trace_api_file, format_args!("{} {}\n", s0, i1));
    crate::message::fflush(trace_api_file);
}

/// Static `trace_api_call (FILE *, Internal *, const char *, int, int)`.
fn trace_api_call_2(
    trace_api_file: *mut libc::FILE,
    internal: &Internal,
    s0: &str,
    i1: i32,
    i2: i32,
) {
    debug_assert!(!trace_api_file.is_null());
    log!(internal, "TRACE {} {}", s0, i1);
    let _ = internal;
    crate::message::cfprint(trace_api_file, format_args!("{} {} {}\n", s0, i1, i2));
    crate::message::fflush(trace_api_file);
}

impl Internal {
    /// `LOG_INTERACTION_START (NAME)`.
    #[inline]
    fn log_interaction_start(&self, name: &str) {
        log!(self, "{} on level {} START", name, self.level);
        let _ = name;
    }

    /// `LOG_INTERACTION_FOR (NAME, VAL)`.
    #[inline]
    fn log_interaction_for(&self, name: &str, val: i32) {
        log!(self, "{}({}) on level {} START", name, val, self.level);
        let _ = (name, val);
    }

    /// `LOG_INTERACTION_RETURN_FOR (NAME, VAL, RET)`.
    #[inline]
    fn log_interaction_return_for(&self, name: &str, val: i32, ret: i32) {
        log!(self, "{}({}) returns {} on level {} END", name, val, ret, self.level);
        if self.opts.exttracecalls == 0 {
            return;
        }
        let file = self.external().trace_api_file;
        if file.is_null() {
            return;
        }
        trace_api_call_2(file, self, name, val, ret);
    }

    /// `LOG_INTERACTION_RETURN_TWO (NAME, RET1, RET2)`.
    #[inline]
    fn log_interaction_return_two(&self, name: &str, ret1: i32, ret2: i32) {
        log!(self, "{} returns {} ({}) on level {} END", name, ret1, ret2, self.level);
        if self.opts.exttracecalls == 0 {
            return;
        }
        let file = self.external().trace_api_file;
        if file.is_null() {
            return;
        }
        trace_api_call_2(file, self, name, ret1, ret2);
    }

    /// `LOG_INTERACTION_END_FOR (NAME, VAL)`.
    #[inline]
    fn log_interaction_end_for(&self, name: &str, val: i32) {
        log!(self, "{}({}) on level {} END", name, val, self.level);
        if self.opts.exttracecalls == 0 {
            return;
        }
        let file = self.external().trace_api_file;
        if file.is_null() {
            return;
        }
        trace_api_call_1(file, self, name, val);
    }

    /// `LOG_INTERACTION_RETURN (NAME, VAL)`.
    #[inline]
    fn log_interaction_return(&self, name: &str, val: i32) {
        log!(self, "{} returns {} on level {} END", name, val, self.level);
        if self.opts.exttracecalls == 0 {
            return;
        }
        let file = self.external().trace_api_file;
        if file.is_null() {
            return;
        }
        trace_api_call_1(file, self, name, val);
    }

    /// The connected external propagator (`external->propagator`).
    #[inline]
    #[allow(clippy::mut_from_ref)]
    fn ext_propagator(&self) -> &mut dyn ExternalPropagator {
        self.external().propagator.as_deref_mut().expect("external propagator connected")
    }

    /// `(size_t) abs (elit) < external->is_observed.size () &&
    /// external->is_observed[abs (elit)]`.
    #[inline]
    fn externally_observed(&self, elit: i32) -> bool {
        let eidx = elit.unsigned_abs() as usize;
        let external = self.external();
        eidx < external.is_observed.len() && external.is_observed[eidx]
    }
}

/*------------------------------------------------------------------------*/

impl Internal {
    /// Mark a variable as an observed one. It can be a new variable. It is
    /// assumed to be clean (not eliminated by previous simplifications).
    pub fn add_observed_var(&mut self, ilit: i32) {
        const F: &str = "void CaDiCaL::Internal::add_observed_var(int)";
        let idx = self.vidx(ilit);
        if idx as i64 >= self.relevanttab.len() as i64 {
            self.relevanttab.resize(1 + idx as usize, 0);
        }
        let r = self.relevanttab[idx as usize];
        if r < u32::MAX {
            self.relevanttab[idx as usize] = r + 1;
            log!(self, "variable {} is observed {} times", idx, r + 1);
        } else {
            log!(self, "variable {} remains observed forever", idx);
        }
        // TODO: instead of actually backtracking, it would be enough to
        // notify backtrack and re-play again every levels' notification to
        // the propagator
        if self.val(ilit) != 0 && self.level != 0 && self.fixed(ilit) == 0 {
            // The variable is already assigned, but we can not send a
            // notification about it because it happened on an earlier
            // decision level.  To not break the stack-like view of the
            // trail, we simply backtrack to undo this unnotifiable
            // assignment.
            require!(
                F,
                FILE,
                self.conflict.is_null(),
                "can not observe assigned variable during conflict analysis"
            );
            let assignment_level = self.var(ilit).level;
            self.backtrack(assignment_level - 1);
        } else if self.level != 0 && self.fixed(ilit) != 0 {
            require!(
                F,
                FILE,
                self.conflict.is_null(),
                "can not observe fixed variable during conflict analysis"
            );
            self.backtrack(0);
        }
    }

    /// Removing an observed variable should happen only once it is ensured
    /// that there is no unexplained propagation in the implication graph
    /// involving this variable. To ensure that, the solver might need to
    /// backtrack so that the variable becomes unassigned.
    pub fn remove_observed_var(&mut self, ilit: i32) {
        const F: &str = "void CaDiCaL::Internal::remove_observed_var(int)";
        if self.fixed(ilit) == 0 && self.level != 0 && self.val(ilit) != 0 {
            require!(
                F,
                FILE,
                self.conflict.is_null(),
                "can not unobserve assigned variable during conflict analysis"
            );
            let assignment_level = self.var(ilit).level;
            self.backtrack(assignment_level - 1);
        }

        debug_assert!(self.fixed(ilit) != 0 || self.val(ilit) == 0);

        let idx = self.vidx(ilit) as usize;
        debug_assert!(idx < self.relevanttab.len());
        debug_assert!(self.fixed(ilit) != 0 || self.relevanttab[idx] > 0);
        if self.fixed(ilit) != 0 {
            self.relevanttab[idx] = 0;
        } else if self.relevanttab[idx] < u32::MAX {
            self.relevanttab[idx] -= 1;
            if self.relevanttab[idx] == 0 {
                log!(self, "variable {} is not observed anymore", idx);
            } else {
                log!(
                    self,
                    "variable {} is unobserved once but remains observed {} times",
                    ilit,
                    self.relevanttab[idx]
                );
            }
        } else {
            log!(self, "variable {} remains observed forever", idx);
        }
    }

    /// Supposed to be used only by mobical.
    pub fn observed(&self, ilit: i32) -> bool {
        debug_assert!((self.vidx(ilit) as usize) < self.relevanttab.len());
        self.relevanttab[self.vidx(ilit) as usize] > 0
    }

    /// Check for unexplained propagations upon disconnecting external
    /// propagator.
    pub fn set_changed_val(&mut self) {
        if self.opts.ilb == 0 {
            return;
        }
        for idx in self.vars() {
            if self.val(idx) == 0 {
                continue;
            }
            if self.var(idx).reason != self.external_reason {
                continue;
            }
            if self.changed_val == 0 {
                self.changed_val = idx;
                continue;
            }
            debug_assert!(self.val(self.changed_val) != 0);
            if self.var(idx).level < self.var(self.changed_val).level {
                self.changed_val = idx;
            }
        }
    }

    pub fn renotify_trail_after_ilb(&mut self) {
        debug_assert!(self.opts.ilb != 0);
        if !self.external_prop
            || self.external_prop_is_lazy
            || self.trail.is_empty()
            || self.opts.ilb == 0
        {
            return;
        }
        log!(self, "notify external propagator about new assignments (after ilb)");
        #[cfg(debug_assertions)]
        log!(
            self,
            "(decision level: {}, trail size: {}, notified {})",
            self.level,
            self.trail.len(),
            self.notified
        );
        self.renotify_full_trail();
    }

    pub fn renotify_trail_after_local_search(&mut self) {
        if !self.external_prop || self.external_prop_is_lazy || self.trail.is_empty() {
            return;
        }
        log!(
            self,
            "notify external propagator about new assignments (after local search)"
        );
        #[cfg(debug_assertions)]
        log!(
            self,
            "(decision level: {}, trail size: {}, notified {})",
            self.level,
            self.trail.len(),
            self.notified
        );
        self.renotify_full_trail();
    }

    pub fn renotify_full_trail_between_trail_pos(
        &mut self,
        start_level: i32,
        end_level: i32,
        propagator_level: i32,
        assigned: &mut Vec<i32>,
        start_new_level: bool,
    ) {
        debug_assert!(assigned.is_empty());
        let mut j = start_level;
        log!(
            self,
            "starting notification of level {} from trail {} .. {}",
            propagator_level,
            start_level,
            end_level
        );
        let _ = propagator_level;
        if start_new_level {
            if !assigned.is_empty() {
                self.log_interaction_for("notify_assignment_batch", assigned.len() as i32);
                self.ext_propagator().notify_assignment(assigned);
                self.log_interaction_end_for("notify_assignment_batch", assigned.len() as i32);
            }
            assigned.clear();
            self.notified_level += 1;
            self.log_interaction_for("notify_new_decision_level", self.notified_level);
            self.ext_propagator().notify_new_decision_level();
            self.log_interaction_end_for("notify_new_decision_level", self.notified_level);
        }
        while j < end_level {
            let ilit = self.trail[j as usize];
            j += 1;
            // In theory, 0 ilit can happen due to pseudo-decision levels
            if ilit == 0 {
                continue;
            }

            if !self.observed(ilit) {
                continue;
            }

            let elit = self.externalize(ilit); // TODO: double-check tainting

            log!(
                self,
                "notifying elit {} @ {} aka {}",
                propagator_level,
                elit,
                loglit!(self, ilit)
            );
            debug_assert!(elit != 0);
            // Fixed variables might get mapped (during compact) to another
            // non-observed but fixed variable.  This happens on root level,
            // so notification about their assignment is already done.
            debug_assert!(self.external().observed(elit) || self.fixed(ilit) != 0);
            if !self.external().ervars[elit.unsigned_abs() as usize] {
                assigned.push(elit);
            }
        }

        if !assigned.is_empty() {
            self.log_interaction_for("notify_assignment_batch", assigned.len() as i32);
            self.ext_propagator().notify_assignment(assigned);
            self.log_interaction_end_for("notify_assignment_batch", assigned.len() as i32);
        }
        assigned.clear();
    }

    /// It repeats ALL assignments of the trail, so the already notified
    /// root-level assignments will be notified multiple times.
    ///
    /// As CaDiCaL is missing some '0' seperators, it is important to go
    /// over slices from the control stack instead of going over the trail
    /// directly.
    pub fn renotify_full_trail(&mut self) {
        let end_of_trail = self.trail.len();
        if self.level != 0 {
            self.notified = 0; // TODO: save the last notified root-level
                               // position somewhere and use it here
            if self.notified_level != 0 {
                self.notify_backtrack(0);
            }
        }
        let mut assigned: Vec<i32> = Vec::new();

        let mut propagator_level = 0;

        let c_size = self.control.len() as i32;
        {
            // first all root-level literals
            let start_level = 0;
            let end_level = if self.control.len() > 1 {
                self.control[1].trail
            } else {
                end_of_trail as i32
            };
            self.renotify_full_trail_between_trail_pos(
                start_level,
                end_level,
                propagator_level,
                &mut assigned,
                false,
            );
        }

        // notify all intermediate levels
        for i in 2..c_size {
            let start_level = self.control[(i - 1) as usize].trail;
            let end_level = self.control[i as usize].trail;
            propagator_level += 1;
            log!(self, "notification of {}", propagator_level);

            self.renotify_full_trail_between_trail_pos(
                start_level,
                end_level,
                propagator_level,
                &mut assigned,
                true,
            );
        }

        // and the current level if there is non-root level one
        if self.level != 0 {
            let start_level = self.control.last().unwrap().trail;
            propagator_level += 1;
            self.renotify_full_trail_between_trail_pos(
                start_level,
                end_of_trail as i32,
                propagator_level,
                &mut assigned,
                true,
            );
        }
        debug_assert!(propagator_level == self.level);
        self.notified = self.trail.len();
    }

    /// Check if the variable is assigned by decision.
    pub fn is_decision(&mut self, ilit: i32) -> bool {
        if self.level == 0 || self.fixed(ilit) != 0 || self.val(ilit) == 0 {
            return false;
        }

        let idx = self.vidx(ilit);
        #[cfg(debug_assertions)]
        log!(
            self,
            self.var(idx).reason,
            "is_decision: i{} (current level: {}, is_fixed: {}, v.level: {}, is_external_reason: {}, v.reason: )",
            ilit,
            self.level,
            self.fixed(ilit),
            self.var(idx).level,
            (self.var(idx).reason == self.external_reason) as i32
        );
        let v = *self.var(idx);
        if v.level == 0 || !v.reason.is_null() {
            return false;
        }
        debug_assert!(v.reason.is_null());
        true
    }

    pub fn force_backtrack(&mut self, new_level: i32) {
        const F: &str = "void CaDiCaL::Internal::force_backtrack(int)";
        require!(
            F,
            FILE,
            self.forced_backt_allowed,
            "not allowed to force backtrack in that state of the solver."
        );
        require!(
            F,
            FILE,
            new_level >= 0,
            "the target level of a forced backtrack must be non-negative."
        );
        require!(
            F,
            FILE,
            self.level > 0 && new_level < self.level,
            "the target level of a forced backtrack must be smaller than the current decision level."
        );

        #[cfg(debug_assertions)]
        log!(
            self,
            "external propagator forces backtrack to decision level{} (from level {})",
            new_level,
            self.level
        );
        self.backtrack(new_level);
    }

    /*--------------------------------------------------------------------*/

    /// Call external propagator to check if there is a literal to be
    /// propagated.  The reason of the propagation is not necessarily asked
    /// at that point.
    ///
    /// In case the externally propagated literal is already falsified, the
    /// reason is asked and conflict analysis starts. In case the externally
    /// propagated literal is already satisfied, nothing happens.
    pub fn external_propagate(&mut self) -> bool {
        if self.level != 0 {
            self.require_mode(Mode::SEARCH);
        }
        debug_assert!(!self.unsat);

        let before = self.num_assigned;
        let mut cb_repropagate_needed = true;
        while cb_repropagate_needed
            && self.conflict.is_null()
            && self.external_prop
            && !self.external_prop_is_lazy
            && !self.private_steps
        {
            #[cfg(debug_assertions)]
            log!(
                self,
                "external propagation starts (decision level: {}, trail size: {}, notified {})",
                self.level,
                self.trail.len(),
                self.notified
            );
            cb_repropagate_needed = false;
            // external->reset_extended (); //TODO for inprocessing

            self.notify_assignments();

            self.log_interaction_start("cb_propagate");
            let mut elit = self.ext_propagator().cb_propagate();
            self.log_interaction_return("cb_propagate", elit);

            cb_require!(
                elit == 0 || self.externally_observed(elit),
                "cb_propagate",
                elit,
                "external propagations are only allowed over observed variables."
            );

            self.stats.ext_prop.ext_cb += 1;
            self.stats.ext_prop.eprop_call += 1;
            while elit != 0 {
                debug_assert!(self.external().is_observed[elit.unsigned_abs() as usize]);
                let mut ilit = self.external().e2i[elit.unsigned_abs() as usize];
                if elit < 0 {
                    ilit = -ilit;
                }
                let tmp = self.val(ilit);
                #[cfg(debug_assertions)]
                {
                    debug_assert!(self.fixed(ilit) != 0 || self.observed(ilit));
                    log!(self, "External propagation of e{} (i{} val: {})", elit, ilit, tmp);
                }
                if tmp == 0 {
                    // variable is not assigned, it can be propagated
                    if self.level == 0 {
                        let res = self.learn_external_reason_clause(ilit, elit, false);
                        let _ = res;
                    } else {
                        self.search_assign_external(ilit);
                    }
                    self.stats.ext_prop.eprop_prop += 1;

                    if self.unsat || !self.conflict.is_null() {
                        break;
                    }
                    self.propagate();
                    if self.unsat || !self.conflict.is_null() {
                        break;
                    }
                    self.notify_assignments();
                } else if tmp < 0 {
                    log!(
                        self,
                        "External propgation of {} is falsified under current trail",
                        ilit
                    );
                    self.stats.ext_prop.eprop_conf += 1;
                    let level_before = self.level;
                    let assigned = self.num_assigned;
                    let res = self.learn_external_reason_clause(ilit, elit, false);
                    let _ = res;
                    let trail_changed = self.num_assigned != assigned
                        || self.level != level_before
                        || self.propagated < self.trail.len();

                    if self.unsat || !self.conflict.is_null() {
                        break;
                    }

                    if trail_changed {
                        self.propagate();
                        if self.unsat || !self.conflict.is_null() {
                            break;
                        }
                        self.notify_assignments();
                    }
                } // else (tmp > 0) -> the case of a satisfied literal is ignored
                self.log_interaction_start("cb_propagate");
                elit = self.ext_propagator().cb_propagate();
                self.log_interaction_return("cb_propagate", elit);
                self.stats.ext_prop.ext_cb += 1;
                self.stats.ext_prop.eprop_call += 1;
            }

            #[cfg(debug_assertions)]
            log!(
                self,
                "External propagation ends (decision level: {}, trail size: {}, notified {})",
                self.level,
                self.trail.len(),
                self.notified
            );
            if !self.unsat && self.conflict.is_null() {
                let mut level_before = self.level;
                let mut assigned = self.num_assigned;
                let mut has_external_clause = self.ask_external_clause();
                // New observed variable might have triggered a backtrack
                // during this ask_external_clause call, so we need to
                // propagate before continuing
                self.stats.ext_prop.ext_cb += 1;
                self.stats.ext_prop.elearn_call += 1;

                let mut trail_changed = self.num_assigned != assigned
                    || self.level != level_before
                    || self.propagated < self.trail.len();
                if trail_changed {
                    self.propagate(); // unsat or conflict will be caught later
                    if !self.unsat || self.conflict.is_null() {
                        self.notify_assignments();
                    }
                }

                #[cfg(debug_assertions)]
                {
                    if has_external_clause {
                        log!(self, "New external clauses are to be added.");
                    } else {
                        log!(self, "No external clauses to be added.");
                    }
                }

                while has_external_clause {
                    level_before = self.level;
                    assigned = self.num_assigned;

                    self.add_external_clause(0, false);
                    trail_changed = self.num_assigned != assigned
                        || self.level != level_before
                        || self.propagated < self.trail.len();
                    cb_repropagate_needed = true;

                    if self.unsat || !self.conflict.is_null() {
                        cb_repropagate_needed = false;
                        break;
                    }

                    if trail_changed {
                        self.propagate();
                        if self.unsat || !self.conflict.is_null() {
                            cb_repropagate_needed = false;
                            break;
                        }

                        self.notify_assignments();
                    }
                    has_external_clause = self.ask_external_clause();
                    self.stats.ext_prop.ext_cb += 1;
                    self.stats.ext_prop.elearn_call += 1;
                }
            }
            #[cfg(debug_assertions)]
            log!(
                self,
                "External clause addition ends on decision level {} at trail size {} (notified {})",
                self.level,
                self.trail.len(),
                self.notified
            );
        }
        if before < self.num_assigned {
            self.did_external_prop = true;
        }
        self.conflict.is_null()
    }

    /*--------------------------------------------------------------------*/

    /// Helper function, calls 'cb_has_external_clause', while maintains
    /// the related redundancy type of the clause.
    pub fn ask_external_clause(&mut self) -> bool {
        self.ext_clause_forgettable = false;
        self.log_interaction_start("cb_has_external_clause");
        let mut forgettable = self.ext_clause_forgettable;
        let res = self.ext_propagator().cb_has_external_clause(&mut forgettable);
        self.ext_clause_forgettable = forgettable;
        self.log_interaction_return_two(
            "cb_has_external_clause",
            res as i32,
            self.ext_clause_forgettable as i32,
        );

        res
    }

    /*--------------------------------------------------------------------*/

    /// Literals of the externally learned clause must be reordered based
    /// on the assignment levels of the literals.  Returns the best clause
    /// idx (except ignore).
    pub fn best_literal_to_watch(&mut self, ignore: i32, trail_over_level: bool) -> usize {
        let mut lit_position: usize = 0;
        let mut lit: i32 = 0;

        let mut lit_level: i32 = 0;
        let mut lit_value: i8 = 0;
        let mut lit_trail: i32 = 0;
        for i in 0..self.clause.len() {
            let other = self.clause[i];
            if other == ignore {
                continue;
            }
            debug_assert!(other != 0);

            let other_level = self.var(other).level;
            let other_value = self.val(other);
            let other_trail = self.var(other).trail;

            if lit == 0                                          // no candidate yet.
                || lit_value < other_value                       // -1 < 0 < 1
                || (lit_value == other_value                     // Tie breaker:
                    && ((lit_value < 0                           // -1:
                        && ((!trail_over_level                   // level over trail:
                            && (lit_level < other_level          // higher level, or
                                || (lit_level == other_level     // equal level:
                                    && lit_trail < other_trail))) // higher trail
                            || (trail_over_level                 // trail over level:
                                && lit_trail < other_trail)))    // higher trail
                        || (lit_value > 0 && lit_level > other_level))) // 1: lower level
            {
                lit = other;
                lit_position = i;
                lit_value = other_value;
                lit_level = other_level;
                lit_trail = other_trail;
            }
        }
        debug_assert!(lit != 0);
        lit_position
    }

    pub fn move_literals_to_watch(&mut self) {
        if self.clause.len() < 2 {
            return;
        }
        if self.level == 0 {
            return;
        }

        let best1 = self.best_literal_to_watch(0, false);
        let lit = self.clause[best1];
        if best1 != 0 {
            self.clause.swap(0, best1);
        }

        let best2 = self.best_literal_to_watch(lit, false);
        // const int other = clause[best2];

        debug_assert!(best2 != 0 && self.clause[best2] != lit);

        if best2 != 1 {
            self.clause.swap(1, best2);
        }
    }

    /*--------------------------------------------------------------------*/

    /// Reads out from the external propagator the lemma/proapgation reason
    /// clause literal by literal. In case propagated_elit is 0, it is about
    /// an external clause via 'cb_add_external_clause_lit'. Otherwise, it
    /// is about learning the reason of 'propagated_elit' via
    /// 'cb_add_reason_clause_lit'.  The learned clause is simplified by the
    /// current root-level assignment (i.e. root-level falsified literals
    /// are removed, root satisfied clauses are skipped). Duplicate literals
    /// are removed, tauotologies are detected and skipped. It always adds
    /// the original (un-simplified) external clause to the proof as an
    /// input clause and the simplified version of it (except exceptions
    /// below) as a derived clause.
    ///
    /// In case the external clause, after simplifications, is satisfied, no
    /// clause is constructed, and the function returns 0. In case the
    /// external clause, after simplifications, is empty, no clause is
    /// constructed, unsat is set true and the function returns 0. In case
    /// the external clause, after simplifications, is unit, no clause is
    /// constructed, 'Internal::clause' has the unit literal (without 0) and
    /// the function returns 0.
    ///
    /// In every other cases a new clause is constructed and the pointer is
    /// in newest_clause
    pub fn add_external_clause(&mut self, propagated_elit: i32, no_backtrack: bool) {
        debug_assert!(self.original.is_empty());
        let mut elit;
        let mut propagated_lit_found = false;

        if propagated_elit != 0 {
            // Propagation reason clauses are by default assumed to be
            // forgettable irredundant. In case they would be unforgettably
            // important, the propagator can add them as an explicit
            // unforgettable external clause or set
            // 'are_reasons_forgettable' to false.
            self.ext_clause_forgettable = self.ext_propagator().are_reasons_forgettable();
            #[cfg(debug_assertions)]
            log!(self, "add external reason of propagated lit: {}", propagated_elit);
            self.log_interaction_for("cb_add_reason_clause_lit", propagated_elit);
            elit = self.ext_propagator().cb_add_reason_clause_lit(propagated_elit);
            self.log_interaction_return_for("cb_add_reason_clause_lit", propagated_elit, elit);
            if elit == propagated_elit {
                propagated_lit_found = true;
            }

            cb_require!(
                elit == 0 || self.externally_observed(elit),
                "cb_add_reason_clause_lit",
                elit,
                "reason clause must contain only observed variables."
            );
        } else {
            self.log_interaction_start("cb_add_external_clause_lit");
            elit = self.ext_propagator().cb_add_external_clause_lit();
            self.log_interaction_return("cb_add_external_clause_lit", elit);

            cb_require!(
                elit == 0 || self.externally_observed(elit),
                "cb_add_external_clause_lit",
                elit,
                "external clause must contain only observed variables."
            );
        }

        // we need to be build a new LRAT chain if we are already in the
        // middle of the analysis (like during failed assumptions)
        log!(self, &self.lrat_chain, "lrat chain before");
        let lrat_chain_ext: Vec<i64> = std::mem::take(&mut self.lrat_chain);
        self.lrat_chain.clear();
        self.clause.clear();

        // Read out the external lemma into original and simplify it into
        // clause
        debug_assert!(self.clause.is_empty());
        debug_assert!(self.original.is_empty());

        debug_assert!(!self.force_no_backtrack);
        debug_assert!(!self.from_propagator);
        self.force_no_backtrack = no_backtrack;
        self.from_propagator = true;
        while elit != 0 {
            self.external().add(elit);
            if propagated_elit != 0 {
                self.log_interaction_for("cb_add_reason_clause_lit", propagated_elit);
                elit = self.ext_propagator().cb_add_reason_clause_lit(propagated_elit);
                self.log_interaction_return_for("cb_add_reason_clause_lit", propagated_elit, elit);
                if elit == propagated_elit {
                    propagated_lit_found = true;
                }
                cb_require!(
                    elit == 0 || self.externally_observed(elit),
                    "cb_add_reason_clause_lit",
                    elit,
                    "reason clause must contain only observed variables."
                );
            } else {
                self.log_interaction_start("cb_add_external_clause_lit");
                elit = self.ext_propagator().cb_add_external_clause_lit();
                self.log_interaction_return("cb_add_external_clause_lit", elit);
                cb_require!(
                    elit == 0 || self.externally_observed(elit),
                    "cb_add_external_clause_lit",
                    elit,
                    "external clause must contain only observed variables."
                );
            }
        }
        self.external().add(elit);

        cb_require!(
            propagated_elit == 0 || propagated_lit_found,
            "cb_add_reason_clause_lit",
            elit,
            "external reason clause must contain the propagated literal."
        );

        debug_assert!(self.original.is_empty());
        debug_assert!(self.clause.is_empty());
        self.force_no_backtrack = false;
        self.from_propagator = false;
        self.lrat_chain = lrat_chain_ext;
        log!(self, &self.lrat_chain, "lrat chain after");
    }

    /*--------------------------------------------------------------------*/

    /// Recursively calls 'learn_external_reason_clause' to explain every
    /// backward reachable externally propagated literal starting from
    /// 'ilit'.
    pub fn explain_reason(&mut self, ilit: i32, reason: CRef, open: &mut i32) {
        if self.opts.exteagerreasons == 0 {
            return;
        }
        #[cfg(debug_assertions)]
        log!(self, reason, "explain_reason of {} (open: {})", ilit, *open);
        debug_assert!(!reason.is_null());
        debug_assert!(reason != self.external_reason);
        let size = reason.size() as usize;
        for i in 0..size {
            let other = reason.lit(i);
            if other == ilit {
                continue;
            }
            if self.flags(other).seen {
                continue;
            }
            if self.var(other).level == 0 {
                continue;
            }
            debug_assert!(self.val(other) < 0);
            debug_assert!(self.var(other).level <= self.level);
            if self.var(other).reason == self.external_reason {
                let r = self.learn_external_reason_clause(-other, 0, true);
                self.var_mut(other).reason = r;
            }
            if self.var(other).level != 0 && !self.var(other).reason.is_null() {
                self.flags_mut(other).seen = true;
                *open += 1;
            }
        }
    }

    /// In case external propagation was used, the reason clauses of the
    /// relevant propagations must be learned lazily before/during conflict
    /// analysis.  While conflict analysis needs to analyze only the current
    /// level, lazy clause learning must check every clause on every level
    /// that is backward reachable from the conflicting clause to guarantee
    /// that the assignment levels of the variables are accurate. So this
    /// explanation round is separated from the conflict analysis, thereby
    /// guranteeing that the flags and datastructures can be properly used
    /// later.
    ///
    /// This function must be called before the conflict analysis, in order
    /// to guarantee that every relevant reason clause is indeed learned
    /// already and to be sure that the levels of assignments are set
    /// correctly.
    ///
    /// Later TODO: experiment with bounded explanation (explain only those
    /// literals that are directly used during conflict analysis +
    /// minimizing/shrinking). The assignment levels are then only
    /// over-approximated.
    pub fn explain_external_propagations(&mut self) {
        debug_assert!(!self.conflict.is_null());
        debug_assert!(self.clause.is_empty());

        let reason = self.conflict;
        let mut seen_lits: Vec<i32> = Vec::new();
        let mut open: i32 = 0; // Seen but not explained literal

        self.explain_reason(0, reason, &mut open); // marks conflict clause lits as seen
        let mut i = self.trail.len(); // Start at end-of-trail
        while i > 0 {
            i -= 1;
            let lit = self.trail[i];
            if !self.flags(lit).seen {
                continue;
            }
            seen_lits.push(lit);
            if self.var(lit).level == 0 {
                continue;
            }
            let r = self.var(lit).reason;
            if !r.is_null() {
                open -= 1;
                self.explain_reason(lit, r, &mut open);
            }
            if open == 0 {
                break;
            }
        }
        debug_assert!(open == 0);

        if self.opts.exteagerrecalc == 0 {
            for &lit in seen_lits.iter() {
                self.flags_mut(lit).seen = false;
            }
            seen_lits.clear();
            #[cfg(debug_assertions)]
            for idx in self.vars() {
                debug_assert!(!self.flags(idx).seen);
            }
        } else {
            debug_assert!(
                self.external_prop
                    && !self.external_prop_is_lazy
                    && self.opts.exteagerreasons != 0
                    && self.opts.exteagerrecalc != 0
            );
            // Traverse now in the opposite direction (from lower to higher
            // levels) and calculate the actual assignment level for the
            // seen assignments.
            for k in (0..seen_lits.len()).rev() {
                let lit = seen_lits[k];
                let r = self.var(lit).reason;
                if !r.is_null() {
                    let mut real_level = 0;
                    let size = r.size() as usize;
                    for j in 0..size {
                        let other = r.lit(j);
                        if other == lit {
                            continue;
                        }
                        let tmp = self.var(other).level;
                        if tmp > real_level {
                            real_level = tmp;
                        }
                    }
                    if self.var(lit).level != 0 && real_level == 0 {
                        let reason = self.var(lit).reason;
                        self.build_chain_for_units(lit, reason, true);
                        self.learn_unit_clause(lit);
                        self.lrat_chain.clear();
                        self.var_mut(lit).reason = CRef::NULL;
                    }
                    debug_assert!(self.var(lit).level >= real_level);
                    if self.var(lit).level > real_level {
                        self.var_mut(lit).level = real_level;
                    }
                }
                self.flags_mut(lit).seen = false;
            }
        }
    }

    /*--------------------------------------------------------------------*/

    /// Learns the reason clause of the propagation of ilit from the
    /// external propagator via 'add_external_clause'.  In case of
    /// falsified propagation steps, if the propagated literal is already
    /// fixed to the opposite value, externalize will not necessarily give
    /// back the original elit (but an equivalent one). To avoid that, in
    /// falsified propagation cases the propagated elit is added as a second
    /// argument.
    pub fn learn_external_reason_clause(
        &mut self,
        ilit: i32,
        falsified_elit: i32,
        no_backtrack: bool,
    ) -> CRef {
        debug_assert!(self.external().propagator.is_some()); // REQ is defined by not allowing
                                                             // unobserving during conflict
        // we cannot modify clause during analysis
        let clause_tmp = std::mem::take(&mut self.clause);

        debug_assert!(self.clause.is_empty());
        debug_assert!(self.original.is_empty());

        self.stats.ext_prop.eprop_expl += 1;

        let elit = if falsified_elit == 0 {
            debug_assert!(self.fixed(ilit) == 0);
            self.externalize(ilit)
        } else {
            falsified_elit
        };

        log!(self, "ilit: {}, elit: {}", ilit, elit);
        self.add_external_clause(elit, no_backtrack);

        #[cfg(debug_assertions)]
        {
            if falsified_elit == 0 && !self.newest_clause.is_null() {
                // Check if external propagation is correct wrt to the
                // topological order defined by the trail. In case it is a
                // falsified external propagation step, the order does not
                // matter, the reason simply supposed to be a falsified
                // clause.
                let propagated_ilit = ilit;
                let c = self.newest_clause;
                for &reason_ilit in c.lits() {
                    debug_assert!(self.var(reason_ilit).trail <= self.var(propagated_ilit).trail);
                }
            }
        }

        self.clause = clause_tmp;
        self.newest_clause
    }

    /// Helper function to be able to call learn_external_reason_clause when
    /// the internal clause is already used in the caller side (for example
    /// during proof checking). These calls are assumed to be without a
    /// falsified elit.  Dont use it in general instead of
    /// learn_external_reason_clause because it does not support the corner
    /// cases where a literal remains in clause.
    pub fn wrapped_learn_external_reason_clause(&mut self, ilit: i32) -> CRef {
        let res;
        let chain_tmp: Vec<i64> = std::mem::take(&mut self.lrat_chain);
        self.lrat_chain.clear();
        if self.clause.is_empty() {
            res = self.learn_external_reason_clause(ilit, 0, true);
        } else {
            let clause_tmp: Vec<i32> = std::mem::take(&mut self.clause);
            self.clause.clear();
            res = self.learn_external_reason_clause(ilit, 0, true);
            // The learn_external_reason clause can leave a literal in
            // clause when there is a falsified elit arg. Here it is not
            // allowed to happen.
            debug_assert!(self.clause.is_empty());

            self.clause = clause_tmp;
        }
        debug_assert!(self.lrat_chain.is_empty());
        self.lrat_chain = chain_tmp;
        res
    }

    /*--------------------------------------------------------------------*/

    /// Checks if the new clause forces backtracking, new assignments or
    /// conflict analysis.
    pub fn handle_external_clause(&mut self, res: CRef, new_id: i64) {
        if self.from_propagator {
            self.stats.ext_prop.elearned += 1;
        }
        if self.from_propagator && res.is_null() {
            self.stats.ext_prop.elearn_unit += 1;
        }
        // new unit clause. For now just backtrack.
        if res.is_null()
            && (self.force_no_backtrack
                || (self.val(self.clause[0]) > 0
                    && self.opts.elevate > 0
                    && (self.opts.elevate > 1 || !self.var(self.clause[0]).reason.is_null())))
        {
            if self.force_no_backtrack {
                self.did_external_prop = true;
            }
            debug_assert!(self.level != 0);
            debug_assert!(new_id != 0);
            let idx = self.vidx(self.clause[0]);
            debug_assert!(self.val(self.clause[0]) >= 0);
            debug_assert!(!self.flags(idx).eliminated());
            debug_assert!(self.val(self.clause[0]) != 0);
            {
                let v = self.var_mut(idx);
                v.level = 0;
                v.reason = CRef::NULL;
            }
            log!(self, "elevate {} to level 0", loglit!(self, idx));
            let uidx = self.vlit(self.clause[0]);
            if self.lrat || self.frat {
                *self.unit_clauses(uidx as i32) = new_id;
            }
            let lit = self.clause[0];
            self.mark_fixed(lit);
            return;
        }

        if res.is_null() {
            if self.from_propagator {
                self.stats.ext_prop.elearn_prop += 1;
            }
            let lit = self.clause[0];
            debug_assert!(self.val(lit) == 0 || self.var(lit).level != 0);
            if self.val(lit) != 0 {
                let l = self.var(lit).level - 1;
                self.backtrack_without_updating_phases(l);
            }
            if self.opts.elevate == -1 && self.val(lit) != 0 {
                self.backtrack_without_updating_phases(0);
            }
            debug_assert!(self.val(lit) == 0);
            self.assign_original_unit(new_id, lit);
            return;
        }

        // at level 0 we have to do nothing...
        if self.level == 0 {
            return;
        }

        debug_assert!(!res.is_null());
        debug_assert!(res.size() >= 2);
        let pos0 = res.lit(0);
        let pos1 = res.lit(1);
        let l1 = self.var(pos1).level;
        let l0 = self.var(pos0).level;
        if self.force_no_backtrack {
            debug_assert!(self.from_propagator);
            debug_assert!(self.val(pos1) < 0);
            debug_assert!(self.val(pos0) >= 0);

            if self.var(pos0).level != l1 {
                self.stats.ext_prop.elearn_elevate += 1;
                log!(
                    self,
                    res,
                    "elevate assignment of {} from level {} to level {} with lazy reason clause",
                    loglit!(self, pos0),
                    l0,
                    l1
                );
                log!(self, "elevate {} to level {}", loglit!(self, pos0), l1);
            } else {
                log!(self, res, "add assignment {} lazy reason clause", loglit!(self, pos0));
            }
            self.var_mut(pos0).level = l1;
            return;
        }
        debug_assert!(!self.force_no_backtrack);

        if self.val(pos1) >= 0 {
            // do nothing
            return;
        }

        if self.val(pos0) < 0 {
            // conflicting
            debug_assert!(self.val(pos1) < 0);
            debug_assert!(0 < l1 && l1 <= self.var(pos0).level);
            if self.opts.elevate == -1 {
                self.backtrack_without_updating_phases(l1);
            }
            // its better to backtrack instead of analyze without propagator
            // but analyze with propagaor
            if self.val(pos0) != 0 && !self.from_propagator {
                self.backtrack_without_updating_phases(l0 - 1);
            } else if self.val(pos0) != 0 && self.from_propagator {
                self.conflict = res;
                self.stats.ext_prop.elearn_conf += 1;
            }
            if self.val(pos1) < 0 && self.val(pos0) == 0 {
                self.search_assign_driving(pos0, res);
            }
            return;
        }

        if self.val(pos0) == 0 {
            // propagating
            debug_assert!(self.val(pos1) < 0);
            if self.opts.elevate == -1 {
                self.backtrack_without_updating_phases(l1);
            }
            if self.val(pos1) < 0 && self.val(pos0) == 0 {
                self.search_assign_driving(pos0, res);
            }
            return;
        }

        if l0 <= l1 {
            // no alternative reason
            return;
        }

        debug_assert!(self.val(pos0) > 0); // elevating
        debug_assert!(self.val(pos1) < 0);

        // It would have propagated pos0 on an earlier level than it is
        // assigned

        // Find the highest literal based on trail-position of the clause

        let highest_idx = self.best_literal_to_watch(pos0, true);
        debug_assert!(highest_idx != 0);
        let highest_literal = self.clause[highest_idx];

        // highest trail level variable
        let m = *self.var(highest_literal);
        debug_assert!(l0 >= m.level);

        // best watch variable
        let v_trail = self.var(pos0).trail;
        let v_reason = self.var(pos0).reason;

        // out-of-order if best watch smaller highest.
        if v_trail < m.trail && self.opts.elevate > 0 {
            debug_assert!(highest_idx != 0);
            if highest_idx != 1 {
                res.set_lit(1, highest_literal);
                res.set_lit(highest_idx, pos1);
            }
            if self.from_propagator {
                self.stats.ext_prop.elearn_ooo += 1;
            }
            log!(
                self,
                res,
                "ignore out-of-order missed assignment of {} from level {} to level {} with new reason clause",
                loglit!(self, pos0),
                self.var(pos0).level,
                self.var(pos1).level
            );
            return;
        }

        // in order
        if v_trail > m.trail && self.opts.elevate > 0 && (self.opts.elevate > 1 || !v_reason.is_null())
        {
            // If v.trail == m.trail, then the propagated literal is the
            // maximum as well, so no need to backtrack we simply reassign
            // the reason and level of the propagation
            log!(
                self,
                res,
                "elevate assignment of {} from level {} to level {} with new reason clause",
                loglit!(self, pos0),
                self.var(pos0).level,
                self.var(pos1).level
            );

            debug_assert!(l1 < l0);
            debug_assert!(self.var(pos1).trail < self.var(pos0).trail);
            debug_assert!(self.var(highest_literal).trail < self.var(pos0).trail);

            {
                let v = self.var_mut(pos0);
                v.level = l1;
                v.reason = res;
            }
            log!(self, "elevate {} to level {}", loglit!(self, pos0), l1);

            if self.from_propagator {
                self.stats.ext_prop.elearn_elevate += 1;
            }

            if self.out_of_order_level == -1 || l1 < self.out_of_order_level {
                self.out_of_order_level = l1;
            }
            let v_trail = self.var(pos0).trail;
            if v_trail > self.out_of_order_trail {
                self.out_of_order_trail = v_trail;
            }
            return;
        }

        // backtrack instead
        log!(
            self,
            res,
            "backtrack due to missed assignment of {} from level {} to level {} with new reason clause",
            pos0,
            l0,
            l1
        );
        debug_assert!(!self.force_no_backtrack);

        if self.opts.elevate == -1 {
            self.backtrack_without_updating_phases(l1);
        } else {
            self.backtrack_without_updating_phases(l0 - 1);
        }

        debug_assert!(self.val(pos0) == 0 && self.val(pos1) < 0);
        self.search_assign_driving(pos0, res);

        // 'm' is a reference in C++, so re-read it after backtracking.
        debug_assert!(self.var(pos0).trail >= self.var(highest_literal).trail);
        debug_assert!(self.var(pos0).level == l1);
        debug_assert!(self.val(pos0) > 0 && self.val(pos1) < 0);
    }

    /*--------------------------------------------------------------------*/

    /// Asks the external propagator if the current solution is OK by
    /// calling 'cb_check_found_model (model)'.
    ///
    /// The checked model is built up after everything is restored from the
    /// reconstruction stack and every variable is reactivated and so it is
    /// not just simply the trail (i.e. it can be expensive).
    ///
    /// If the external propagator approves the model, the function returns
    /// true.
    ///
    /// If the propagator does not approve the model, the solver asks the
    /// propagator to add an external clause.  This external clause,
    /// however, does NOT have to be falsified by the current model. The
    /// possible cases and reactions are described below in the function.
    /// The possible states after that function:
    /// - A solution was found and accepted by the external propagator
    /// - A conflicting clause was learned from the external propagator
    /// - The empty clause was learned due to something new learned from
    ///   the external propagator.
    ///
    /// In case only new variables were introduced, but no new clauses were
    /// added, the function will return without a conflict to the outer CDCL
    /// loop, where the new (not yet satisfied) variables are recognized and
    /// the search continues.
    pub fn external_check_solution(&mut self) -> bool {
        if !self.external_prop {
            return true;
        }

        let mut trail_changed = true;
        let mut added_new_clauses = false;
        while trail_changed || added_new_clauses {
            self.notify_assignments();
            if !self.satisfied() {
                break;
            }
            trail_changed = false; // to be on the safe side
            added_new_clauses = false;
            log!(self, "Final check by external propagator is invoked.");
            self.stats.ext_prop.echeck_call += 1;
            self.external().reset_extended();
            self.external().extend();

            let mut etrail: Vec<i32> = Vec::new();

            // Here the variables must be filtered by external->is_observed,
            // because fixed variables are internally not necessarily
            // observed anymore.
            let last = std::cmp::min(
                self.external().is_observed.len() as i32 - 1,
                self.external().max_var,
            );
            let mut idx = 1;
            while idx <= last {
                if !self.external().is_observed[idx as usize] {
                    idx += 1;
                    continue;
                }
                let lit = self.external().ival(idx);
                etrail.push(lit);
                #[cfg(debug_assertions)]
                {
                    #[cfg(feature = "logging")]
                    {
                        let p = self.external().vals[idx as usize];
                        log!(self, "evals[{}]: {} ival({}): {}", idx, p as i32, idx, lit);
                    }
                }
                idx += 1;
            }

            self.forced_backt_allowed = true;
            let assigned = self.num_assigned;
            let level_before = self.level;
            self.log_interaction_start("cb_check_found_model");
            let is_consistent = self.ext_propagator().cb_check_found_model(&etrail);
            self.log_interaction_return("cb_check_found_model", is_consistent as i32);
            self.stats.ext_prop.ext_cb += 1;
            self.forced_backt_allowed = false;

            if self.num_assigned != assigned
                || self.level != level_before
                || self.propagated < self.trail.len()
            {
                // In case an external forced backtracking was performed,
                // the CDCL loop needs to continue withouth further checks
                // of the model.
                trail_changed = true;
                let _ = trail_changed;
                return self.conflict.is_null();
            }

            if is_consistent {
                log!(self, "Found solution is approved by external propagator.");
                return true;
            }

            let mut has_external_clause = self.ask_external_clause();

            self.stats.ext_prop.ext_cb += 1;
            self.stats.ext_prop.elearn_call += 1;

            if has_external_clause {
                log!(self, "Found solution triggered new clauses from external propagator.");
            }

            while has_external_clause {
                let level_before = self.level;
                let assigned = self.num_assigned;
                self.add_external_clause(0, false);
                // NOTE: shadows the outer 'trail_changed' as in C++.
                let trail_changed = self.num_assigned != assigned
                    || self.level != level_before
                    || self.propagated < self.trail.len();
                added_new_clauses = true;
                //
                // There are many possible scenarios here:
                // - Learned conflicting clause: return to CDCL loop
                //   (conflict true)
                // - Learned conflicting unit clause that after
                //   backtrack+BCP leads to a new complete solution: force
                //   the outer loop to check the new model (trail_changed is
                //   true, but (conflict & unsat) is false)
                // - Learned empty clause: return to CDCL loop (unsat true)
                // - Learned a non-conflicting unit clause: Though it does
                //   not invalidate the current solution, the solver will
                //   backtrack to the root level and will repropagate it.
                //   The search will start again (saved phases hopefully
                //   make it quick), but it is needed in order to guarantee
                //   that every fixed variable is properly handled+notified
                //   (important for incremental use cases).
                // - Otherwise: the solution is considered approved and the
                //   CDCL-loop can return with res = 10.
                //
                if self.unsat || !self.conflict.is_null() || trail_changed {
                    break;
                }
                has_external_clause = self.ask_external_clause();
                self.stats.ext_prop.ext_cb += 1;
                self.stats.ext_prop.elearn_call += 1;
            }
            log!(self, "No more external clause to add.");
            if self.unsat || !self.conflict.is_null() {
                break;
            }
        }

        if !self.unsat && !self.conflict.is_null() {
            let conflict_level = self.var(self.conflict.lit(0)).level;
            if conflict_level != self.level {
                self.backtrack(conflict_level);
            }
        }

        self.conflict.is_null()
    }

    /*--------------------------------------------------------------------*/

    /// Notify the external propagator that an observed variable got
    /// assigned.
    pub fn notify_assignments(&mut self) {
        if !self.external_prop || self.external_prop_is_lazy || self.private_steps {
            return;
        }

        let end_of_trail = self.trail.len();

        if self.notified >= end_of_trail {
            return;
        }

        log!(self, "notify external propagator about new assignments");
        let mut assigned: Vec<i32> = Vec::new();

        while self.notified < end_of_trail {
            let ilit = self.trail[self.notified];
            self.notified += 1;
            if !self.observed(ilit) {
                continue;
            }

            let elit = self.externalize(ilit); // TODO: double-check tainting
            debug_assert!(elit != 0);
            if self.external().ervars[elit.unsigned_abs() as usize] {
                continue;
            }
            // Fixed variables might get mapped (during compact) to another
            // non-observed but fixed variable.  This happens on root level,
            // so notification about their assignment is already done.
            debug_assert!(
                self.external().observed(elit)
                    || (self.fixed(ilit) != 0
                        && !self.external().ervars[elit.unsigned_abs() as usize])
            );
            assigned.push(elit);
        }
        if !assigned.is_empty() {
            self.log_interaction_for("notify_assignment_batch", assigned.len() as i32);
            self.ext_propagator().notify_assignment(&assigned);
            self.log_interaction_end_for("notify_assignment_batch", assigned.len() as i32);
        }
        assigned.clear();
    }

    /*--------------------------------------------------------------------*/

    pub fn connect_propagator(&mut self) {
        if self.level != 0 {
            self.backtrack(0);
        }
    }

    /*--------------------------------------------------------------------*/

    /// Notify the external propagator that a new decision level is
    /// started.
    pub fn notify_decision(&mut self) {
        if !self.external_prop || self.external_prop_is_lazy || self.private_steps {
            return;
        }
        self.notify_assignments();
        self.notified_level = self.level;
        self.log_interaction_for("notify_new_decision_level", self.level);
        self.ext_propagator().notify_new_decision_level();
        self.log_interaction_end_for("notify_new_decision_level", self.level);
    }

    /*--------------------------------------------------------------------*/

    /// Notify the external propagator that backtrack to new_level.
    pub fn notify_backtrack(&mut self, new_level: usize) {
        if !self.external_prop || self.external_prop_is_lazy || self.private_steps {
            return;
        }
        debug_assert!(self.notified_level as usize > new_level);
        self.log_interaction_for("notify_backtrack", new_level as i32);
        self.ext_propagator().notify_backtrack(new_level);
        self.log_interaction_end_for("notify_backtrack", new_level as i32);
        self.notified_level = new_level as i32;
    }

    /*--------------------------------------------------------------------*/

    /// Ask the external propagator if there is a suggested literal as next
    /// decision.
    pub fn ask_decision(&mut self) -> i32 {
        if !self.external_prop || self.external_prop_is_lazy || self.private_steps {
            return 0;
        }

        debug_assert!(!self.unsat);
        debug_assert!(self.conflict.is_null());
        self.notify_assignments();
        let level_before = self.level;
        self.forced_backt_allowed = true;
        self.log_interaction_start("cb_decide");
        let elit = self.ext_propagator().cb_decide();
        self.log_interaction_return("cb_decide", elit);
        self.forced_backt_allowed = false;
        self.stats.ext_prop.ext_cb += 1;

        if level_before != self.level {
            self.propagate();
            debug_assert!(!self.unsat);
            debug_assert!(self.conflict.is_null());
            self.notify_assignments();

            // In case the external propagator forced to backtrack below the
            // pseduo decision levels, we must go back to the CDCL loop
            // instead of making a decision.
            if (self.level as usize) < self.assumptions.len()
                || (self.level as usize == self.assumptions.len() && !self.constraint.is_empty())
            {
                return 0;
            }
        }

        if elit == 0 {
            return 0;
        }
        log!(self, "external propagator proposes decision: {}", elit);

        cb_require!(
            self.externally_observed(elit),
            "cb_decide",
            elit,
            "external decisions are only allowed over observed variables."
        );

        debug_assert!(self.external().is_observed[elit.unsigned_abs() as usize]);

        let mut ilit = self.external().e2i[elit.unsigned_abs() as usize];
        if elit < 0 {
            ilit = -ilit;
        }

        debug_assert!(self.fixed(ilit) != 0 || self.observed(ilit));

        log!(
            self,
            "Asking external propagator for decision returned: {} (internal: {}, fixed: {}, val: {})",
            elit,
            ilit,
            self.fixed(ilit),
            self.val(ilit)
        );

        cb_require!(
            self.fixed(ilit) == 0 && self.val(ilit) == 0,
            "cb_decide",
            elit,
            "external decisions are only allowed over unassigned variables."
        );

        ilit
    }

    /*--------------------------------------------------------------------*/

    /// Check if the clause is a forgettable clause coming from the
    /// external propagator.
    pub fn is_external_forgettable(&mut self, id: i64) -> bool {
        debug_assert!(self.opts.check != 0);
        self.external().forgettable_original.contains_key(&(id as u64))
    }

    /// When an external forgettable clause is deleted, it is marked in the
    /// 'forgettable_original' hash, so that the internal model checking can
    /// ignore it.
    pub fn mark_garbage_external_forgettable(&mut self, id: i64) {
        debug_assert!(self.opts.check != 0);
        debug_assert!(self.is_external_forgettable(id));

        let key = id as u64;
        let lits = self.external().forgettable_original.entry(key).or_default();
        log!(self, &*lits, "forgettable external lemma is deleted:");
        // Mark as removed by flipping the first flag to false.
        lits[0] = 0;
    }

    /*--------------------------------------------------------------------*/

    /// Check that the literals in the clause are properly ordered. Used
    /// only internally for debug purposes.
    pub fn check_watched_literal_invariants(&mut self) {
        #[cfg(debug_assertions)]
        {
            let clause = &self.clause;
            let mut v0 = 0;
            let mut v1 = 0;

            if self.val(clause[0]) > 0 {
                v0 = 1;
            } else if self.val(clause[0]) < 0 {
                v0 = -1;
            }

            if self.val(clause[1]) > 0 {
                v1 = 1;
            } else if self.val(clause[1]) < 0 {
                v1 = -1;
            }
            debug_assert!(v0 >= v1);

            if self.val(clause[0]) > 0 {
                if self.val(clause[1]) > 0 {
                    // Case 1: Both literals are satisfied
                    // They are ordered by lower to higher decision level
                    debug_assert!(self.var(clause[0]).level <= self.var(clause[1]).level);

                    // Every other literal of the clause is either
                    //    - satisfied at higher level
                    //    - unassigned
                    //    - falsified
                    for i in 2..clause.len() {
                        debug_assert!(
                            self.val(clause[i]) <= 0
                                || (self.var(clause[1]).level <= self.var(clause[i]).level)
                        );
                    }
                } else if self.val(clause[1]) == 0 {
                    // Case 2: First satisfied, next unassigned

                    // Every other literal of the clause is either
                    //    - unassigned
                    //    - falsified
                    for i in 2..clause.len() {
                        debug_assert!(self.val(clause[i]) <= 0);
                    }
                } else {
                    // Case 3: First satisfied, next falsified -> could have
                    // been a reason of a previous propagation Every other
                    // literal of the clause is falsified but at a lower
                    // decision level
                    for i in 2..clause.len() {
                        debug_assert!(
                            self.val(clause[i]) < 0
                                && (self.var(clause[1]).level >= self.var(clause[i]).level)
                        );
                    }
                }
            } else if self.val(clause[0]) == 0 {
                if self.val(clause[1]) == 0 {
                    // Case 4: Both literals are unassigned

                    // Every other literal of the clause is either
                    //    - unassigned
                    //    - falsified
                    for i in 2..clause.len() {
                        debug_assert!(self.val(clause[i]) <= 0);
                    }
                } else {
                    // Case 5: First unassigned, next falsified -> PROPAGATE
                    // Every other literal of the clause is falsified but at
                    // a lower decision level
                    for i in 2..clause.len() {
                        debug_assert!(
                            self.val(clause[i]) < 0
                                && (self.var(clause[1]).level >= self.var(clause[i]).level)
                        );
                    }
                }
            } else {
                debug_assert!(self.val(clause[0]) < 0 && self.val(clause[1]) < 0); // Case 6: Both literals are falsified

                // They are ordered by higher to lower decision level
                debug_assert!(self.var(clause[0]).level >= self.var(clause[1]).level);

                // Every other literal of the clause is falsified, but at a
                // lower level
                for i in 2..clause.len() {
                    debug_assert!(
                        self.val(clause[i]) < 0
                            && (self.var(clause[1]).level >= self.var(clause[i]).level)
                    );
                }
            }
        }
    }

    /*--------------------------------------------------------------------*/

    /// An expensive function that can be used for deep-debug trail-related
    /// issues in mobical. Do not use it unless it is really unavoidable.
    ///
    /// eq_class contains all the merged external literals that are
    /// currently compacted to the internal literal of `trail[0]` and return
    /// true.
    ///
    /// In case `trail[0]` does not exists or is not on the root level, the
    /// function returns false (indicating that there was no merger literal
    /// found).
    ///
    /// (Only compiled with assertions in C++, available always here.)
    pub fn get_merged_literals(&mut self, eq_class: &mut Vec<i32>) -> bool {
        eq_class.clear();

        if self.trail.is_empty() {
            return false;
        }

        let ilit = self.trail[0];
        let lit_level = self.var(ilit).level as usize;

        if lit_level == 0 {
            // Collect all the variables that are merged and mapped to that
            // ilit
            let e2i_size = self.external().e2i.len();
            let ivar = ilit.abs();
            for i in 0..e2i_size {
                let e = self.external().e2i[i];
                let other = e.abs();
                if other == ivar {
                    if e == ilit {
                        eq_class.push(i as i32);
                    } else {
                        eq_class.push((i as i32).wrapping_neg());
                    }
                }
            }

            return true;
        }

        false
    }

    /// Collect all external variables that are FIXED internally. Again an
    /// expensive function that should be called only for debugging in
    /// mobical.
    ///
    /// Do not use it unless it is really unavoidable.
    ///
    /// (Only compiled with assertions in C++, available always here.)
    pub fn get_all_fixed_literals(&mut self, fixed_lits: &mut Vec<i32>) {
        fixed_lits.clear();
        if self.trail.is_empty() {
            return;
        }

        let e2i_size = self.external().e2i.len() as i32;
        for eidx in 1..e2i_size {
            let ilit = self.external().e2i[eidx as usize];
            if ilit != 0 && !self.external().ervars[eidx as usize] {
                if self.flags(ilit).status == Flags::FIXED {
                    fixed_lits.push(self.val(ilit.abs()) as i32 * eidx);
                }
            }
        }
    }
}

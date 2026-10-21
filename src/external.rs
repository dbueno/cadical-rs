//! Port of `external.hpp` (the `External` layer between `Solver` and
//! `Internal`: external to internal variable mapping, extension stack,
//! callbacks), the constructor from `external.cpp`, and `External::fixed`
//! (implemented in `internal.hpp` in C++).  All other functions of
//! `external.cpp` are at the end of this file.

use std::collections::HashMap;

use crate::internal::Internal;
use crate::range::Range;
use crate::solver::{ExternalPropagator, FixedAssignmentListener, Learner, Terminator};

pub struct External {
    /*==== start of state ================================================*/
    /// The actual internal solver.
    pub internal: *mut Internal,

    /// External maximum variable index.
    pub max_var: i32,
    /// Allocated external size.
    pub vsize: usize,

    /// Current external (extended) assignment.
    pub vals: Vec<bool>,
    /// External 'idx' to internal 'lit'.
    pub e2i: Vec<i32>,

    /// External assumptions.
    pub assumptions: Vec<i32>,
    /// External constraint.  Terminated by zero.
    pub constraint: Vec<i32>,

    /// External units.  Needed to compute LRAT for eclause.
    pub ext_units: Vec<i64>,
    /// To avoid duplicate units.
    pub ext_flags: Vec<bool>,

    /// External version of original input clause.
    pub eclause: Vec<i32>,

    /// Have been extended.
    pub extended: bool,
    pub concluded: bool,

    /// Solution reconstruction extension stack.
    pub extension: Vec<i32>,

    /// Literal witness on extension stack.
    pub witness: Vec<bool>,
    /// Literal tainted in adding literals.
    pub tainted: Vec<bool>,
    /// Variables added through Extended Resolution.
    pub ervars: Vec<bool>,

    /// Reference counts for frozen variables.
    pub frozentab: Vec<u32>,

    /// Regularly checked terminator if non-zero.  Owned (see
    /// `Solver::connect_terminator` / `disconnect_terminator`).
    pub terminator: Option<Box<dyn Terminator>>,

    /// If there is a learner export learned clauses.
    pub learner: Option<Box<dyn Learner>>,

    /// If there is a listener for fixed assignments.
    pub fixed_listener: Option<Box<dyn FixedAssignmentListener>>,

    /// If there is an external propagator.
    pub propagator: Option<Box<dyn ExternalPropagator>>,

    /// Only for user propagator interaction tracing.
    pub trace_api_file: *mut libc::FILE,

    /// Quick flag for each external variable.
    pub is_observed: Vec<bool>,

    /// Saved 'forgettable' original clauses coming from the external
    /// propagator.  The value starts with a Boolean flag indicating if the
    /// clause is still present or got already deleted, and then followed
    /// by the literals of the clause.  (Only iterated in checking code
    /// where the order does not matter.)
    pub forgettable_original: HashMap<u64, Vec<i32>>,

    /*--------------------------------------------------------------------*/
    /// Given solution checking for debugging (`signed char *solution`,
    /// `None` if not set).
    pub solution: Option<Vec<i8>>,
    /// Given solution checking for debugging.
    pub solution_size: i32,
    /// Saved original formula for checking.
    pub original: Vec<i32>,

    /// If 'opts.checkfrozen' is set make sure that only literals are added
    /// which were never completely molten before.
    pub moltentab: Vec<bool>,
    /*==== end of state ==================================================*/
}

impl External {
    /// `External (Internal *)`: also sets `internal->external`.  Boxed
    /// since `Internal` keeps a back pointer.
    pub fn new(internal: *mut Internal) -> Box<External> {
        debug_assert!(!internal.is_null());
        let mut external = Box::new(External {
            internal,
            max_var: 0,
            vsize: 0,
            vals: Vec::new(),
            e2i: Vec::new(),
            assumptions: Vec::new(),
            constraint: Vec::new(),
            ext_units: Vec::new(),
            ext_flags: Vec::new(),
            eclause: Vec::new(),
            extended: false,
            concluded: false,
            extension: Vec::new(),
            witness: Vec::new(),
            tainted: Vec::new(),
            ervars: Vec::new(),
            frozentab: Vec::new(),
            terminator: None,
            learner: None,
            fixed_listener: None,
            propagator: None,
            trace_api_file: std::ptr::null_mut(),
            is_observed: Vec::new(),
            forgettable_original: HashMap::new(),
            solution: None,
            solution_size: 0,
            original: Vec::new(),
            moltentab: Vec::new(),
        });
        // SAFETY: 'internal' is a live boxed 'Internal'.
        unsafe {
            debug_assert!((*internal).external.is_null());
            (*internal).external = &mut *external;
        }
        external
    }

    /// Back pointer to the `Internal` solver.
    #[inline(always)]
    #[allow(clippy::mut_from_ref)]
    pub fn internal(&self) -> &mut Internal {
        debug_assert!(!self.internal.is_null());
        // SAFETY: owned by the same 'Solver' at a stable address.
        unsafe { &mut *self.internal }
    }

    /// Provides safe variable iterations (`vars`).
    #[inline(always)]
    pub fn vars(&self) -> Range {
        Range::new(self.max_var)
    }

    /// These two just factor out common sanity (assertion) checking code.
    #[inline(always)]
    pub fn vidx(&self, elit: i32) -> i32 {
        debug_assert!(elit != 0);
        debug_assert!(elit != i32::MIN);
        let res = elit.abs();
        debug_assert!(res <= self.max_var);
        res
    }

    #[inline(always)]
    pub fn vlit(&self, elit: i32) -> i32 {
        debug_assert!(elit != 0);
        debug_assert!(elit != i32::MIN);
        debug_assert!(elit.abs() <= self.max_var);
        elit
    }

    #[inline]
    pub fn is_valid_input(&self, elit: i32) -> bool {
        debug_assert!(elit != 0);
        debug_assert!(elit != i32::MIN);
        let eidx = elit.abs();
        eidx > self.max_var || !self.ervars[eidx as usize]
    }

    /*--------------------------------------------------------------------*/

    // Marking external literals.

    #[inline]
    pub fn elit2ulit(&self, elit: i32) -> u32 {
        debug_assert!(elit != 0);
        debug_assert!(elit != i32::MIN);
        let idx = elit.abs() - 1;
        debug_assert!(idx <= self.max_var);
        2u32 * idx as u32 + (elit < 0) as u32
    }

    #[inline]
    pub fn marked(&self, map: &[bool], elit: i32) -> bool {
        let ulit = self.elit2ulit(elit) as usize;
        if ulit < map.len() {
            map[ulit]
        } else {
            false
        }
    }

    #[inline]
    pub fn mark(&self, map: &mut Vec<bool>, elit: i32) {
        let ulit = self.elit2ulit(elit) as usize;
        if ulit >= map.len() {
            map.resize(ulit + 1, false);
        }
        map[ulit] = true;
    }

    #[inline]
    pub fn unmark(&self, map: &mut [bool], elit: i32) {
        let ulit = self.elit2ulit(elit) as usize;
        if ulit < map.len() {
            map[ulit] = false;
        }
    }

    /*--------------------------------------------------------------------*/

    #[inline]
    pub fn frozen(&self, elit: i32) -> bool {
        debug_assert!(elit != 0);
        debug_assert!(elit != i32::MIN);
        let eidx = elit.abs();
        if eidx > self.max_var {
            return false;
        }
        if eidx as usize >= self.frozentab.len() {
            return false;
        }
        self.frozentab[eidx as usize] > 0
    }

    /// We call it 'ival' as abbreviation for 'val' with 'int' return type
    /// (IPASIR semantics: `ival (lit) == ival (-lit)`).
    #[inline]
    pub fn ival(&self, elit: i32) -> i32 {
        debug_assert!(elit != i32::MIN);
        let eidx = elit.abs();
        let mut val = false;
        if eidx <= self.max_var && (eidx as usize) < self.vals.len() {
            val = self.vals[eidx as usize];
        }
        if elit < 0 {
            val = !val;
        }
        if val {
            elit
        } else {
            -elit
        }
    }

    /// Implemented in 'internal.hpp' in C++.
    #[inline]
    pub fn fixed(&self, elit: i32) -> i32 {
        debug_assert!(elit != 0);
        debug_assert!(elit != i32::MIN);
        let eidx = elit.abs();
        if eidx > self.max_var {
            return 0;
        }
        let mut ilit = self.e2i[eidx as usize];
        if ilit == 0 {
            return 0;
        }
        if elit < 0 {
            ilit = -ilit;
        }
        self.internal().fixed(ilit)
    }

    /*--------------------------------------------------------------------*/

    #[inline]
    pub fn check_learned_empty_clause(&mut self) {
        if self.solution.is_some() {
            self.check_no_solution_after_learning_empty_clause();
        }
    }

    #[inline]
    pub fn check_learned_unit_clause(&mut self, unit: i32) {
        if self.solution.is_some() {
            self.check_solution_on_learned_unit_clause(unit);
        }
    }

    #[inline]
    pub fn check_learned_clause(&mut self) {
        if self.solution.is_some() {
            self.check_solution_on_learned_clause();
        }
    }

    #[inline]
    pub fn check_shrunken_clause(&mut self, c: crate::clause::CRef) {
        if self.solution.is_some() {
            self.check_solution_on_shrunken_clause(c);
        }
    }

    /// For debugging and testing only.  See 'solution.hpp' for more
    /// details.
    #[inline]
    pub fn sol(&self, elit: i32) -> i32 {
        let solution = self.solution.as_ref().expect("solution");
        debug_assert!(elit != i32::MIN);
        let eidx = elit.abs();
        if eidx > self.max_var {
            return 0;
        } else if eidx > self.solution_size {
            return elit;
        }
        let mut value = solution[eidx as usize];
        if value == 0 {
            return 0;
        }
        if elit < 0 {
            value = -value;
        }
        if value > 0 {
            elit
        } else {
            -elit
        }
    }
}

/*------------------------------------------------------------------------*/
// Port of the remaining functions of 'external.cpp'.

#[allow(unused_imports)]
use crate::prelude::*;

impl External {
    /// Back pointer to `Internal` with an unbounded lifetime, so that
    /// fields of `External` can be used together with the internal solver
    /// (as C++ does with 'internal->...').
    #[inline(always)]
    #[allow(clippy::mut_from_ref)]
    pub fn internal_unbound<'a>(&self) -> &'a mut Internal {
        debug_assert!(!self.internal.is_null());
        // SAFETY: see 'internal ()'.  'Internal' is a separate heap object.
        unsafe { &mut *self.internal }
    }

    pub fn enlarge(&mut self, new_max_var: i32) {
        debug_assert!(!self.extended);

        let mut new_vsize = if self.vsize != 0 { 2 * self.vsize } else { 1 + new_max_var as usize };
        while new_vsize <= new_max_var as usize {
            new_vsize *= 2;
        }
        log!(self, "enlarge external size from {} to new size {}", self.vsize, new_vsize);
        self.vsize = new_vsize;
    }

    /// `extension` defaults to `false` in C++
    pub fn init(&mut self, new_max_var: i32, extension: bool) {
        debug_assert!(!self.extended);
        if new_max_var <= self.max_var {
            return;
        }
        let internal = self.internal_unbound();
        let new_vars = new_max_var - self.max_var;
        let old_internal_max_var = internal.max_var;
        let new_internal_max_var = old_internal_max_var + new_vars;
        internal.init_vars(new_internal_max_var);
        if new_max_var as usize >= self.vsize {
            self.enlarge(new_max_var);
        }
        log!(self, "initialized {} external variables", new_vars);
        reserve_at_least(&mut self.ext_units, 2 * new_max_var as usize + 2);
        reserve_at_least(&mut self.e2i, new_max_var as usize + 1);
        reserve_at_least(&mut self.ervars, new_max_var as usize + 1);
        reserve_at_least(&mut self.ext_flags, new_max_var as usize + 1);
        reserve_at_least(&mut internal.i2e, new_max_var as usize + 1);
        if self.max_var == 0 {
            debug_assert!(self.e2i.is_empty());
            self.e2i.push(0);
            self.ext_units.push(0);
            self.ext_units.push(0);
            self.ext_flags.push(false);
            self.ervars.push(false);
            debug_assert!(internal.i2e.is_empty());
            internal.i2e.push(0);
        } else {
            debug_assert!(self.e2i.len() == self.max_var as usize + 1);
            debug_assert!(internal.i2e.len() == old_internal_max_var as usize + 1);
        }
        let mut iidx: u32 = (old_internal_max_var + 1) as u32;
        let mut eidx: u32 = self.max_var as u32 + 1;
        while eidx <= new_max_var as u32 {
            log!(self, "mapping external {} to internal {}", eidx, iidx);
            debug_assert!(self.e2i.len() == eidx as usize);
            self.e2i.push(iidx as i32);
            self.ext_units.push(0);
            self.ext_units.push(0);
            self.ext_flags.push(false);
            self.ervars.push(false);
            internal.i2e.push(eidx as i32);
            debug_assert!(internal.i2e[iidx as usize] == eidx as i32);
            debug_assert!(self.e2i[eidx as usize] == iidx as i32);
            eidx += 1;
            iidx += 1;
        }
        if extension {
            internal.stats.variables_extension += new_vars as i64;
        } else {
            internal.stats.variables_original += new_vars as i64;
        }
        if internal.opts.checkfrozen != 0 && new_max_var as i64 >= self.moltentab.len() as i64 {
            self.moltentab.resize(1 + new_max_var as usize, false);
        }
        debug_assert!(iidx as usize == new_internal_max_var as usize + 1);
        debug_assert!(eidx as usize == new_max_var as usize + 1);
        debug_assert!(self.ext_units.len() == new_max_var as usize * 2 + 2);
        self.max_var = new_max_var;
    }

    /*----------------------------------------------------------------------*/

    pub fn reset_assumptions(&mut self) {
        self.assumptions.clear();
        self.internal().reset_assumptions();
    }

    pub fn reset_concluded(&mut self) {
        self.concluded = false;
        self.internal().reset_concluded();
    }

    pub fn reset_constraint(&mut self) {
        self.constraint.clear();
        self.internal().reset_constraint();
    }

    pub fn reset_extended(&mut self) {
        if !self.extended {
            return;
        }
        log!(self, "reset extended");
        self.extended = false;
    }

    pub fn reset_limits(&mut self) {
        self.internal().reset_limits();
    }

    /*----------------------------------------------------------------------*/

    /// when extension is true, elit should be a fresh variable and we can
    /// set a flag that it is an extension variable.  This is then used in
    /// the API contracts, that extension variables are never part of the
    /// input
    ///
    /// `extension` defaults to `false` in C++
    pub fn internalize(&mut self, elit: i32, extension: bool) -> i32 {
        let mut ilit;
        if elit != 0 {
            debug_assert!(elit != i32::MIN);
            let eidx = elit.abs();
            if extension && eidx <= self.max_var {
                fatal!("can not add a definition for an already used variable {}", eidx);
            }
            if eidx > self.max_var {
                self.init(eidx, extension);
            }
            if extension {
                debug_assert!(self.ervars.len() > eidx as usize);
                self.ervars[eidx as usize] = true;
            }
            ilit = self.e2i[eidx as usize];
            if elit < 0 {
                ilit = -ilit;
            }
            let internal = self.internal_unbound();
            if ilit == 0 {
                debug_assert!(internal.max_var < i32::MAX);
                ilit = (internal.max_var as u32 + 1u32) as i32;
                internal.init_vars(ilit);
                self.e2i[eidx as usize] = ilit;
                log!(self, "mapping external {} to internal {}", eidx, ilit);
                self.e2i[eidx as usize] = ilit;
                internal.i2e.push(eidx);
                debug_assert!(internal.i2e[ilit as usize] == eidx);
                debug_assert!(self.e2i[eidx as usize] == ilit);
                if elit < 0 {
                    ilit = -ilit;
                }
            }
            if internal.opts.checkfrozen != 0 {
                debug_assert!((eidx as i64) < self.moltentab.len() as i64);
                if self.moltentab[eidx as usize] {
                    fatal!("can not reuse molten literal {}", eidx);
                }
            }
            let status = internal.flags(ilit).status;
            if status == Flags::UNUSED {
                internal.mark_active(ilit);
            } else if status != Flags::ACTIVE && status != Flags::FIXED {
                internal.reactivate(ilit);
            }
            if !self.marked(&self.tainted, elit) && self.marked(&self.witness, -elit) {
                debug_assert!(internal.opts.checkfrozen == 0);
                log!(self, "marking tainted {}", elit);
                let mut tainted = std::mem::take(&mut self.tainted);
                self.mark(&mut tainted, elit);
                self.tainted = tainted;
            }
        } else {
            ilit = 0;
        }
        ilit
    }

    pub fn add(&mut self, elit: i32) {
        debug_assert!(elit != i32::MIN);

        if elit != 0 {
            require!(
                "void CaDiCaL::External::add(int)",
                "../src/external.cpp",
                self.is_valid_input(elit),
                "extension variable '{}' defined by the solver internally (all user variables have to be declared explicitly if 'factor' is enabled)",
                elit.abs()
            );
        }
        self.reset_extended();

        let internal = self.internal_unbound();

        let mut forgettable = false;

        if internal.opts.check != 0 && (internal.opts.checkwitness != 0 || internal.opts.checkfailed != 0) {
            forgettable = internal.from_propagator && internal.ext_clause_forgettable;

            // Forgettable clauses (coming from the external propagator) are
            // not saved into the external 'original' stack. They are stored
            // separately in external 'forgettable_original', from where they
            // are deleted when the corresponding clause is deleted (actually
            // deleted, not just marked as garbage).
            if !forgettable {
                self.original.push(elit);
            }
        }

        let ilit = self.internalize(elit, false);
        debug_assert!((elit == 0) == (ilit == 0));

        // The external literals of the new clause must be saved for later
        // when the proof is printed during add_original_lit (0)
        if elit != 0 && (internal.proof.is_some() || forgettable) {
            self.eclause.push(elit);
            if internal.lrat {
                // actually find unit of -elit (flips elit < 0)
                let eidx = (elit > 0) as u32 + 2u32 * elit.unsigned_abs();
                debug_assert!((eidx as usize) < self.ext_units.len());
                let id = self.ext_units[eidx as usize];
                let added = self.ext_flags[elit.unsigned_abs() as usize];
                if id != 0 && !added {
                    self.ext_flags[elit.unsigned_abs() as usize] = true;
                    internal.lrat_chain.push(id);
                }
            }
        }

        if elit == 0 && internal.proof.is_some() && internal.lrat {
            for k in 0..self.eclause.len() {
                let elit = self.eclause[k];
                self.ext_flags[elit.unsigned_abs() as usize] = false;
            }
        }

        if elit != 0 {
            log!(self, "adding external {} as internal {}", elit, ilit);
        }
        internal.add_original_lit(ilit);

        // Clean-up saved external literals once proof line is printed
        if elit == 0 && (internal.proof.is_some() || forgettable) {
            self.eclause.clear();
        }
    }

    pub fn assume(&mut self, elit: i32) {
        debug_assert!(elit != 0);
        self.reset_extended();
        let internal = self.internal_unbound();
        if let Some(proof) = internal.proof.as_mut() {
            proof.add_assumption(elit);
        }
        self.assumptions.push(elit);
        let ilit = self.internalize(elit, false);
        debug_assert!(ilit != 0);
        log!(self, "assuming external {} as internal {}", elit, ilit);
        internal.assume(ilit);
    }

    pub fn flip(&mut self, elit: i32) -> bool {
        debug_assert!(elit != 0);
        debug_assert!(elit != i32::MIN);
        debug_assert!(self.propagator.is_none());

        let eidx = elit.abs();
        if eidx > self.max_var {
            return false;
        }
        if self.marked(&self.witness, elit) {
            return false;
        }
        let ilit = self.e2i[eidx as usize];
        if ilit == 0 {
            return false;
        }
        let res = self.internal().flip(ilit);
        if res && self.extended {
            self.reset_extended();
        }
        res
    }

    pub fn flippable(&mut self, elit: i32) -> bool {
        debug_assert!(elit != 0);
        debug_assert!(elit != i32::MIN);
        debug_assert!(self.propagator.is_none());

        let eidx = elit.abs();
        if eidx > self.max_var {
            return false;
        }
        if self.marked(&self.witness, elit) {
            return false;
        }
        let ilit = self.e2i[eidx as usize];
        if ilit == 0 {
            return false;
        }
        self.internal().flippable(ilit)
    }

    pub fn failed(&mut self, elit: i32) -> bool {
        debug_assert!(elit != 0);
        debug_assert!(elit != i32::MIN);
        let eidx = elit.abs();
        if eidx > self.max_var {
            return false;
        }
        let mut ilit = self.e2i[eidx as usize];
        if ilit == 0 {
            return false;
        }
        if elit < 0 {
            ilit = -ilit;
        }
        self.internal().failed(ilit)
    }

    pub fn constrain(&mut self, elit: i32) {
        if !self.constraint.is_empty() && *self.constraint.last().unwrap() == 0 {
            log!(self, &self.constraint, "replacing previous constraint");
            self.reset_constraint();
        }
        debug_assert!(elit != i32::MIN);
        self.reset_extended();
        let ilit = self.internalize(elit, false);
        debug_assert!((elit == 0) == (ilit == 0));
        let internal = self.internal_unbound();
        if elit != 0 {
            log!(self, "adding external {} as internal {} to constraint", elit, ilit);
        } else if let Some(proof) = internal.proof.as_mut() {
            proof.add_constraint(&self.constraint);
        }
        self.constraint.push(elit);
        internal.constrain(ilit);
    }

    pub fn failed_constraint(&mut self) -> bool {
        self.internal().failed_constraint()
    }

    pub fn phase(&mut self, elit: i32) {
        debug_assert!(elit != 0);
        debug_assert!(elit != i32::MIN);
        let ilit = self.internalize(elit, false);
        self.internal().phase(ilit);
    }

    pub fn unphase(&mut self, elit: i32) {
        debug_assert!(elit != 0);
        debug_assert!(elit != i32::MIN);
        let eidx = elit.abs();
        if eidx > self.max_var {
            log!(self, "resetting forced phase of unused external {} ignored", elit);
            return;
        }
        let mut ilit = self.e2i[eidx as usize];
        if ilit == 0 {
            log!(self, "resetting forced phase of unused external {} ignored", elit);
            return;
        }
        if elit < 0 {
            ilit = -ilit;
        }
        self.internal().unphase(ilit);
    }

    /*----------------------------------------------------------------------*/

    // External propagation related functions
    //
    // Note that when an already assigned variable is added as observed, the
    // solver will backtrack to undo this assignment.
    //
    pub fn add_observed_var(&mut self, elit: i32) {
        debug_assert!(self.propagator.is_some()); // REQ is in Solver::add_observed_var

        debug_assert!(elit != 0);
        debug_assert!(elit != i32::MIN);
        self.reset_extended(); // tainting!

        let eidx = elit.abs();

        require!(
            "void CaDiCaL::External::add_observed_var(int)",
            "../src/external.cpp",
            eidx > self.max_var || (!self.marked(&self.witness, elit) && !self.marked(&self.witness, -elit)),
            "Only clean variables are allowed to be observed."
        );
        // if (eidx <= max_var &&
        //     (marked (witness, elit) || marked (witness, -elit))) {
        //   LOG ("Error, only clean variables are allowed to become
        //   observed."); assert (false);

        //   // TODO: here needs to come the taint and restore of the newly
        //   // observed variable. Restore_clauses must be called before
        //   // continue.
        //   // LOG ("marking tainted %d", elit);
        //   // mark (tainted, elit);
        //   // mark (tainted, -elit);
        //   // restore_clauses ...
        // }

        if eidx as i64 >= self.is_observed.len() as i64 {
            self.is_observed.resize(1 + eidx as usize, false);
        }

        if self.is_observed[eidx as usize] {
            return;
        }

        log!(self, "marking {} as externally watched", eidx);

        // Will do the necessary internalization
        self.freeze(elit);
        self.is_observed[eidx as usize] = true;

        let ilit = self.internalize(elit, false);
        // internal add-observed-var backtracks to a lower decision level to
        // unassign the variable in case it was already assigned previously
        // (but not on the current level)
        self.internal().add_observed_var(ilit);

        if self.propagator.as_ref().unwrap().is_lazy() {
            return;
        }

        // In case this variable was already assigned (e.g. via unit clause)
        // and got compacted to map to another (not observed) variable, it
        // can not be unnasigned so it must be notified explicitly now. (->
        // Can lead to repeated fixed assignment notifications, in case it
        // was unobserved and observed again. But a repeated notification is
        // less error-prone than never notifying an assignment.)
        let tmp = self.fixed(elit);
        if tmp == 0 {
            return;
        }
        let unit = if tmp < 0 { -elit } else { elit };

        log!(self, "notify propagator about fixed assignment upon observe for {}", unit);

        // internal add-observed-var had to backtrack to root-level already
        debug_assert!(self.internal().level == 0);

        let assigned: Vec<i32> = vec![unit];
        self.propagator.as_mut().unwrap().notify_assignment(&assigned);
    }

    // A variable weakened by variable elimination (or any other technique which
    // pushes witness literals on the extension stack) can not be observed right
    // away: the external propagator would see assignments of a variable which is
    // not fully constrained by the clauses currently in the solver, since some of
    // its clauses only live on the extension stack.
    //
    // Tainting both phases forces 'restore_clauses' to restore every weakened
    // clause which has this variable as witness literal, after which the variable
    // is clean and may be observed.  This implements the 'TODO' in
    // 'add_observed_var' above.
    //
    // Restoring requires root level, therefore 'Solver::add_observed_var' only
    // calls this when not solving.
    #[cfg(feature = "bitwuzla")]
    pub fn restore_before_observing(&mut self, elit: i32) {
        debug_assert!(self.propagator.is_some()); // REQ is in Solver::add_observed_var
        debug_assert!(elit != 0);
        debug_assert!(elit != i32::MIN);

        let eidx = elit.abs();
        if eidx > self.max_var {
            return;
        }
        if !self.marked(&self.witness, elit) && !self.marked(&self.witness, -elit) {
            return;
        }

        log!(self, "restoring clauses of weakened variable {} before observing it", eidx);
        self.reset_extended(); // tainting!

        if self.internal().level != 0 {
            self.internal().backtrack(0);
        }

        // 'internalize' taints a literal if its negation occurs as witness literal
        // on the extension stack, and reactivates it if necessary.  Internalizing
        // both phases therefore taints exactly the phases needed to restore all
        // clauses witnessed by this variable.
        self.internalize(elit, false);
        self.internalize(-elit, false);

        let _ = self.internal().restore_clauses();

        debug_assert!(!self.marked(&self.witness, elit) && !self.marked(&self.witness, -elit));
    }

    pub fn remove_observed_var(&mut self, elit: i32) {
        debug_assert!(self.propagator.is_some()); // REQ is in Solver::remove_observed_var

        let eidx = elit.abs();

        if eidx > self.max_var {
            // Ignore call if variable does not exist
            return;
        }

        // Ignore call if variable is not observed
        if eidx as usize >= self.is_observed.len() {
            return;
        }
        if self.is_observed[eidx as usize] {
            // Follow opposite order of add_observed_var, first remove
            // internal is_observed
            let ilit = self.e2i[eidx as usize]; // internalize (elit);
            self.internal().remove_observed_var(ilit);

            self.is_observed[eidx as usize] = false;
            self.melt(elit);
            log!(self, "unmarking {} as externally watched", eidx);
        }
    }

    pub fn reset_observed_vars(&mut self) {
        // Shouldn't be called if there is no connected propagator
        debug_assert!(self.propagator.is_some()); // REQ is in Solver::reset_observed_vars
        self.reset_extended();

        self.internal().notified = 0;
        log!(self, "reset notified counter to 0");

        if self.is_observed.is_empty() {
            return;
        }

        for elit in self.vars() {
            let eidx = elit.abs();
            debug_assert!(eidx <= self.max_var);
            if eidx as usize >= self.is_observed.len() {
                break;
            }
            if self.is_observed[eidx as usize] {
                let ilit = self.internalize(elit, false);
                self.internal().remove_observed_var(ilit);
                log!(self, "unmarking {} as externally watched", eidx);
                self.is_observed[eidx as usize] = false;
                self.melt(elit);
            }
        }
    }

    pub fn observed(&mut self, elit: i32) -> bool {
        debug_assert!(elit != 0);
        debug_assert!(elit != i32::MIN);
        let eidx = elit.abs();
        if eidx > self.max_var {
            return false;
        }
        if eidx >= self.is_observed.len() as i32 {
            return false;
        }

        self.is_observed[eidx as usize]
    }

    pub fn is_witness(&mut self, elit: i32) -> bool {
        debug_assert!(elit != 0);
        debug_assert!(elit != i32::MIN);
        let eidx = elit.abs();
        if eidx > self.max_var {
            return false;
        }
        self.marked(&self.witness, elit) || self.marked(&self.witness, -elit)
    }

    pub fn is_decision(&mut self, elit: i32) -> bool {
        debug_assert!(elit != 0);
        debug_assert!(elit != i32::MIN);
        let eidx = elit.abs();
        if eidx > self.max_var {
            return false;
        }

        let ilit = self.internalize(elit, false);
        self.internal().is_decision(ilit)
    }

    pub fn force_backtrack(&mut self, new_level: i32) {
        debug_assert!(self.propagator.is_some()); // REQ is is in Solver::force_backtrack

        log!(self, "force backtrack to level {}", new_level);
        self.internal().force_backtrack(new_level);
    }

    /*----------------------------------------------------------------------*/

    pub fn propagate_assumptions(&mut self) -> i32 {
        let res = self.internal().propagate_assumptions();
        if res == 10 && !self.extended {
            self.extend(); // Call solution reconstruction
        }
        self.check_solve_result(res);
        self.reset_limits();
        res
    }

    pub fn implied(&mut self, trailed: &mut Vec<i32>) {
        let mut ilit_implicants: Vec<i32> = Vec::new();
        self.internal().implied(&mut ilit_implicants);

        // Those implied literals must be filtered out that are witnesses on
        // the reconstruction stack -> no inplace externalize is possible.
        // (Internal does not see these marks, so no earlier filter is
        // possible.)

        trailed.clear();

        for &ilit in ilit_implicants.iter() {
            debug_assert!(ilit != 0);
            let elit = self.internal().externalize(ilit);
            let eidx = elit.abs();
            let is_extension_var = self.ervars[eidx as usize];
            if !self.marked(&self.tainted, elit) && !is_extension_var {
                trailed.push(elit);
            }
        }
    }

    pub fn conclude_unknown(&mut self) {
        if self.internal().proof.is_none() || self.concluded {
            return;
        }
        self.concluded = true;

        let mut trail: Vec<i32> = Vec::new();
        self.implied(&mut trail);
        self.internal().proof.as_mut().unwrap().conclude_unknown(&trail);
    }

    /*----------------------------------------------------------------------*/

    /// Internal checker if 'solve' claims the formula to be satisfiable.
    pub fn check_satisfiable(&mut self) {
        log!(self, "checking satisfiable");
        if !self.extended {
            self.extend();
        }
        if self.internal().opts.checkwitness != 0 {
            self.check_assignment(External::ival);
        }
        if self.internal().opts.checkassumptions != 0 && !self.assumptions.is_empty() {
            self.check_assumptions_satisfied();
        }
        if self.internal().opts.checkconstraint != 0 && !self.constraint.is_empty() {
            self.check_constraint_satisfied();
        }
    }

    /// Internal checker if 'solve' claims formula to be unsatisfiable.
    pub fn check_unsatisfiable(&mut self) {
        log!(self, "checking unsatisfiable");
        if self.internal().opts.checkfailed == 0 {
            return;
        }
        if !self.assumptions.is_empty() || !self.constraint.is_empty() {
            self.check_failing();
        }
    }

    /// Check result of 'solve' to be correct.
    pub fn check_solve_result(&mut self, res: i32) {
        if self.internal().opts.check == 0 {
            return;
        }
        if res == 10 {
            self.check_satisfiable();
        }
        if res == 20 {
            self.check_unsatisfiable();
        }
    }

    /// Prepare checking that completely molten literals are not used as
    /// argument of 'add' or 'assume', which is invalid under freezing
    /// semantics.  This case would be caught by our 'restore'
    /// implementation so is only needed for checking the deprecated
    /// 'freeze' semantics.
    pub fn update_molten_literals(&mut self) {
        if self.internal().opts.checkfrozen == 0 {
            return;
        }
        debug_assert!(self.max_var as usize + 1 == self.moltentab.len());
        #[cfg(feature = "logging")]
        let mut registered: i32 = 0;
        #[cfg(feature = "logging")]
        let mut molten: i32 = 0;
        for lit in self.vars() {
            if self.moltentab[lit as usize] {
                log!(self, "skipping already molten literal {}", lit);
                #[cfg(feature = "logging")]
                {
                    molten += 1;
                }
            } else if self.frozen(lit) {
                log!(self, "skipping currently frozen literal {}", lit);
            } else {
                log!(self, "new molten literal {}", lit);
                self.moltentab[lit as usize] = true;
                #[cfg(feature = "logging")]
                {
                    registered += 1;
                    molten += 1;
                }
            }
        }
        log!(self, "registered {} new molten literals", registered);
        log!(self, "reached in total {} molten literals", molten);
    }

    pub fn solve(&mut self, preprocess_only: bool) -> i32 {
        self.reset_extended();
        self.update_molten_literals();
        let res = self.internal().solve(preprocess_only);
        self.check_solve_result(res);
        self.reset_limits();
        res
    }

    pub fn terminate(&mut self) {
        self.internal().terminate();
    }

    pub fn lookahead(&mut self) -> i32 {
        self.reset_extended();
        self.update_molten_literals();
        let ilit = self.internal().lookahead();
        let elit = if ilit != 0 && ilit != i32::MIN { self.internal().externalize(ilit) } else { 0 };
        log!(self, "lookahead internal {} external {}", ilit, elit);
        elit
    }

    /// `min_depth` defaults to `0` in C++.
    pub fn generate_cubes(&mut self, depth: i32, min_depth: i32) -> CubesWithStatus {
        self.reset_extended();
        self.update_molten_literals();
        self.reset_limits();
        let cubes = self.internal().generate_cubes(depth, min_depth);
        // The C++ code maps 'externalize' over copies of the cubes (thus
        // only printing messages and not changing the returned cubes).
        for cube in cubes.cubes.iter() {
            msg!(self, "Cube : ");
            for &ilit in cube.iter() {
                let elit = if ilit != 0 { self.internal().externalize(ilit) } else { 0 };
                msg!(self, "lookahead internal {} external {}", ilit, elit);
            }
        }

        cubes
    }

    /*----------------------------------------------------------------------*/

    pub fn freeze(&mut self, elit: i32) {
        self.reset_extended();
        let ilit = self.internalize(elit, false);
        let eidx = self.vidx(elit) as u32;
        if eidx as usize >= self.frozentab.len() {
            self.frozentab.resize(eidx as usize + 1, 0);
        }
        let r = &mut self.frozentab[eidx as usize];
        if *r < u32::MAX {
            *r += 1;
            log!(
                self,
                "external variable {} frozen once and now frozen {} times",
                eidx,
                self.frozentab[eidx as usize]
            );
        } else {
            log!(self, "external variable {} frozen but remains frozen forever", eidx);
        }
        self.internal().freeze(ilit);
    }

    pub fn melt(&mut self, elit: i32) {
        self.reset_extended();
        let ilit = self.internalize(elit, false);
        let eidx = self.vidx(elit) as u32;
        debug_assert!((eidx as usize) < self.frozentab.len());
        let r = self.frozentab[eidx as usize];
        debug_assert!(r > 0);
        if r < u32::MAX {
            self.frozentab[eidx as usize] = r - 1;
            if self.frozentab[eidx as usize] == 0 {
                if self.observed(elit) {
                    self.frozentab[eidx as usize] += 1;
                    log!(self, "external variable {} is observed, can not be completely molten", eidx);
                } else {
                    log!(self, "external variable {} melted once and now completely melted", eidx);
                }
            } else {
                log!(
                    self,
                    "external variable {} melted once but remains frozen {} times",
                    eidx,
                    self.frozentab[eidx as usize]
                );
            }
        } else {
            log!(self, "external variable {} melted but remains frozen forever", eidx);
        }
        self.internal().melt(ilit);
    }

    /*----------------------------------------------------------------------*/

    /// C++ takes the member function pointer `int (External::*) (int) const`.
    pub fn check_assignment(&mut self, a: fn(&External, i32) -> i32) {
        // First check all assigned and consistent.
        //
        for idx in self.vars() {
            if a(self, idx) == 0 {
                fatal!("unassigned variable: {}", idx);
            }
            let value_idx = a(self, idx);
            let value_neg_idx = a(self, -idx);
            if value_idx == idx {
                debug_assert!(value_neg_idx == idx);
            } else {
                debug_assert!(value_idx == -idx);
                debug_assert!(value_neg_idx == -idx);
            }
            if value_idx != value_neg_idx {
                fatal!("inconsistently assigned literals {} and {}", idx, -idx);
            }
        }

        // Then check that all (saved) original clauses are satisfied.
        //
        let mut satisfied = false;
        let end = self.original.len();
        let mut start = 0;
        let mut count: i64 = 0;
        for i in 0..end {
            let lit = self.original[i];
            if lit == 0 {
                if !satisfied {
                    crate::message::fatal_message_start();
                    crate::message::fputs("unsatisfied clause:\n", crate::message::c_stderr());
                    for j in start..i {
                        cfprintf!(crate::message::c_stderr(), "{} ", self.original[j]);
                    }
                    crate::message::fputc(b'0' as i32, crate::message::c_stderr());
                    crate::message::fatal_message_end();
                }
                satisfied = false;
                start = i + 1;
                count += 1;
            } else if !satisfied && a(self, lit) == lit {
                satisfied = true;
            }
        }

        let mut presence_flag;
        // Check those forgettable external clauses that are still present,
        // but only if the external propagator is still connected (otherwise
        // solution reconstruction is allowed to touch the previously
        // observed variables so there is no guarantee that the final model
        // will satisfy these clauses.)
        for (_, forgettables) in self.forgettable_original.iter() {
            if self.propagator.is_none() {
                break;
            }
            presence_flag = true;
            satisfied = false;
            count += 1;
            for &lit in forgettables.iter() {
                if presence_flag {
                    // First integer is a Boolean flag, not a literal
                    if lit == 0 {
                        // Deleted clauses can be ignored, they count as
                        // satisfied
                        satisfied = true;
                        break;
                    }
                    presence_flag = false;
                    continue;
                }

                if a(self, lit) == lit {
                    satisfied = true;
                    break;
                }
            }

            if !satisfied {
                crate::message::fatal_message_start();
                crate::message::fputs("unsatisfied external forgettable clause:\n", crate::message::c_stderr());
                for j in 1..forgettables.len() {
                    cfprintf!(crate::message::c_stderr(), "{} ", forgettables[j]);
                }
                crate::message::fputc(b'0' as i32, crate::message::c_stderr());
                crate::message::fatal_message_end();
            }
        }
        verbose!(self, 1, "satisfying assignment checked on {} clauses", count);
        let _ = count;
    }

    /*----------------------------------------------------------------------*/

    pub fn check_assumptions_satisfied(&mut self) {
        for &lit in self.assumptions.iter() {
            // Not 'signed char' !!!!
            let tmp = self.ival(lit);
            if tmp != lit {
                fatal!("assumption {} falsified", lit);
            }
            if tmp == 0 {
                fatal!("assumption {} unassigned", lit);
            }
        }
        verbose!(self, 1, "checked that {} assumptions are satisfied", self.assumptions.len());
    }

    pub fn check_constraint_satisfied(&mut self) {
        for &lit in self.constraint.iter() {
            if self.ival(lit) == lit {
                verbose!(self, 1, "checked that constraint is satisfied");
                return;
            }
        }
        fatal!("constraint not satisfied");
    }

    pub fn check_failing(&mut self) {
        let mut checker = Box::new(Solver::new());
        // C++ shares the terminator pointer with the checker.  Here the
        // (owned) terminator is lent to the checker and given back after
        // solving.
        if let Some(t) = self.terminator.take() {
            checker.connect_terminator(t);
        }
        checker.prefix("checker ");
        #[cfg(feature = "logging")]
        if self.internal().opts.log != 0 {
            checker.set("log", 1);
        }
        checker.set("factorcheck", 0);

        for k in 0..self.assumptions.len() {
            let lit = self.assumptions[k];
            if !self.failed(lit) {
                continue;
            }
            log!(self, "checking failed literal {} in core", lit);
            checker.add(lit);
            checker.add(0);
        }
        if self.failed_constraint() {
            log!(self, &self.constraint, "checking failed constraint");
            for &lit in self.constraint.iter() {
                checker.add(lit);
            }
        } else if !self.constraint.is_empty() {
            log!(self, &self.constraint, "constraint satisfied and ignored");
        }

        // Add original clauses as last step, failing () and
        // failed_constraint () might add more external clauses (due to lazy
        // explanation)
        for &lit in self.original.iter() {
            checker.add(lit);
        }

        // Add every forgettable external clauses
        for (_, forgettables) in self.forgettable_original.iter() {
            let mut presence_flag = true;
            for &lit in forgettables.iter() {
                if presence_flag {
                    // First integer is a Boolean flag, not a literal, ignore
                    // it here
                    presence_flag = false;
                    continue;
                }
                checker.add(lit);
            }
            checker.add(0);
        }

        let res = checker.solve();
        if let Some(t) = checker.disconnect_terminator() {
            self.terminator = Some(t);
        }
        if res != 20 {
            fatal!("failed assumptions do not form a core");
        }
        drop(checker);
        verbose!(self, 1, "checked that {} failing assumptions form a core", self.assumptions.len());
    }

    /*----------------------------------------------------------------------*/

    // Traversal of unit clauses is implemented here.
    //
    // See the long comment in 'external.cpp' on why frozen and non-frozen
    // units are distinguished during clause traversal.

    pub fn traverse_all_frozen_units_as_clauses(&mut self, it: &mut dyn ClauseIterator) -> bool {
        if self.internal().unsat {
            return true;
        }

        let mut clause: Vec<i32> = Vec::new();

        for idx in self.vars() {
            if !self.frozen(idx) {
                continue;
            }
            let tmp = self.fixed(idx);
            if tmp == 0 {
                continue;
            }
            let unit = if tmp < 0 { -idx } else { idx };
            clause.push(unit);
            if !it.clause(&clause) {
                return false;
            }
            clause.clear();
        }

        true
    }

    pub fn traverse_all_non_frozen_units_as_witnesses(&mut self, it: &mut dyn WitnessIterator) -> bool {
        if self.internal().unsat {
            return true;
        }

        let mut clause_and_witness: Vec<i32> = Vec::new();
        for idx in self.vars() {
            if self.frozen(idx) {
                continue;
            }
            let tmp = self.fixed(idx);
            if tmp == 0 {
                continue;
            }
            let unit = if tmp < 0 { -idx } else { idx };
            let ilit = self.e2i[idx as usize] * if tmp < 0 { -1 } else { 1 };
            // heurstically add + max_var to the id to avoid reusing ids
            let id: i64 = if self.internal().lrat { self.internal().unit_id(ilit) } else { 1 };
            debug_assert!(id != 0);
            clause_and_witness.push(unit);
            if !it.witness(&clause_and_witness, &clause_and_witness, id + self.max_var as i64) {
                return false;
            }
            clause_and_witness.clear();
        }

        true
    }

    /*----------------------------------------------------------------------*/

    pub fn copy_flags(&self, other: &mut External) {
        let this_internal = self.internal_unbound();
        let other_internal = other.internal_unbound();
        let limit = self.max_var.min(other.max_var) as u32;
        let mut eidx: u32 = 1;
        while eidx <= limit {
            let this_ilit = self.e2i[eidx as usize];
            if this_ilit == 0 {
                eidx += 1;
                continue;
            }
            let other_ilit = other.e2i[eidx as usize];
            if other_ilit == 0 {
                eidx += 1;
                continue;
            }
            if !this_internal.active(this_ilit) {
                eidx += 1;
                continue;
            }
            if !other_internal.active(other_ilit) {
                eidx += 1;
                continue;
            }
            debug_assert!(this_ilit != i32::MIN);
            debug_assert!(other_ilit != i32::MIN);
            let this_flags = &this_internal.ftab[this_ilit.unsigned_abs() as usize];
            let other_flags = &mut other_internal.ftab[other_ilit.unsigned_abs() as usize];
            this_flags.copy(other_flags);
            eidx += 1;
        }
    }

    /*----------------------------------------------------------------------*/

    pub fn export_learned_empty_clause(&mut self) {
        debug_assert!(self.learner.is_some());
        let learner = self.learner.as_mut().unwrap();
        if learner.learning(0) {
            log!(self, "exporting learned empty clause");
            self.learner.as_mut().unwrap().learn(0);
        } else {
            log!(self, "not exporting learned empty clause");
        }
    }

    pub fn export_learned_unit_clause(&mut self, ilit: i32) {
        debug_assert!(self.learner.is_some());
        if self.learner.as_mut().unwrap().learning(1) {
            log!(self, "exporting learned unit clause");
            let elit = self.internal().externalize(ilit);
            debug_assert!(elit != 0);
            let learner = self.learner.as_mut().unwrap();
            learner.learn(elit);
            learner.learn(0);
        } else {
            log!(self, "not exporting learned unit clause");
        }
    }

    pub fn export_learned_large_clause(&mut self, clause: &[i32]) {
        debug_assert!(self.learner.is_some());
        let size = clause.len();
        debug_assert!(size <= i32::MAX as usize);
        if self.learner.as_mut().unwrap().learning(size as i32) {
            log!(self, "exporting learned clause of size {}", size);
            let internal = self.internal_unbound();
            for &ilit in clause.iter() {
                let elit = internal.externalize(ilit);
                debug_assert!(elit != 0);
                self.learner.as_mut().unwrap().learn(elit);
            }
            self.learner.as_mut().unwrap().learn(0);
        } else {
            log!(self, "not exporting learned clause of size {}", size);
        }
    }
}

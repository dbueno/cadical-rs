//! Port of `cadical/test/api/example_propagators.cpp`.
//!
//! Some example implementations of the `ExternalPropagator` trait.  In
//! these examples we solve pigeonhole-type SAT problems by assigning
//! exactly `p_limit` pigeons to `n` holes, such that each hole contains at
//! most one pigeon and each pigeon belongs to exactly one hole.  If
//! `p_limit > n`, the problem is UNSAT; if `p_limit <= n`, it is SAT.
//! See the C++ file for the (long) explanations of the IPASIR-UP
//! interface, which are kept here in abbreviated form.
//!
//! Porting notes (see also the API notes in the test report):
//!
//! * In C++ the propagator objects keep a `Solver *` and call back into
//!   the solver from within call-backs (`force_backtrack` in
//!   `cb_check_found_model`, `add_observed_var` in `cb_propagate`), which
//!   in turn re-enter the propagator (`notify_backtrack`).  The Rust API
//!   has no safe way to do this: the solver owns the propagator as a
//!   `Box<dyn ExternalPropagator>` and is itself mutably borrowed while
//!   calling it.  We mirror the C++ code with a raw `*mut Solver` (the
//!   solver lives in a `Box` whose address never changes) and make sure the
//!   propagator does not touch its own state after calling into the solver.
//! * The C++ constructor / destructor connect / disconnect the propagator.
//!   Here the user facing objects (`ObserverPropagator`,
//!   `ActivePropagator`) are guards whose `new` connects a freshly boxed
//!   propagator implementation and whose `Drop` disconnects it.
//! * State that the constructor sets after connecting (in C++ via `this`)
//!   is shared through `Rc<Cell<..>>`.

mod common;
use common::{out, outln};

use cadical::{ExternalPropagator, FixedAssignmentListener, Solver};
use std::cell::Cell;
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;
use std::sync::atomic::{AtomicI32, Ordering::Relaxed};

const N: i32 = 3;
static P_LIMIT: AtomicI32 = AtomicI32::new(N);

fn p_limit() -> i32 {
    P_LIMIT.load(Relaxed)
}

fn ph(p: i32, h: i32) -> i32 {
    assert!(0 <= p);
    assert!(p < p_limit());
    assert!(0 <= h);
    assert!(h < N);
    p * N + h + 1
}

fn p_id(lit: i32) -> i32 {
    (lit.abs() - 1) / N
}

fn h_id(lit: i32) -> i32 {
    (lit.abs() - 1) % N
}

fn formula(solver: &mut Solver) {
    // At most one pigeon per hole
    for h in 0..N {
        for p1 in 0..p_limit() {
            for p2 in p1 + 1..p_limit() {
                solver.add(-ph(p1, h));
                solver.add(-ph(p2, h));
                solver.add(0);
            }
        }
    }

    // At least one hole per pigeon
    for p in 0..p_limit() {
        for h in 0..N {
            solver.add(ph(p, h));
        }
        solver.add(0);
    }
}

fn partial_formula(solver: &mut Solver) {
    // At least one hole per pigeon
    for p in 0..p_limit() {
        for h in 0..N {
            solver.add(ph(p, h));
        }
        solver.add(0);
    }

    // In this encoding the at most one pigeon per hole constraints will be
    // checked and enforced dynamically in the external propagator
    // (see ActivePropagator).
}

/// Short-lived mutable reference to the solver behind a raw pointer (the
/// C++ `solver->...`).
macro_rules! solver {
    ($p:expr) => {
        // SAFETY: the solver is boxed in the example functions and outlives
        // the propagator (see the module comment on re-entrancy).
        unsafe { &mut *$p }
    };
}

/*----------------------------------------------------------------------------*/
//
// ObserverPropagator:
//
// A very simple ExternalPropagator that only reports the called IPASIR-UP
// functions with their arguments, without any actual interactions with the
// solver.

struct ObserverShared {
    // Used to demonstrate forced backtrack
    first_model: Cell<bool>,
    // Used to show add_observed_var during cb_propagate
    propagation_count: Cell<usize>,
    non_observed_lit: Cell<i32>,
    fixed_lit: Cell<i32>,
}

/// The actual `ExternalPropagator` (owned by the solver).
struct ObserverImpl {
    solver: *mut Solver,
    shared: Rc<ObserverShared>,
}

/// The `FixedAssignmentListener` part of the C++ `ObserverPropagator` (in
/// Rust a second object, since the solver owns each connected call-back).
struct ObserverFixedListener;

/// User facing object (C++ `ObserverPropagator`): connects in `new` and
/// disconnects in `Drop`.
struct ObserverPropagator {
    solver: *mut Solver,
    #[allow(dead_code)]
    shared: Rc<ObserverShared>,
}

impl ObserverPropagator {
    fn new(solver: *mut Solver) -> ObserverPropagator {
        let shared = Rc::new(ObserverShared {
            first_model: Cell::new(true),
            propagation_count: Cell::new(0),
            non_observed_lit: Cell::new(0),
            fixed_lit: Cell::new(0),
        });

        // 'is_lazy' and 'are_reasons_forgettable' are 'false' (default
        // trait methods).

        // Fatal error: can not observe variables without a connected
        // propagator
        // solver!(solver).add_observed_var(1);

        solver!(solver).connect_external_propagator(Box::new(ObserverImpl { solver, shared: shared.clone() }));

        // It is recommended to connect the FixedAssignmentListener before
        // the formula is given to the solver.
        solver!(solver).connect_fixed_listener(Box::new(ObserverFixedListener));

        // Fatal error: can not connect more than one propagator
        // solver!(solver).connect_external_propagator (...);

        outln!(
            "[obs-prop] ObserverPropagator is created and connected both as an ExternalPropagator and as a FixedAssignmentListener."
        );

        // Fatal error: invalid literal '0'
        // solver!(solver).add_observed_var(0);

        for h in 0..N {
            for p in 0..p_limit() {
                solver!(solver).add_observed_var(ph(p, h));
            }
        }

        let mut max_var = solver!(solver).vars();
        outln!("Maximum variable in solver: {}", max_var);

        let new_var = max_var + 5;
        // Observing a variable before using it in any clause will force the
        // solver to create the variable.
        solver!(solver).add_observed_var(new_var);

        // Removing a non-observed (or not even existing) variable has no
        // effect, the solver will not create the variable and will not
        // throw any errors.
        solver!(solver).remove_observed_var(new_var + 223);
        assert!(solver!(solver).vars() < new_var + 223);

        max_var = solver!(solver).vars();
        outln!("New maximum variable in solver: {}", max_var);

        // When a unit clause is found by the SAT solver,
        // notify_fixed_assignment will be immediately called.
        shared.non_observed_lit.set(new_var - 1);
        shared.fixed_lit.set(-shared.non_observed_lit.get());
        solver!(solver).clause1(-shared.non_observed_lit.get());

        ObserverPropagator { solver, shared }
    }
}

impl Drop for ObserverPropagator {
    fn drop(&mut self) {
        outln!("[obs-prop][~ObserverPropagator starts]");

        // Note that disconnecting a propagator will also invoke unobserving
        // every observed variable.  In case any of these variables are
        // currently assigned (e.g., because the solver is in a SAT state),
        // it will force the solver to backtrack in order to unassign the
        // variables.
        drop(solver!(self.solver).disconnect_external_propagator());
        drop(solver!(self.solver).disconnect_fixed_listener());

        // Fatal error: can not unobserve variables without a connected
        // propagator solver->remove_observed_var (6);

        // Fatal error: can not disconnect propagator without a connected
        // propagator solver->disconnect_external_propagator();

        outln!("[obs-prop] ObserverPropagator is disconnected.");
    }
}

impl FixedAssignmentListener for ObserverFixedListener {
    fn notify_fixed_assignment(&mut self, lit: i32) {
        outln!("[fal][notify_fixed_assignment][{}]", lit);
    }
}

impl ExternalPropagator for ObserverImpl {
    fn notify_assignment(&mut self, lits: &[i32]) {
        out!("[obs-prop][notify_assignment][ ");
        for lit in lits {
            out!("{} ", lit);
        }
        outln!("]");
    }

    fn notify_new_decision_level(&mut self) {
        outln!("[obs-prop][notify_new_decision_level]");

        // Fatal error: not allowed to force backtrack in that state of the
        // solver solver->force_backtrack(0);
    }

    fn notify_backtrack(&mut self, new_level: usize) {
        outln!("[obs-prop][notify_backtrack][ to level {} ]", new_level);

        // Fatal error: not allowed to force backtrack in that state of the
        // solver solver->force_backtrack(0);
    }

    fn cb_check_found_model(&mut self, model: &[i32]) -> bool {
        out!("[obs-prop][cb_check_found_model][ ");
        for lit in model {
            out!("{} ", lit);
        }
        outln!("]");

        // In this callback we are allowed to force the solver to backtrack
        // (and thereby throw away the found model).  Note however that if
        // backtrack was forced, the return value of this function is
        // ignored by the solver.
        if self.shared.first_model.get() {
            self.shared.first_model.set(false);
            let solver = self.solver;
            solver!(solver).force_backtrack(0);
            return true;
        }

        true
    }

    fn cb_decide(&mut self) -> i32 {
        outln!("[obs-prop][cb_decide][0]");

        // Fatal error: the target level of a forced backtrack must be
        // non-negative. solver->force_backtrack(-6);

        // Fatal error: cadical: the target level of a forced backtrack must
        // be smaller than the current decision level.
        // solver->force_backtrack(n*p_limit+5);

        // Fatal error: external decisions are only allowed over observed
        // variables. return non_observed_lit;

        // Fatal error: external decisions are only allowed over unassigned
        // variables. return fixed_lit;

        0
    }

    fn cb_propagate(&mut self) -> i32 {
        out!("[obs-prop][cb_propagate]");
        let count = self.shared.propagation_count.get() + 1;
        self.shared.propagation_count.set(count);

        // Here 6 and 7 are just arbitrarily picked numbers to demonstrate
        // some special features of cb_propagate in combination with
        // add_observed_var.
        if count == 6 {
            // It is allowed to add new observed variables during this
            // callback.
            let solver = self.solver;
            let fresh_variable = solver!(solver).vars() + 1;
            solver!(solver).add_observed_var(fresh_variable);

            // It is not necessary to use the newly observed variable in the
            // propagation.
            outln!("[0]");
            return 0;
        } else if count == 7 {
            let non_observed_lit = self.shared.non_observed_lit.get();
            outln!("[{}]", -non_observed_lit);
            // In case the newly observed variable is already assigned in
            // the solver, the SAT solver will need to backtrack to undo the
            // corresponding assignment.  This forces the solver to backtrack
            // to level 0 and triggers the corresponding 'notify_backtrack'
            // callback at the same time (re-entering this propagator, so we
            // must not touch 'self' after this call).
            let solver = self.solver;
            solver!(solver).add_observed_var(non_observed_lit);

            return -non_observed_lit;
        }

        outln!("[0]");
        0
    }

    fn cb_add_reason_clause_lit(&mut self, propagated_lit: i32) -> i32 {
        let _ = propagated_lit;
        // In this example we have no used external propagations, so this
        // function will not be called by the SAT solver.
        let _ = self.shared.fixed_lit.get();
        assert!(false);
        0
    }

    fn cb_has_external_clause(&mut self, is_forgettable: &mut bool) -> bool {
        let _ = is_forgettable;
        outln!("[obs-prop][cb_has_external_clause][no]");

        // Fatal error: not allowed to force backtrack in that state of the
        // solver
        // solver->force_backtrack(0);

        false
    }

    fn cb_add_external_clause_lit(&mut self) -> i32 {
        // In this example we have no external clauses to add, so this
        // function will not be called by the SAT solver.
        assert!(false);
        0
    }
}

// This helper class is used to recognize when an external propagation or
// external falsified clause can be added to the solver.

struct AssignmentStatus {
    // Used to recognize if there are yet unassigned variables
    next_unassigned_pos: usize,

    // The actual assignment regarding each object. 1 indicates that the
    // element is selected, 0 indicates unknown (unassigned), and -1
    // indicates that it is not selected under the current assignment.
    amap: Vec<i32>,

    // Number of selected elements
    p_count: usize,
}

impl AssignmentStatus {
    fn new(size: usize) -> AssignmentStatus {
        AssignmentStatus { next_unassigned_pos: 0, amap: vec![0; size], p_count: 0 }
    }

    #[allow(dead_code)]
    fn reset(&mut self) {
        for v in self.amap.iter_mut() {
            *v = 0;
        }
        self.next_unassigned_pos = 0;
        self.p_count = 0;
    }

    fn assign(&mut self, pos: usize, val: i32) {
        assert!(self.amap[pos] == 0);
        if val > 0 {
            self.p_count += 1;
            self.amap[pos] = 1;
        } else {
            self.amap[pos] = -1;
        }

        if self.next_unassigned_pos == pos {
            loop {
                self.next_unassigned_pos += 1;
                if !(self.next_unassigned_pos < self.amap.len() && self.amap[self.next_unassigned_pos] != 0) {
                    break;
                }
            }
        }
    }

    fn unassign(&mut self, pos: usize) {
        assert!(self.amap[pos] != 0);
        if self.amap[pos] > 0 {
            self.p_count -= 1;
        }
        self.amap[pos] = 0;
        if pos < self.next_unassigned_pos {
            self.next_unassigned_pos = pos;
        }
    }

    // The assignment propagates if exactly one element is already selected
    // and there are yet unassigned positions.
    fn propagates(&self) -> bool {
        self.p_count == 1 && self.next_unassigned_pos < self.amap.len()
    }

    // It returns the first selected index (or -1 if there is none)
    fn get_val(&self) -> i32 {
        for i in 0..self.amap.len() {
            if self.amap[i] > 0 {
                return i as i32;
            }
        }
        -1
    }

    // Returns true if there are more than one selected elements
    fn conflicting(&self) -> bool {
        self.p_count > 1
    }
}

/*----------------------------------------------------------------------------*/
//
// ActivePropagator:
//
// A more complex ExternalPropagator that follows the assignment steps of
// the solver and provides additional propagation steps based on the not
// pre-encoded part of the problem (the at most one pigeon per hole
// constraints).

struct ActiveImpl {
    // Initially every hole and every pigeons are unassigned
    hole_map: Vec<AssignmentStatus>,
    pigeon_map: Vec<AssignmentStatus>,

    // Since we ignore in this example the out-of-order fixed assignments,
    // the trail is a stack (instead of a deque)
    observed_trail: Vec<Vec<i32>>,

    // Used for storing the current external (reason) clauses during
    // interactions with the solver.
    clause: Vec<i32>,
    next_lit: usize,

    // The reason literals of external propagations (see C++).
    reason_map: BTreeMap<i32, i32>,

    // The external propagations that are currently unassigned.
    unassigned_reasons: BTreeSet<i32>,

    // Used to demonstrate some illegal use cases.
    #[allow(dead_code)]
    non_observed_lit: Rc<Cell<i32>>,
}

/// User facing object (C++ `ActivePropagator`).
struct ActivePropagator {
    solver: *mut Solver,
}

impl ActivePropagator {
    fn new(solver: *mut Solver) -> ActivePropagator {
        let non_observed_lit = Rc::new(Cell::new(0));
        let mut imp = ActiveImpl {
            hole_map: (0..N).map(|_| AssignmentStatus::new(p_limit() as usize)).collect(),
            pigeon_map: (0..p_limit()).map(|_| AssignmentStatus::new(N as usize)).collect(),
            observed_trail: Vec::new(),
            clause: Vec::new(),
            next_lit: 0,
            reason_map: BTreeMap::new(),
            unassigned_reasons: BTreeSet::new(),
            non_observed_lit: non_observed_lit.clone(),
        };

        // In this example we can always cheaply re-add external clauses if
        // necessary, so we allow the SAT solver to consider them during
        // clause database reduction ('are_reasons_forgettable' below).

        // Create the root-level of the trail (in C++ done at the end of
        // the constructor, but the trail is not used before solving).
        imp.observed_trail.push(Vec::new());

        solver!(solver).connect_external_propagator(Box::new(imp));

        outln!("[act-prop] ActivePropagator is created and connected as an ExternalPropagator");

        // Observe all variables of the encoding
        for h in 0..N {
            for p in 0..N + 1 {
                solver!(solver).add_observed_var(ph(p, h));
            }
        }

        non_observed_lit.set(solver!(solver).vars() + 1);

        ActivePropagator { solver }
    }
}

impl Drop for ActivePropagator {
    fn drop(&mut self) {
        outln!("[act-prop][~ActivePropagator starts]");

        // Clearing 'observed_trail', 'hole_map' and 'pigeon_map' happens
        // when the disconnected propagator is dropped.
        drop(solver!(self.solver).disconnect_external_propagator());
        outln!("[act-prop] ActivePropagator is disconnected.");
    }
}

impl ActiveImpl {
    fn explain_propagation(&mut self, propagated_lit: i32) {
        assert!(propagated_lit < 0);

        self.clause.clear();
        self.next_lit = 0;

        self.clause.push(propagated_lit);
        // 'std::map::operator[]' inserts a default value if missing.
        let reason = *self.reason_map.entry(propagated_lit).or_insert(0);
        self.clause.push(reason);
        self.clause.push(0);
    }
}

impl ExternalPropagator for ActiveImpl {
    fn are_reasons_forgettable(&self) -> bool {
        true
    }

    fn notify_assignment(&mut self, lits: &[i32]) {
        out!("[act-prop][notify_assignment][ ");
        for &lit in lits {
            out!("{} ", lit);

            // Add the new assignment to the observed trail
            self.observed_trail.last_mut().unwrap().push(lit);

            // Update the maps based on the assignment
            let pig_id = p_id(lit);
            let hole_id = h_id(lit);
            self.hole_map[hole_id as usize].assign(pig_id as usize, lit);
            self.pigeon_map[pig_id as usize].assign(hole_id as usize, lit);

            // In case it was a previously externally propagated step, this
            // notification of assignment is actually about the reassignment
            // of it, hence we might need the reason clause of it later.
            self.unassigned_reasons.remove(&lit);
        }
        outln!("]");
    }

    fn notify_new_decision_level(&mut self) {
        outln!("[act-prop][notify_new_decision_level]");

        // Create a new decision level on the observed trail
        self.observed_trail.push(Vec::new());
    }

    fn notify_backtrack(&mut self, new_level: usize) {
        out!("[act-prop][notify_backtrack][ {} -> {} ][unassigned: ", self.observed_trail.len() - 1, new_level);

        // Undo all the backtracked assignments on the observed trail and
        // in the assignment maps.
        while self.observed_trail.len() > new_level + 1 {
            let top = self.observed_trail.pop().unwrap();
            for &lit in &top {
                out!("{} ", lit);

                let pig_id = p_id(lit);
                let hole_id = h_id(lit);
                self.hole_map[hole_id as usize].unassign(pig_id as usize);
                self.pigeon_map[pig_id as usize].unassign(hole_id as usize);

                // In case it was a previously externally propagated literal,
                // we mark the reason clause of it for deletion, but do not
                // delete it yet.
                if self.reason_map.contains_key(&lit) {
                    self.unassigned_reasons.insert(lit);
                }
            }
        }
        outln!("]");
    }

    fn cb_check_found_model(&mut self, model: &[i32]) -> bool {
        out!("[act-prop][cb_check_found_model][ ");
        for lit in model {
            out!("{} ", lit);
        }
        outln!("]");

        true
    }

    fn cb_decide(&mut self) -> i32 {
        outln!("[act-prop][cb_decide][0]");

        // Here we can erase the reasons of the unassigned externally
        // propagated literals, since it is sure that none of them will be
        // reused (i.e., reassigned) by the SAT solver anymore.
        for lit in &self.unassigned_reasons {
            self.reason_map.remove(lit);
        }

        0
    }

    fn cb_propagate(&mut self) -> i32 {
        out!("[act-prop][cb_propagate]");

        for h in 0..N {
            if self.hole_map[h as usize].propagates() {
                let lit = -ph(self.hole_map[h as usize].next_unassigned_pos as i32, h);
                outln!("[{}]", lit);
                self.reason_map.insert(lit, -ph(self.hole_map[h as usize].get_val(), h));
                return lit;
            }
        }

        for p in 0..p_limit() {
            if self.pigeon_map[p as usize].propagates() {
                let lit = -ph(p, self.pigeon_map[p as usize].next_unassigned_pos as i32);
                outln!("[{}]", lit);
                self.reason_map.insert(lit, -ph(p, self.pigeon_map[p as usize].get_val()));
                return lit;
            }
        }

        outln!("[0]");
        0
    }

    fn cb_add_reason_clause_lit(&mut self, propagated_lit: i32) -> i32 {
        // In this example we explicitly saved the reason of every external
        // propagation step in the 'reason_map', so we can simply look it up
        // and construct the necessary clause when required.
        out!("[act-prop][cb_add_reason_clause_lit][{}][ ", propagated_lit);

        if self.clause.is_empty() {
            self.explain_propagation(propagated_lit);
        }
        assert!(self.next_lit < self.clause.len());

        let lit = self.clause[self.next_lit];
        self.next_lit += 1;
        if lit == 0 {
            self.clause.clear();
            self.next_lit = 0;
        }

        outln!("{} ]", lit);
        lit
    }

    fn cb_has_external_clause(&mut self, is_forgettable: &mut bool) -> bool {
        out!("[act-prop][cb_has_external_clause][ ");

        for h in 0..N {
            if self.hole_map[h as usize].conflicting() {
                *is_forgettable = true;
                self.clause.clear();

                for p in 0..p_limit() {
                    let pid = self.hole_map[h as usize].amap[p as usize];
                    if pid > 0 {
                        let lit = -ph(p, h);
                        self.clause.push(lit);
                        out!("{} ", lit);
                    }
                }

                self.clause.push(0);
                self.next_lit = 0;
                outln!("]");
                return true;
            }
        }

        for p in 0..p_limit() {
            if self.pigeon_map[p as usize].conflicting() {
                *is_forgettable = true;
                self.clause.clear();

                for h in 0..N {
                    let hole_val = self.pigeon_map[p as usize].amap[h as usize];
                    if hole_val > 0 {
                        let lit = -ph(p, h);
                        self.clause.push(lit);
                        out!("{} ", lit);
                    }
                }

                self.clause.push(0);
                self.next_lit = 0;
                outln!("]");
                return true;
            }
        }

        *is_forgettable = true;
        self.clause.clear();

        outln!("no ]");
        false
    }

    fn cb_add_external_clause_lit(&mut self) -> i32 {
        if self.next_lit < self.clause.len() {
            let lit = self.clause[self.next_lit];
            self.next_lit += 1;
            if lit == 0 {
                self.clause.clear();
                self.next_lit = 0;
            }
            return lit;
        }

        assert!(false);
        0
    }
}

fn observer_example() {
    let solver: *mut Solver = Box::into_raw(Box::new(Solver::new()));

    // We use the simplified interface (so there are no explicit variable
    // declarations)
    solver!(solver).set("factor", 0);

    // Fatal error: can not observe variables without a connected propagator
    // solver.add_observed_var(4);

    P_LIMIT.store(N, Relaxed); // satisfiable example

    let observer = ObserverPropagator::new(solver);
    formula(solver!(solver));

    let res = solver!(solver).solve();
    outln!("Result: {}", res);

    assert!(res == 10);
    if res == 10 {
        out!("s ");
        let mut h = 1;
        while h <= solver!(solver).vars() {
            out!("{} ", solver!(solver).val(h));
            h += 1;
        }
        outln!();
    }

    // C++ destroys 'observer' before 'solver'.
    drop(observer);
    // SAFETY: allocated with 'Box::into_raw' above, no other users left.
    drop(unsafe { Box::from_raw(solver) });
}

fn active_propagator_example() {
    let solver: *mut Solver = Box::into_raw(Box::new(Solver::new()));

    // We use the simplified interface (so there are no explicit variable
    // declarations)
    solver!(solver).set("factor", 0);

    // We generate for this example an unsatisfiable PHP problem.
    P_LIMIT.store(N + 1, Relaxed);

    let propagator = ActivePropagator::new(solver);

    partial_formula(solver!(solver));

    let res = solver!(solver).solve();
    outln!("Result: {}", res);
    assert!(res == 20);

    drop(propagator);
    // SAFETY: allocated with 'Box::into_raw' above, no other users left.
    drop(unsafe { Box::from_raw(solver) });
}

fn main() {
    observer_example();
    outln!("-----------------------------------------------------------");
    active_propagator_example();
}

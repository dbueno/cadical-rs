//! The public API of the solver: port of `cadical.hpp` (the [`Solver`]
//! class and the call-back traits) and of `solver.cpp` (its
//! implementation).
//!
//! # Overview
//!
//! [`Solver`] provides the actual API of the CaDiCaL solver.  Besides its
//! constructor and destructor most important is the IPASIR part (`add`,
//! `assume`, `solve`, `val`, `failed`, `connect_terminator`,
//! `connect_learner`).  The following example (from
//! `test/api/example.cpp`) shows typical API usage:
//!
//! ```
//! use cadical::solver::Solver;
//!
//! let mut solver = Solver::new();
//!
//! // ------------------------------------------------------------------
//! // Encode Problem and check without assumptions.
//!
//! let tie = solver.declare_one_more_variable();
//! let shirt = solver.declare_one_more_variable();
//! assert!(solver.vars() >= 2);
//!
//! solver.clause(&[-tie, shirt]);
//! solver.clause(&[tie, shirt]);
//! solver.clause(&[-tie, -shirt]);
//!
//! let res = solver.solve();        // Solve instance.
//! assert_eq!(res, 10);             // Check it is 'SATISFIABLE'.
//!
//! let res = solver.val(tie);      // Obtain assignment of 'TIE'.
//! assert!(res < 0);                // Check 'TIE' assigned to 'false'.
//!
//! let res = solver.val(shirt);     // Obtain assignment of 'SHIRT'.
//! assert!(res > 0);                // Check 'SHIRT' assigned to 'true'.
//!
//! // ------------------------------------------------------------------
//! // Incrementally solve again under one assumption.
//!
//! solver.assume(tie);              // Now force 'TIE' to true.
//!
//! let res = solver.solve();        // Solve again incrementally.
//! assert_eq!(res, 20);             // Check it is 'UNSATISFIABLE'.
//!
//! assert!(solver.failed(tie));     // Yes, 'TIE' in core.
//! assert!(!solver.failed(shirt));  // No, 'SHIRT' not in core.
//!
//! // ------------------------------------------------------------------
//! // Incrementally solve once more under another assumption.
//!
//! solver.assume(-shirt);           // Now force 'SHIRT' to false.
//!
//! let res = solver.solve();        // Solve again incrementally.
//! assert_eq!(res, 20);             // Check it is 'UNSATISFIABLE'.
//!
//! assert!(!solver.failed(tie));    // No, 'TIE' not in core.
//! assert!(solver.failed(-shirt));  // Yes, '!SHIRT' in core.
//! ```
//!
//! # States and transitions
//!
//! The internal solver state follows the IPASIR API model used in the
//! incremental track of the SAT competition.  Compared to IPASIR there is
//! also an [`ADDING`] state in which the solver stays while adding non-zero
//! literals until the clause is completed through adding a zero literal.
//! The additional [`INITIALIZING`], [`CONFIGURING`] and [`DELETING`]
//! states are also not part of IPASIR but also useful for testing and
//! debugging.
//!
//! We have the following transitions which are all synchronous except for
//! the reentrant `terminate` call:
//!
//! ```text
//!                         new
//! INITIALIZING --------------------------> CONFIGURING
//!
//!                    set / trace
//!  CONFIGURING --------------------------> CONFIGURING
//!
//!               add (non zero literal)
//!        VALID --------------------------> ADDING
//!
//!               add (zero literal)
//!        VALID --------------------------> STEADY
//!
//!               assume (non zero literal)
//!        READY --------------------------> STEADY
//!
//!                        solve
//!        READY --------------------------> SOLVING
//!
//!                     (internal)
//!      SOLVING --------------------------> SOLVED
//!
//!                val (non zero literal)
//!    SATISFIED --------------------------> SATISFIED
//!
//!               failed (non zero literal)
//!  UNSATISFIED --------------------------> UNSATISFIED
//!
//!               implied (non zero literal)
//! INCONCLUSIVE --------------------------> INCONCLUSIVE
//!
//!                        delete
//!        VALID --------------------------> DELETING
//! ```
//!
//! where
//!
//! ```text
//!       SOLVED = SATISFIED    | UNSATISFIED | INCONCLUSIVE
//!        READY = CONFIGURING  | STEADY      | SOLVED
//!        VALID = READY        | ADDING
//!      INVALID = INITIALIZING | DELETING
//! ```
//!
//! The [`SOLVING`] state is only visible in different contexts, i.e., from
//! another thread or from a signal handler.  It is used to implement
//! `terminate`.  Here is the only asynchronous transition:
//!
//! ```text
//!               terminate (asynchronously)
//!      SOLVING  ------------------------->  STEADY
//! ```
//!
//! The important behaviour to remember is that adding, assuming or
//! constraining a literal (immediately) destroys the satisfying assignment
//! in the [`SATISFIED`] state and vice versa resets all assumptions in the
//! [`UNSATISFIED`] state.  This is exactly the behaviour required by the
//! IPASIR interface.
//!
//! Furthermore, the model can only be queried through `val` in the
//! [`SATISFIED`] state, while extracting failed assumptions with `failed`
//! only in the [`UNSATISFIED`] state.  Solving can only be started in the
//! [`STEADY`] or [`CONFIGURING`] state or after the previous call to
//! `solve` yielded an [`INCONCLUSIVE`], [`SATISFIED`] or [`UNSATISFIED`]
//! state.
//!
//! All literals have to be valid literals too, i.e., 32-bit integers
//! different from `i32::MIN`.  If any of these requirements is violated the
//! solver aborts with an 'API contract violation' message (exactly as the
//! C++ library, the message names the C++ function).
//!
//! HINT: If you do not understand why a contract is violated you can run
//! `mobical` on the failing API call trace.  Point the environment variable
//! `CADICAL_API_TRACE` to the file where you want to save the trace during
//! execution of your program linking against the library.  You probably
//! need for `mobical` to use the option `--do-not-enforce-contracts` though
//! to force running into the same contract violation.
//!
//! Additional API calls (like `freeze` and `melt`) do not change the state
//! of the solver and are all described below.
//!
//! # Call-backs
//!
//! Call-back objects are passed as `Box<dyn Trait>` and owned by the
//! solver; `disconnect_*` returns the box.  To keep access to a connected
//! object, connect a clone of an `Rc<RefCell<T>>` or `Arc<Mutex<T>>`: every
//! call-back trait (and the proof tracer traits) is implemented for these
//! wrappers by forwarding to `T`.  The object is borrowed (locked) during
//! each call-back, so do not hold a borrow (lock) across a call into the
//! solver.
//!
//! Closures can be used directly as [`Terminator`] (`FnMut () -> bool`),
//! [`FixedAssignmentListener`] (`FnMut (i32)`), [`ClauseIterator`]
//! (`FnMut (&[i32]) -> bool`) and [`WitnessIterator`]
//! (`FnMut (&[i32], &[i32], i64) -> bool`).  For learners use
//! [`learner_fn`] or [`Solver::connect_learner_fn`], which hand over whole
//! clauses.
//!
//! # Rust conveniences
//!
//! Besides the faithful port of the C++ API (which returns the IPASIR
//! integer status codes) there are a few thin helpers which do not change
//! any semantics: [`Solver::add_clause`], [`Solver::assume_all`],
//! [`Solver::solve_result`], [`Solver::simplify_result`],
//! [`Solver::propagate_result`], [`Solver::val`] (C++ `val (lit)`),
//! [`Solver::value`], [`Solver::model`], [`Solver::result`],
//! [`Solver::set_options`], [`Solver::connect_learner_fn`],
//! [`Solver::traverse_clauses_with`], [`Solver::trace_api_calls`] (taking
//! a path), [`Solver::termination_handle`] and the [`SolveResult`] enum.

#![warn(missing_docs)]

use std::ffi::{CStr, CString};
use std::sync::atomic::{AtomicBool, Ordering::Relaxed};
use std::cell::RefCell;
use std::rc::Rc;
use std::sync::{Arc, Mutex, MutexGuard, PoisonError};

use crate::config::Config;
use crate::contract::require_solver_pointer_to_be_non_zero;
use crate::external::External;
use crate::file::File;
use crate::internal::Internal;
use crate::message::{c_stderr, c_stdout, fflush, fputc, fputs};
use crate::options::Options;
use crate::parse::Parser;
use crate::terminal::{terr, tout, Terminal};
use crate::tracer::{FileTracer, InternalTracer, StatTracer, Tracer, TracerRef};
use crate::util::is_power_of_two;

pub use crate::internal::CubesWithStatus;

/// Major semantic version (`CADICAL_MAJOR`).
///
/// We support semantic versioning (<https://semver.org/>), which means
/// that we aim at not breaking API usage when increasing the minor or
/// patch version, but assume API breaking changes when increasing the
/// major version.
pub const CADICAL_MAJOR: i32 = 3;
/// Minor semantic version (`CADICAL_MINOR`).
pub const CADICAL_MINOR: i32 = 0;
/// Semantic patch version (`CADICAL_PATCH`).
pub const CADICAL_PATCH: i32 = 0;

/*========================================================================*/

/// `enum Status`: the SAT competition standardized the exit code of SAT
/// solvers to the following which then is also used as return code for
/// `solve` functions.  See also the Rust enum [`SolveResult`].
pub type Status = i32;
/// Satisfiable (`10`).
pub const SATISFIABLE: Status = 10;
/// Unsatisfiable (`20`).
pub const UNSATISFIABLE: Status = 20;
/// Unknown (`0`): limit reached or interrupted through `terminate`.
pub const UNKNOWN: Status = 0;

/// `enum State` of the API state machine.  States are represented by a
/// bit-set in order to combine them (see the module documentation for the
/// transitions).
pub type State = i32;
/// During initialization (invalid).
pub const INITIALIZING: State = 1;
/// Configure options (with 'set').
pub const CONFIGURING: State = 2;
/// Ready to call 'solve'.
pub const STEADY: State = 4;
/// Adding clause literals (zero missing).
pub const ADDING: State = 8;
/// While solving (within 'solve').
pub const SOLVING: State = 16;
/// Satisfiable allows 'val'.
pub const SATISFIED: State = 32;
/// Unsatisfiable allows 'failed'.
pub const UNSATISFIED: State = 64;
/// During and after deletion (invalid).
pub const DELETING: State = 128;
/// Unknown allows 'implied'.
pub const INCONCLUSIVE: State = 256;
/// `CONFIGURING | STEADY | SATISFIED | UNSATISFIED | INCONCLUSIVE` (used
/// to check contracts).
pub const READY: State = CONFIGURING | STEADY | SATISFIED | UNSATISFIED | INCONCLUSIVE;
/// `READY | ADDING` (used to check contracts).
pub const VALID: State = READY | ADDING;
/// `INITIALIZING | DELETING` (used to check contracts).
pub const INVALID: State = INITIALIZING | DELETING;

/// Rust enum version of the IPASIR status codes returned by `solve`,
/// `simplify`, `propagate` and `lookahead` related functions (a thin
/// convenience, the integer returning functions are the reference).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(i32)]
pub enum SolveResult {
    /// `0`: limit reached, interrupted through `terminate`, or (for
    /// `propagate`) neither a conflict nor a complete assignment found.
    Unknown = 0,
    /// `10`: the formula is satisfiable under the assumptions.
    Satisfiable = 10,
    /// `20`: the formula is unsatisfiable under the assumptions.
    Unsatisfiable = 20,
}

impl SolveResult {
    /// Map an IPASIR status code (`10`, `20`, anything else is unknown).
    pub fn from_code(code: i32) -> SolveResult {
        match code {
            SATISFIABLE => SolveResult::Satisfiable,
            UNSATISFIABLE => SolveResult::Unsatisfiable,
            _ => SolveResult::Unknown,
        }
    }

    /// The IPASIR status code (`0`, `10` or `20`).
    pub fn code(self) -> i32 {
        self as i32
    }

    /// Is the result `Satisfiable`?
    pub fn is_sat(self) -> bool {
        self == SolveResult::Satisfiable
    }

    /// Is the result `Unsatisfiable`?
    pub fn is_unsat(self) -> bool {
        self == SolveResult::Unsatisfiable
    }

    /// Is the result `Unknown`?
    pub fn is_unknown(self) -> bool {
        self == SolveResult::Unknown
    }
}

impl From<SolveResult> for i32 {
    fn from(r: SolveResult) -> i32 {
        r.code()
    }
}

/*========================================================================*/

/// `__FILE__` in the C++ contract messages.
const FILE: &str = "../src/solver.cpp";

/// The global 'tracing_api_calls_through_environment_variable_method'
/// flag is used to ensure that only one solver traces to a file.
/// Otherwise the method to use an environment variable to point to the
/// trace file is bogus, since those different solver instances would all
/// write to the same file producing garbage.  A more sophisticated
/// solution would use a different mechanism to tell the solver to which
/// file to trace to, but in our experience it is quite convenient to get
/// traces out of applications which use the solver as library by just
/// setting an environment variable without requiring to change any
/// application code.
static TRACING_API_CALLS_THROUGH_ENVIRONMENT_VARIABLE_METHOD: AtomicBool = AtomicBool::new(false);

/// The global 'tracing_nb_lidrup_env_var_method' flag is used to ensure
/// that only one solver produces a proof file. Otherwise the method to use
/// an environment variable to point to the trace file is bogus, since those
/// different solver instances would all write to the same file producing
/// garbage. See also the comment on
/// `TRACING_API_CALLS_THROUGH_ENVIRONMENT_VARIABLE_METHOD` above.
static TRACING_NB_LIDRUP_ENV_VAR_METHOD: AtomicBool = AtomicBool::new(false);

/*========================================================================*/

/// The CaDiCaL SAT solver (public API, port of `class Solver` in
/// `cadical.hpp`).
///
/// The `Solver` is a 'facade' object for `External`.  It exposes the
/// public API of `External` but hides everything else.  The CaDiCaL code
/// is split into three layers:
///
/// * `Solver`: facade object providing the actual API of the solver,
/// * `External`: communication layer between `Solver` and `Internal`,
/// * `Internal`: the actual solver code.
///
/// Separating `External` from `Internal` also allows us to map external
/// literals to internal literals, which is useful with many fixed or
/// eliminated variables (during 'compact' the internal variable range is
/// reduced and external variables are remapped).
///
/// Most functions document the API contract in the form
/// `require (STATES)` / `ensure (STATES)` (see the module documentation
/// for the states).  Violating a contract aborts the process with an
/// 'invalid API usage' message.
///
/// # Threads
///
/// `Solver` is neither `Send` nor `Sync`.  Connected call-backs (terminator,
/// learner, listener, propagator, proof tracers) are `Box<dyn Trait>`
/// without a `Send` bound, so they may hold `Rc`, `Cell` or raw pointers
/// (the C API and `mobical` rely on that), and the solver keeps
/// C `FILE *` handles and raw pointers between its layers.  To use a solver
/// on another thread, create it on that thread (for example inside
/// `std::thread::spawn`) and send inputs and results over channels.  To
/// stop a running `solve` from any thread or a signal handler use
/// [`Solver::termination_handle`].
///
/// ```compile_fail
/// fn assert_send<T: Send>() {}
/// assert_send::<cadical::Solver>();
/// ```
pub struct Solver {
    /// The solver is in the state ADDING if either the current clause or
    /// the constraint (or both) is not yet terminated.
    pub(crate) adding_clause: bool,
    pub(crate) adding_constraint: bool,
    /// API states as discussed in the module documentation.
    pub(crate) _state: State,

    /// Hidden internal solver (owned, from `Box::into_raw`).
    pub(crate) internal: *mut Internal,
    /// Hidden API to internal solver mapping (owned, from
    /// `Box::into_raw`).
    pub(crate) external: *mut External,

    /// Close file if owned by solver.
    pub(crate) close_trace_api_file: bool,
    /// Also acts as flag that we are tracing.
    pub(crate) trace_api_file: *mut libc::FILE,
    /// Rust addition: the trace file was opened by
    /// [`Solver::trace_api_calls`] (from a path) and is closed on drop.
    pub(crate) owns_trace_api_file: bool,
}

/// A handle to asynchronously force termination of a solver from another
/// thread or a signal handler (Rust addition: in C++ users call
/// `terminate ()` on the shared solver pointer from another thread, which
/// Rust's aliasing rules do not allow while `solve` holds `&mut Solver`).
///
/// The handle is `Send + Sync + Clone` and only sets an atomic flag, which
/// is also async-signal-safe.  This is the supported way to stop a running
/// solver from outside.  It is equivalent to [`Solver::terminate`] minus
/// the API contract checks.
///
/// ```
/// use std::{thread, time::Duration};
///
/// let mut solver = cadical::Solver::new();
/// let handle = solver.termination_handle();
/// let timer = thread::spawn(move || {
///     thread::sleep(Duration::from_millis(10));
///     handle.terminate();
/// });
/// // A hard instance (pigeon hole 12 -> 11) which does not finish in 10ms.
/// let (p, h) = (12, 11);
/// let var = |i: i32, j: i32| i * h + j + 1;
/// for i in 0..p {
///     solver.clause(&(0..h).map(|j| var(i, j)).collect::<Vec<_>>());
/// }
/// for j in 0..h {
///     for i in 0..p {
///         for k in i + 1..p {
///             solver.clause(&[-var(i, j), -var(k, j)]);
///         }
///     }
/// }
/// let res = solver.solve_result();
/// timer.join().unwrap();
/// assert!(res.is_unknown());
/// ```
///
/// If the flag is set while the solver is not solving, the next `solve`
/// call returns `0` (unknown) right away; the flag is reset when that call
/// returns (as in C++).
#[derive(Clone, Debug)]
pub struct TerminationHandle(pub(crate) Arc<AtomicBool>);

impl TerminationHandle {
    /// Force termination of the solver asynchronously.  The solver
    /// terminates `solve` as soon as it checks the flag (the result is
    /// then `0` / unknown).
    pub fn terminate(&self) {
        self.0.store(true, Relaxed);
    }
}

// The handle must be usable from other threads.
const _: fn() = || {
    fn assert_send_sync<T: Send + Sync>() {}
    assert_send_sync::<TerminationHandle>();
};

impl Solver {
    /// Access to the internal solver (`Testing::internal`, `App`,
    /// `Parser`, `Mobical`).  Crate-private: it hands out an aliasing
    /// `&mut` from `&self`, which is only sound under the single-threaded,
    /// non-reentrant usage discipline of the port.  External code uses
    /// [`crate::testing::Testing`] (tests only).
    #[inline(always)]
    #[allow(clippy::mut_from_ref)]
    pub(crate) fn internal(&self) -> &mut Internal {
        // SAFETY: owned by this solver, stable address.
        unsafe { &mut *self.internal }
    }

    /// Access to the external layer (`Testing::external`, `App`,
    /// `Mobical`).  Crate-private, see [`Solver::internal`].
    #[inline(always)]
    #[allow(clippy::mut_from_ref)]
    pub(crate) fn external(&self) -> &mut External {
        // SAFETY: owned by this solver, stable address.
        unsafe { &mut *self.external }
    }

    /// Handle to force termination asynchronously from another thread or
    /// a signal handler (Rust addition).  This is the documented way to
    /// interrupt `solve` from outside, see [`TerminationHandle`] for an
    /// example.  All handles of a solver share one flag.
    pub fn termination_handle(&self) -> TerminationHandle {
        TerminationHandle(self.internal().termination_forced.clone())
    }

    /// Return the current state of the solver (see the module
    /// documentation for the states).
    #[inline]
    pub fn state(&self) -> State {
        self._state
    }

    /// Similar to [`Solver::state`] but using the standard competition exit
    /// codes of `10` for 'SATISFIABLE', `20` for 'UNSATISFIABLE' and `0`
    /// otherwise.
    #[inline]
    pub fn status(&self) -> i32 {
        if self._state == SATISFIED {
            SATISFIABLE
        } else if self._state == UNSATISFIED {
            UNSATISFIABLE
        } else {
            UNKNOWN
        }
    }
}

/*========================================================================*/

/// Connected terminators are checked for termination regularly.  If the
/// `terminate` function of the terminator returns true the solver is
/// terminated synchronously as soon it calls this function.
///
/// Any closure `FnMut () -> bool` is a terminator.
pub trait Terminator {
    /// Return `true` to terminate the solver.
    fn terminate(&mut self) -> bool;
}

impl<F: FnMut() -> bool> Terminator for F {
    fn terminate(&mut self) -> bool {
        self()
    }
}

/// Connected learners which can be used to export learned clauses.  The
/// `learning` can check the size of the learned clause and only if it
/// returns true then the individual literals of the learned clause are
/// given to the learner through `learn` one by one terminated by a zero
/// literal.
pub trait Learner {
    /// Return `true` if the learned clause of the given size should be
    /// exported (through `learn`).
    fn learning(&mut self, size: i32) -> bool;
    /// Receives the literals of the exported clause one by one terminated
    /// by a zero literal.
    fn learn(&mut self, lit: i32);
}

/// Connected listener gets notified whenever the truth value of a variable
/// is fixed (for example during inprocessing or due to derived unit
/// clauses).
///
/// Any closure `FnMut (i32)` is a listener.
pub trait FixedAssignmentListener {
    /// The literal `lit` became fixed (root-level implied).
    fn notify_fixed_assignment(&mut self, lit: i32);
}

impl<F: FnMut(i32)> FixedAssignmentListener for F {
    fn notify_fixed_assignment(&mut self, lit: i32) {
        self(lit)
    }
}

/*------------------------------------------------------------------------*/

/// Allows to connect an external propagator to propagate values to
/// variables with an external clause as a reason or to learn new clauses
/// during the CDCL loop (without restart), see IPASIR-UP.
pub trait ExternalPropagator {
    /// Lazy propagator only checks complete assignments (C++ data member
    /// `bool is_lazy = false`).
    fn is_lazy(&self) -> bool {
        false
    }

    /// Reason external clauses can be deleted (C++ data member
    /// `bool are_reasons_forgettable = false`).
    fn are_reasons_forgettable(&self) -> bool {
        false
    }

    /// Notify the propagator about assignments to observed variables.  The
    /// notification is not necessarily eager.  It usually happens before
    /// the call of propagator callbacks and when a driving clause is
    /// leading to an assignment.
    fn notify_assignment(&mut self, lits: &[i32]);

    /// The notification for the assignement follow the standard trail
    /// used in SAT solvers.  The assignment is a stack with (possibly
    /// empty) decisions.  New assignments are pushed at the end of the
    /// stack.  When backtracking, you get the information on how many
    /// decision (called levels in SAT solvers) you have to keep (see
    /// `notify_backtrack`).
    fn notify_new_decision_level(&mut self);

    /// Backtrack to `new_level`: all decision and assignments before
    /// decision number `new_level` are kept, all other (at the end of
    /// stack) are removed.  In particular, when backtracking to level `0`,
    /// no decision is left and only assignments done before the first
    /// decision (literals that have to be true in all models of the
    /// formula) are kept.  The number will always be lower than the number
    /// of decisions on the trail, so backtracking will always have an
    /// effect.
    fn notify_backtrack(&mut self, new_level: usize);

    /// Check by the external propagator the found complete solution (after
    /// solution reconstruction).  If it returns false, the propagator
    /// needs to explain why, either by providing an external clause during
    /// the next callback or introduce new observed variables during this
    /// callback.
    fn cb_check_found_model(&mut self, model: &[i32]) -> bool;

    /// Ask the external propagator for the next decision literal.  If it
    /// returns `0`, the solver makes its own choice.  If it is an already
    /// assigned variable or a non-valid literal (e.g., not observed), a
    /// runtime error is triggered.
    fn cb_decide(&mut self) -> i32 {
        0
    }

    /// Ask the external propagator if there is an external propagation to
    /// make under the current assignment.  It returns either a literal to
    /// be propagated or `0`, indicating that there is no external
    /// propagation under the current assignment.  In case the returned
    /// literal is not an observed variable, a runtime error is triggered.
    fn cb_propagate(&mut self) -> i32 {
        0
    }

    /// Ask the external propagator for the reason clause of a previous
    /// external propagation step (done by `cb_propagate`).  The clause
    /// must be added literal-by-literal closed with a `0`.  Further, the
    /// clause must contain the propagated literal.
    ///
    /// The clause will be learned as an irredundant non-forgettable
    /// clause, unless `are_reasons_forgettable` returns true.
    fn cb_add_reason_clause_lit(&mut self, propagated_lit: i32) -> i32 {
        let _ = propagated_lit;
        0
    }

    /// The following two functions are used to add external clauses to
    /// the solver during the CDCL loop.  The external clause is added
    /// literal-by-literal and learned by the solver as an irredundant
    /// (original) input clause.
    ///
    /// The clause can be arbitrary, but if it is root-satisfied or
    /// tautology, the solver will ignore it without learning it.
    /// Root-falsified literals are eagerly removed from the clause.
    /// Falsified clauses trigger conflict analysis, propagating clauses
    /// trigger propagation.  In case 'chrono' is '0', the solver
    /// backtracks to propagate the new literal on the correct decision
    /// level, as otherwise it potentially will be an out-of-order
    /// assignment on the current level.
    ///
    /// Unit clauses always (unless root-satisfied, see above) trigger
    /// backtracking (independently from the value of the 'chrono' option
    /// and independently from being falsified or satisfied or unassigned)
    /// to level '0'.  Empty clause (or root falsified clause, see above)
    /// makes the problem 'UNSATISFIABLE' and stops the search immediately.
    /// A literal '0' must close the clause.
    ///
    /// The external propagator indicates that there is a clause to add.
    /// The parameter of the function allows the user to indicate how
    /// 'forgettable' the external clause is.  Forgettable clauses are
    /// allowed to be removed by the SAT solver during clause database
    /// reduction.  However, it is up to the solver to decide when actually
    /// the clause is deleted.  For example, unit clauses, even forgettable
    /// ones, will not be deleted.  In case the clause is not 'forgettable'
    /// (the parameter is false), the solver considers the clause to be
    /// irredundant.
    ///
    /// In case the solver produces incremental proofs, these external
    /// clauses are added to the proof during solving at real-time, i.e.,
    /// the proof checker can ignore them until that point (so added as
    /// input clause, but input after the query line).
    ///
    /// Currently, every external clause is expected to be over observed
    /// (therefore frozen) variables, hence no tainting or restore steps are
    /// performed upon their addition.
    fn cb_has_external_clause(&mut self, is_forgettable: &mut bool) -> bool;

    /// The actual function called to add the external clause (one literal
    /// per call, terminated by `0`).
    fn cb_add_external_clause_lit(&mut self) -> i32;
}

/*------------------------------------------------------------------------*/

/// Allows to traverse all remaining irredundant clauses.  Satisfied and
/// eliminated clauses are not included, nor any derived units unless such
/// a unit literal is frozen.  Falsified literals are skipped.  If the
/// solver is inconsistent only the empty clause is traversed.
///
/// If `clause` returns false traversal aborts early.
pub trait ClauseIterator {
    /// Visit one clause.  Return `false` to abort the traversal.
    fn clause(&mut self, clause: &[i32]) -> bool;
}

/*------------------------------------------------------------------------*/

/// Allows to traverse all clauses on the extension stack together with
/// their witness cubes.  If the solver is inconsistent, i.e., an empty
/// clause is found and the formula is unsatisfiable, then nothing is
/// traversed.
///
/// The clauses traversed in `traverse_clauses` together with the clauses
/// on the extension stack are logically equivalent to the original
/// clauses.  See our SAT'19 paper for more details.
///
/// The witness literals can be used to extend and fix an assignment on the
/// remaining clauses to satisfy the clauses on the extension stack too.
///
/// All derived units of non-frozen variables are included too, but not the
/// units for frozen literals.
///
/// If `witness` returns false traversal aborts early.
pub trait WitnessIterator {
    /// Visit one clause with its witness (`id` defaults to `0` in C++).
    /// Return `false` to abort the traversal.
    fn witness(&mut self, clause: &[i32], witness: &[i32], id: i64) -> bool;
}

/// Any closure `FnMut (&[i32], &[i32], i64) -> bool` (clause, witness, id)
/// is a witness iterator (see also
/// [`Solver::traverse_witnesses_backward_with`]).
impl<F: FnMut(&[i32], &[i32], i64) -> bool> WitnessIterator for F {
    fn witness(&mut self, clause: &[i32], witness: &[i32], id: i64) -> bool {
        self(clause, witness, id)
    }
}

/// Any closure `FnMut (&[i32]) -> bool` is a clause iterator (see also
/// [`Solver::traverse_clauses_with`]).
impl<F: FnMut(&[i32]) -> bool> ClauseIterator for F {
    fn clause(&mut self, clause: &[i32]) -> bool {
        self(clause)
    }
}

/*------------------------------------------------------------------------*/

/// A [`Learner`] built from a closure receiving whole clauses (Rust
/// addition).  Clauses with at most `max_length` literals are collected
/// literal by literal through the [`Learner`] protocol and handed to the
/// closure once complete (without the terminating zero).  Create it with
/// [`learner_fn`] or connect one directly with
/// [`Solver::connect_learner_fn`].
pub struct LearnerFn<F> {
    max_length: i32,
    clause: Vec<i32>,
    f: F,
}

/// Wrap a closure receiving whole learned clauses of at most `max_length`
/// literals as a [`Learner`] (see [`LearnerFn`]).
///
/// ```
/// use cadical::{learner_fn, Solver};
/// let mut solver = Solver::new();
/// solver.connect_learner(Box::new(learner_fn(2, |clause: &[i32]| {
///     assert!(!clause.is_empty() && clause.len() <= 2);
/// })));
/// ```
pub fn learner_fn<F: FnMut(&[i32])>(max_length: i32, f: F) -> LearnerFn<F> {
    LearnerFn { max_length, clause: Vec::new(), f }
}

impl<F: FnMut(&[i32])> Learner for LearnerFn<F> {
    fn learning(&mut self, size: i32) -> bool {
        size <= self.max_length
    }
    fn learn(&mut self, lit: i32) {
        if lit != 0 {
            self.clause.push(lit);
        } else {
            (self.f)(&self.clause);
            self.clause.clear();
        }
    }
}

/*------------------------------------------------------------------------*/
// Shared ownership of call-backs (Rust addition).
//
// Connected call-backs are owned by the solver ('Box<dyn Trait>').  To
// keep access to the call-back object (for example to read collected
// data after 'solve') connect a clone of an 'Rc<RefCell<T>>' or
// 'Arc<Mutex<T>>' instead: all call-back traits (and the proof tracer
// traits in 'tracer.rs') are implemented for these by forwarding to 'T'.
//
// The object is borrowed (locked) for the duration of each call-back, so
// do not keep a 'borrow_mut ()' (or a lock guard) alive across a call
// into the solver which may invoke the call-back ('solve', 'simplify',
// 'propagate', 'add', ...), as that panics ('RefCell') or deadlocks
// ('Mutex').

/// Lock a mutex ignoring poisoning (a call-back panicking while the lock
/// is held already aborts or unwinds through the solver anyway).
#[inline]
pub(crate) fn lock_shared<T: ?Sized>(m: &Mutex<T>) -> MutexGuard<'_, T> {
    m.lock().unwrap_or_else(PoisonError::into_inner)
}

/// Implements a call-back trait for `Rc<RefCell<T>>` and `Arc<Mutex<T>>`
/// by forwarding every (`&mut self`) method to `T`.
macro_rules! impl_shared_callback {
    ($tr:ident { $( fn $name:ident (&mut self $(, $arg:ident : $ty:ty)* ) $(-> $ret:ty)? ; )* }) => {
        impl<T: $tr + ?Sized> $tr for ::std::rc::Rc<::std::cell::RefCell<T>> {
            $( #[inline] fn $name(&mut self $(, $arg: $ty)*) $(-> $ret)? { self.borrow_mut().$name($($arg),*) } )*
        }
        impl<T: $tr + ?Sized> $tr for ::std::sync::Arc<::std::sync::Mutex<T>> {
            $( #[inline] fn $name(&mut self $(, $arg: $ty)*) $(-> $ret)? { $crate::solver::lock_shared(self).$name($($arg),*) } )*
        }
    };
}
pub(crate) use impl_shared_callback;

impl_shared_callback!(Terminator {
    fn terminate(&mut self) -> bool;
});

impl_shared_callback!(Learner {
    fn learning(&mut self, size: i32) -> bool;
    fn learn(&mut self, lit: i32);
});

impl_shared_callback!(FixedAssignmentListener {
    fn notify_fixed_assignment(&mut self, lit: i32);
});

impl_shared_callback!(ClauseIterator {
    fn clause(&mut self, clause: &[i32]) -> bool;
});

impl_shared_callback!(WitnessIterator {
    fn witness(&mut self, clause: &[i32], witness: &[i32], id: i64) -> bool;
});

/// Implements [`ExternalPropagator`] for a shared wrapper (the two `&self`
/// flags need a separate accessor).
macro_rules! impl_shared_propagator {
    ($ty:ty, |$s:ident| $get:expr, |$sm:ident| $get_mut:expr) => {
        impl<T: ExternalPropagator + ?Sized> ExternalPropagator for $ty {
            fn is_lazy(&self) -> bool {
                { let $s = self; $get }.is_lazy()
            }
            fn are_reasons_forgettable(&self) -> bool {
                { let $s = self; $get }.are_reasons_forgettable()
            }
            fn notify_assignment(&mut self, lits: &[i32]) {
                { let $sm = self; $get_mut }.notify_assignment(lits)
            }
            fn notify_new_decision_level(&mut self) {
                { let $sm = self; $get_mut }.notify_new_decision_level()
            }
            fn notify_backtrack(&mut self, new_level: usize) {
                { let $sm = self; $get_mut }.notify_backtrack(new_level)
            }
            fn cb_check_found_model(&mut self, model: &[i32]) -> bool {
                { let $sm = self; $get_mut }.cb_check_found_model(model)
            }
            fn cb_decide(&mut self) -> i32 {
                { let $sm = self; $get_mut }.cb_decide()
            }
            fn cb_propagate(&mut self) -> i32 {
                { let $sm = self; $get_mut }.cb_propagate()
            }
            fn cb_add_reason_clause_lit(&mut self, propagated_lit: i32) -> i32 {
                { let $sm = self; $get_mut }.cb_add_reason_clause_lit(propagated_lit)
            }
            fn cb_has_external_clause(&mut self, is_forgettable: &mut bool) -> bool {
                { let $sm = self; $get_mut }.cb_has_external_clause(is_forgettable)
            }
            fn cb_add_external_clause_lit(&mut self) -> i32 {
                { let $sm = self; $get_mut }.cb_add_external_clause_lit()
            }
        }
    };
}

impl_shared_propagator!(Rc<RefCell<T>>, |s| s.borrow(), |s| s.borrow_mut());
impl_shared_propagator!(Arc<Mutex<T>>, |s| lock_shared(s), |s| lock_shared(s));

/*========================================================================*/
// API call logging ('LOG_API_CALL_BEGIN', 'LOG_API_CALL_END' and
// 'LOG_API_CALL_RETURNS' with their overloaded static helpers).  Only
// compiled with the 'logging' feature (C++ 'LOGGING').

#[cfg(feature = "logging")]
mod api_logging {
    use crate::internal::Internal;
    use crate::logging::Logger;
    use crate::terminal::tout;

    // Needs to be kept in sync with the color schemes used in
    // 'logging.rs': api_code = blue_code, log_code = magenta_code,
    // emph_code = bright_magenta_code.

    pub fn call(internal: &Internal, name: &str, suffix: &str) {
        Logger::log(
            internal,
            format_args!(
                "API call {}'{} ()'{} {}",
                tout().blue_code(),
                name,
                tout().magenta_code(),
                suffix
            ),
        );
    }

    pub fn call_i(internal: &Internal, name: &str, arg: i32, suffix: &str) {
        Logger::log(
            internal,
            format_args!(
                "API call {}'{} ({})'{} {}",
                tout().blue_code(),
                name,
                arg,
                tout().magenta_code(),
                suffix
            ),
        );
    }

    pub fn call_ii(internal: &Internal, name: &str, arg: i32, b: i32, suffix: &str) {
        Logger::log(
            internal,
            format_args!(
                "API call {}'{} ({}, {})'{} {}",
                tout().blue_code(),
                name,
                arg,
                b,
                tout().magenta_code(),
                suffix
            ),
        );
    }

    pub fn call_iii(internal: &Internal, name: &str, arg: i32, b: i32, c: i32) {
        Logger::log(
            internal,
            format_args!(
                "API call {}'{} ({}, {})'{} {}",
                tout().blue_code(),
                name,
                arg,
                b,
                tout().magenta_code(),
                c
            ),
        );
    }

    pub fn call_s(internal: &Internal, name: &str, arg: &str, suffix: &str) {
        Logger::log(
            internal,
            format_args!(
                "API call {}'{} (\"{}\")'{} {}",
                tout().blue_code(),
                name,
                arg,
                tout().magenta_code(),
                suffix
            ),
        );
    }

    pub fn call_si(internal: &Internal, name: &str, a1: &str, a2: i32, s: &str) {
        Logger::log(
            internal,
            format_args!(
                "API call {}'{} (\"{}\", {})'{} {}",
                tout().blue_code(),
                name,
                a1,
                a2,
                tout().magenta_code(),
                s
            ),
        );
    }

    pub fn returns_ss(internal: &Internal, name: &str, arg: &str, res: Option<&str>) {
        Logger::log(
            internal,
            format_args!(
                "API call {}'{} (\"{}\")'{} returns '{}'",
                tout().blue_code(),
                name,
                arg,
                tout().magenta_code(),
                res.unwrap_or("<null>")
            ),
        );
    }

    pub fn returns_sis(internal: &Internal, name: &str, a1: &str, a2: i32, res: Option<&str>) {
        Logger::log(
            internal,
            format_args!(
                "API call {}'{} (\"{}\", {})'{} returns '{}'",
                tout().blue_code(),
                name,
                a1,
                a2,
                tout().magenta_code(),
                res.unwrap_or("<null>")
            ),
        );
    }

    pub fn returns_bool(res: bool) -> &'static str {
        if res {
            "returns 'true'"
        } else {
            "returns 'false'"
        }
    }
}

/// Runs the body only with the `logging` feature and if the `log` option
/// is set (`LOG_API_CALL_*` guards).
macro_rules! api_log {
    ($self:ident, |$i:ident| $body:expr) => {
        #[cfg(feature = "logging")]
        {
            let $i: &Internal = $self.internal();
            if $i.opts.log != 0 {
                $body;
            }
        }
    };
}

/// `STATE (S)`: log state transitions.
macro_rules! state {
    ($self:ident, $s:ident) => {
        $self.set_state($s, stringify!($s))
    };
}

impl Solver {
    fn set_state(&mut self, s: State, name: &str) {
        debug_assert!(is_power_of_two(s as u32));
        if self._state == s {
            return;
        }
        self._state = s;
        log!(
            self.internal,
            "API enters state {}{}{}",
            tout().bright_magenta_code(),
            name,
            tout().normal_code()
        );
        let _ = name;
    }

    /*--------------------------------------------------------------------*/
    // 'LOG_API_CALL_BEGIN (...)' overloads.

    #[inline(always)]
    fn log_begin(&self, name: &str) {
        api_log!(self, |i| {
            crate::logging::Logger::log_empty_line(i);
            api_logging::call(i, name, "started")
        });
        let _ = name;
    }

    #[inline(always)]
    fn log_begin_i(&self, name: &str, arg: i32) {
        api_log!(self, |i| {
            crate::logging::Logger::log_empty_line(i);
            api_logging::call_i(i, name, arg, "started")
        });
        let _ = (name, arg);
    }

    #[inline(always)]
    fn log_begin_ii(&self, name: &str, arg: i32, b: i32) {
        api_log!(self, |i| {
            crate::logging::Logger::log_empty_line(i);
            api_logging::call_ii(i, name, arg, b, "started")
        });
        let _ = (name, arg, b);
    }

    #[inline(always)]
    fn log_begin_s(&self, name: &str, arg: &str) {
        api_log!(self, |i| {
            crate::logging::Logger::log_empty_line(i);
            api_logging::call_s(i, name, arg, "started")
        });
        let _ = (name, arg);
    }

    #[inline(always)]
    fn log_begin_si(&self, name: &str, arg1: &str, arg2: i32) {
        api_log!(self, |i| {
            crate::logging::Logger::log_empty_line(i);
            api_logging::call_si(i, name, arg1, arg2, "started")
        });
        let _ = (name, arg1, arg2);
    }

    /*--------------------------------------------------------------------*/
    // 'LOG_API_CALL_END (...)' overloads.

    #[inline(always)]
    fn log_end(&self, name: &str) {
        api_log!(self, |i| api_logging::call(i, name, "succeeded"));
        let _ = name;
    }

    #[inline(always)]
    fn log_end_i(&self, name: &str, lit: i32) {
        api_log!(self, |i| api_logging::call_i(i, name, lit, "succeeded"));
        let _ = (name, lit);
    }

    #[inline(always)]
    fn log_end_s(&self, name: &str, arg: &str) {
        api_log!(self, |i| {
            crate::logging::Logger::log_empty_line(i);
            api_logging::call_s(i, name, arg, "succeeded")
        });
        let _ = (name, arg);
    }

    #[inline(always)]
    fn log_end_sb(&self, name: &str, arg: &str, res: bool) {
        api_log!(self, |i| api_logging::call_s(
            i,
            name,
            arg,
            if res { "succeeded" } else { "failed" }
        ));
        let _ = (name, arg, res);
    }

    #[inline(always)]
    fn log_end_sib(&self, name: &str, arg: &str, val: i32, res: bool) {
        api_log!(self, |i| api_logging::call_si(
            i,
            name,
            arg,
            val,
            if res { "succeeded" } else { "failed" }
        ));
        let _ = (name, arg, val, res);
    }

    /*--------------------------------------------------------------------*/
    // 'LOG_API_CALL_RETURNS (...)' overloads.

    #[inline(always)]
    fn log_returns_b(&self, name: &str, res: bool) {
        api_log!(self, |i| api_logging::call(i, name, api_logging::returns_bool(res)));
        let _ = (name, res);
    }

    #[inline(always)]
    fn log_returns_i(&self, name: &str, res: i32) {
        api_log!(self, |i| api_logging::call(i, name, &format!("returns '{}'", res)));
        let _ = (name, res);
    }

    #[inline(always)]
    fn log_returns_i64(&self, name: &str, res: i64) {
        api_log!(self, |i| api_logging::call(i, name, &format!("returns '{}'", res)));
        let _ = (name, res);
    }

    #[inline(always)]
    fn log_returns_ii(&self, name: &str, lit: i32, res: i32) {
        api_log!(self, |i| api_logging::call_i(i, name, lit, &format!("returns '{}'", res)));
        let _ = (name, lit, res);
    }

    #[inline(always)]
    fn log_returns_ib(&self, name: &str, lit: i32, res: bool) {
        api_log!(self, |i| api_logging::call_i(i, name, lit, api_logging::returns_bool(res)));
        let _ = (name, lit, res);
    }

    #[inline(always)]
    fn log_returns_iii(&self, name: &str, lit: i32, b: i32, res: i32) {
        api_log!(self, |i| api_logging::call_iii(i, name, lit, b, res));
        let _ = (name, lit, b, res);
    }

    #[inline(always)]
    fn log_returns_sb(&self, name: &str, arg: &str, res: bool) {
        api_log!(self, |i| api_logging::call_s(i, name, arg, api_logging::returns_bool(res)));
        let _ = (name, arg, res);
    }

    #[inline(always)]
    fn log_returns_ss(&self, name: &str, arg: &str, res: Option<&str>) {
        api_log!(self, |i| api_logging::returns_ss(i, name, arg, res));
        let _ = (name, arg, res);
    }

    #[inline(always)]
    fn log_returns_sis(&self, name: &str, arg1: &str, arg2: i32, res: Option<&str>) {
        api_log!(self, |i| api_logging::returns_sis(i, name, arg1, arg2, res));
        let _ = (name, arg1, arg2, res);
    }

    /*--------------------------------------------------------------------*/
    // 'TRACE (...)': log the begin of the API call and write it to the API
    // trace file (if tracing).

    #[inline]
    fn trace0(&self, s0: &str) {
        if self.internal.is_null() {
            return;
        }
        self.log_begin(s0);
        if self.trace_api_file.is_null() {
            return;
        }
        self.trace_api_call(s0);
    }

    #[inline]
    fn trace_i(&self, s0: &str, i1: i32) {
        if self.internal.is_null() {
            return;
        }
        self.log_begin_i(s0, i1);
        if self.trace_api_file.is_null() {
            return;
        }
        self.trace_api_call_i(s0, i1);
    }

    #[inline]
    fn trace_s(&self, s0: &str, s1: &str) {
        if self.internal.is_null() {
            return;
        }
        self.log_begin_s(s0, s1);
        if self.trace_api_file.is_null() {
            return;
        }
        self.trace_api_call_s(s0, s1);
    }

    #[inline]
    fn trace_si(&self, s0: &str, s1: &str, i2: i32) {
        if self.internal.is_null() {
            return;
        }
        self.log_begin_si(s0, s1, i2);
        if self.trace_api_file.is_null() {
            return;
        }
        self.trace_api_call_si(s0, s1, i2);
    }

    /*--------------------------------------------------------------------*/
    // API contract checks ('contract.hpp').  The first argument is the
    // C++ '__PRETTY_FUNCTION__' of the checking function, so that the
    // messages are identical to the C++ library.

    /// `REQUIRE_INITIALIZED ()`.
    #[inline]
    fn require_initialized(&self, f: &str) {
        require_solver_pointer_to_be_non_zero(self as *const Solver as *const (), f, FILE);
        require!(f, FILE, !self.external.is_null(), "external solver not initialized");
        require!(f, FILE, !self.internal.is_null(), "internal solver not initialized");
    }

    /// `REQUIRE_VALID_STATE ()`.
    #[inline]
    fn require_valid_state(&self, f: &str) {
        self.require_initialized(f);
        require!(f, FILE, self.state() & VALID != 0, "solver in invalid state");
    }

    /// `REQUIRE_READY_STATE ()`.
    #[inline]
    fn require_ready_state(&self, f: &str) {
        self.require_valid_state(f);
        require!(
            f,
            FILE,
            self.state() != ADDING,
            "clause incomplete (terminating zero not added)"
        );
    }

    /// `REQUIRE_VALID_OR_SOLVING_STATE ()`.
    #[inline]
    fn require_valid_or_solving_state(&self, f: &str) {
        self.require_initialized(f);
        require!(
            f,
            FILE,
            self.state() & (VALID | SOLVING) != 0,
            "solver neither in valid nor solving state"
        );
    }

    /// `REQUIRE_VALID_LIT (LIT)`.
    #[inline]
    fn require_valid_lit(&self, f: &str, lit: i32) {
        require!(f, FILE, lit != 0 && lit != i32::MIN, "invalid literal '{}'", lit);
        require!(
            f,
            FILE,
            self.external().is_valid_input(lit),
            "extension variable '{}' defined by the solver internally (all user variables have to be declared explicitly if 'factor' is enabled)",
            lit.abs()
        );
    }
}

/*========================================================================*/
// Port of 'solver.cpp'.

impl Solver {
    #[doc(hidden)]
    pub fn transition_to_steady_state(&mut self) {
        if self.state() == CONFIGURING {
            log!(
                self.internal,
                "API leaves state {}CONFIGURING{}",
                tout().bright_magenta_code(),
                tout().normal_code()
            );
            if self.internal().opts.check != 0 && self.internal().opts.checkproof != 0 {
                self.internal().check();
            }
        } else if self.state() == SATISFIED {
            log!(
                self.internal,
                "API leaves state {}SATISFIED{}",
                tout().bright_magenta_code(),
                tout().normal_code()
            );
            self.external().reset_assumptions();
            self.external().reset_concluded();
            self.external().reset_constraint();
        } else if self.state() == UNSATISFIED {
            log!(
                self.internal,
                "API leaves state {}UNSATISFIED{}",
                tout().bright_magenta_code(),
                tout().normal_code()
            );
            self.external().reset_assumptions();
            self.external().reset_concluded();
            self.external().reset_constraint();
        } else if self.state() == INCONCLUSIVE {
            self.external().reset_assumptions();
            self.external().reset_concluded();
            self.external().reset_constraint();
        }
        if self.state() != STEADY {
            state!(self, STEADY);
        }
    }

    /*--------------------------------------------------------------------*/
    // API call tracing (for 'mobical').

    #[doc(hidden)]
    pub fn trace_api_call(&self, s0: &str) {
        debug_assert!(!self.trace_api_file.is_null());
        log!(self.internal, "TRACE {}", s0);
        cfprintf!(self.trace_api_file, "{}\n", s0);
        fflush(self.trace_api_file);
    }

    /// C++ overload `Solver::trace_api_call` (renamed).
    #[doc(hidden)]
    pub fn trace_api_call_i(&self, s0: &str, i1: i32) {
        debug_assert!(!self.trace_api_file.is_null());
        log!(self.internal, "TRACE {} {}", s0, i1);
        cfprintf!(self.trace_api_file, "{} {}\n", s0, i1);
        fflush(self.trace_api_file);
    }

    /// C++ overload `Solver::trace_api_call` (renamed).
    #[doc(hidden)]
    pub fn trace_api_call_ii(&self, s0: &str, i1: i32, b: i32) {
        debug_assert!(!self.trace_api_file.is_null());
        log!(self.internal, "TRACE {} {} {}", s0, i1, b);
        cfprintf!(self.trace_api_file, "{} {} {}\n", s0, i1, b);
        fflush(self.trace_api_file);
    }

    /// C++ overload `Solver::trace_api_call` (renamed).
    #[doc(hidden)]
    pub fn trace_api_call_s(&self, s0: &str, s1: &str) {
        debug_assert!(!self.trace_api_file.is_null());
        log!(self.internal, "TRACE {} {}", s0, s1);
        cfprintf!(self.trace_api_file, "{} {}\n", s0, s1);
        fflush(self.trace_api_file);
    }

    /// C++ overload `Solver::trace_api_call` (renamed).
    #[doc(hidden)]
    pub fn trace_api_call_si(&self, s0: &str, s1: &str, i2: i32) {
        debug_assert!(!self.trace_api_file.is_null());
        log!(self.internal, "TRACE {} {} {}", s0, s1, i2);
        cfprintf!(self.trace_api_file, "{} {} {}\n", s0, s1, i2);
        fflush(self.trace_api_file);
    }

    /*--------------------------------------------------------------------*/

    /// Returns the maximum variable index.
    ///
    /// Variables are usually added and initialized implicitly whenever a
    /// literal is used as an argument except for the functions `val`,
    /// `fixed`, `failed` and `frozen`.  However, the library internally
    /// keeps a maximum variable index, which can be queried.
    ///
    /// With factor (BVA) the solver might also add new variables.  In that
    /// case the user is required to use this to check which variables are
    /// currently free before adding new variables of their own.  The
    /// alternative is to declare more variables in batches with
    /// [`Solver::declare_more_variables`].  Using [`Solver::resize`] in
    /// combination with any technique that could add variables (currently
    /// only factor) is not advised.  After each application of `add`,
    /// `vars ()` will return an updated value, even if you did not import
    /// the entire clause yet.
    ///
    /// `require (VALID | SOLVING)`, `ensure (VALID | SOLVING)`.
    pub fn vars(&mut self) -> i32 {
        const F: &str = "int CaDiCaL::Solver::vars()";
        self.trace0("vars");
        self.require_valid_or_solving_state(F);
        let res = self.external().max_var;
        self.log_returns_i("vars", res);
        res
    }

    /// Increase the maximum variable index explicitly.  This function
    /// makes sure that at least `min_max_var` variables are initialized.
    /// Since it might need to reallocate tables, it destroys a satisfying
    /// assignment and has the same state transition and conditions as
    /// `assume` etc.
    ///
    /// `require (READY)`, `ensure (STEADY)`.
    pub fn resize(&mut self, min_max_var: i32) {
        const F: &str = "void CaDiCaL::Solver::resize(int)";
        self.trace_i("resize", min_max_var);
        self.require_valid_state(F);
        self.transition_to_steady_state();
        self.external().reset_extended();
        self.external().init(min_max_var, false);
        self.log_end_i("resize", min_max_var);
    }

    /// Increase the maximum variable index by a number of new variables.
    /// Initializes `number_of_vars` new variables and protects them from
    /// being used by the solver as extension variables (BVA).
    ///
    /// It returns the new maximum variable index which is the highest
    /// variable name of the consecutive range of newly declared variables.
    /// It has the same state transition and conditions as `resize` above.
    ///
    /// `require (READY)`, `ensure (STEADY)`.
    pub fn declare_more_variables(&mut self, number_of_vars: i32) -> i32 {
        const F: &str = "int CaDiCaL::Solver::declare_more_variables(int)";
        self.trace_i("declare_more_variables", number_of_vars);
        self.require_valid_state(F);
        self.transition_to_steady_state();
        self.external().reset_extended();
        let new_max_var = self.external().max_var + number_of_vars;
        self.external().init(new_max_var, false);
        self.log_end_i("declare_more_variables", number_of_vars);
        new_max_var
    }

    /// Returns the next fresh variable that was not used internally (and
    /// declares it, see [`Solver::declare_more_variables`]).
    ///
    /// `require (READY)`, `ensure (STEADY)`.
    pub fn declare_one_more_variable(&mut self) -> i32 {
        const F: &str = "int CaDiCaL::Solver::declare_one_more_variable()";
        self.trace0("declare_one_more_variable");
        self.require_valid_state(F);
        self.transition_to_steady_state();
        self.external().reset_extended();
        let new_max_var = self.external().max_var + 1;
        self.external().init(new_max_var, false);
        self.log_end("declare_one_more_variable");
        new_max_var
    }

    /*--------------------------------------------------------------------*/

    /// This function can be used to write API calls to a file.  The same
    /// format is used which `mobical` can read, execute and also shrink
    /// through delta debugging.
    ///
    /// Tracing API calls can also be achieved by using the environment
    /// variable `CADICAL_API_TRACE`.  That alternative is useful if you do
    /// not want to change the source code using the solver, e.g., if you
    /// only have a binary with the solver linked in.  However, that method
    /// only allows to trace one solver instance, while with the following
    /// function API tracing can be enabled for different solver instances
    /// individually.
    ///
    /// This is the low-level variant taking a C `FILE *` (C++
    /// `trace_api_calls (FILE *)`); most users want
    /// [`Solver::trace_api_calls`] which takes a path.  The solver will
    /// flush the file after every trace API call but does not close it
    /// during deletion.  It remains owned by the user of the library (a C
    /// `FILE *`, e.g., from `libc::fopen`) and must stay open until the
    /// solver is dropped.
    ///
    /// `require (VALID)`, `ensure (VALID)`.
    pub fn trace_api_calls_file(&mut self, file: *mut libc::FILE) {
        const F: &str = "void CaDiCaL::Solver::trace_api_calls(FILE *)";
        self.log_begin("trace_api_calls");
        self.require_valid_state(F);
        require!(F, FILE, !file.is_null(), "invalid zero file argument");
        require!(
            F,
            FILE,
            !TRACING_API_CALLS_THROUGH_ENVIRONMENT_VARIABLE_METHOD.load(Relaxed),
            "already tracing API calls using environment variable 'CADICAL_API_TRACE'"
        );
        require!(F, FILE, self.trace_api_file.is_null(), "called twice");
        self.trace_api_file = file;
        self.log_end("trace_api_calls");
        self.trace_api_call("init");
    }

    /// Trace API calls to the file at `path` (created or truncated), for
    /// example to replay them with `mobical` (Rust addition, see
    /// [`Solver::trace_api_calls_file`] for the C `FILE *` variant and the
    /// `CADICAL_API_TRACE` environment variable alternative).  The file is
    /// flushed after every traced call and closed when the solver is
    /// dropped.  Returns the I/O error if the file can not be opened.
    ///
    /// `require (VALID)`, `ensure (VALID)`.
    pub fn trace_api_calls<P: AsRef<std::path::Path>>(&mut self, path: P) -> std::io::Result<()> {
        let path = path.as_ref();
        let cpath = CString::new(path.as_os_str().as_encoded_bytes())
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidInput, e))?;
        // SAFETY: valid C strings.
        let file = unsafe { libc::fopen(cpath.as_ptr(), b"w\0".as_ptr() as *const libc::c_char) };
        if file.is_null() {
            return Err(std::io::Error::last_os_error());
        }
        self.trace_api_calls_file(file);
        self.owns_trace_api_file = true;
        Ok(())
    }

    /*--------------------------------------------------------------------*/
    // Option handling.

    /// Determine whether `name` is a valid option name.
    pub fn is_valid_option(name: &str) -> bool {
        Options::has(name).is_some()
    }

    /// Determine whether `name` enables a specific preprocessing
    /// technique.
    pub fn is_preprocessing_option(name: &str) -> bool {
        Options::is_preprocessing_option(name)
    }

    /// Determine whether `arg` is a valid long option of the form
    /// `--<name>`, `--<name>=<val>` or `--no-<name>` similar to
    /// [`Solver::set_long_option`].  Legal values are `true`, `false`, or
    /// `[-]<mantissa>[e<exponent>]`.
    pub fn is_valid_long_option(arg: &str) -> bool {
        let mut name = String::new();
        let mut tmp = 0;
        Options::parse_long_option(arg, &mut name, &mut tmp)
    }

    /// Get the current value of the option `name`.  If `name` is invalid
    /// then zero is returned.  Here `--...` arguments are invalid options.
    ///
    /// `require (VALID | SOLVING)`.
    pub fn get(&mut self, arg: &str) -> i32 {
        const F: &str = "int CaDiCaL::Solver::get(const char *)";
        self.require_valid_or_solving_state(F);
        self.internal().opts.get(arg)
    }

    /// Explicit version of setting an option.  If the option `name` exists
    /// and `val` can be parsed then `true` is returned.  If the option
    /// value is out of range the actual value is computed as the closest
    /// (minimum or maximum) value possible, but still `true` is returned.
    ///
    /// Thus options can only be set right after initialization (except for
    /// `log`, `quiet`, `report` and `verbose`).
    ///
    /// `require (CONFIGURING)`, `ensure (CONFIGURING)`.
    pub fn set(&mut self, arg: &str, val: i32) -> bool {
        const F: &str = "bool CaDiCaL::Solver::set(const char *, int)";
        self.trace_si("set", arg, val);
        self.require_valid_state(F);
        if arg != "log" && arg != "quiet" && arg != "report" && arg != "verbose" {
            require!(
                F,
                FILE,
                self.state() == CONFIGURING,
                "can only set option 'set (\"{}\", {})' right after initialization",
                arg,
                val
            );
        }
        let res = self.internal().opts.set(arg, val);
        self.log_end_sib("set", arg, val, res);

        res
    }

    /// This function accepts options in command line syntax:
    /// `--<name>=<val>`, `--<name>`, or `--no-<name>`.
    ///
    /// It actually calls the previous [`Solver::set`] function after
    /// parsing `arg`.  The same values are expected as for
    /// [`Solver::is_valid_long_option`] and as with `set` any value outside
    /// of the range of legal values for a particular option are set to
    /// either the minimum or maximum depending on which side of the valid
    /// interval they lie.
    ///
    /// `require (CONFIGURING)`, `ensure (CONFIGURING)`.
    pub fn set_long_option(&mut self, arg: &str) -> bool {
        const F: &str = "bool CaDiCaL::Solver::set_long_option(const char *)";
        self.log_begin_s("set", arg);
        self.require_valid_state(F);
        require!(
            F,
            FILE,
            self.state() == CONFIGURING,
            "can only set option '{}' right after initialization",
            arg
        );
        let res;
        let bytes = arg.as_bytes();
        if bytes.first() != Some(&b'-') || bytes.get(1) != Some(&b'-') {
            res = false;
        } else {
            let mut val = 0;
            let mut name = String::new();
            res = Options::parse_long_option(arg, &mut name, &mut val);
            if res {
                self.set(&name, val);
            }
        }
        self.log_end_sb("set", arg, res);
        res
    }

    /// Increase preprocessing and inprocessing limits by `10^<val>`.
    /// Values below `0` are ignored and values above `9` are reduced to
    /// `9`.
    ///
    /// `require (READY)`, `ensure (READY)`.
    pub fn optimize(&mut self, arg: i32) {
        const F: &str = "void CaDiCaL::Solver::optimize(int)";
        self.log_begin_i("optimize", arg);
        self.require_valid_state(F);
        self.internal().opts.optimize(arg);
        self.log_end_i("optimize", arg);
    }

    /// Specify search limits, where currently `name` can be
    /// `"conflicts"`, `"decisions"`, `"preprocessing"`, `"localsearch"`
    /// (and `"ticks"`).
    ///
    /// The first two limits are unbounded by default.  Thus using a
    /// negative limit for conflicts or decisions switches back to the
    /// default of unlimited search (for that particular limit).  The
    /// preprocessing limit determines the number of preprocessing rounds,
    /// which is zero by default.  Similarly, the local search limit
    /// determines the number of local search rounds (zero by default).
    ///
    /// As with `set`, the return value denotes whether the limit `name` is
    /// valid.  These limits are only valid for the next `solve` or
    /// `simplify` call and reset to their default after `solve` returns
    /// (as well as overwritten and reset during calls to `simplify` and
    /// `lookahead`).  We actually also have an internal `"terminate"`
    /// limit which however should only be used for testing and debugging.
    ///
    /// `require (READY)`, `ensure (READY)`.
    pub fn limit(&mut self, arg: &str, val: i32) -> bool {
        const F: &str = "bool CaDiCaL::Solver::limit(const char *, int)";
        self.trace_si("limit", arg, val);
        self.require_valid_state(F);
        let res = self.internal().limit(arg, val);
        self.log_end_sib("limit", arg, val, res);
        res
    }

    /// Determine whether `arg` is a valid limit name (see
    /// [`Solver::limit`]).
    pub fn is_valid_limit(&mut self, arg: &str) -> bool {
        Internal::is_valid_limit(arg)
    }

    /// Set the default verbose message prefix (default `"c "`).
    ///
    /// `require (VALID | SOLVING)`.
    pub fn prefix(&mut self, str: &str) {
        const F: &str = "void CaDiCaL::Solver::prefix(const char *)";
        self.log_begin_s("prefix", str);
        self.require_valid_or_solving_state(F);
        self.internal().prefix = str.to_string();
        self.log_end_s("prefix", str);
    }

    /// Determine whether `name` is a valid configuration.
    pub fn is_valid_configuration(name: &str) -> bool {
        Config::has(name)
    }

    /// Overwrite (some) options with the forced values of the
    /// configuration.  The result is `true` iff the `name` is a valid
    /// configuration.
    ///
    /// `require (CONFIGURING)`, `ensure (CONFIGURING)`.
    pub fn configure(&mut self, name: &str) -> bool {
        const F: &str = "bool CaDiCaL::Solver::configure(const char *)";
        self.trace_s("configure", name);
        self.log_begin_s("configure", name);
        self.require_valid_state(F);
        require!(
            F,
            FILE,
            self.state() == CONFIGURING,
            "can only set configuration '{}' right after initialization",
            name
        );
        let res = Config::set(&mut self.internal().opts, name);
        self.log_end_sb("configure", name, res);
        res
    }

    /*===== IPASIR BEGIN =================================================*/

    /// Add valid literal to clause or zero to terminate clause.
    ///
    /// `require (VALID)` (recall `VALID = READY | ADDING`),
    /// `if (lit) ensure (ADDING)` (and thus VALID but not READY),
    /// `if (!lit) ensure (STEADY)` (and thus READY).
    pub fn add(&mut self, lit: i32) {
        const F: &str = "void CaDiCaL::Solver::add(int)";
        self.trace_i("add", lit);
        self.require_valid_state(F);
        if lit != 0 {
            if self.internal().opts.factor != 0 && self.internal().opts.factorcheck == 1 {
                require!(
                    F,
                    FILE,
                    lit.abs() <= self.external().max_var,
                    "adding literal '{}' with undeclared variable '{}' (checking that user variables are declared explicitly failed as both 'factor' and 'factorcheck' are enabled)",
                    lit,
                    lit.abs()
                );
            }
            if self.internal().opts.factorcheck == 2 {
                require!(
                    F,
                    FILE,
                    lit.abs() <= self.external().max_var,
                    "adding literal '{}' with undeclared variable '{}' (checking that user variables are declared explicitly failed as 'factorcheck == 2' even if 'factor' is disabled)",
                    lit,
                    lit.abs()
                );
            }
        }
        if lit != 0 {
            self.require_valid_lit(F, lit);
        }
        self.transition_to_steady_state();
        self.external().add(lit);
        self.adding_clause = lit != 0;
        if self.adding_clause {
            state!(self, ADDING);
        } else if !self.adding_constraint {
            state!(self, STEADY);
        }
        self.log_end_i("add", lit);
    }

    /// Add unit clause (C++ overload `clause (int)`).
    ///
    /// `require (VALID)`, `ensure (STEADY)`.
    pub fn clause1(&mut self, a: i32) {
        const F: &str = "void CaDiCaL::Solver::clause(int)";
        self.require_valid_lit(F, a);
        self.add(a);
        self.add(0);
    }

    /// Add binary clause (C++ overload `clause (int, int)`).
    ///
    /// `require (VALID)`, `ensure (STEADY)`.
    pub fn clause2(&mut self, a: i32, b: i32) {
        const F: &str = "void CaDiCaL::Solver::clause(int, int)";
        self.require_valid_lit(F, a);
        self.require_valid_lit(F, b);
        self.add(a);
        self.add(b);
        self.add(0);
    }

    /// Add ternary clause (C++ overload `clause (int, int, int)`).
    ///
    /// `require (VALID)`, `ensure (STEADY)`.
    pub fn clause3(&mut self, a: i32, b: i32, c: i32) {
        const F: &str = "void CaDiCaL::Solver::clause(int, int, int)";
        self.require_valid_lit(F, a);
        self.require_valid_lit(F, b);
        self.require_valid_lit(F, c);
        self.add(a);
        self.add(b);
        self.add(c);
        self.add(0);
    }

    /// Add quaternary clause (C++ overload `clause (int, int, int, int)`).
    ///
    /// `require (VALID)`, `ensure (STEADY)`.
    pub fn clause4(&mut self, a: i32, b: i32, c: i32, d: i32) {
        const F: &str = "void CaDiCaL::Solver::clause(int, int, int, int)";
        self.require_valid_lit(F, a);
        self.require_valid_lit(F, b);
        self.require_valid_lit(F, c);
        self.require_valid_lit(F, d);
        self.add(a);
        self.add(b);
        self.add(c);
        self.add(d);
        self.add(0);
    }

    /// Add quinternary clause (C++ overload
    /// `clause (int, int, int, int, int)`).
    ///
    /// `require (VALID)`, `ensure (STEADY)`.
    pub fn clause5(&mut self, a: i32, b: i32, c: i32, d: i32, e: i32) {
        const F: &str = "void CaDiCaL::Solver::clause(int, int, int, int, int)";
        self.require_valid_lit(F, a);
        self.require_valid_lit(F, b);
        self.require_valid_lit(F, c);
        self.require_valid_lit(F, d);
        self.require_valid_lit(F, e);
        self.add(a);
        self.add(b);
        self.add(c);
        self.add(d);
        self.add(e);
        self.add(0);
    }

    /// Add literal array as clause (C++ overload
    /// `clause (const int *, size_t)`).  The literals must all be valid
    /// (non-zero and different from `i32::MIN`).
    ///
    /// `require (VALID)`, `ensure (STEADY)`.
    pub fn clause_array(&mut self, lits: &[i32]) {
        const F: &str = "void CaDiCaL::Solver::clause(const int *, size_t)";
        // 'REQUIRE (!size || lits, "first argument 'lits' zero while second
        // argument 'size' not")' holds trivially for a slice.
        for &lit in lits {
            self.require_valid_lit(F, lit);
            self.add(lit);
        }
        self.add(0);
    }

    /// Add literal vector as clause (C++ overload
    /// `clause (const std::vector<int> &)`).  The literals must all be
    /// valid (non-zero and different from `i32::MIN`).
    ///
    /// `require (VALID)`, `ensure (STEADY)`.
    pub fn clause(&mut self, lits: &[i32]) {
        const F: &str = "void CaDiCaL::Solver::clause(const std::vector<int> &)";
        for &lit in lits {
            self.require_valid_lit(F, lit);
            self.add(lit);
        }
        self.add(0);
    }

    /// This function can be used to check if the formula is already
    /// inconsistent (contains the empty clause or was proven to be
    /// root-level unsatisfiable).
    pub fn inconsistent(&mut self) -> bool {
        self.internal().unsat
    }

    /// Adds a literal to the constraint clause.  Same functionality as
    /// `add` but the clause only exists for the next call to solve (same
    /// lifetime as assumptions).  Only one constraint may exists at a
    /// time.  A new constraint replaces the old.  The main application of
    /// this functionality is the model checking algorithm IC3.  See our
    /// FMCAD'21 paper \[FroleyksBiere-FMCAD'19\] for more details.
    ///
    /// Add valid literal to the constraint clause or zero to terminate it.
    ///
    /// `require (VALID)`, `if (lit) ensure (ADDING)`,
    /// `if (!lit && !adding_clause) ensure (STEADY)`.
    pub fn constrain(&mut self, lit: i32) {
        const F: &str = "void CaDiCaL::Solver::constrain(int)";
        self.trace_i("constrain", lit);
        self.require_valid_state(F);
        if lit != 0 {
            self.require_valid_lit(F, lit);
        }
        self.transition_to_steady_state();
        self.external().constrain(lit);
        self.adding_constraint = lit != 0;
        if self.adding_constraint {
            state!(self, ADDING);
        } else if !self.adding_clause {
            state!(self, STEADY);
        }
        self.log_end_i("constrain", lit);
    }

    /// Assume valid non zero literal for next call to `solve`.  These
    /// assumptions are reset after the call to `solve` as well as after
    /// returning from `simplify` and `lookahead`.
    ///
    /// `require (READY)`, `ensure (STEADY)`.
    pub fn assume(&mut self, lit: i32) {
        const F: &str = "void CaDiCaL::Solver::assume(int)";
        self.trace_i("assume", lit);
        self.require_valid_state(F);
        self.require_valid_lit(F, lit);
        self.transition_to_steady_state();
        self.external().assume(lit);
        self.log_end_i("assume", lit);
    }

    /// This function determines a good splitting literal.  The result can
    /// be zero if the formula is proven to be satisfiable or
    /// unsatisfiable.  This can then be checked by `state ()`.  If the
    /// formula is empty and the function is not able to determine
    /// satisfiability also zero is returned but the state remains steady.
    ///
    /// `require (READY)`, `ensure (INCONCLUSIVE | SATISFIED | UNSATISFIED)`.
    pub fn lookahead(&mut self) -> i32 {
        const F: &str = "int CaDiCaL::Solver::lookahead()";
        self.trace0("lookahead");
        self.require_valid_or_solving_state(F);
        self.transition_to_steady_state();
        let lit = self.external().lookahead();
        self.log_end_i("lookahead", lit);
        lit
    }

    /// Generate cubes by lookahead up to the given `depth` (`min_depth`
    /// defaults to `0` in C++).  Returns the status (`10`, `20` or `0`) and
    /// the cubes.
    pub fn generate_cubes(&mut self, depth: i32, min_depth: i32) -> CubesWithStatus {
        const F: &str = "Solver::CubesWithStatus CaDiCaL::Solver::generate_cubes(int, int)";
        self.trace0("lookahead_cubes");
        self.require_valid_or_solving_state(F);
        let cubes = self.external().generate_cubes(depth, min_depth);
        self.trace0("lookahead_cubes");

        CubesWithStatus { status: cubes.status, cubes: cubes.cubes }
    }

    /// Reset the assumptions (and the conclusion of an incremental proof).
    ///
    /// `require (READY)`, `ensure (STEADY)`.
    pub fn reset_assumptions(&mut self) {
        const F: &str = "void CaDiCaL::Solver::reset_assumptions()";
        self.trace0("reset_assumptions");
        self.require_valid_state(F);
        self.transition_to_steady_state();
        self.external().reset_assumptions();
        self.external().reset_concluded();
        self.log_end("reset_assumptions");
    }

    /// Reset the constraint (and the conclusion of an incremental proof).
    ///
    /// `require (READY)`, `ensure (STEADY)`.
    pub fn reset_constraint(&mut self) {
        const F: &str = "void CaDiCaL::Solver::reset_constraint()";
        self.trace0("reset_constraint");
        self.require_valid_state(F);
        self.transition_to_steady_state();
        self.external().reset_constraint();
        self.external().reset_concluded();
        self.log_end("reset_constraint");
    }

    /*--------------------------------------------------------------------*/

    /// Collects a subset of those literals that are implied by unit
    /// propagation by assuming the currently defined (potentially empty)
    /// set of assumptions.  In case unit propagation over the defined set
    /// of assumptions (or over the clause database on its own) leads to
    /// conflict, the function returns `20`.  In most other case, the
    /// function returns `0` (indicating 'UNKNOWN') and [`Solver::implied`]
    /// lists the non-conflicting current value of the trail.  If ILB is
    /// off, in the rare case where no decision was needed and propagation
    /// assigned all literals, then the implied literals will contain all
    /// assigned literals, which is a model.  If ILB is on, propagate might
    /// also return SAT.  In this case, the implied literals will still only
    /// contain the implied literals.
    ///
    /// Returns `0` = UNKNOWN, `10` = SATISFIABLE, `20` = UNSATISFIABLE.
    /// The 'UNKNOWN' result means that unit propagation did not lead to a
    /// conflict nor to a complete assignment, or limit reached or
    /// interrupted through `terminate`.
    ///
    /// `require (READY)`, `ensure (INCONCLUSIVE | SATISFIED | UNSATISFIED)`.
    pub fn propagate(&mut self) -> i32 {
        const F: &str = "int CaDiCaL::Solver::propagate()";
        self.trace0("propagate_assumptions");
        self.require_valid_state(F);
        self.transition_to_steady_state();
        let res = self.external().propagate_assumptions();
        if TRACING_NB_LIDRUP_ENV_VAR_METHOD.load(Relaxed) {
            self.flush_proof_trace(true);
        }
        self.log_returns_i("propagate_assumptions", res);
        if res == 10 {
            state!(self, SATISFIED);
        } else if res == 20 {
            state!(self, UNSATISFIED);
        } else {
            state!(self, INCONCLUSIVE);
        }
        res
    }

    /// See the comment for [`Solver::propagate`] above: stores the implied
    /// literals in `entrailed`.
    ///
    /// `require (INCONCLUSIVE)`, `ensure (INCONCLUSIVE)`.
    pub fn implied(&mut self, entrailed: &mut Vec<i32>) {
        const F: &str = "void CaDiCaL::Solver::implied(std::vector<int> &)";
        self.trace0("implied");
        self.require_valid_state(F);
        require!(
            F,
            FILE,
            self.state() == INCONCLUSIVE || self.state() == SATISFIED,
            "can only get implied literals only in unknown or satisfied state"
        );
        self.external().conclude_unknown();
        self.external().implied(entrailed);
        if TRACING_NB_LIDRUP_ENV_VAR_METHOD.load(Relaxed) {
            self.flush_proof_trace(true);
        }
        self.log_returns_i("implied", entrailed.len() as i32);
    }

    /*--------------------------------------------------------------------*/

    /// Factored out common code for `solve`, `simplify` and `lookahead`.
    #[doc(hidden)]
    pub fn call_external_solve_and_check_results(&mut self, preprocess_only: bool) -> i32 {
        self.transition_to_steady_state();
        debug_assert!(self.state() & READY != 0);
        state!(self, SOLVING);
        let res = self.external().solve(preprocess_only);
        if res == 10 {
            state!(self, SATISFIED);
        } else if res == 20 {
            state!(self, UNSATISFIED);
        } else {
            state!(self, INCONCLUSIVE);
        }
        res
    }

    /// Try to solve the current formula.  Returns
    ///
    /// * `0` = UNKNOWN (limit reached or interrupted through `terminate`),
    /// * `10` = SATISFIABLE,
    /// * `20` = UNSATISFIABLE.
    ///
    /// Note, that while in this call the solver actually transitions to
    /// state [`SOLVING`], which however is only visible from a different
    /// context, i.e., from a different thread or from a signal handler.
    /// Only right before returning from this call it goes into a 'READY'
    /// state.  See also [`Solver::solve_result`].
    ///
    /// `require (READY)`, `ensure (INCONCLUSIVE | SATISFIED | UNSATISFIED)`.
    pub fn solve(&mut self) -> i32 {
        const F: &str = "int CaDiCaL::Solver::solve()";
        self.trace0("solve");
        self.require_ready_state(F);
        let res = self.call_external_solve_and_check_results(false);
        self.log_returns_i("solve", res);
        if TRACING_NB_LIDRUP_ENV_VAR_METHOD.load(Relaxed) {
            self.flush_proof_trace(true);
        }
        res
    }

    /// This function executes the given number of preprocessing rounds
    /// (`rounds` defaults to `3` in C++).  It is similar to `solve` with
    /// `limit ("preprocessing", rounds)` except that no CDCL nor local
    /// search, nor lucky phases are executed.  The result values are also
    /// the same: `0` = UNKNOWN, `10` = SATISFIABLE, `20` = UNSATISFIABLE.
    ///
    /// As `solve` it resets current assumptions and limits before
    /// returning.  The numbers of rounds should not be negative.  If the
    /// number of rounds is zero only clauses are restored (if necessary)
    /// and top level unit propagation is performed, which both take some
    /// time.
    ///
    /// `require (READY)`, `ensure (INCONCLUSIVE | SATISFIED | UNSATISFIED)`.
    pub fn simplify(&mut self, rounds: i32) -> i32 {
        const F: &str = "int CaDiCaL::Solver::simplify(int)";
        self.trace_i("simplify", rounds);
        self.require_ready_state(F);
        require!(F, FILE, rounds >= 0, "negative number of simplification rounds '{}'", rounds);
        self.internal().limit("preprocessing", rounds);
        let lucky = self.internal().opts.lucky;
        self.internal().opts.lucky = 0;
        let res = self.call_external_solve_and_check_results(true);
        self.internal().opts.lucky = lucky;
        self.log_returns_ii("simplify", rounds, res);
        res
    }

    /*--------------------------------------------------------------------*/

    /// Get the value of a valid non-zero literal.  This follows the IPASIR
    /// semantics which says to return `lit` if `lit` is assigned to 'true'
    /// and `-lit` if `lit` is assigned to 'false'.  This has the
    /// consequence that the returned literal is always assigned to 'true'
    /// and thus might be a bit confusing.  To avoid the headache of these
    /// semantics (which we unfortunately should follow to be compatible
    /// with IPASIR) the user can simply use positive variable indices
    /// instead of literals.  Then the returned integer is negative if the
    /// variable is assigned to 'false' and positive it is assigned to
    /// 'true'.  See also [`Solver::value`] and [`Solver::model`].
    ///
    /// This is C++ `val (lit)` (with the default
    /// `use_default_value_for_declared_but_not_used_variable = true`), see
    /// [`Solver::val_with`] for the full form.
    ///
    /// `require (SATISFIED)`, `ensure (SATISFIED)`.
    #[inline]
    pub fn val(&mut self, lit: i32) -> i32 {
        self.val_with(lit, true)
    }

    /// Full form of [`Solver::val`] (C++ `val (int, bool)`).  If
    /// `use_default_value_for_declared_but_not_used_variable` is `false`
    /// the literal must belong to a variable which was actually used (not
    /// only declared).
    ///
    /// `require (SATISFIED)`, `ensure (SATISFIED)`.
    pub fn val_with(&mut self, lit: i32, use_default_value_for_declared_but_not_used_variable: bool) -> i32 {
        const F: &str = "int CaDiCaL::Solver::val(int, bool)";
        let use_default = use_default_value_for_declared_but_not_used_variable;
        self.log_begin_ii("val", lit, use_default as i32);
        self.require_valid_state(F);
        self.require_valid_lit(F, lit);
        require!(F, FILE, self.state() == SATISFIED, "can only get value in satisfied state");
        if !use_default {
            require!(F, FILE, lit < self.external().max_var, "lit of undeclare variable");
        }
        if !self.external().extended {
            self.external().extend();
        }
        self.external().conclude_sat();
        let res = self.external().ival(lit);
        self.log_returns_iii("val", lit, use_default as i32, res);
        debug_assert!(self.state() == SATISFIED);
        debug_assert!(res == lit || res == -lit);
        res
    }

    /// Try to flip the value of the given literal without falsifying the
    /// formula.  Returns `true` if this was successful.  Otherwise the
    /// model is not changed and `false` is returned.  If a literal was
    /// eliminated or substituted flipping will fail on that literal and in
    /// particular the solver will not taint it nor restore any clauses.
    ///
    /// The `flip` function can only flip the value of a variables not
    /// acting as witness on the reconstruction stack.
    ///
    /// As a side effect of calling this function first all assigned
    /// variables are propagated again without using blocking literal.
    /// Thus the first call to this function after obtaining a model adds a
    /// substantial overhead.  Subsequent calls will not need to properly
    /// propagate again.
    ///
    /// Furthermore if the reconstruction stack is non-empty and has been
    /// traversed to reconstruct a full extended model for eliminated
    /// variables (and to satisfy removed blocked clauses), the values of
    /// these witness variables obtained via `val` before become invalid.
    /// The user thus will need to call `val` again after calling `flip`
    /// which will trigger then a traversal of the reconstruction stack.
    ///
    /// So try to avoid mixing `flip` and `val` (for efficiency only).
    /// Further, this functionality is currently not supported in the
    /// presence of an external propagator.
    ///
    /// `require (SATISFIED)`, `ensure (SATISFIED)`.
    pub fn flip(&mut self, lit: i32) -> bool {
        const F: &str = "bool CaDiCaL::Solver::flip(int)";
        self.trace_i("flip", lit);
        self.require_valid_state(F);
        self.require_valid_lit(F, lit);
        require!(F, FILE, self.state() == SATISFIED, "can only flip value in satisfied state");
        require!(
            F,
            FILE,
            self.external().propagator.is_none(),
            "can only flip when no external propagator is present"
        );
        let res = self.external().flip(lit);
        self.log_returns_ib("flip", lit, res);
        debug_assert!(self.state() == SATISFIED);
        res
    }

    /// Same as `flip` without actually flipping it.  This functionality is
    /// currently not supported in the presence of an external propagator.
    ///
    /// `require (SATISFIED)`, `ensure (SATISFIED)`.
    pub fn flippable(&mut self, lit: i32) -> bool {
        const F: &str = "bool CaDiCaL::Solver::flippable(int)";
        self.trace_i("flippable", lit);
        self.require_valid_state(F);
        self.require_valid_lit(F, lit);
        require!(F, FILE, self.state() == SATISFIED, "can only flip value in satisfied state");
        require!(
            F,
            FILE,
            self.external().propagator.is_none(),
            "can only flip when no external propagator is present"
        );
        let res = self.external().flippable(lit);
        self.log_returns_ib("flippable", lit, res);
        debug_assert!(self.state() == SATISFIED);
        res
    }

    /// Determine whether the valid non-zero literal is in the core.
    /// Returns `true` if the literal is in the core and `false` otherwise.
    /// Note that the core does not have to be minimal.
    ///
    /// `require (UNSATISFIED)`, `ensure (UNSATISFIED)`.
    pub fn failed(&mut self, lit: i32) -> bool {
        const F: &str = "bool CaDiCaL::Solver::failed(int)";
        self.trace_i("failed", lit);
        self.require_valid_state(F);
        self.require_valid_lit(F, lit);
        require!(
            F,
            FILE,
            self.state() == UNSATISFIED,
            "can only get failed assumptions in unsatisfied state"
        );
        let res = self.external().failed(lit);
        self.log_returns_ib("failed", lit, res);
        debug_assert!(self.state() == UNSATISFIED);
        res
    }

    /// Determine whether the constraint was used to proof the
    /// unsatisfiability.  Note that the formula might still be
    /// unsatisfiable without the constraint.
    ///
    /// `require (UNSATISFIED)`, `ensure (UNSATISFIED)`.
    pub fn constraint_failed(&mut self) -> bool {
        const F: &str = "bool CaDiCaL::Solver::constraint_failed()";
        self.trace0("constraint_failed");
        self.require_valid_state(F);
        require!(
            F,
            FILE,
            self.state() == UNSATISFIED,
            "can only determine if constraint failed in unsatisfied state"
        );
        let res = self.external().failed_constraint();
        self.log_returns_b("constraint_failed", res);
        debug_assert!(self.state() == UNSATISFIED);
        res
    }

    /// Root level assigned variables can be queried with this function.
    /// It returns `1` if the literal is implied by the formula, `-1` if its
    /// negation is implied, or `0` if this is unclear at this point.
    ///
    /// `require (VALID)`, `ensure (VALID)`.
    pub fn fixed(&self, lit: i32) -> i32 {
        const F: &str = "int CaDiCaL::Solver::fixed(int) const";
        self.trace_i("fixed", lit);
        self.require_valid_state(F);
        self.require_valid_lit(F, lit);
        let res = self.external().fixed(lit);
        self.log_returns_ii("fixed", lit, res);
        res
    }

    /// Force the default decision phase of a variable to a certain value.
    ///
    /// `require (VALID | SOLVING)`.
    pub fn phase(&mut self, lit: i32) {
        const F: &str = "void CaDiCaL::Solver::phase(int)";
        self.trace_i("phase", lit);
        self.require_valid_or_solving_state(F);
        self.require_valid_lit(F, lit);
        self.external().phase(lit);
        self.log_end_i("phase", lit);
    }

    /// Remove a forced default decision phase (see [`Solver::phase`]).
    ///
    /// `require (VALID | SOLVING)`.
    pub fn unphase(&mut self, lit: i32) {
        const F: &str = "void CaDiCaL::Solver::unphase(int)";
        self.trace_i("unphase", lit);
        self.require_valid_or_solving_state(F);
        self.require_valid_lit(F, lit);
        self.external().unphase(lit);
        self.log_end_i("unphase", lit);
    }

    /*--------------------------------------------------------------------*/

    /// Force termination of `solve` asynchronously (see also
    /// [`Solver::termination_handle`] for use from another thread).
    ///
    /// `require (SOLVING | READY)`, `ensure (INCONCLUSIVE)` (actually not
    /// immediately, i.e., synchronously).
    pub fn terminate(&mut self) {
        const F: &str = "void CaDiCaL::Solver::terminate()";
        self.log_begin("terminate");
        self.require_valid_or_solving_state(F);
        self.external().terminate();
        self.log_end("terminate");
    }

    /// Add call-back which is checked regularly for termination.  There
    /// can only be one terminator connected.  If a second one is added the
    /// first one is implicitly disconnected (and dropped).
    ///
    /// `require (VALID)`, `ensure (VALID)`.
    pub fn connect_terminator(&mut self, terminator: Box<dyn Terminator>) {
        const F: &str = "void CaDiCaL::Solver::connect_terminator(Terminator *)";
        self.log_begin("connect_terminator");
        self.require_valid_state(F);
        // 'REQUIRE (terminator, "can not connect zero terminator")' holds
        // trivially for a 'Box'.
        #[cfg(feature = "logging")]
        {
            if self.external().terminator.is_some() {
                log!(self.internal, "connecting new terminator (disconnecting previous one)");
            } else {
                log!(self.internal, "connecting new terminator (no previous one)");
            }
        }
        self.external().terminator = Some(terminator);
        self.log_end("connect_terminator");
    }

    /// Disconnect the terminator.  Returns the previously connected
    /// terminator (if any).
    ///
    /// `require (VALID)`, `ensure (VALID)`.
    pub fn disconnect_terminator(&mut self) -> Option<Box<dyn Terminator>> {
        const F: &str = "void CaDiCaL::Solver::disconnect_terminator()";
        self.log_begin("disconnect_terminator");
        self.require_valid_state(F);
        #[cfg(feature = "logging")]
        {
            if self.external().terminator.is_some() {
                log!(self.internal, "disconnecting previous terminator");
            } else {
                log!(self.internal, "ignoring to disconnect terminator (no previous one)");
            }
        }
        let res = self.external().terminator.take();
        self.log_end("disconnect_terminator");
        res
    }

    /*--------------------------------------------------------------------*/

    /// Add call-back which allows to export learned clauses (replaces a
    /// previously connected learner, which is dropped).
    ///
    /// `require (VALID)`, `ensure (VALID)`.
    pub fn connect_learner(&mut self, learner: Box<dyn Learner>) {
        const F: &str = "void CaDiCaL::Solver::connect_learner(Learner *)";
        self.log_begin("connect_learner");
        self.require_valid_state(F);
        #[cfg(feature = "logging")]
        {
            if self.external().learner.is_some() {
                log!(self.internal, "connecting new learner (disconnecting previous one)");
            } else {
                log!(self.internal, "connecting new learner (no previous one)");
            }
        }
        self.external().learner = Some(learner);
        self.log_end("connect_learner");
    }

    /// Disconnect the learner.  Returns the previously connected learner
    /// (if any).
    ///
    /// `require (VALID)`, `ensure (VALID)`.
    pub fn disconnect_learner(&mut self) -> Option<Box<dyn Learner>> {
        const F: &str = "void CaDiCaL::Solver::disconnect_learner()";
        self.log_begin("disconnect_learner");
        self.require_valid_state(F);
        #[cfg(feature = "logging")]
        {
            if self.external().learner.is_some() {
                log!(self.internal, "disconnecting previous learner");
            } else {
                log!(self.internal, "ignoring to disconnect learner (no previous one)");
            }
        }
        let res = self.external().learner.take();
        self.log_end("disconnect_learner");
        res
    }

    /*===== IPASIR END ===================================================*/

    /// Add call-back which allows to observe when a variable is fixed
    /// (replaces a previously connected listener, which is dropped).
    ///
    /// Listeners are treated as real-time listeners, thus previously found
    /// fixed assignments are not sent out.
    ///
    /// `require (VALID)`, `ensure (VALID)`.
    pub fn connect_fixed_listener(&mut self, fixed_listener: Box<dyn FixedAssignmentListener>) {
        const F: &str =
            "void CaDiCaL::Solver::connect_fixed_listener(FixedAssignmentListener *)";
        self.log_begin("connect_fixed_listener");
        self.require_valid_state(F);

        #[cfg(feature = "logging")]
        {
            if self.external().fixed_listener.is_some() {
                log!(
                    self.internal,
                    "connecting new listener of fixed assignments (disconnecting previous one)"
                );
            } else {
                log!(self.internal, "connecting new listener of fixed assigments (no previous one)");
            }
        }
        if self.external().fixed_listener.is_some() {
            self.disconnect_fixed_listener();
        }
        self.external().fixed_listener = Some(fixed_listener);
        // Listeners are treated as real-time listeners, thus previously
        // found fixed assignments are not sent out (would be rather
        // expensive to recover it retrospect, see
        // external_propagate.cpp/get_fixed_literals () function).
        self.log_end("connect_fixed_listener");
    }

    /// Disconnect the listener of fixed assignments.  Returns the
    /// previously connected listener (if any).
    ///
    /// `require (VALID)`, `ensure (VALID)`.
    pub fn disconnect_fixed_listener(&mut self) -> Option<Box<dyn FixedAssignmentListener>> {
        const F: &str = "void CaDiCaL::Solver::disconnect_fixed_listener()";
        self.log_begin("disconnect_fixed_listener");
        self.require_valid_state(F);
        #[cfg(feature = "logging")]
        {
            if self.external().fixed_listener.is_some() {
                log!(self.internal, "disconnecting previous listener of fixed assignments");
            } else {
                log!(
                    self.internal,
                    "ignoring to disconnect listener of fixed assignments (no previous one)"
                );
            }
        }
        let res = self.external().fixed_listener.take();
        self.log_end("disconnect_fixed_listener");
        res
    }

    /*===== IPASIR-UP BEGIN ==============================================*/

    /// Add call-back which allows to learn, propagate and backtrack based
    /// on external constraints.  Only one external propagator can be
    /// connected and after connection every related variable must be
    /// 'observed' (use [`Solver::add_observed_var`]).  Disconnection of
    /// the external propagator resets all the observed variables.
    ///
    /// `require (VALID)`, `ensure (VALID)`.
    pub fn connect_external_propagator(&mut self, propagator: Box<dyn ExternalPropagator>) {
        const F: &str = "void CaDiCaL::Solver::connect_external_propagator(ExternalPropagator *)";
        self.log_begin("connect_external_propagator");
        self.require_valid_state(F);
        // 'REQUIRE (propagator, "can not connect zero propagator")' holds
        // trivially for a 'Box'.
        require!(
            F,
            FILE,
            self.external().propagator.is_none(),
            "can not connect more than one propagator"
        );

        if self.external().propagator.is_some() {
            self.disconnect_external_propagator();
        }

        self.external().propagator = Some(propagator);
        self.internal().connect_propagator();
        self.internal().external_prop = true;
        let is_lazy = self.external().propagator.as_ref().unwrap().is_lazy();
        self.internal().external_prop_is_lazy = is_lazy;
        self.log_end("connect_external_propagator");
    }

    /// Disconnect the external propagator (resets all observed
    /// variables).  Returns the previously connected propagator.
    ///
    /// `require (VALID)`, `ensure (VALID)`.
    pub fn disconnect_external_propagator(&mut self) -> Option<Box<dyn ExternalPropagator>> {
        const F: &str = "void CaDiCaL::Solver::disconnect_external_propagator()";
        self.log_begin("disconnect_external_propagator");
        self.require_valid_state(F);
        require!(
            F,
            FILE,
            self.external().propagator.is_some(),
            "can not disconnect propagator without a connected propagator"
        );
        self.external().reset_observed_vars();

        let res = self.external().propagator.take();
        self.internal().set_changed_val();
        self.internal().external_prop = false;
        self.internal().external_prop_is_lazy = true;
        self.internal().notified = 0;
        self.log_end("disconnect_external_propagator");
        res
    }

    /// Mark as 'observed' those variables that are relevant to the
    /// external propagator.  External propagation, clause addition during
    /// search and notifications are all over these observed variables.  A
    /// variable can not be observed without having an external propagator
    /// already connected.  Observed variables are "frozen" internally, and
    /// so inprocessing will not consider them as candidates for
    /// elimination.  An observed variable is allowed to be a fresh variable
    /// and it can be added also during solving.
    ///
    /// `require (VALID_OR_SOLVING)`, `ensure (VALID_OR_SOLVING)`.
    pub fn add_observed_var(&mut self, idx: i32) {
        const F: &str = "void CaDiCaL::Solver::add_observed_var(int)";
        self.trace_i("observe", idx);
        self.require_valid_or_solving_state(F);
        self.require_valid_lit(F, idx);
        require!(
            F,
            FILE,
            self.external().propagator.is_some(),
            "can not observe variables without a connected propagator"
        );
        self.external().add_observed_var(idx);
        self.log_end_i("observe", idx);
    }

    /// Removes the 'observed' flag from the given variable.  A variable
    /// can be set unobserved only when it is unassigned, in order to
    /// guarantee that no yet unexplained external propagation involves it.
    ///
    /// `require (VALID_OR_SOLVING)`, `ensure (VALID_OR_SOLVING)`.
    pub fn remove_observed_var(&mut self, idx: i32) {
        const F: &str = "void CaDiCaL::Solver::remove_observed_var(int)";
        self.trace_i("unobserve", idx);
        self.require_valid_or_solving_state(F);
        self.require_valid_lit(F, idx);
        require!(
            F,
            FILE,
            self.external().propagator.is_some(),
            "can not unobserve variables without a connected propagator"
        );
        self.external().remove_observed_var(idx);
        self.log_end_i("unobserve", idx);
    }

    /// Removes all the 'observed' flags from the variables.  Disconnecting
    /// the propagator invokes this step as well.
    ///
    /// `require (VALID)`, `ensure (VALID)`.
    pub fn reset_observed_vars(&mut self) {
        const F: &str = "void CaDiCaL::Solver::reset_observed_vars()";
        self.trace0("reset_observed_vars");
        self.require_valid_or_solving_state(F);
        require!(
            F,
            FILE,
            self.external().propagator.is_some(),
            "can not reset observed variables without a connected propagator"
        );
        self.external().reset_observed_vars();
        self.log_end("reset_observed_vars");
    }

    /*===== IPASIR-UP END ================================================*/

    /// Number of active variables.  Variables become active if a clause is
    /// added with it.  They become inactive if they are eliminated or
    /// fixed at the root level.
    ///
    /// `require (VALID)`, `ensure (VALID)`.
    pub fn active(&self) -> i32 {
        const F: &str = "int CaDiCaL::Solver::active() const";
        self.trace0("active");
        self.require_valid_state(F);
        let res = self.internal().active_count();
        self.log_returns_i("active", res);
        res
    }

    /// Number of active redundant clauses.  Redundant clauses are reduced
    /// regularly and thus this function is less useful.
    ///
    /// `require (VALID)`, `ensure (VALID)`.
    pub fn redundant(&self) -> i64 {
        const F: &str = "int64_t CaDiCaL::Solver::redundant() const";
        self.trace0("redundant");
        self.require_valid_state(F);
        let res = self.internal().redundant();
        self.log_returns_i64("redundant", res);
        res
    }

    /// Number of active irredundant clauses.  Clauses become inactive if
    /// they are satisfied, subsumed, eliminated.
    ///
    /// `require (VALID)`, `ensure (VALID)`.
    pub fn irredundant(&self) -> i64 {
        const F: &str = "int64_t CaDiCaL::Solver::irredundant() const";
        self.trace0("irredundant");
        self.require_valid_state(F);
        let res = self.internal().irredundant();
        self.log_returns_i64("irredundant", res);
        res
    }

    /*--------------------------------------------------------------------*/

    /// Freeze a variable (reference counting).
    ///
    /// We have the following common reference counting functions, which
    /// avoid to restore clauses but require substantial user guidance.
    /// This was the only way to use inprocessing in incremental SAT
    /// solving in Lingeling (and before in MiniSAT's 'freeze' / 'thaw') and
    /// which did not use automatic clause restoring.  In general this is
    /// slower than restoring clauses and should not be used.
    ///
    /// In essence the user freezes variables which potentially are still
    /// needed in clauses added or assumptions used after the next `solve`
    /// call.  As in Lingeling you can freeze a variable multiple times, but
    /// then have to melt it the same number of times again in order to
    /// enable variable eliminating on it etc.  The arguments can be
    /// literals (negative indices) but conceptually variables are frozen.
    ///
    /// In the old way of doing things without restore you should not use a
    /// variable incrementally (in `add` or `assume`), which was used before
    /// and potentially could have been eliminated in a previous `solve`
    /// call.  This can lead to spurious satisfying assignment.  In order to
    /// check this API contract one can use the `checkfrozen` option.  This
    /// has the drawback that restoring clauses implicitly would fail with a
    /// fatal error message even if in principle the solver could just
    /// restore clauses.  Thus this option is disabled by default.
    ///
    /// See our SAT'19 paper \[FazekasBiereScholl-SAT'19\] for more details.
    ///
    /// `require (VALID)`, `ensure (VALID)`.
    pub fn freeze(&mut self, lit: i32) {
        const F: &str = "void CaDiCaL::Solver::freeze(int)";
        self.trace_i("freeze", lit);
        self.require_valid_state(F);
        self.require_valid_lit(F, lit);
        self.external().freeze(lit);
        self.log_end_i("freeze", lit);
    }

    /// Melt a frozen variable once (see [`Solver::freeze`]).  Also needs
    /// `require (frozen (lit))`.
    ///
    /// `require (VALID)`, `ensure (VALID)`.
    pub fn melt(&mut self, lit: i32) {
        const F: &str = "void CaDiCaL::Solver::melt(int)";
        self.trace_i("melt", lit);
        self.require_valid_state(F);
        self.require_valid_lit(F, lit);
        require!(
            F,
            FILE,
            self.external().frozen(lit),
            "can not melt completely melted literal '{}'",
            lit
        );
        self.external().melt(lit);
        self.log_end_i("melt", lit);
    }

    /// Is the variable of `lit` frozen (see [`Solver::freeze`])?
    ///
    /// `require (VALID)`, `ensure (VALID)`.
    pub fn frozen(&self, lit: i32) -> bool {
        const F: &str = "bool CaDiCaL::Solver::frozen(int) const";
        self.trace_i("frozen", lit);
        self.require_valid_state(F);
        self.require_valid_lit(F, lit);
        let res = self.external().frozen(lit);
        self.log_returns_ib("frozen", lit, res);
        res
    }

    /*--------------------------------------------------------------------*/

    /// Enables clausal proof tracing to an already opened C `FILE *` (with
    /// the given `name` used in messages) in the format selected by the
    /// options and returns `true` (C++ overload
    /// `trace_proof (FILE *, const char *)`).  Writing proofs has to be
    /// enabled before calling `solve`, `add` and `dimacs`, that is in state
    /// [`CONFIGURING`].  Otherwise only partial proofs would be written.
    ///
    /// `require (CONFIGURING)`, `ensure (CONFIGURING)`.
    pub fn trace_proof_file(&mut self, external_file: *mut libc::FILE, name: &str) -> bool {
        const F: &str = "bool CaDiCaL::Solver::trace_proof(FILE *, const char *)";
        self.trace_s("trace_proof", name);
        self.require_valid_state(F);
        require!(
            F,
            FILE,
            self.state() == CONFIGURING,
            "can only start proof tracing to '{}' right after initialization",
            name
        );
        let internal_file = File::write_fp(self.internal, external_file, name);
        debug_assert!(!internal_file.is_null());
        // SAFETY: 'File::write_fp' returns a freshly boxed 'File'.
        self.internal().trace(unsafe { Box::from_raw(internal_file) });
        self.log_returns_sb("trace_proof", name, true);
        true
    }

    /// Enables clausal proof tracing to the file at `path` (compressed if
    /// the path has a compression suffix and the helper is available) and
    /// returns `true` if successfully opened for writing.  Writing proofs
    /// has to be enabled before calling `solve`, `add` and `dimacs`, that
    /// is in state [`CONFIGURING`].  Otherwise only partial proofs would be
    /// written.
    ///
    /// `require (CONFIGURING)`, `ensure (CONFIGURING)`.
    pub fn trace_proof(&mut self, path: &str) -> bool {
        const F: &str = "bool CaDiCaL::Solver::trace_proof(const char *)";
        self.trace_s("trace_proof", path);
        self.require_valid_state(F);
        require!(
            F,
            FILE,
            self.state() == CONFIGURING,
            "can only start proof tracing to '{}' right after initialization",
            path
        );
        let internal_file = File::write(self.internal, path);
        let res = !internal_file.is_null();
        // C++ calls 'internal->trace (internal_file)' even if opening the
        // file failed (connecting a tracer with a zero file, which crashes
        // as soon as a proof line is written).  The Rust 'Internal::trace'
        // takes an owned file, so we only connect a tracer on success.
        if res {
            // SAFETY: 'File::write' returns a freshly boxed 'File'.
            self.internal().trace(unsafe { Box::from_raw(internal_file) });
        }
        self.log_returns_sb("trace_proof", path, res);
        res
    }

    /// Flushing the proof trace file eventually calls `fflush` on the
    /// actual file or pipe and thus if this function returns all the proof
    /// steps should have been written (with the same guarantees as
    /// `fflush`).
    ///
    /// The argument (`false` by default in C++) forces to print the number
    /// of addition and deletion steps in the proof even if the verbosity
    /// level is zero but not if quiet is set as well.  The default for the
    /// stand-alone solver is to print this information (in the 'closing
    /// proof' section) but for API usage of the library we want to stay
    /// silent unless explicitly requested or verbosity is non-zero (and as
    /// explained quiet is not set).
    ///
    /// This function can be called multiple times.
    ///
    /// `require (VALID)`, `ensure (VALID)`.
    pub fn flush_proof_trace(&mut self, print_statistics_unless_quiet: bool) {
        const F: &str = "void CaDiCaL::Solver::flush_proof_trace(bool)";
        self.trace0("flush_proof_trace");
        self.require_valid_state(F);
        require!(F, FILE, !self.internal().file_tracers.is_empty(), "proof is not traced");
        require!(
            F,
            FILE,
            !self.internal().file_tracers.last_mut().unwrap().closed(),
            "proof trace already closed"
        );
        self.internal().flush_trace(print_statistics_unless_quiet);
        self.log_end("flush_proof_trace");
    }

    /// Close proof trace early.  Similar to `flush` we allow the user to
    /// control with `print` (`false` by default in C++) in a more
    /// fine-grained way whether statistics about the size of the written
    /// proof file and if compressed on-the-fly the number of actual bytes
    /// written (including deflation percentage) are printed.  Before
    /// actually closing (or detaching in case of writing to `<stdout>`) we
    /// check whether `flush_proof_trace` was called since the last time a
    /// proof step (addition or deletion) was traced.  If this is not the
    /// case we would call `flush_proof_trace` with the same `print`
    /// argument.
    ///
    /// `require (VALID)`, `ensure (VALID)`.
    pub fn close_proof_trace(&mut self, print_statistics_unless_quiet: bool) {
        const F: &str = "void CaDiCaL::Solver::close_proof_trace(bool)";
        self.trace0("close_proof_trace");
        self.require_valid_state(F);
        require!(F, FILE, !self.internal().file_tracers.is_empty(), "proof is not traced");
        require!(
            F,
            FILE,
            !self.internal().file_tracers.last_mut().unwrap().closed(),
            "proof trace already closed"
        );
        self.internal().close_trace(print_statistics_unless_quiet);
        self.log_end("close_proof_trace");
    }

    /*--------------------------------------------------------------------*/

    /// Enables clausal proof tracing with or without antecedents using the
    /// [`Tracer`] interface defined in `tracer.rs`
    /// (`finalize_clauses` defaults to `false` in C++).  Returns the handle
    /// needed to disconnect the tracer again.
    ///
    /// `require (CONFIGURING)`, `ensure (CONFIGURING)`.
    pub fn connect_proof_tracer(
        &mut self,
        tracer: Box<dyn Tracer>,
        antecedents: bool,
        finalize_clauses: bool,
    ) -> TracerRef {
        const F: &str = "void CaDiCaL::Solver::connect_proof_tracer(Tracer *, bool, bool)";
        self.log_begin("connect proof tracer");
        self.require_valid_state(F);
        require!(
            F,
            FILE,
            self.state() == CONFIGURING,
            "can only start proof tracing to right after initialization"
        );
        let res = self.internal().connect_proof_tracer(tracer, antecedents, finalize_clauses);
        self.log_end("connect proof tracer");
        res
    }

    /// C++ overload for `InternalTracer *` (renamed, for internal use).
    /// `finalize_clauses` defaults to `false` in C++.
    ///
    /// `require (CONFIGURING)`, `ensure (CONFIGURING)`.
    pub fn connect_proof_tracer_internal(
        &mut self,
        tracer: Box<dyn InternalTracer>,
        antecedents: bool,
        finalize_clauses: bool,
    ) -> TracerRef {
        const F: &str = "void CaDiCaL::Solver::connect_proof_tracer(InternalTracer *, bool, bool)";
        self.log_begin("connect proof tracer");
        self.require_valid_state(F);
        require!(
            F,
            FILE,
            self.state() == CONFIGURING,
            "can only start proof tracing to right after initialization"
        );
        let res = self.internal().connect_proof_tracer_internal(tracer, antecedents, finalize_clauses);
        self.log_end("connect proof tracer");
        res
    }

    /// C++ overload for `StatTracer *` (renamed, for internal use).
    /// `finalize_clauses` defaults to `false` in C++.
    ///
    /// `require (CONFIGURING)`, `ensure (CONFIGURING)`.
    pub fn connect_proof_tracer_stat(
        &mut self,
        tracer: Box<dyn StatTracer>,
        antecedents: bool,
        finalize_clauses: bool,
    ) -> TracerRef {
        const F: &str = "void CaDiCaL::Solver::connect_proof_tracer(StatTracer *, bool, bool)";
        self.log_begin("connect proof tracer with stats");
        self.require_valid_state(F);
        require!(
            F,
            FILE,
            self.state() == CONFIGURING,
            "can only start proof tracing to right after initialization"
        );
        let res = self.internal().connect_proof_tracer_stat(tracer, antecedents, finalize_clauses);
        self.log_end("connect proof tracer with stats");
        res
    }

    /// C++ overload for `FileTracer *` (renamed, for internal use).
    /// `finalize_clauses` defaults to `false` in C++.
    ///
    /// `require (CONFIGURING)`, `ensure (CONFIGURING)`.
    pub fn connect_proof_tracer_file(
        &mut self,
        tracer: Box<dyn FileTracer>,
        antecedents: bool,
        finalize_clauses: bool,
    ) -> TracerRef {
        const F: &str = "void CaDiCaL::Solver::connect_proof_tracer(FileTracer *, bool, bool)";
        self.log_begin("connect proof tracer with file");
        self.require_valid_state(F);
        require!(
            F,
            FILE,
            self.state() == CONFIGURING,
            "can only start proof tracing right after initialization"
        );
        let res = self.internal().connect_proof_tracer_file(tracer, antecedents, finalize_clauses);
        self.log_end("connect proof tracer with file");
        res
    }

    /// Disconnect proof tracer.  Also done upon deletion of the solver
    /// instance.  Returns the tracer if successful (`Some` == C++ `true`).
    ///
    /// `require (VALID)`, `ensure (VALID)`.
    pub fn disconnect_proof_tracer(&mut self, tracer: TracerRef) -> Option<Box<dyn Tracer>> {
        const F: &str = "bool CaDiCaL::Solver::disconnect_proof_tracer(Tracer *)";
        self.log_begin("disconnect proof tracer");
        self.require_valid_state(F);
        require!(F, FILE, tracer.0 != 0, "can not disconnect zero tracer");
        let res = self.internal().disconnect_proof_tracer(tracer);
        self.log_returns_b("connect proof tracer", res.is_some());
        res
    }

    /// C++ overload for `StatTracer *` (renamed).  Returns the tracer if
    /// successful (`Some` == C++ `true`).
    ///
    /// `require (VALID)`, `ensure (VALID)`.
    pub fn disconnect_proof_tracer_stat(&mut self, tracer: TracerRef) -> Option<Box<dyn StatTracer>> {
        const F: &str = "bool CaDiCaL::Solver::disconnect_proof_tracer(StatTracer *)";
        self.log_begin("disconnect proof tracer");
        self.require_valid_state(F);
        require!(F, FILE, tracer.0 != 0, "can not disconnect zero tracer");
        let res = self.internal().disconnect_proof_tracer_stat(tracer);
        self.log_returns_b("disconnect proof tracer", res.is_some());
        res
    }

    /// C++ overload for `FileTracer *` (renamed).  Returns the tracer if
    /// successful (`Some` == C++ `true`).
    ///
    /// `require (VALID)`, `ensure (VALID)`.
    pub fn disconnect_proof_tracer_file(&mut self, tracer: TracerRef) -> Option<Box<dyn FileTracer>> {
        const F: &str = "bool CaDiCaL::Solver::disconnect_proof_tracer(FileTracer *)";
        self.log_begin("disconnect proof tracer");
        self.require_valid_state(F);
        require!(F, FILE, tracer.0 != 0, "can not disconnect zero tracer");
        let res = self.internal().disconnect_proof_tracer_file(tracer);
        self.log_returns_b("disconnect proof tracer", res.is_some());
        res
    }

    /*--------------------------------------------------------------------*/

    /// Triggers the conclusion of incremental proofs.  If the solver is
    /// [`SATISFIED`] it will trigger `extend ()` and give the model to the
    /// proof tracer through `conclude_sat ()`.  If the solver is
    /// [`UNSATISFIED`] it will trigger `failing ()` which will learn new
    /// clauses as explained below: In case of failed assumptions will
    /// provide a core negated as a clause through the proof tracer
    /// interface.  With a failing constraint these can be multiple clauses.
    /// Then it will trigger a `conclude_unsat ()` event with the ids of the
    /// newly learnt clauses or the id of the global conflict.  In case the
    /// solver is in [`INCONCLUSIVE`], it will collect the currently
    /// "entrailed" literals and add them to the proof.
    ///
    /// `require (SATISFIED | UNSATISFIED | INCONCLUSIVE)`, same `ensure`.
    pub fn conclude(&mut self) {
        const F: &str = "void CaDiCaL::Solver::conclude()";
        self.trace0("conclude");
        self.require_valid_state(F);
        require!(
            F,
            FILE,
            self.state() == UNSATISFIED || self.state() == SATISFIED || self.state() == INCONCLUSIVE,
            "can only conclude in satisfied, unsatisfied or inconclusive state"
        );
        if self.state() == UNSATISFIED {
            self.internal().conclude_unsat();
        } else if self.state() == SATISFIED {
            self.external().conclude_sat();
        } else if self.state() == INCONCLUSIVE {
            self.external().conclude_unknown();
        }
        debug_assert!(
            self.state() == UNSATISFIED || self.state() == SATISFIED || self.state() == INCONCLUSIVE
        );
        self.log_end("conclude");
    }

    /*--------------------------------------------------------------------*/

    /// Print build configuration to a file (C `stdout` or `stderr`) with
    /// the given prefix (`"c "` by default in C++).  If the file is
    /// `<stdout>` or `<stderr>` then terminal color codes might be used.
    pub fn build(file: *mut libc::FILE, prefix: &str) {
        debug_assert!(file == c_stdout() || file == c_stderr());

        let terminal: Option<&'static Terminal> = if file == c_stdout() {
            Some(tout())
        } else if file == c_stderr() {
            Some(terr())
        } else {
            None
        };

        let v = crate::version::version();
        let i = crate::version::identifier();
        let c = crate::version::compiler();
        let b = crate::version::date();
        let f = crate::version::flags();

        fputs(prefix, file);
        if let Some(t) = terminal {
            t.magenta(false);
        }
        fputs("Version ", file);
        if let Some(t) = terminal {
            t.normal();
        }
        fputs(v, file);
        if let Some(i) = i {
            if let Some(t) = terminal {
                t.magenta(false);
            }
            fputc(b' ' as i32, file);
            fputs(i, file);
            if let Some(t) = terminal {
                t.normal();
            }
        }
        fputc(b'\n' as i32, file);

        if let Some(c) = c {
            fputs(prefix, file);
            if let Some(t) = terminal {
                t.magenta(false);
            }
            fputs(c, file);
            if let Some(f) = f {
                fputc(b' ' as i32, file);
                fputs(f, file);
            }
            if let Some(t) = terminal {
                t.normal();
            }
            fputc(b'\n' as i32, file);
        }

        if let Some(b) = b {
            fputs(prefix, file);
            if let Some(t) = terminal {
                t.magenta(false);
            }
            fputs(b, file);
            if let Some(t) = terminal {
                t.normal();
            }
            fputc(b'\n' as i32, file);
        }

        fflush(file);
    }

    /// Return the version string (e.g. `"3.0.1"`).
    pub fn version() -> &'static str {
        crate::version::version()
    }

    /// Return the name of this library (e.g. `"cadical-3.0.1"`).
    pub fn signature() -> &'static str {
        crate::version::signature()
    }

    /// Print current option and value list.
    ///
    /// `require (VALID)`, `ensure (VALID)`.
    pub fn options(&mut self) {
        const F: &str = "void CaDiCaL::Solver::options()";
        self.require_valid_state(F);
        self.internal().opts.print();
    }

    /// Print usage information for long options.
    pub fn usage() {
        Options::usage();
    }

    /// Print configuration usage options.
    pub fn configurations() {
        Config::usage();
    }

    /// Prints statistics to `stdout`.
    ///
    /// `require (!DELETING)`, `ensure (!DELETING)`.
    pub fn statistics(&mut self) {
        const F: &str = "void CaDiCaL::Solver::statistics()";
        if self.state() == DELETING {
            return;
        }
        self.trace0("stats");
        self.require_valid_or_solving_state(F);
        self.internal().print_statistics();
        self.log_end("stats");
    }

    /// Print resource usage (time and memory) to `stdout`.
    ///
    /// `require (!DELETING)`, `ensure (!DELETING)`.
    pub fn resources(&mut self) {
        const F: &str = "void CaDiCaL::Solver::resources()";
        if self.state() == DELETING {
            return;
        }
        self.trace0("resources");
        self.require_valid_or_solving_state(F);
        self.internal().print_resource_usage();
        self.log_end("resources");
    }

    /*--------------------------------------------------------------------*/

    /// Factoring out common code to all `read_dimacs` functions (C++
    /// private overload `read_dimacs (File *, ...)`, renamed).
    ///
    /// `require (VALID)`, `ensure (VALID)`.
    #[doc(hidden)]
    pub fn read_dimacs_internal(
        &mut self,
        file: *mut File,
        vars: &mut i32,
        strict: i32,
        incremental: Option<&mut bool>,
        cubes: Option<&mut Vec<i32>>,
    ) -> Option<String> {
        const F: &str =
            "const char *CaDiCaL::Solver::read_dimacs(File *, int &, int, bool *, vector<int> *)";
        self.require_valid_state(F);
        require!(
            F,
            FILE,
            self.state() == CONFIGURING,
            "can only read DIMACS file right after initialization"
        );
        let incremental: *mut bool = match incremental {
            Some(r) => r,
            None => std::ptr::null_mut(),
        };
        let cubes: *mut Vec<i32> = match cubes {
            Some(r) => r,
            None => std::ptr::null_mut(),
        };
        let mut parser = Parser::new(self as *mut Solver, file, incremental, cubes);
        let err = parser.parse_dimacs(vars, strict);
        drop(parser);
        err
    }

    /// Read a DIMACS file from an already opened C `FILE *` with the given
    /// `name` (C++ overload `read_dimacs (FILE *, const char *, int &,
    /// int)`).  `strict` defaults to `1` in C++.
    ///
    /// If the `strict` argument is zero then the number of variables and
    /// clauses specified in the DIMACS headers are ignored, i.e., the
    /// header `p cnf 0 0` is always legal.  If the `strict` argument is
    /// larger `1` strict formatting of the header is required, i.e., single
    /// spaces everywhere and no trailing white space.  The maximum variable
    /// index of the header is stored in `vars`.
    ///
    /// Returns `None` if successful and otherwise an error message.
    ///
    /// `require (CONFIGURING)`, `ensure (CONFIGURING)`.
    pub fn read_dimacs_file(
        &mut self,
        external_file: *mut libc::FILE,
        name: &str,
        vars: &mut i32,
        strict: i32,
    ) -> Option<String> {
        const F: &str = "const char *CaDiCaL::Solver::read_dimacs(FILE *, const char *, int &, int)";
        self.log_begin_s("read_dimacs", name);
        self.require_valid_state(F);
        require!(
            F,
            FILE,
            self.state() == CONFIGURING,
            "can only read DIMACS file right after initialization"
        );
        let file = File::read_fp(self.internal, external_file, name);
        debug_assert!(!file.is_null());
        let err = self.read_dimacs_internal(file, vars, strict, None, None);
        // SAFETY: 'File::read_fp' returns a freshly boxed 'File'.
        drop(unsafe { Box::from_raw(file) });
        self.log_returns_ss("read_dimacs", name, err.as_deref());
        err
    }

    /// Read a DIMACS file from `path` (compressed files are supported if
    /// the corresponding helper is available).  `strict` defaults to `1` in
    /// C++ (see [`Solver::read_dimacs_file`]).  Returns `None` if
    /// successful and otherwise an error message.
    ///
    /// `require (CONFIGURING)`, `ensure (CONFIGURING)`.
    pub fn read_dimacs(&mut self, path: &str, vars: &mut i32, strict: i32) -> Option<String> {
        const F: &str = "const char *CaDiCaL::Solver::read_dimacs(const char *, int &, int)";
        self.log_begin_s("read_dimacs", path);
        self.require_valid_state(F);
        require!(
            F,
            FILE,
            self.state() == CONFIGURING,
            "can only read DIMACS file right after initialization"
        );
        let file = File::read(self.internal, path);
        if file.is_null() {
            return Some(
                self.internal()
                    .error_message
                    .init(format_args!("failed to read DIMACS file '{}'", path))
                    .to_string(),
            );
        }
        let err = self.read_dimacs_internal(file, vars, strict, None, None);
        // SAFETY: 'File::read' returns a freshly boxed 'File'.
        drop(unsafe { Box::from_raw(file) });
        self.log_returns_ss("read_dimacs", path, err.as_deref());
        err
    }

    /// Same as [`Solver::read_dimacs_file`] but parses both DIMACS and
    /// INCCNF files (with `p inccnf` header and `a <cube>` lines).  If the
    /// parser finds a `p inccnf` header or cubes then `incremental` is set
    /// to true and the cubes are stored in the given vector (each cube
    /// terminated by a zero).
    ///
    /// `require (CONFIGURING)`, `ensure (CONFIGURING)`.
    pub fn read_dimacs_file_inccnf(
        &mut self,
        external_file: *mut libc::FILE,
        name: &str,
        vars: &mut i32,
        strict: i32,
        incremental: &mut bool,
        cubes: &mut Vec<i32>,
    ) -> Option<String> {
        const F: &str = "const char *CaDiCaL::Solver::read_dimacs(FILE *, const char *, int &, int, bool &, vector<int> &)";
        self.log_begin_s("read_dimacs", name);
        self.require_valid_state(F);
        require!(
            F,
            FILE,
            self.state() == CONFIGURING,
            "can only read DIMACS file right after initialization"
        );
        let file = File::read_fp(self.internal, external_file, name);
        debug_assert!(!file.is_null());
        let err = self.read_dimacs_internal(file, vars, strict, Some(incremental), Some(cubes));
        // SAFETY: 'File::read_fp' returns a freshly boxed 'File'.
        drop(unsafe { Box::from_raw(file) });
        self.log_returns_ss("read_dimacs", name, err.as_deref());
        err
    }

    /// Same as [`Solver::read_dimacs`] but parses both DIMACS and INCCNF
    /// files (see [`Solver::read_dimacs_file_inccnf`]).
    ///
    /// `require (CONFIGURING)`, `ensure (CONFIGURING)`.
    pub fn read_dimacs_inccnf(
        &mut self,
        path: &str,
        vars: &mut i32,
        strict: i32,
        incremental: &mut bool,
        cubes: &mut Vec<i32>,
    ) -> Option<String> {
        const F: &str = "const char *CaDiCaL::Solver::read_dimacs(const char *, int &, int, bool &, vector<int> &)";
        self.log_begin_s("read_dimacs", path);
        self.require_valid_state(F);
        require!(
            F,
            FILE,
            self.state() == CONFIGURING,
            "can only read DIMACS file right after initialization"
        );
        let file = File::read(self.internal, path);
        if file.is_null() {
            return Some(
                self.internal()
                    .error_message
                    .init(format_args!("failed to read DIMACS file '{}'", path))
                    .to_string(),
            );
        }
        let err = self.read_dimacs_internal(file, vars, strict, Some(incremental), Some(cubes));
        // SAFETY: 'File::read' returns a freshly boxed 'File'.
        drop(unsafe { Box::from_raw(file) });
        self.log_returns_ss("read_dimacs", path, err.as_deref());
        err
    }

    /// Read solution in competition format for debugging and testing (used
    /// by the stand-alone solver and `mobical`).
    ///
    /// `require (VALID)`, `ensure (VALID)`.
    #[doc(hidden)]
    pub fn read_solution(&mut self, path: &str) -> Option<String> {
        const F: &str = "const char *CaDiCaL::Solver::read_solution(const char *)";
        self.log_begin_s("solution", path);
        self.require_valid_state(F);
        let file = File::read(self.internal, path);
        if file.is_null() {
            return Some(
                self.internal()
                    .error_message
                    .init(format_args!("failed to read solution file '{}'", path))
                    .to_string(),
            );
        }
        let mut parser =
            Parser::new(self as *mut Solver, file, std::ptr::null_mut(), std::ptr::null_mut());
        let err = parser.parse_solution();
        drop(parser);
        // SAFETY: 'File::read' returns a freshly boxed 'File'.
        drop(unsafe { Box::from_raw(file) });
        if err.is_none() {
            self.external().check_assignment(External::sol);
        }
        self.log_returns_ss("read_solution", path, err.as_deref());
        err
    }

    /*--------------------------------------------------------------------*/

    /// Print DIMACS file to `<stdout>` for debugging and testing purposes,
    /// including derived units and assumptions.  Since it will print in
    /// terms of internal literals it is otherwise not really useful.  To
    /// write a DIMACS formula in terms of external variables use
    /// [`Solver::write_dimacs`].
    ///
    /// `require (!INITIALIZING)`, `ensure (!INITIALIZING)`.
    #[doc(hidden)]
    pub fn dump_cnf(&mut self) {
        const F: &str = "void CaDiCaL::Solver::dump_cnf()";
        self.trace0("dump");
        self.require_initialized(F);
        self.internal().dump();
        self.log_end("dump");
    }

    /*--------------------------------------------------------------------*/
    // Used in mobical to test external propagation internally.  These
    // functions should not be called for any other purposes.

    /// The connected external propagator (for `mobical`).
    #[doc(hidden)]
    pub fn get_propagator(&mut self) -> Option<&mut (dyn ExternalPropagator + 'static)> {
        self.external().propagator.as_deref_mut()
    }

    /// Is the variable of `lit` observed (for `mobical`)?
    #[doc(hidden)]
    pub fn observed(&mut self, lit: i32) -> bool {
        const F: &str = "bool CaDiCaL::Solver::observed(int)";
        self.trace_i("observed", lit);
        self.require_valid_or_solving_state(F);
        self.require_valid_lit(F, lit);
        let res = self.external().observed(lit);
        self.log_returns_ib("observed", lit, res);
        res
    }

    /// Is `lit` a witness on the reconstruction stack (for `mobical`)?
    #[doc(hidden)]
    pub fn is_witness(&mut self, lit: i32) -> bool {
        const F: &str = "bool CaDiCaL::Solver::is_witness(int)";
        self.trace_i("is_witness", lit);
        self.require_valid_or_solving_state(F);
        self.require_valid_lit(F, lit);
        let res = self.external().is_witness(lit);
        self.log_returns_ib("is_witness", lit, res);
        res
    }

    /// Get reason of valid observed literal (true = it is an observed
    /// variable and it got assigned by a decision during the CDCL loop.
    /// Otherwise: false).
    ///
    /// `require (VALID_OR_SOLVING)`, `ensure (VALID_OR_SOLVING)`.
    pub fn is_decision(&mut self, lit: i32) -> bool {
        const F: &str = "bool CaDiCaL::Solver::is_decision(int)";
        self.trace_i("is_decision", lit);
        self.require_valid_or_solving_state(F);
        self.require_valid_lit(F, lit);
        let res = self.external().is_decision(lit);
        self.log_returns_ib("is_decision", lit, res);
        res
    }

    /// Force solve to backtrack to certain decision level.  Can be called
    /// only during `cb_decide` and `cb_check_found_model` of a connected
    /// external propagator.  Invoking in any other time will trigger a
    /// runtime error.  Otherwise, the external propagator will be notified
    /// about the backtrack via `notify_backtrack` and the search continues.
    ///
    /// `require (SOLVING)`, `ensure (SOLVING)`.
    pub fn force_backtrack(&mut self, new_level: i32) {
        const F: &str = "void CaDiCaL::Solver::force_backtrack(int)";
        self.trace_i("force_backtrack", new_level);
        self.require_valid_or_solving_state(F);
        require!(
            F,
            FILE,
            self.external().propagator.is_some(),
            "can not force backtrack without a connected propagator"
        );
        self.external().force_backtrack(new_level);
    }

    /*--------------------------------------------------------------------*/

    /// Traverse irredundant clauses (see [`ClauseIterator`]).  The return
    /// value is false if traversal is aborted early due to the visitor
    /// function returning false.
    ///
    /// `require (VALID)`, `ensure (VALID)`.
    pub fn traverse_clauses(&self, it: &mut dyn ClauseIterator) -> bool {
        const F: &str = "bool CaDiCaL::Solver::traverse_clauses(ClauseIterator &) const";
        self.log_begin("traverse_clauses");
        self.require_valid_state(F);
        let res = self.external().traverse_all_frozen_units_as_clauses(it)
            && self.internal().traverse_clauses(it)
            && self.internal().traverse_constraint(it);
        self.log_returns_b("traverse_clauses", res);
        res
    }

    /// Traverse the extension stack in reverse order (see
    /// [`WitnessIterator`]).  The return value is false if traversal is
    /// aborted early due to the visitor function returning false.
    ///
    /// `require (VALID)`, `ensure (VALID)`.
    pub fn traverse_witnesses_backward(&self, it: &mut dyn WitnessIterator) -> bool {
        const F: &str =
            "bool CaDiCaL::Solver::traverse_witnesses_backward(WitnessIterator &) const";
        self.log_begin("traverse_witnesses_backward");
        self.require_valid_state(F);
        let res = self.external().traverse_all_non_frozen_units_as_witnesses(it)
            && self.external().traverse_witnesses_backward(it);
        self.log_returns_b("traverse_witnesses_backward", res);
        res
    }

    /// Traverse the extension stack in forward order (see
    /// [`WitnessIterator`]).  The return value is false if traversal is
    /// aborted early due to the visitor function returning false.
    ///
    /// `require (VALID)`, `ensure (VALID)`.
    pub fn traverse_witnesses_forward(&self, it: &mut dyn WitnessIterator) -> bool {
        const F: &str = "bool CaDiCaL::Solver::traverse_witnesses_forward(WitnessIterator &) const";
        self.log_begin("traverse_witnesses_forward");
        self.require_valid_state(F);
        let res = self.external().traverse_witnesses_forward(it)
            && self.external().traverse_all_non_frozen_units_as_witnesses(it);
        self.log_returns_b("traverse_witnesses_forward", res);
        res
    }

    /*--------------------------------------------------------------------*/

    /// Write current irredundant clauses and all derived unit clauses to a
    /// file in DIMACS format.  Clauses on the extension stack are not
    /// included, nor any redundant clauses.
    ///
    /// The `min_max_var` parameter (`0` by default in C++) gives a lower
    /// bound on the number `<vars>` of variables used in the DIMACS
    /// `p cnf <vars> ...` header.
    ///
    /// Returns `None` if successful and otherwise an error message.
    ///
    /// `require (VALID)`, `ensure (VALID)`.
    pub fn write_dimacs(&mut self, path: &str, min_max_var: i32) -> Option<String> {
        const F: &str = "const char *CaDiCaL::Solver::write_dimacs(const char *, int)";
        self.log_begin_si("write_dimacs", path, min_max_var);
        self.require_valid_state(F);
        let start = self.internal().time();
        self.internal().restore_clauses();
        let mut counter = ClauseCounter { vars: 0, clauses: 0 };
        let _ = self.traverse_clauses(&mut counter);
        log!(
            self.internal,
            "found maximal variable {} and {} clauses",
            counter.vars,
            counter.clauses
        );
        let file = File::write(self.internal, path);
        let mut res: Option<String> = None;
        if !file.is_null() {
            let actual_max_vars = std::cmp::max(min_max_var, counter.vars);
            msg!(
                self.internal,
                "writing {}'p cnf {} {}'{} header",
                tout().green_code(),
                actual_max_vars,
                counter.clauses,
                tout().normal_code()
            );
            {
                // SAFETY: 'File::write' returns a freshly boxed 'File'.
                let f = unsafe { &mut *file };
                f.put_str("p cnf ");
                f.put_int(actual_max_vars);
                f.put_char(b' ');
                f.put_i64(counter.clauses);
                f.put_char(b'\n');
            }
            let mut writer = ClauseWriter { file };
            if !self.traverse_clauses(&mut writer) {
                res = Some(
                    self.internal()
                        .error_message
                        .init(format_args!("writing to DIMACS file '{}' failed", path))
                        .to_string(),
                );
            }
            // SAFETY: see above.
            drop(unsafe { Box::from_raw(file) });
        } else {
            res = Some(
                self.internal()
                    .error_message
                    .init(format_args!("failed to open DIMACS file '{}' for writing", path))
                    .to_string(),
            );
        }
        if res.is_none() {
            let end = self.internal().time();
            msg!(
                self.internal,
                "wrote {} clauses in {} seconds {} time",
                counter.clauses,
                crate::format::fmt_f(end - start, 2),
                if self.internal().opts.realtime != 0 { "real" } else { "process" }
            );
        }
        self.log_returns_sis("write_dimacs", path, min_max_var, res.as_deref());
        res
    }

    /// The extension stack for reconstruction a solution can be written
    /// too (clauses and witnesses, one pair per line).  Returns `None` if
    /// successful and otherwise an error message.
    ///
    /// `require (VALID)`, `ensure (VALID)`.
    pub fn write_extension(&mut self, path: &str) -> Option<String> {
        const F: &str = "const char *CaDiCaL::Solver::write_extension(const char *)";
        self.log_begin_s("write_extension", path);
        self.require_valid_state(F);
        let mut res: Option<String> = None;
        let start = self.internal().time();
        let file = File::write(self.internal, path);
        let mut writer = WitnessWriter { file, witnesses: 0 };
        if !file.is_null() {
            if !self.traverse_witnesses_backward(&mut writer) {
                res = Some(
                    self.internal()
                        .error_message
                        .init(format_args!("writing to DIMACS file '{}' failed", path))
                        .to_string(),
                );
            }
            // SAFETY: 'File::write' returns a freshly boxed 'File'.
            drop(unsafe { Box::from_raw(file) });
        } else {
            res = Some(
                self.internal()
                    .error_message
                    .init(format_args!("failed to open extension file '{}' for writing", path))
                    .to_string(),
            );
        }
        if res.is_none() {
            let end = self.internal().time();
            msg!(
                self.internal,
                "wrote {} witnesses in {} seconds {} time",
                writer.witnesses,
                crate::format::fmt_f(end - start, 2),
                if self.internal().opts.realtime != 0 { "real" } else { "process" }
            );
        }
        self.log_returns_ss("write_extension", path, res.as_deref());
        res
    }

    /*--------------------------------------------------------------------*/

    /// Copy `self` into a fresh `other`.  The copy procedure is not a deep
    /// clone, but only copies irredundant clauses and units.  It also makes
    /// sure that witness reconstruction works with the copy as with the
    /// original formula such that both solvers have the same models.
    /// Assumptions are not copied.  Options however are copied as well as
    /// flags which remember the current state of variables in
    /// preprocessing.
    ///
    /// `require (READY)` and `ensure (READY)` for `self`,
    /// `other.require (CONFIGURING)`, `other.ensure (CONFIGURING | STEADY)`.
    pub fn copy(&self, other: &mut Solver) {
        const F: &str = "void CaDiCaL::Solver::copy(Solver &) const";
        self.require_ready_state(F);
        require!(F, FILE, other.state() & CONFIGURING != 0, "target solver already modified");
        self.internal().opts.copy(&mut other.internal().opts);
        let other_external = other.external;
        {
            let mut clause_copier = ClauseCopier { dst: other };
            self.traverse_clauses(&mut clause_copier);
        }
        let mut witness_copier = WitnessCopier { dst: other_external };
        self.traverse_witnesses_forward(&mut witness_copier);
        // SAFETY: 'other_external' is owned by 'other' (alive).
        self.external().copy_flags(unsafe { &mut *other_external });
    }

    /*--------------------------------------------------------------------*/
    // Messages in a common style (used by 'App' and 'Mobical').

    /// Print section header.
    ///
    /// `require (VALID | DELETING)`.
    #[doc(hidden)]
    pub fn section(&mut self, title: &str) {
        const F: &str = "void CaDiCaL::Solver::section(const char *)";
        if self.state() == DELETING {
            return;
        }
        self.require_initialized(F);
        if !self.internal.is_null() {
            self.internal().section(title);
        }
    }

    /// Ordinary message.
    ///
    /// `require (VALID | DELETING)`.
    #[doc(hidden)]
    pub fn message(&mut self, args: std::fmt::Arguments<'_>) {
        const F: &str = "void CaDiCaL::Solver::message(const char *, ...)";
        if self.state() == DELETING {
            return;
        }
        self.require_initialized(F);
        self.internal().message(args);
    }

    /// Empty line - only prefix (C++ overload `Solver::message ()`).
    ///
    /// `require (VALID | DELETING)`.
    #[doc(hidden)]
    pub fn message_empty(&mut self) {
        const F: &str = "void CaDiCaL::Solver::message()";
        if self.state() == DELETING {
            return;
        }
        self.require_initialized(F);
        self.internal().message_empty();
    }

    /// Explicit verbose level (`section` and `message` use `0`).
    ///
    /// `require (VALID | DELETING)`.
    #[doc(hidden)]
    pub fn verbose(&mut self, level: i32, args: std::fmt::Arguments<'_>) {
        const F: &str = "void CaDiCaL::Solver::verbose(int, const char *, ...)";
        if self.state() == DELETING {
            return;
        }
        self.require_valid_or_solving_state(F);
        self.internal().verbose(level, args);
    }

    /// Produce error message (and exit with status 1).
    #[doc(hidden)]
    pub fn error(&mut self, args: std::fmt::Arguments<'_>) {
        const F: &str = "void CaDiCaL::Solver::error(const char *, ...)";
        if self.state() == DELETING {
            return;
        }
        self.require_initialized(F);
        self.internal().error(args);
    }

    /// Get the value of some statistics or `-1` if the statistics does not
    /// exist or is not supported.  Supported are `"conflicts"`,
    /// `"decisions"`, `"ticks"`, `"propagations"`, `"clauses"`,
    /// `"redundant"`, `"irredundant"`, `"fixed"`, `"eliminated"` and
    /// `"subsitutued"` (sic).  Only requires the state to be initialized.
    pub fn get_statistic_value(&self, opt: &str) -> i64 {
        const F: &str = "int64_t CaDiCaL::Solver::get_statistic_value(const char *) const";
        self.require_initialized(F);
        let stats = &self.internal().stats;
        match opt {
            "conflicts" => stats.conflicts,
            "decisions" => stats.decisions,
            "ticks" => stats.ticks.search[0] + stats.ticks.search[1],
            "propagations" => stats.propagations.search,
            "clauses" => stats.current.total,
            "redundant" => stats.current.redundant,
            "irredundant" => stats.current.irredundant,
            "fixed" => stats.all.fixed,
            "eliminated" => stats.all.eliminated + stats.all.fasteliminated,
            "subsitutued" => stats.all.substituted,
            _ => -1,
        }
    }
}

/*------------------------------------------------------------------------*/

// Helper iterators of 'solver.cpp'.

struct ClauseCounter {
    vars: i32,
    clauses: i64,
}

impl ClauseIterator for ClauseCounter {
    fn clause(&mut self, c: &[i32]) -> bool {
        for &lit in c {
            debug_assert!(lit != i32::MIN);
            let idx = lit.abs();
            if idx > self.vars {
                self.vars = idx;
            }
        }
        self.clauses += 1;
        true
    }
}

struct ClauseWriter {
    file: *mut File,
}

impl ClauseIterator for ClauseWriter {
    fn clause(&mut self, c: &[i32]) -> bool {
        // SAFETY: the file is alive during the traversal.
        let file = unsafe { &mut *self.file };
        for &lit in c {
            if !file.put_int(lit) {
                return false;
            }
            if !file.put_char(b' ') {
                return false;
            }
        }
        file.put_str("0\n")
    }
}

struct WitnessWriter {
    file: *mut File,
    witnesses: i64,
}

impl WitnessWriter {
    fn write(&mut self, a: &[i32]) -> bool {
        // SAFETY: the file is alive during the traversal.
        let file = unsafe { &mut *self.file };
        for &lit in a {
            if !file.put_int(lit) {
                return false;
            }
            if !file.put_char(b' ') {
                return false;
            }
        }
        file.put_char(b'0')
    }
}

impl WitnessIterator for WitnessWriter {
    fn witness(&mut self, c: &[i32], w: &[i32], _id: i64) -> bool {
        if !self.write(c) {
            return false;
        }
        // SAFETY: the file is alive during the traversal.
        if !unsafe { &mut *self.file }.put_char(b' ') {
            return false;
        }
        if !self.write(w) {
            return false;
        }
        // SAFETY: see above.
        if !unsafe { &mut *self.file }.put_char(b'\n') {
            return false;
        }
        self.witnesses += 1;
        true
    }
}

struct ClauseCopier<'a> {
    dst: &'a mut Solver,
}

impl ClauseIterator for ClauseCopier<'_> {
    fn clause(&mut self, c: &[i32]) -> bool {
        for &lit in c {
            self.dst.add(lit);
        }
        self.dst.add(0);
        true
    }
}

struct WitnessCopier {
    dst: *mut External,
}

impl WitnessIterator for WitnessCopier {
    fn witness(&mut self, c: &[i32], w: &[i32], id: i64) -> bool {
        // SAFETY: the destination external solver is alive during 'copy'.
        unsafe { &mut *self.dst }.push_external_clause_and_witness_on_extension_stack(c, w, id);
        true
    }
}

/*------------------------------------------------------------------------*/

/// `getenv (name)` as a Rust string (lossy for non UTF-8 values).
fn getenv(name: &str) -> Option<String> {
    let cname = CString::new(name).unwrap();
    // SAFETY: 'getenv' with a valid C string.
    let p = unsafe { libc::getenv(cname.as_ptr()) };
    if p.is_null() {
        None
    } else {
        // SAFETY: 'getenv' returns a valid C string.
        Some(unsafe { CStr::from_ptr(p) }.to_string_lossy().into_owned())
    }
}

impl Solver {
    /// Create a new solver (`Solver ()`), which starts in state
    /// [`CONFIGURING`].
    ///
    /// If the environment variable `CADICAL_API_TRACE` (or
    /// `CADICALAPITRACE`) is set, API calls are traced to the file it
    /// points to (only one solver instance can do this at a time).  If the
    /// environment variable `CADICAL_LIDRUP_TRACE` (or
    /// `CADICALLIDRUPTRACE`) is set, a (non-binary) LIDRUP proof is written
    /// to that file.
    pub fn new() -> Solver {
        let mut solver = Solver {
            adding_clause: false,
            adding_constraint: false,
            _state: INITIALIZING,
            internal: std::ptr::null_mut(),
            external: std::ptr::null_mut(),
            close_trace_api_file: false,
            trace_api_file: std::ptr::null_mut(),
            owns_trace_api_file: false,
        };

        let mut path = getenv("CADICAL_API_TRACE");
        if path.is_none() {
            path = getenv("CADICALAPITRACE");
        }
        if let Some(ref p) = path {
            if TRACING_API_CALLS_THROUGH_ENVIRONMENT_VARIABLE_METHOD.load(Relaxed) {
                fatal!(
                    "can not trace API calls of two solver instances using environment variable 'CADICAL_API_TRACE'"
                );
            }
            let cpath = CString::new(p.as_str()).unwrap_or_default();
            // SAFETY: valid C strings.
            let file = unsafe { libc::fopen(cpath.as_ptr(), b"w\0".as_ptr() as *const libc::c_char) };
            if file.is_null() {
                fatal!(
                    "failed to open file '{}' to trace API calls using environment variable 'CADICAL_API_TRACE'",
                    p
                );
            }
            solver.trace_api_file = file;
            solver.close_trace_api_file = true;
            TRACING_API_CALLS_THROUGH_ENVIRONMENT_VARIABLE_METHOD.store(true, Relaxed);
        } else {
            TRACING_API_CALLS_THROUGH_ENVIRONMENT_VARIABLE_METHOD.store(false, Relaxed);
            solver.close_trace_api_file = false;
            solver.trace_api_file = std::ptr::null_mut();
        }

        solver.adding_clause = false;
        solver.adding_constraint = false;
        solver._state = INITIALIZING;
        solver.internal = Box::into_raw(Internal::new());
        solver.trace0("init");
        solver.external = Box::into_raw(External::new(solver.internal));
        state!(solver, CONFIGURING);
        if TRACING_API_CALLS_THROUGH_ENVIRONMENT_VARIABLE_METHOD.load(Relaxed) {
            let p = path.as_deref().unwrap_or("(null)");
            solver.message(format_args!("tracing API calls to '{}'", p));
        }

        let mut lidrup_path = getenv("CADICAL_LIDRUP_TRACE");
        if lidrup_path.is_none() {
            lidrup_path = getenv("CADICALLIDRUPTRACE");
        }
        if let Some(lidrup_path) = lidrup_path {
            if TRACING_NB_LIDRUP_ENV_VAR_METHOD.load(Relaxed) {
                fatal!(
                    "can not trace LIDRUP of two solver instances using environment variable 'CADICAL_LIDRUP_TRACE'"
                );
            }
            // Here we use the solver interface to setup non-binary IDRUP
            // tracing to the defined file. Options set by the user can and
            // will overwrite these settings if neeed be.
            solver.set("lidrup", 1);
            solver.set("binary", 0);
            solver.trace_proof(&lidrup_path);
            TRACING_NB_LIDRUP_ENV_VAR_METHOD.store(true, Relaxed);
        } else {
            TRACING_NB_LIDRUP_ENV_VAR_METHOD.store(false, Relaxed);
        }

        solver
    }
}

impl Default for Solver {
    fn default() -> Self {
        Solver::new()
    }
}

impl Drop for Solver {
    /// `~Solver ()`: traces `reset`, enters state [`DELETING`] and deletes
    /// the internal and external solver (including still connected
    /// tracers and call-backs).
    fn drop(&mut self) {
        // While unwinding a panic (a Rust bug or an unported part) do not
        // run the destructor chain (which might panic again).
        if std::thread::panicking() {
            return;
        }

        const F: &str = "CaDiCaL::Solver::~Solver()";
        self.trace0("reset");
        self.require_valid_or_solving_state(F);
        state!(self, DELETING);

        TRACING_NB_LIDRUP_ENV_VAR_METHOD.store(false, Relaxed);

        // After deleting 'internal' logging does not work anymore.
        #[cfg(feature = "logging")]
        let (logging, level, prefix) = {
            let i = self.internal();
            (i.opts.log != 0, i.level, i.prefix.clone())
        };

        // SAFETY: both were created with 'Box::into_raw' in 'new' and are
        // not referenced anymore after this point.
        unsafe {
            drop(Box::from_raw(self.internal));
            self.internal = std::ptr::null_mut();
            drop(Box::from_raw(self.external));
            self.external = std::ptr::null_mut();
        }

        if self.close_trace_api_file {
            self.close_trace_api_file = false;
            debug_assert!(!self.trace_api_file.is_null());
            debug_assert!(TRACING_API_CALLS_THROUGH_ENVIRONMENT_VARIABLE_METHOD.load(Relaxed));
            // SAFETY: opened with 'fopen' in 'new'.
            unsafe {
                libc::fclose(self.trace_api_file);
            }
            TRACING_API_CALLS_THROUGH_ENVIRONMENT_VARIABLE_METHOD.store(false, Relaxed);
        }

        // Rust addition: close the API trace file opened from a path by
        // 'trace_api_calls' (after 'reset' has been traced above).
        if self.owns_trace_api_file {
            self.owns_trace_api_file = false;
            debug_assert!(!self.trace_api_file.is_null());
            // SAFETY: opened with 'fopen' in 'trace_api_calls'.
            unsafe {
                libc::fclose(self.trace_api_file);
            }
            self.trace_api_file = std::ptr::null_mut();
        }

        // Need to log success of this API call manually.
        #[cfg(feature = "logging")]
        if logging {
            crate::message::cprint(format_args!(
                "{}{}LOG {}{}{} API call {}'reset ()'{} succeeded{}\n",
                prefix,
                tout().magenta_code(),
                tout().bright_magenta_code(),
                level,
                tout().magenta_code(),
                tout().blue_code(),
                tout().magenta_code(),
                tout().normal_code()
            ));
            fflush(c_stdout());
        }
    }
}

/*------------------------------------------------------------------------*/
// Thin Rust conveniences (never changing the underlying semantics).

impl Solver {
    /// Add a clause given as a slice of (valid, non-zero) literals (same
    /// as [`Solver::clause`]).
    ///
    /// `require (VALID)`, `ensure (STEADY)`.
    pub fn add_clause(&mut self, lits: &[i32]) {
        self.clause(lits)
    }

    /// Assume all given literals (calls [`Solver::assume`] for each).
    ///
    /// `require (READY)`, `ensure (STEADY)`.
    pub fn assume_all(&mut self, lits: &[i32]) {
        for &lit in lits {
            self.assume(lit);
        }
    }

    /// [`Solver::solve`] returning a [`SolveResult`].
    pub fn solve_result(&mut self) -> SolveResult {
        SolveResult::from_code(self.solve())
    }

    /// [`Solver::simplify`] returning a [`SolveResult`].
    pub fn simplify_result(&mut self, rounds: i32) -> SolveResult {
        SolveResult::from_code(self.simplify(rounds))
    }

    /// [`Solver::propagate`] returning a [`SolveResult`].
    pub fn propagate_result(&mut self) -> SolveResult {
        SolveResult::from_code(self.propagate())
    }

    /// The current [`Solver::status`] as a [`SolveResult`].
    pub fn result(&self) -> SolveResult {
        SolveResult::from_code(self.status())
    }

    /// Is `lit` assigned to true in the current model?  Equivalent to
    /// `val (lit, true) == lit` (see [`Solver::val`]).
    ///
    /// `require (SATISFIED)`, `ensure (SATISFIED)`.
    pub fn value(&mut self, lit: i32) -> bool {
        self.val(lit) == lit
    }

    /// The model restricted to the variables `1..=vars ()` as literals
    /// (positive if true, negative if false), obtained through
    /// [`Solver::val`].
    ///
    /// `require (SATISFIED)`, `ensure (SATISFIED)`.
    pub fn model(&mut self) -> Vec<i32> {
        let max_var = self.vars();
        (1..=max_var).map(|idx| self.val(idx)).collect()
    }

    /// Connect a closure receiving every learned clause with at most
    /// `max_length` literals as a whole (without the terminating zero).
    /// Implemented on top of the literal-by-literal [`Learner`] protocol
    /// (see [`LearnerFn`]); replaces a previously connected learner.
    ///
    /// ```
    /// use std::{cell::RefCell, rc::Rc};
    /// let mut solver = cadical::Solver::new();
    /// let units = Rc::new(RefCell::new(Vec::new()));
    /// let sink = units.clone();
    /// solver.connect_learner_fn(1, move |clause| sink.borrow_mut().push(clause[0]));
    /// solver.clause(&[1, 2]);
    /// solver.clause(&[1, -2]);
    /// solver.solve();
    /// println!("learned units: {:?}", units.borrow());
    /// ```
    ///
    /// `require (VALID)`, `ensure (VALID)`.
    pub fn connect_learner_fn<F: FnMut(&[i32]) + 'static>(&mut self, max_length: i32, f: F) {
        self.connect_learner(Box::new(learner_fn(max_length, f)))
    }

    /// [`Solver::traverse_clauses`] with a closure receiving each clause;
    /// return `false` from the closure to stop early.  Returns `false` if
    /// the traversal was stopped.
    ///
    /// ```
    /// let mut solver = cadical::Solver::new();
    /// solver.clause(&[1, 2]);
    /// solver.clause(&[-1, 3]);
    /// let mut clauses = Vec::new();
    /// solver.traverse_clauses_with(|c| {
    ///     clauses.push(c.to_vec());
    ///     true
    /// });
    /// assert_eq!(clauses.len(), 2);
    /// ```
    ///
    /// `require (VALID)`, `ensure (VALID)`.
    pub fn traverse_clauses_with<F: FnMut(&[i32]) -> bool>(&self, mut f: F) -> bool {
        self.traverse_clauses(&mut f)
    }

    /// [`Solver::traverse_witnesses_backward`] with a closure receiving
    /// `(clause, witness, id)`; return `false` to stop early.
    ///
    /// `require (VALID)`, `ensure (VALID)`.
    pub fn traverse_witnesses_backward_with<F: FnMut(&[i32], &[i32], i64) -> bool>(
        &self,
        mut f: F,
    ) -> bool {
        self.traverse_witnesses_backward(&mut f)
    }

    /// [`Solver::traverse_witnesses_forward`] with a closure receiving
    /// `(clause, witness, id)`; return `false` to stop early.
    ///
    /// `require (VALID)`, `ensure (VALID)`.
    pub fn traverse_witnesses_forward_with<F: FnMut(&[i32], &[i32], i64) -> bool>(
        &self,
        mut f: F,
    ) -> bool {
        self.traverse_witnesses_forward(&mut f)
    }

    /// Set a list of options (each as with [`Solver::set`]).  Returns
    /// `false` as soon as one option is invalid (the remaining options are
    /// not set).
    ///
    /// `require (CONFIGURING)`, `ensure (CONFIGURING)`.
    pub fn set_options(&mut self, options: &[(&str, i32)]) -> bool {
        for &(name, val) in options {
            if !self.set(name, val) {
                return false;
            }
        }
        true
    }
}

/*------------------------------------------------------------------------*/

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn configuring_state_and_options() {
        let mut solver = Solver::new();
        assert_eq!(solver.state(), CONFIGURING);
        assert_eq!(solver.status(), UNKNOWN);
        assert_eq!(solver.result(), SolveResult::Unknown);
        assert!(Solver::is_valid_option("quiet"));
        assert!(!Solver::is_valid_option("no-such-option"));
        assert!(Solver::is_valid_long_option("--quiet"));
        assert!(Solver::is_valid_long_option("--no-quiet"));
        assert!(!Solver::is_valid_long_option("--no-such-option=1"));
        assert!(Solver::is_valid_configuration("sat"));
        assert!(!Solver::is_valid_configuration("no-such-configuration"));
        assert!(solver.set("quiet", 1));
        assert_eq!(solver.get("quiet"), 1);
        assert!(!solver.set("no-such-option", 1));
        assert!(solver.set_long_option("--seed=42"));
        assert_eq!(solver.get("seed"), 42);
        assert!(!solver.set_long_option("seed=43"));
        assert!(solver.configure("unsat"));
        assert!(solver.is_valid_limit("conflicts"));
        assert!(!solver.is_valid_limit("no-such-limit"));
        assert!(solver.limit("conflicts", 5));
        assert!(!solver.limit("no-such-limit", 5));
        solver.prefix("x ");
        assert_eq!(solver.internal().prefix, "x ");
        assert_eq!(solver.get_statistic_value("conflicts"), 0);
        assert_eq!(solver.get_statistic_value("no-such-statistic"), -1);
        assert_eq!(solver.state(), CONFIGURING);
        assert!(!solver.inconsistent());
        assert_eq!(Solver::signature(), "cadical-3.0.1");
        assert_eq!(Solver::version(), "3.0.1");
    }

    #[test]
    fn solve_result_codes() {
        assert_eq!(SolveResult::from_code(10), SolveResult::Satisfiable);
        assert_eq!(SolveResult::from_code(20), SolveResult::Unsatisfiable);
        assert_eq!(SolveResult::from_code(0), SolveResult::Unknown);
        assert_eq!(SolveResult::Satisfiable.code(), SATISFIABLE);
        assert_eq!(i32::from(SolveResult::Unsatisfiable), UNSATISFIABLE);
        assert!(SolveResult::Satisfiable.is_sat());
        assert!(SolveResult::Unsatisfiable.is_unsat());
        assert!(SolveResult::Unknown.is_unknown());
    }

    #[test]
    fn termination_handle_sets_flag() {
        let solver = Solver::new();
        let handle = solver.termination_handle();
        assert!(!solver.internal().termination_forced.load(Relaxed));
        handle.terminate();
        assert!(solver.internal().termination_forced.load(Relaxed));
    }

    #[test]
    fn api_trace_format() {
        let dir = std::env::temp_dir();
        let path = dir.join(format!("cadical-rs-p8-api-trace-{}.trace", std::process::id()));
        let cpath = CString::new(path.to_str().unwrap()).unwrap();
        // SAFETY: valid C strings.
        let file = unsafe { libc::fopen(cpath.as_ptr(), b"w\0".as_ptr() as *const libc::c_char) };
        assert!(!file.is_null());
        {
            let mut solver = Solver::new();
            solver.trace_api_calls_file(file);
            solver.set("quiet", 1);
            solver.limit("conflicts", 7);
            solver.configure("plain");
            let _ = solver.get("quiet"); // not traced
            let _ = solver.vars();
        }
        // SAFETY: opened above.
        unsafe { libc::fclose(file) };
        let trace = std::fs::read_to_string(&path).unwrap();
        let _ = std::fs::remove_file(&path);
        assert_eq!(
            trace,
            "init\nset quiet 1\nlimit conflicts 7\nconfigure plain\nvars\nreset\n"
        );
    }

    #[test]
    fn api_trace_to_path() {
        let path = std::env::temp_dir().join(format!("cadical-rs-api-trace-path-{}.trace", std::process::id()));
        {
            let mut solver = Solver::new();
            solver.trace_api_calls(&path).unwrap();
            solver.clause(&[1, -2]);
            assert_eq!(solver.solve(), SATISFIABLE);
        }
        let trace = std::fs::read_to_string(&path).unwrap();
        let _ = std::fs::remove_file(&path);
        assert_eq!(trace, "init\nadd 1\nadd -2\nadd 0\nsolve\nreset\n");
        let mut solver = Solver::new();
        assert!(solver.trace_api_calls("/nonexistent-dir/x.trace").is_err());
    }

    #[test]
    fn shared_callbacks_stay_accessible() {
        use std::cell::RefCell;
        use std::rc::Rc;
        use std::sync::{Arc, Mutex};

        #[derive(Default)]
        struct Count(usize);
        impl Terminator for Count {
            fn terminate(&mut self) -> bool {
                self.0 += 1;
                false
            }
        }
        #[derive(Default)]
        struct Units(Vec<i32>);
        impl FixedAssignmentListener for Units {
            fn notify_fixed_assignment(&mut self, lit: i32) {
                self.0.push(lit);
            }
        }

        let mut solver = Solver::new();
        let count = Arc::new(Mutex::new(Count::default()));
        solver.connect_terminator(Box::new(count.clone()));
        let units = Rc::new(RefCell::new(Units::default()));
        solver.connect_fixed_listener(Box::new(units.clone()));
        let learned = Rc::new(RefCell::new(Vec::new()));
        let sink = learned.clone();
        solver.connect_learner_fn(10, move |c| sink.borrow_mut().push(c.to_vec()));
        solver.clause(&[1, 2]);
        solver.clause(&[1, -2]);
        solver.clause(&[-1, 3, 4]);
        assert_eq!(solver.solve(), SATISFIABLE);
        assert_eq!(solver.val(1), 1);
        assert_eq!(solver.val_with(-1, true), 1);
        assert!(count.lock().unwrap().0 > 0);
        // A unit input clause is fixed during the next 'solve'.
        solver.clause(&[5]);
        assert_eq!(solver.solve(), SATISFIABLE);
        assert!(units.borrow().0.contains(&5));

        let mut n = 0;
        assert!(solver.traverse_clauses_with(|_| {
            n += 1;
            true
        }));
        assert!(n > 0);
        assert!(!solver.traverse_clauses_with(|_| false));
        let mut w = 0;
        solver.traverse_witnesses_forward_with(|_, _, _| {
            w += 1;
            true
        });
        solver.traverse_witnesses_backward_with(|_, _, _| true);

        // The clause-wise learner reassembles clauses from the literals.
        let mut got = Vec::new();
        let mut l = learner_fn(2, |c: &[i32]| got.push(c.to_vec()));
        assert!(l.learning(2));
        assert!(!l.learning(3));
        for lit in [3, -4, 0, 5, 0] {
            l.learn(lit);
        }
        drop(l);
        assert_eq!(got, vec![vec![3, -4], vec![5]]);
    }

    #[test]
    fn closures_as_callbacks() {
        let mut calls = 0;
        let mut t = || {
            calls += 1;
            calls > 1
        };
        assert!(!Terminator::terminate(&mut t));
        assert!(Terminator::terminate(&mut t));
        let mut fixed = Vec::new();
        let mut l = |lit: i32| fixed.push(lit);
        FixedAssignmentListener::notify_fixed_assignment(&mut l, -3);
        assert_eq!(fixed, vec![-3]);
    }
}

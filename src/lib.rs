//! `cadical`: a faithful Rust port of the [CaDiCaL] SAT solver (3.0.1) by
//! Armin Biere, Katalin Fazekas, Mathias Fleury, Florian Pollitt, Tobias
//! Faller, Nils Froleyks and contributors.
//!
//! The port is function-by-function: for the same input and options it
//! makes the same decisions, conflicts and statistics as the C++ solver.
//! The public API is [`Solver`] (module [`solver`], a port of
//! `cadical.hpp`) plus the call-back traits.  Method names, integer status
//! codes (`10` = SAT, `20` = UNSAT, `0` = unknown) and API contracts
//! follow the C++ API; a few thin Rust conveniences are layered on top
//! (see the [`solver`] module documentation).  All other modules are the
//! solver internals: they are public for the tests and tools in this
//! repository but are not a stable API.
//!
//! [CaDiCaL]: https://github.com/arminbiere/cadical
//!
//! # Quick start
//!
//! Literals are non-zero `i32`: variable `v` (from `1`) is the literal `v`,
//! its negation is `-v`.
//!
//! ```
//! use cadical::Solver;
//!
//! let mut solver = Solver::new();
//! solver.clause(&[1, 2]);        // x1 or x2
//! solver.clause(&[-1, 2]);       // not x1 or x2
//! solver.clause(&[-2, 3]);       // x2 implies x3
//!
//! assert_eq!(solver.solve(), 10);  // or `solver.solve_result().is_sat()`
//! assert_eq!(solver.val(2), 2);    // x2 is true (IPASIR: returns lit or -lit)
//! assert!(solver.value(3));        // x3 is true
//! let model = solver.model();      // [±1, 2, 3]: one literal per variable
//! assert_eq!(&model[1..], &[2, 3]);
//! ```
//!
//! Clauses can also be added literal by literal, terminated by `0`, as in
//! IPASIR: `solver.add(1); solver.add(2); solver.add(0);`.
//!
//! # Assumptions and failed literals
//!
//! Assumptions hold for the next `solve` call only.  If the formula is
//! unsatisfiable under them, [`Solver::failed`] tells which assumptions
//! were used in the refutation (an unsatisfiable core).
//!
//! ```
//! # use cadical::Solver;
//! let mut solver = Solver::new();
//! solver.clause(&[-1, -2]);       // not both
//! solver.assume_all(&[1, 2, 3]);
//! assert!(solver.solve_result().is_unsat());
//! assert!(solver.failed(1) && solver.failed(2));
//! assert!(!solver.failed(3));
//! ```
//!
//! # Incremental use
//!
//! The solver keeps its state between calls: add more clauses, solve
//! again.  Variables that you want to keep using across calls while
//! preprocessing is enabled should be frozen ([`Solver::freeze`]) if
//! they only appear in assumptions; variables in added clauses are handled
//! automatically (eliminated variables are restored).
//!
//! ```
//! # use cadical::Solver;
//! let mut solver = Solver::new();
//! solver.clause(&[1, 2, 3]);
//! let mut models = 0;
//! // Enumerate all models by blocking each one.
//! while solver.solve_result().is_sat() {
//!     models += 1;
//!     let block: Vec<i32> = solver.model().iter().map(|&lit| -lit).collect();
//!     solver.clause(&block);
//! }
//! assert_eq!(models, 7);
//! ```
//!
//! # Terminating from another thread
//!
//! [`Solver`] is not `Send` (see its documentation), but
//! [`Solver::termination_handle`] returns a `Send + Sync` handle which
//! stops a running `solve` (result unknown) and can also be used from a
//! signal handler.  A [`Terminator`] call-back (any `FnMut() -> bool`) is
//! polled by the solver itself:
//!
//! ```
//! # use cadical::Solver;
//! use std::time::{Duration, Instant};
//!
//! let mut solver = Solver::new();
//! let handle = solver.termination_handle();
//! std::thread::spawn(move || {
//!     std::thread::sleep(Duration::from_secs(60));
//!     handle.terminate(); // stop after a minute at the latest
//! });
//! let deadline = Instant::now() + Duration::from_secs(30);
//! solver.connect_terminator(Box::new(move || Instant::now() > deadline));
//! solver.clause(&[1]);
//! assert!(solver.solve_result().is_sat());
//! ```
//!
//! # Learned clauses
//!
//! ```
//! # use cadical::Solver;
//! use std::sync::{Arc, Mutex};
//!
//! let mut solver = Solver::new();
//! let learned = Arc::new(Mutex::new(Vec::<Vec<i32>>::new()));
//! let sink = learned.clone();
//! // Receive every learned clause with at most 3 literals.
//! solver.connect_learner_fn(3, move |clause| sink.lock().unwrap().push(clause.to_vec()));
//! for a in [-1, 1] {
//!     for b in [-2, 2] {
//!         solver.clause(&[a, b]);
//!     }
//! }
//! assert!(solver.solve_result().is_unsat());
//! assert!(!learned.lock().unwrap().is_empty());
//! ```
//!
//! Call-back objects are owned by the solver.  To keep access to a
//! call-back you implemented yourself, connect a clone of an
//! `Rc<RefCell<T>>` (or `Arc<Mutex<T>>`), for which all call-back traits
//! are implemented by forwarding.
//!
//! # Proofs
//!
//! Proof tracing must be enabled right after construction (before adding
//! clauses).  The format is selected by options (default binary DRAT;
//! `binary=0` for ASCII, `lrat`, `frat`, `idrup`, `lidrup`, `veripb`).
//!
//! ```
//! # use cadical::Solver;
//! let path = std::env::temp_dir().join(format!("cadical-doc-{}.drat", std::process::id()));
//! let mut solver = Solver::new();
//! solver.set("binary", 0);
//! assert!(solver.trace_proof(path.to_str().unwrap()));
//! solver.clause(&[1]);
//! solver.clause(&[-1]);
//! assert!(solver.solve_result().is_unsat());
//! solver.close_proof_trace(false);
//! let proof = std::fs::read_to_string(&path).unwrap();
//! assert!(proof.lines().any(|line| line == "0")); // the empty clause
//! # std::fs::remove_file(&path).unwrap();
//! ```
//!
//! Custom tracers implement [`Tracer`] (all events have empty defaults) and
//! are connected with [`Solver::connect_proof_tracer`].
//!
//! # External propagators (IPASIR-UP)
//!
//! An [`ExternalPropagator`] observes assignments to its variables and can
//! propagate literals, make decisions and add clauses during search.  A
//! minimal lazy propagator enforcing "at most one of 1, 2, 3" by checking
//! complete models:
//!
//! ```
//! use cadical::{ExternalPropagator, Solver};
//!
//! #[derive(Default)]
//! struct AtMostOne {
//!     pending: Vec<i32>, // clause being handed to the solver (reversed)
//! }
//!
//! impl ExternalPropagator for AtMostOne {
//!     fn is_lazy(&self) -> bool {
//!         true // only check complete models
//!     }
//!     fn notify_assignment(&mut self, _lits: &[i32]) {}
//!     fn notify_new_decision_level(&mut self) {}
//!     fn notify_backtrack(&mut self, _new_level: usize) {}
//!     fn cb_check_found_model(&mut self, model: &[i32]) -> bool {
//!         let on: Vec<i32> = model.iter().copied().filter(|&l| l > 0).collect();
//!         if on.len() <= 1 {
//!             return true;
//!         }
//!         // Refute the model with the clause (-a | -b), pushed reversed.
//!         self.pending = vec![0, -on[1], -on[0]];
//!         false
//!     }
//!     fn cb_has_external_clause(&mut self, is_forgettable: &mut bool) -> bool {
//!         *is_forgettable = false;
//!         !self.pending.is_empty()
//!     }
//!     fn cb_add_external_clause_lit(&mut self) -> i32 {
//!         self.pending.pop().unwrap()
//!     }
//! }
//!
//! let mut solver = Solver::new();
//! solver.connect_external_propagator(Box::new(AtMostOne::default()));
//! for v in 1..=3 {
//!     solver.add_observed_var(v);
//! }
//! solver.clause(&[1, 2, 3]);
//! solver.clause(&[1, 2]);
//! solver.clause(&[2, 3]);
//! assert!(solver.solve_result().is_sat());
//! assert_eq!(solver.model(), vec![-1, 2, -3]);
//! ```
//!
//! # Porting notes
//!
//! See `PORTING.md` for the porting conventions and `PORT_STATUS.md` for
//! the status of the individual modules.  One module per C++ translation
//! unit (header and implementation with the same base name share one
//! module).

// The port mirrors C++ naming and structure; keep the compiler quiet about
// it so that real errors are not drowned (see 'PORTING.md').
#![allow(dead_code)]
#![allow(unused)]
#![allow(non_snake_case)]
#![allow(non_camel_case_types)]
#![allow(non_upper_case_globals)]
#![allow(static_mut_refs)]
#![allow(unreachable_code)]
#![allow(clippy::all)]

// Macro modules first (textual macro scoping).
#[macro_use]
pub mod logging;
#[macro_use]
pub mod message;
#[macro_use]
pub mod profile;
#[macro_use]
pub mod ema;
#[macro_use]
pub mod limit;
#[macro_use]
pub mod contract;
#[macro_use]
pub mod cover;

pub mod analyze;
pub mod app;
pub mod arena;
pub mod assume;
pub mod averages;
pub mod backbone;
pub mod backtrack;
pub mod backward;
pub mod bins;
pub mod block;
pub mod ccadical;
pub mod checker;
pub mod clause;
pub mod collect;
pub mod compact;
pub mod condition;
pub mod config;
pub mod congruence;
pub mod constrain;
pub mod decide;
pub mod decompose;
pub mod deduplicate;
pub mod definition;
pub mod delay;
pub mod drattracer;
pub mod elim;
pub mod elimfast;
pub mod extend;
pub mod external;
pub mod external_propagate;
pub mod factor;
pub mod file;
pub mod flags;
pub mod flip;
pub mod format;
pub mod frattracer;
pub mod gates;
pub mod heap;
pub mod idruptracer;
pub mod instantiate;
pub mod internal;
pub mod ipasir;
pub mod kitten;
pub mod level;
pub mod lidruptracer;
pub mod lookahead;
pub mod lratchecker;
pub mod lrattracer;
pub mod lucky;
pub mod minimize;
#[doc(hidden)]
pub mod mobical;
pub mod occs;
pub mod options;
pub mod parse;
pub mod phases;
pub mod prelude;
pub mod probe;
pub mod proof;
pub mod propagate;
pub mod queue;
pub mod radix;
pub mod random;
pub mod range;
pub mod reap;
pub mod reduce;
pub mod reluctant;
pub mod rephase;
pub mod report;
pub mod resources;
pub mod restart;
pub mod restore;
pub mod score;
pub mod shrink;
pub mod signal;
pub mod solution;
pub mod solver;
pub mod sort;
pub mod stable;
pub mod stats;
pub mod subsume;
pub mod sweep;
pub mod terminal;
pub mod ternary;
pub mod testing;
pub mod tier;
pub mod tracer;
pub mod transred;
pub mod unstable;
pub mod util;
pub mod var;
pub mod veripbtracer;
pub mod version;
pub mod vivify;
pub mod walk;
pub mod walk_full_occs;
pub mod warmup;
pub mod watch;

pub use solver::{
    learner_fn, ClauseIterator, ExternalPropagator, FixedAssignmentListener, Learner, LearnerFn,
    SolveResult, Solver, TerminationHandle, Terminator, WitnessIterator, SATISFIABLE, UNKNOWN,
    UNSATISFIABLE,
};
pub use tracer::{ConclusionType, FileTracer, InternalTracer, StatTracer, Tracer, TracerRef};

const _: () = assert!(std::mem::size_of::<clause::Clause>() == 24 && std::mem::size_of::<watch::Watch>() == 16);

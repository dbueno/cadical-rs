//! Callbacks: export short learned clauses with a closure, observe fixed
//! literals through a shared listener object, stop the search with a
//! termination handle from a timer thread, and write a DRAT proof.
//!
//! ```text
//! cargo run --release --example learner -- [holes] [proof-file]
//! ```

use std::cell::RefCell;
use std::rc::Rc;
use std::time::Duration;

use cadical::{FixedAssignmentListener, Solver};

/// A listener we want to keep access to after solving: connect a clone of
/// an 'Rc<RefCell<..>>' (the trait is implemented for it by forwarding).
#[derive(Default)]
struct Units {
    fixed: Vec<i32>,
}

impl FixedAssignmentListener for Units {
    fn notify_fixed_assignment(&mut self, lit: i32) {
        self.fixed.push(lit);
    }
}

fn main() {
    let mut args = std::env::args().skip(1);
    let holes: i32 = args.next().map(|s| s.parse().expect("number of holes")).unwrap_or(7);
    let proof = args.next();
    let pigeons = holes + 1;

    let mut solver = Solver::new();
    if let Some(path) = &proof {
        // Must happen right after construction (before adding clauses).
        solver.set("binary", 0); // ASCII DRAT
        assert!(solver.trace_proof(path), "can not write proof to '{path}'");
    }

    // Learned clauses with at most 3 literals, as whole slices.
    let learned = Rc::new(RefCell::new(Vec::<Vec<i32>>::new()));
    let sink = learned.clone();
    solver.connect_learner_fn(3, move |clause| sink.borrow_mut().push(clause.to_vec()));

    let units = Rc::new(RefCell::new(Units::default()));
    solver.connect_fixed_listener(Box::new(units.clone()));

    // Give up after 10 seconds, from another thread.
    let handle = solver.termination_handle();
    std::thread::spawn(move || {
        std::thread::sleep(Duration::from_secs(10));
        handle.terminate();
    });

    // Pigeon hole principle: 'pigeons' pigeons do not fit into 'holes' holes.
    let p = |i: i32, j: i32| i * holes + j + 1;
    for i in 0..pigeons {
        solver.clause(&(0..holes).map(|j| p(i, j)).collect::<Vec<_>>());
    }
    for j in 0..holes {
        for i in 0..pigeons {
            for k in i + 1..pigeons {
                solver.clause(&[-p(i, j), -p(k, j)]);
            }
        }
    }

    let res = solver.solve_result();
    println!("result: {res:?}");
    let learned = learned.borrow();
    println!("{} short learned clauses exported", learned.len());
    for clause in learned.iter().take(5) {
        println!("  {clause:?}");
    }
    println!("{} fixed literals notified", units.borrow().fixed.len());

    if proof.is_some() {
        solver.close_proof_trace(false);
        println!("proof written to '{}'", proof.unwrap());
    }
}

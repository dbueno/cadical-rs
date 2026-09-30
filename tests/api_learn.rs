//! Port of `cadical/test/api/learn.cpp`.
//!
//! In C++ the `Wrapper` object connects itself as learner and the test
//! reads its `clauses` counter after solving.  In Rust the solver owns the
//! connected learner (`Box<dyn Learner>`), so the counter is shared through
//! an `Rc<Cell<..>>` (see the API notes).

mod common;
use common::{out, outln};

use cadical::{Learner, Solver};
use std::cell::Cell;
use std::rc::Rc;

struct Wrapper {
    solver: *const Solver, // Only used for printing (as in C++).
    clause: Vec<i32>,
    clauses: Rc<Cell<u32>>,
}

impl Wrapper {
    /// Creates the learner, connects it to `solver` and returns the shared
    /// `clauses` counter.
    fn connect(solver: &mut Solver) -> Rc<Cell<u32>> {
        let clauses = Rc::new(Cell::new(0));
        let wrapper = Wrapper { solver: &*solver, clause: Vec::new(), clauses: clauses.clone() };
        solver.connect_learner(Box::new(wrapper));
        clauses
    }
}

impl Learner for Wrapper {
    fn learning(&mut self, size: i32) -> bool {
        let _ = size;
        true
    }
    fn learn(&mut self, lit: i32) {
        if lit != 0 {
            self.clause.push(lit);
        } else {
            out!("solver[{:p}] imported clause of size {}:", self.solver, self.clause.len());
            for lit in &self.clause {
                out!(" {}", lit);
            }
            outln!();
            self.clause.clear();
            self.clauses.set(self.clauses.get() + 1);
        }
    }
}

fn formula(solver: &mut Solver) {
    let mut r = -1;
    while r < 3 {
        let mut s = -1;
        while s < 3 {
            let mut t = -1;
            while t < 3 {
                solver.add(r * 1);
                solver.add(s * 2);
                solver.add(t * 3);
                solver.add(0);
                t += 2;
            }
            s += 2;
        }
        r += 2;
    }
}

fn main() {
    let mut ping = Solver::new();
    let mut pong = Solver::new();
    ping.set("log", 1);
    pong.set("log", 1);
    ping.set("congruence", 0);
    pong.set("congruence", 0);
    ping.set("sweep", 0);
    pong.set("sweep", 0);
    ping.set("otfs", 0);
    pong.set("otfs", 0);
    ping.set("factor", 0);
    pong.set("factor", 0);
    ping.set("fastelim", 0);
    pong.set("fastelim", 0);
    let wing = Wrapper::connect(&mut ping);
    let wong = Wrapper::connect(&mut pong);
    formula(&mut ping);
    formula(&mut pong);
    let a = ping.solve();
    outln!("ping returns {}", a);
    outln!("wong imported {} clauses", wing.get());
    let b = pong.solve();
    outln!("pong returns {}", b);
    outln!("wing imported {} clauses", wing.get());
    assert!(a == b);
    assert!(a == 20);
    assert!(wing.get() == wong.get());
    assert!(wing.get() > 3);
    // '~Wrapper' disconnects the learners.
    drop(ping.disconnect_learner());
    drop(pong.disconnect_learner());
}

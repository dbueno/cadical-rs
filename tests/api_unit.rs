//! Port of `cadical/test/api/unit.cpp`.

mod common;
use common::outln;

use cadical::Solver;

fn main() {
    let mut solver = Solver::new();
    solver.set("factor", 0);
    solver.add(1);
    solver.add(0);
    let mut res = solver.solve();
    outln!("solver.solve () = {}", res);
    assert!(res == 10);
    res = solver.val(1);
    outln!("solver.val (1) = {}", res);
    outln!("solver.val (-1) = {}", solver.val(-1));
    outln!("solver.val (2) = {}", solver.val(2));
    outln!("solver.val (3) = {}", solver.val(3));
    assert!(res > 0);
}

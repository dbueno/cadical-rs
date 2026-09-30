//! Port of `cadical/test/api/morenmore.cpp`.

use cadical::Solver;

fn main() {
    let mut solver = Solver::new();
    solver.set("factor", 0);
    let n = 100;
    for i in 1..n {
        for j in 1..i {
            solver.add(-j);
        }
        solver.add(i);
        solver.add(0);
    }
    let mut res = solver.solve();
    assert!(res == 10);
    for i in 1..n {
        res = solver.val(i);
        assert!(res > 0);
    }
}

//! Port of `cadical/test/api/newdelete.cpp`.

use cadical::Solver;

fn main() {
    let solver = Box::new(Solver::new());
    drop(solver);
}

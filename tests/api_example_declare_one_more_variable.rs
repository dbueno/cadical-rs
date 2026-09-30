//! Port of `cadical/test/api/example_declare_one_more_variable.cpp`.

use cadical::Solver;

fn main() {
    let mut solver = Box::new(Solver::new());

    // ------------------------------------------------------------------
    // Encode Problem and check without assumptions.

    let tie = solver.declare_one_more_variable();
    let shirt = solver.declare_one_more_variable();
    assert!(solver.vars() >= 2);

    solver.add(-tie);
    solver.add(shirt);
    solver.add(0);
    solver.add(tie);
    solver.add(shirt);
    solver.add(0);
    solver.add(-tie);
    solver.add(-shirt);
    solver.add(0);

    let mut res = solver.solve(); // Solve instance.
    assert!(res == 10); // Check it is 'SATISFIABLE'.

    res = solver.val(tie); // Obtain assignment of 'TIE'.
    assert!(res == -tie); // Check 'TIE' assigned to 'false'.

    res = solver.val(shirt); // Obtain assignment of 'SHIRT'.
    assert!(res == shirt); // Check 'SHIRT' assigned to 'true'.

    res = solver.val(-tie);
    assert!(res == -tie);

    res = solver.val(-shirt);
    assert!(res == shirt);

    // ------------------------------------------------------------------
    // Incrementally solve again under one assumption.

    solver.assume(tie); // Now force 'TIE' to true.

    res = solver.solve(); // Solve again incrementally.
    assert!(res == 20); // Check it is 'UNSATISFIABLE'.

    let failed = solver.failed(tie); // Check 'TIE' responsible.
    assert!(failed); // Yes, 'TIE' in core.

    let failed = solver.failed(shirt); // Check 'SHIRT' responsible.
    assert!(!failed); // No, 'SHIRT' not in core.

    // ------------------------------------------------------------------
    // Incrementally solve once more under another assumption.

    solver.assume(-shirt); // Now force 'SHIRT' to false.

    res = solver.solve(); // Solve again incrementally.
    assert!(res == 20); // Check it is 'UNSATISFIABLE'.

    let failed = solver.failed(tie); // Check 'TIE' responsible.
    assert!(!failed); // No, 'TIE' not in core.

    let failed = solver.failed(-shirt); // Check '!SHIRT' responsible.
    assert!(failed); // Yes, '!SHIRT' in core.

    // ------------------------------------------------------------------

    drop(solver);
}

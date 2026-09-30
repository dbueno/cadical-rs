//! Port of `cadical/test/api/example_constraint.cpp`.

use cadical::Solver;

fn main() {
    let mut solver = Box::new(Solver::new());
    let tie = solver.declare_more_variables(2);
    let shirt = tie - 1;

    // ------------------------------------------------------------------
    // Encode Problem and check without assumptions.

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
    assert!(res < 0); // Check 'TIE' assigned to 'false'.

    res = solver.val(shirt); // Obtain assignment of 'SHIRT'.
    assert!(res > 0); // Check 'SHIRT' assigned to 'true'.

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
    // Incrementally solve with constraint.

    solver.constrain(tie);
    solver.constrain(-shirt);
    solver.constrain(0);

    res = solver.solve(); // Solve again incrementally.
    assert!(res == 20); // Check it is 'UNSATISFIABLE'.

    let failed = solver.constraint_failed(); // Check constraint responsible.
    assert!(failed); // Yes, constraint was used.

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

//! Port of `cadical/test/api/example.cpp` (the example from the header
//! file).

use cadical::Solver;

fn main() {
    let mut solver = Box::new(Solver::new());
    solver.set("factor", 0);

    // ------------------------------------------------------------------
    // Encode Problem and check without assumptions.

    const TIE: i32 = 1;
    const SHIRT: i32 = 2;

    solver.add(-TIE);
    solver.add(SHIRT);
    solver.add(0);
    solver.add(TIE);
    solver.add(SHIRT);
    solver.add(0);
    solver.add(-TIE);
    solver.add(-SHIRT);
    solver.add(0);

    let mut res = solver.solve(); // Solve instance.
    assert!(res == 10); // Check it is 'SATISFIABLE'.

    res = solver.val(TIE); // Obtain assignment of 'TIE'.
    assert!(res == -TIE); // Check 'TIE' assigned to 'false'.

    res = solver.val(SHIRT); // Obtain assignment of 'SHIRT'.
    assert!(res == SHIRT); // Check 'SHIRT' assigned to 'true'.

    res = solver.val(-TIE);
    assert!(res == -TIE);

    res = solver.val(-SHIRT);
    assert!(res == SHIRT);

    // ------------------------------------------------------------------
    // Incrementally solve again under one assumption.

    solver.assume(TIE); // Now force 'TIE' to true.

    res = solver.solve(); // Solve again incrementally.
    assert!(res == 20); // Check it is 'UNSATISFIABLE'.

    let failed = solver.failed(TIE); // Check 'TIE' responsible.
    assert!(failed); // Yes, 'TIE' in core.

    let failed = solver.failed(SHIRT); // Check 'SHIRT' responsible.
    assert!(!failed); // No, 'SHIRT' not in core.

    // ------------------------------------------------------------------
    // Incrementally solve once more under another assumption.

    solver.assume(-SHIRT); // Now force 'SHIRT' to false.

    res = solver.solve(); // Solve again incrementally.
    assert!(res == 20); // Check it is 'UNSATISFIABLE'.

    let failed = solver.failed(TIE); // Check 'TIE' responsible.
    assert!(!failed); // No, 'TIE' not in core.

    let failed = solver.failed(-SHIRT); // Check '!SHIRT' responsible.
    assert!(failed); // Yes, '!SHIRT' in core.

    // ------------------------------------------------------------------

    drop(solver);
}

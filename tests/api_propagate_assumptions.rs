//! Port of `cadical/test/api/propagate_assumptions.cpp`.
//!
//! The C++ test uses a global `Solver *`; here it is passed explicitly.

mod common;
use common::{out, outln};

use cadical::Solver;
use std::collections::BTreeSet;

fn check_test_case(solver: &mut Solver, constrain: &[i32], assumptions: &[i32], expected_result: i32) {
    out!("Test case: ");
    out!("<");
    if !constrain.is_empty() {
        for &lit in constrain {
            solver.constrain(lit);
            out!(" {}", lit);
        }
        solver.constrain(0);
    }

    out!(" >[");
    if !assumptions.is_empty() {
        for &lit in assumptions {
            solver.assume(lit);
            out!(" {}", lit);
        }
    }
    out!(" ] -> ");

    let mut res = solver.propagate();
    out!("{} ", res);

    assert!(res == expected_result);

    // Check if returned set is subset of the expected result

    if res == 10 {
        out!(" (model: [");

        let mut model = Vec::new();
        for idx in 1..=3 {
            let lit = solver.val(idx);
            model.push(lit);
            out!(" {}", lit);
        }
        outln!(" ])");

        if !constrain.is_empty() {
            for &lit in constrain {
                solver.constrain(lit);
            }
            solver.constrain(0);
        }
        if !assumptions.is_empty() {
            for &lit in assumptions {
                solver.assume(lit);
            }
        }
        for &lit in &model {
            solver.assume(lit);
        }

        res = solver.solve();
        assert!(res == 10);
    } else if res == 0 {
        out!(" (implicants: [");
        let mut implicants = Vec::new();
        solver.implied(&mut implicants);
        // Check that every propagation holds
        for &lit in &implicants {
            out!(" {}", lit);
            for &lit in assumptions {
                solver.assume(lit);
            }
            if !constrain.is_empty() {
                for &lit in constrain {
                    solver.constrain(lit);
                }
                solver.constrain(0);
            }

            solver.assume(-lit);

            res = solver.solve();
            assert!(res == 20);
        }
        outln!(" ])");
    } else {
        out!(" (core: [");
        assert!(res == 20);
        let mut core = BTreeSet::new();
        for &lit in assumptions {
            if solver.failed(lit) {
                core.insert(lit);
                out!(" {}", lit);
            }
        }
        outln!(" ])");

        // Rerun call with the core-subset of assumptions
        if !constrain.is_empty() {
            for &lit in constrain {
                solver.constrain(lit);
            }
            solver.constrain(0);
        }
        for &lit in &core {
            solver.assume(lit);
        }

        res = solver.solve();
        assert!(res == 20);
    }
}

// Taken from incproof.cpp test file
fn path(name: &str) -> String {
    format!("{}/test-api-propagate-{}", common::build_dir(), name)
}

fn main() {
    let mut solver = Box::new(Solver::new());
    // ------------------------------------------------------------------
    // Encode Problem and check without assumptions.

    const TIE: i32 = 1;
    const SHIRT: i32 = 2;
    const HAT: i32 = 3;
    const SHOES: i32 = 4;
    const SLIPPERS: i32 = 5;

    solver.set("binary", 0);
    solver.set("lidrup", 1);
    solver.set("factor", 0);
    solver.trace_proof(&path("propagate_assumptions.lidrup"));
    solver.set("flushproof", 1);

    solver.add(-TIE);
    solver.add(SHIRT);
    solver.add(0);
    solver.add(TIE);
    solver.add(SHIRT);
    solver.add(0);
    solver.add(-TIE);
    solver.add(-SHIRT);
    solver.add(0);

    // ------------------------------------------------------------------
    // Check different test cases, signature:
    // ({literals of constrain},{assumption literals},expected results)

    let s = &mut *solver;

    check_test_case(s, &[], &[], 0);

    check_test_case(s, &[HAT], &[], 0);

    check_test_case(s, &[HAT], &[-HAT], 20);

    check_test_case(s, &[], &[TIE, -TIE], 20);

    check_test_case(s, &[], &[TIE], 20);

    check_test_case(s, &[], &[-TIE], 0);

    check_test_case(s, &[], &[SHIRT], 0);
    check_test_case(s, &[], &[-SHIRT, HAT], 20);

    check_test_case(s, &[], &[SHIRT, TIE], 20);
    check_test_case(s, &[], &[SHIRT, -TIE], 0);
    check_test_case(s, &[], &[-SHIRT, TIE], 20);
    check_test_case(s, &[], &[-SHIRT, -TIE], 20);
    check_test_case(s, &[HAT], &[SHIRT, -TIE, HAT], 10);

    // Check when root-level propagation satisfies
    s.add(-TIE);
    s.add(0);
    s.add(SHIRT);
    s.add(0);
    s.add(HAT);
    s.add(0);

    check_test_case(s, &[HAT], &[SHIRT, -TIE, HAT], 10);
    check_test_case(s, &[], &[], 10);

    // Check when root-level propagation falsifies
    s.add(-HAT);
    s.add(0);
    check_test_case(s, &[], &[], 20);

    s.close_proof_trace(true);
    drop(solver);

    // Check when last level propagation is needed for conflict detection
    let mut solver = Box::new(Solver::new());
    solver.set("factor", 0);

    solver.add(SHOES);
    solver.add(SLIPPERS);
    solver.add(0);
    solver.add(-SHOES);
    solver.add(-SLIPPERS);
    solver.add(0);

    solver.add(-HAT);
    solver.add(SLIPPERS);
    solver.add(0);
    solver.add(-TIE);
    solver.add(SHIRT);
    solver.add(0);
    solver.add(-6);
    solver.add(7);
    solver.add(0);
    solver.add(-6);
    solver.add(-8);
    solver.add(0);
    solver.add(-7);
    solver.add(-SHIRT);
    solver.add(-TIE);
    solver.add(8);
    solver.add(0);

    check_test_case(&mut solver, &[], &[HAT, TIE, 6], 20);

    // The C++ test never deletes the second solver.
    std::mem::forget(solver);
}

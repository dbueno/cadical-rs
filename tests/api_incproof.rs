//! Port of `cadical/test/api/incproof.cpp`.

mod common;

use cadical::Solver;

fn path(name: &str) -> String {
    format!("{}/test-api-apitrace-{}", common::build_dir(), name)
}

fn main() {
    {
        for lrat in 0..2 {
            let mut solver = Box::new(Solver::new());
            solver.set("log", 1);
            solver.set("binary", 0);
            solver.set("verbose", 3);
            solver.set("flushproof", 1);
            solver.configure("plain");
            solver.set("elim", 1);
            solver.set("lrat", lrat);
            solver.trace_proof(&path(if lrat != 0 { "inctrace1.lrat" } else { "inctrace1.drup" }));
            solver.clause3(1, 2, 3);
            solver.simplify(3);
            solver.clause3(-1, -2, -3);
            solver.solve();
            solver.close_proof_trace(true);
            drop(solver);
        }
    }

    {
        for lrat in 0..2 {
            let mut solver = Box::new(Solver::new());
            solver.set("log", 1);
            solver.set("binary", 0);
            solver.set("verbose", 3);
            solver.set("flushproof", 1);
            solver.configure("plain");
            solver.set("elim", 1);
            solver.set("lrat", lrat);
            solver.trace_proof(&path(if lrat != 0 { "inctrace2.lrat" } else { "inctrace2.drup" }));
            let mut i = -1;
            while i <= -1 {
                let mut j = -1;
                while j <= 1 {
                    let mut k = -1;
                    while k <= 1 {
                        solver.clause3(i * 1, j * 2, k * 3);
                        k += 2;
                    }
                    j += 2;
                }
                i += 2;
            }
            solver.simplify(3);
            let mut i = 1;
            while i <= 1 {
                let mut j = -1;
                while j <= 1 {
                    let mut k = -1;
                    while k <= 1 {
                        solver.clause3(i * 1, j * 2, k * 3);
                        k += 2;
                    }
                    j += 2;
                }
                i += 2;
            }
            solver.solve();
            solver.close_proof_trace(true);
            drop(solver);
        }
    }
}

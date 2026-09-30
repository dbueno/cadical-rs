//! Solve the N-queens puzzle and count all its solutions.
//!
//! ```text
//! cargo run --release --example nqueens -- 8
//! ```

use cadical::Solver;

fn main() {
    let n: i32 = std::env::args().nth(1).map(|s| s.parse().expect("board size")).unwrap_or(8);
    assert!(n > 0, "board size must be positive");

    // Variable 'q(r, c)' is true iff there is a queen on row 'r', column 'c'.
    let q = |r: i32, c: i32| r * n + c + 1;
    let mut solver = Solver::new();

    for r in 0..n {
        // At least one queen per row.
        solver.clause(&(0..n).map(|c| q(r, c)).collect::<Vec<_>>());
    }
    // At most one queen per row, column and diagonal (pairwise encoding).
    for r1 in 0..n {
        for c1 in 0..n {
            for r2 in r1..n {
                for c2 in 0..n {
                    if (r2, c2) <= (r1, c1) {
                        continue;
                    }
                    let attacks = r1 == r2 || c1 == c2 || (r1 - r2).abs() == (c1 - c2).abs();
                    if attacks {
                        solver.clause(&[-q(r1, c1), -q(r2, c2)]);
                    }
                }
            }
        }
    }

    let mut solutions = 0;
    while solver.solve_result().is_sat() {
        solutions += 1;
        let queens: Vec<i32> = (1..=n * n).filter(|&v| solver.value(v)).collect();
        if solutions == 1 {
            println!("first solution:");
            for r in 0..n {
                let row: String = (0..n).map(|c| if solver.value(q(r, c)) { " Q" } else { " ." }).collect();
                println!("{row}");
            }
        }
        // Block this solution (it suffices to block the positions of the queens).
        solver.clause(&queens.iter().map(|&v| -v).collect::<Vec<_>>());
    }
    println!("{n}-queens has {solutions} solutions");
}

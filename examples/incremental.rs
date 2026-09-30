//! Incremental solving with assumptions: find the smallest number of
//! colours for a graph (here the Petersen graph) by activating
//! "at most k colours" constraints through assumption literals, and show
//! the unsatisfiable core ('failed' assumptions) for the first failing k.
//!
//! ```text
//! cargo run --release --example incremental
//! ```

use cadical::Solver;

fn main() {
    // Petersen graph: outer 5-cycle, inner pentagram, spokes.
    let mut edges = Vec::new();
    for i in 0..5 {
        edges.push((i, (i + 1) % 5));
        edges.push((5 + i, 5 + (i + 2) % 5));
        edges.push((i, 5 + i));
    }
    let nodes = 10;
    let max_colours = 4;

    // Variable 'x(v, c)': node 'v' has colour 'c'.
    let x = |v: i32, c: i32| v * max_colours + c + 1;
    // Selector 'use_colour(c)': colour 'c' may be used.
    let use_colour = |c: i32| nodes * max_colours + c + 1;

    let mut solver = Solver::new();
    for v in 0..nodes {
        solver.clause(&(0..max_colours).map(|c| x(v, c)).collect::<Vec<_>>());
        for c in 0..max_colours {
            // Colour 'c' is only available if its selector is true.
            solver.clause(&[-x(v, c), use_colour(c)]);
        }
    }
    for &(u, v) in &edges {
        for c in 0..max_colours {
            solver.clause(&[-x(u, c), -x(v, c)]);
        }
    }

    // Try k = 1, 2, ... colours by assuming the other selectors false.
    // The solver keeps learned clauses between the calls.
    for k in 1..=max_colours {
        let assumptions: Vec<i32> = (k..max_colours).map(|c| -use_colour(c)).collect();
        solver.assume_all(&assumptions);
        let res = solver.solve_result();
        if res.is_sat() {
            let colouring: Vec<i32> =
                (0..nodes).map(|v| (0..max_colours).find(|&c| solver.value(x(v, c))).unwrap()).collect();
            println!("k = {k}: colourable, colouring = {colouring:?}");
            break;
        }
        let core: Vec<i32> = assumptions.iter().copied().filter(|&a| solver.failed(a)).collect();
        println!("k = {k}: not colourable (failed assumptions: {core:?})");
    }

    println!(
        "{} conflicts, {} decisions in total",
        solver.get_statistic_value("conflicts"),
        solver.get_statistic_value("decisions")
    );
}

//! Port of `cadical/test/api/traverse.cpp`.

mod common;
use common::{out, outln};

use cadical::{ClauseIterator, Solver, WitnessIterator};

fn path(suffix: &str) -> String {
    format!("{}/test-api-traverse.{}", common::build_dir(), suffix)
}

struct WitnessChecker;

impl WitnessChecker {
    fn match2(&self, a: i32, b: i32) -> bool {
        (a == -3 && b == 1) || (a == 1 && b == -3) || (a == -3 && b == 2) || (a == 2 && b == -3)
    }
    fn match3(&self, a: i32, b: i32, c: i32) -> bool {
        (a == 3 && b == -1 && c == -2)
            || (a == 3 && b == -2 && c == -1)
            || (a == -1 && b == 3 && c == -2)
            || (a == -2 && b == 3 && c == -1)
            || (a == -1 && b == -2 && c == 3)
            || (a == -2 && b == -1 && c == 3)
    }
}

impl WitnessIterator for WitnessChecker {
    fn witness(&mut self, c: &[i32], w: &[i32], _id: i64) -> bool {
        for lit in w {
            out!("{} ", lit);
        }
        out!("0 ");
        for lit in c {
            out!("{} ", lit);
        }
        outln!("0");
        if c.len() == 1 {
            assert!(c[0] == 5);
            assert!(w.len() == 1);
            assert!(w[0] == 5);
        } else {
            assert!(w.len() == 1);
            assert!(w[0] != -3);
            assert!(w[0] != 3);
            assert!(w[0].abs() == 1 || w[0].abs() == 2);
            if c.len() == 2 {
                assert!(self.match2(c[0], c[1]));
            } else {
                assert!(c.len() == 3);
                assert!(self.match3(c[0], c[1], c[2]));
            }
        }
        true
    }
}

struct ClauseChecker;

impl ClauseIterator for ClauseChecker {
    fn clause(&mut self, c: &[i32]) -> bool {
        for lit in c {
            out!("{} ", lit);
        }
        outln!("0");
        assert!(c.len() == 1);
        assert!(c[0] == 4);
        true
    }
}

fn main() {
    let mut cadical = Solver::new();
    cadical.set("lucky", 0);
    cadical.set("factor", 0);

    // And gate 3 = 1 & 2>

    cadical.add(-3);
    cadical.add(1);
    cadical.add(0);

    cadical.add(-3);
    cadical.add(2);
    cadical.add(0);

    cadical.add(3);
    cadical.add(-1);
    cadical.add(-2);
    cadical.add(0);

    // Force 4 to true.

    cadical.add(4);
    cadical.add(1);
    cadical.add(2);
    cadical.add(0);

    cadical.add(4);
    cadical.add(-1);
    cadical.add(2);
    cadical.add(0);

    cadical.add(4);
    cadical.add(1);
    cadical.add(-2);
    cadical.add(0);

    cadical.add(4);
    cadical.add(-1);
    cadical.add(-2);
    cadical.add(0);

    // Force 5 to true too.

    cadical.add(5);
    cadical.add(1);
    cadical.add(0);

    cadical.add(5);
    cadical.add(-1);
    cadical.add(0);

    cadical.freeze(3);
    cadical.freeze(4);

    cadical.simplify(1);

    // Now we expect '5' to be part of the witness, but '3' and '4' to be part
    // the traversed clauses and check this too.  See the long comment on
    // 'frozen' versus 'non-frozen' unit traversal in 'external.cpp'.

    cadical.write_dimacs(&path("clauses"), 5);
    cadical.write_extension(&path("extensions"));

    outln!("clauses");
    let mut clause_checker = ClauseChecker;
    cadical.traverse_clauses(&mut clause_checker);

    outln!("witnesses");
    let mut witness_checker = WitnessChecker;
    cadical.traverse_witnesses_backward(&mut witness_checker);
}

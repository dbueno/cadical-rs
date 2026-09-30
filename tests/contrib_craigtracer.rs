//! Port of `cadical/test/contrib/craigtracer.cpp` (uses the Rust port of
//! `contrib/craigtracer` in `tests/common/craigtracer.rs`).

mod common;

use cadical::{Solver, UNSATISFIABLE};
use common::craigtracer::{CraigCnfType, CraigClauseType, CraigConstruction, CraigInterpolant, CraigTracer, CraigVarType};

fn main() {
    let mut solver = Box::new(Solver::new());
    solver.set("factor", 0); // important: deactivate BVA
    let (tracer, tracer_ref) = CraigTracer::connect(&mut solver, true);
    tracer.borrow_mut().set_craig_construction(CraigConstruction::ASYMMETRIC);

    tracer.borrow_mut().label_variable(1, CraigVarType::Global);
    tracer.borrow_mut().label_clause(1, CraigClauseType::AClause);
    tracer.borrow_mut().label_clause(2, CraigClauseType::BClause);
    solver.set("factor", 0);
    solver.add(-1);
    solver.add(0);
    solver.add(1);
    solver.add(0);
    assert!(solver.solve() == UNSATISFIABLE);

    let mut next_var = 2;
    let mut clauses: Vec<Vec<i32>> = Vec::new();
    let result = tracer.borrow_mut().create_craig_interpolant(CraigInterpolant::Asymmetric, &mut clauses, &mut next_var);
    assert!(result == CraigCnfType::Normal);
    assert!(clauses == vec![vec![-1]]);
    assert!(next_var == 2);

    let disconnected = solver.disconnect_proof_tracer(tracer_ref);
    assert!(disconnected.is_some());
    drop(disconnected);
    drop(tracer);
    drop(solver);
}

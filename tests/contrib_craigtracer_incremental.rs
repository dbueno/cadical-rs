//! Port of `cadical/test/contrib/craigtracer_incremental.cpp` (uses the
//! Rust port of `contrib/craigtracer` in `src/craigtracer.rs`).

mod common;

use cadical::{Solver, UNSATISFIABLE};
use cadical::craigtracer::{CraigCnfType, CraigClauseType, CraigConstruction, CraigInterpolant, CraigTracer, CraigVarType};

fn main() {
    let mut solver = Box::new(Solver::new());
    solver.set("factor", 0); // important: deactivate BVA
    let (tracer, tracer_ref) = CraigTracer::connect(&mut solver, true);
    tracer.borrow_mut().set_craig_construction(CraigConstruction::ASYMMETRIC);

    tracer.borrow_mut().label_variable(1, CraigVarType::ALocal);
    tracer.borrow_mut().label_variable(2, CraigVarType::BLocal);
    tracer.borrow_mut().label_variable(3, CraigVarType::Global);
    tracer.borrow_mut().label_clause(1, CraigClauseType::AClause);
    tracer.borrow_mut().label_clause(2, CraigClauseType::BClause);
    solver.set("factor", 0);
    solver.add(1);
    solver.add(0);
    solver.add(2);
    solver.add(0);

    // ------------------------------------------------
    // A side is UNSATISFIABLE => Craig interpolant is CONSTANT0
    solver.assume(-1);
    assert!(solver.solve() == UNSATISFIABLE);

    let mut next_var = 2;
    let mut clauses: Vec<Vec<i32>> = Vec::new();
    let mut result =
        tracer.borrow_mut().create_craig_interpolant(CraigInterpolant::Asymmetric, &mut clauses, &mut next_var);
    assert!(result == CraigCnfType::Constant0);
    assert!(clauses == vec![Vec::<i32>::new()]);
    assert!(next_var == 2);

    // ------------------------------------------------
    // B side is UNSATISFIABLE
    solver.assume(-2);
    assert!(solver.solve() == UNSATISFIABLE);

    result = tracer.borrow_mut().create_craig_interpolant(CraigInterpolant::Asymmetric, &mut clauses, &mut next_var);
    assert!(result == CraigCnfType::Constant1);
    assert!(clauses == Vec::<Vec<i32>>::new());
    assert!(next_var == 2);

    // ------------------------------------------------
    tracer.borrow_mut().label_clause(3, CraigClauseType::AClause);
    tracer.borrow_mut().label_constraint(CraigClauseType::BClause);
    solver.add(-1);
    solver.add(3);
    solver.add(0);
    solver.constrain(-2);
    solver.constrain(-3);
    solver.constrain(0);
    assert!(solver.solve() == UNSATISFIABLE);

    result = tracer.borrow_mut().create_craig_interpolant(CraigInterpolant::Asymmetric, &mut clauses, &mut next_var);
    assert!(result == CraigCnfType::Normal);
    assert!(clauses == vec![vec![3]]);
    assert!(next_var == 2);

    let disconnected = solver.disconnect_proof_tracer(tracer_ref);
    assert!(disconnected.is_some());
    drop(disconnected);
    drop(tracer);
    drop(solver);
}

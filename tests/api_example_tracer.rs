//! Port of `cadical/test/api/example_tracer.cpp`.
//!
//! Like the C++ test this uses internal parts of the library (`Testing`,
//! `File`, the built-in checkers and tracers) which are not part of the
//! stable API.  The proof files are written to the test output directory
//! (see `common::build_dir`) instead of `/tmp`.

mod common;

use cadical::checker::Checker;
use cadical::file::File;
use cadical::frattracer::FratTracer;
use cadical::internal::Internal;
use cadical::lratchecker::LratChecker;
use cadical::lrattracer::LratTracer;
use cadical::testing::Testing;
use cadical::{FileTracer, InternalTracer, Solver, StatTracer};

fn main() {
    let mut solver = Box::new(Solver::new());
    let internal: *mut Internal = Testing::new(&mut solver).internal();

    let prefix = format!("{}/cadical-api-test-example-tracer", common::build_dir());
    let pid = common::pid();

    let lrat_proof_path = format!("{}-{}-lrat.proof", prefix, pid);
    let frat_proof_path = format!("{}-{}-frat.proof", prefix, pid);
    let veripb_proof_path = format!("{}-{}-veripb.proof", prefix, pid);

    let f1 = File::write(internal, &lrat_proof_path);
    let f2 = File::write(internal, &frat_proof_path);
    assert!(!f1.is_null() && !f2.is_null());
    // SAFETY: 'File::write' returns a pointer obtained from 'Box::into_raw'.
    let (f1, f2) = unsafe { (Box::from_raw(f1), Box::from_raw(f2)) };

    let t1: Box<dyn InternalTracer> = Box::new(LratChecker::new(internal));
    let t2: Box<dyn InternalTracer> = Box::new(Checker::new(internal));
    let ft1: Box<dyn FileTracer> = Box::new(LratTracer::new(internal, f1, false));
    let ft2: Box<dyn FileTracer> = Box::new(FratTracer::new(internal, f2, false, false));
    let st1: Box<dyn StatTracer> = Box::new(LratChecker::new(internal));
    let st2: Box<dyn StatTracer> = Box::new(Checker::new(internal));

    // ------------------------------------------------------------------

    let t1 = solver.connect_proof_tracer_internal(t1, true, false);
    let _t2 = solver.connect_proof_tracer_internal(t2, false, false);
    let ft1 = solver.connect_proof_tracer_file(ft1, true, false);
    solver.set("veripb", 4);
    solver.trace_proof(&veripb_proof_path);
    let _ft2 = solver.connect_proof_tracer_file(ft2, false, true);
    let st1 = solver.connect_proof_tracer_stat(st1, true, false);
    let _st2 = solver.connect_proof_tracer_stat(st2, false, false);

    let var2 = solver.declare_more_variables(2);
    let var1 = var2 - 1;
    solver.add(var1);
    solver.add(var2);
    solver.add(0);

    solver.add(-var1);
    solver.add(-var2);
    solver.add(0);

    solver.add(var1);
    solver.add(-var2);
    solver.add(0);

    solver.constrain(-var1);
    solver.constrain(var2);
    solver.constrain(0);

    solver.solve();

    solver.failed(var1);
    solver.conclude();

    solver.add(-var1);
    solver.add(var2);
    solver.add(0);

    solver.solve();

    solver.conclude();

    // tracers that are not disconnected are deleted when deleting solver
    //
    let t1 = solver.disconnect_proof_tracer(t1);
    let ft1 = solver.disconnect_proof_tracer_file(ft1);
    let st1 = solver.disconnect_proof_tracer_stat(st1);
    assert!(t1.is_some() && ft1.is_some() && st1.is_some());

    // ------------------------------------------------------------------

    drop(t1);
    drop(ft1);
    drop(st1);
    drop(solver);

    // Rust addition: keep the proofs for comparison with the C++ test if
    // 'CADICAL_APITEST_KEEP' is set.
    if std::env::var_os("CADICAL_APITEST_KEEP").is_none() {
        let _ = std::fs::remove_file(&lrat_proof_path);
        let _ = std::fs::remove_file(&frat_proof_path);
        let _ = std::fs::remove_file(&veripb_proof_path);
    }
}

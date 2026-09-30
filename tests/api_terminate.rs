//! Port of `cadical/test/api/terminate.cpp`.
//!
//! The C++ test uses a global solver and calls `solver.terminate ()` from
//! a `SIGALRM` handler.  We do the same through a raw pointer to the
//! solver (see the API notes: the `TerminationHandle` returned by
//! `Solver::termination_handle` is the sound Rust way to do this).

use cadical::Solver;

const N: i32 = 11;

fn ph(p: i32, h: i32) -> i32 {
    assert!(0 <= p);
    assert!(p < N + 1);
    assert!(0 <= h);
    assert!(h < N);
    1 + h * (N + 1) + p
}

extern "C" {
    // 'useconds_t' is 'unsigned' (not exposed by the 'libc' crate).
    fn ualarm(usecs: libc::c_uint, interval: libc::c_uint) -> libc::c_uint;
}

static mut SOLVER: *mut Solver = std::ptr::null_mut();

extern "C" fn handler(_: libc::c_int) {
    // SAFETY: 'SOLVER' points to the solver in 'main' which outlives the
    // alarm (same as the global solver in C++).
    unsafe { (*SOLVER).terminate() }
}

fn main() {
    let mut solver = Box::new(Solver::new());
    // SAFETY: set before the signal handler is installed.
    unsafe { SOLVER = &mut *solver };
    solver.set("factor", 0);

    // Construct a pigeon hole formula for 'n+1' pigeons in 'n' holes.
    //
    for h in 0..N {
        for p1 in 0..N + 1 {
            for p2 in p1 + 1..N + 1 {
                solver.add(-ph(p1, h));
                solver.add(-ph(p2, h));
                solver.add(0);
            }
        }
    }

    for p in 0..N + 1 {
        for h in 0..N {
            solver.add(ph(p, h));
        }
        solver.add(0);
    }

    // SAFETY: installing a signal handler and arming the timer.
    unsafe {
        libc::signal(libc::SIGALRM, handler as extern "C" fn(libc::c_int) as libc::sighandler_t);
        ualarm(100_000, 0);
    }
    let res = solver.solve();
    assert!(res == 0);
    solver.statistics();
}

//! Port of `cadical/test/api/apitrace.cpp`.

mod common;

use cadical::Solver;
use std::ffi::CString;

fn path(name: &str) -> String {
    format!("{}/test-api-apitrace-{}.trace", common::build_dir(), name)
}

fn trace(name: &str) -> *mut libc::FILE {
    let p = CString::new(path(name)).unwrap();
    // SAFETY: valid C strings.
    unsafe { libc::fopen(p.as_ptr(), b"w\0".as_ptr() as *const libc::c_char) }
}

fn fclose(file: *mut libc::FILE) {
    // SAFETY: opened with 'fopen' in 'trace'.
    unsafe { libc::fclose(file) };
}

fn main() {
    {
        let file = trace("file1");
        {
            let mut solver = Solver::new();
            solver.trace_api_calls_file(file);
        }
        fclose(file);
    }

    {
        std::env::set_var("CADICAL_API_TRACE", path("environment1"));
        {
            let mut solver = Solver::new();
            let var1 = solver.declare_one_more_variable();
            let var2 = solver.declare_one_more_variable();
            solver.add(var1);
            solver.add(var2);
            solver.add(0);
            solver.solve();
        }
        std::env::remove_var("CADICAL_API_TRACE");
    }

    // For now, when 'factor' is disabled and we do not check for wrong API
    // usage with respect to declared variables, the following two go through.

    {
        let file = trace("file2");
        {
            let mut solver = Solver::new();
            solver.set("factor", 0);
            solver.trace_api_calls_file(file);
            solver.set("factorcheck", 0);
            solver.add(1);
            solver.add(0);
            solver.add(-1);
            solver.add(0);
            solver.solve();
        }
        fclose(file);
    }

    {
        std::env::set_var("CADICAL_API_TRACE", path("environment2"));
        {
            let mut solver = Solver::new();
            solver.set("factor", 0);
            solver.set("factorcheck", 0);
            solver.add(-1);
            solver.add(-2);
            solver.add(0);
            solver.solve();
        }
        std::env::remove_var("CADICAL_API_TRACE");
    }
}

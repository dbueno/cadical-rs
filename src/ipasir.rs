//! Port of `ipasir.h` and `ipasir.cpp`: the IPASIR C API (the generic
//! incremental reentrant SAT solver API used for instance in the SAT
//! competition), exported with C linkage from the static library.  It is
//! implemented on top of the C API in `ccadical.rs`.

use std::ffi::c_char;

use crate::ccadical::{
    ccadical_add, ccadical_assume, ccadical_failed, ccadical_init, ccadical_release,
    ccadical_set_learn, ccadical_set_option, ccadical_set_terminate, ccadical_signature,
    ccadical_solve, ccadical_val, CCaDiCaL, CCaDiCaLLearn, CCaDiCaLTerminate,
};

/// Name of this library.
#[no_mangle]
pub extern "C" fn ipasir_signature() -> *const c_char {
    ccadical_signature()
}

/// Create a new solver (with 'factor' disabled, since IPASIR users do not
/// declare their variables explicitly).
#[no_mangle]
pub extern "C" fn ipasir_init() -> *mut libc::c_void {
    let cadical = ccadical_init();
    ccadical_set_option(cadical, b"factor\0".as_ptr() as *const c_char, 0);
    cadical as *mut libc::c_void
}

/// Delete the solver.
#[no_mangle]
pub extern "C" fn ipasir_release(solver: *mut libc::c_void) {
    ccadical_release(solver as *mut CCaDiCaL);
}

/// Add literal to clause or zero to terminate clause.
#[no_mangle]
pub extern "C" fn ipasir_add(solver: *mut libc::c_void, lit: i32) {
    ccadical_add(solver as *mut CCaDiCaL, lit);
}

/// Assume literal for the next call to `ipasir_solve`.
#[no_mangle]
pub extern "C" fn ipasir_assume(solver: *mut libc::c_void, lit: i32) {
    ccadical_assume(solver as *mut CCaDiCaL, lit);
}

/// Solve (returns 10, 20 or 0).
#[no_mangle]
pub extern "C" fn ipasir_solve(solver: *mut libc::c_void) -> i32 {
    ccadical_solve(solver as *mut CCaDiCaL)
}

/// Value of a literal in the model (IPASIR semantics).
#[no_mangle]
pub extern "C" fn ipasir_val(solver: *mut libc::c_void, lit: i32) -> i32 {
    ccadical_val(solver as *mut CCaDiCaL, lit)
}

/// Is the assumption `lit` in the core?
#[no_mangle]
pub extern "C" fn ipasir_failed(solver: *mut libc::c_void, lit: i32) -> i32 {
    ccadical_failed(solver as *mut CCaDiCaL, lit)
}

/// Set (or reset with a zero call-back) the terminator call-back.
#[no_mangle]
pub extern "C" fn ipasir_set_terminate(
    solver: *mut libc::c_void,
    state: *mut libc::c_void,
    terminate: CCaDiCaLTerminate,
) {
    ccadical_set_terminate(solver as *mut CCaDiCaL, state, terminate);
}

/// Set (or reset with a zero call-back) the learner call-back.
#[no_mangle]
pub extern "C" fn ipasir_set_learn(
    solver: *mut libc::c_void,
    state: *mut libc::c_void,
    max_length: i32,
    learn: CCaDiCaLLearn,
) {
    ccadical_set_learn(solver as *mut CCaDiCaL, state, max_length, learn);
}

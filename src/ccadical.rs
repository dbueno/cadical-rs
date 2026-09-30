//! Port of `ccadical.h` and `ccadical.cpp`: the C API (exported with C
//! linkage from the static library `libcadical.a`, so that C programs
//! written against `ccadical.h` link unchanged).
//!
//! The opaque `CCaDiCaL *` handle points to a [`Wrapper`] owning a
//! [`Solver`].  In C++ the wrapper itself implements the `Learner` and
//! `Terminator` interfaces.  Since the Rust solver owns its call-backs,
//! the wrapper connects small adaptor objects which forward to the C
//! function pointers with their `void *state`.
//!
//! The legacy names `ccadical_reset`, `ccadical_sat` and `ccadical_deref`
//! are macros in `ccadical.h` and thus need no symbols.

use std::ffi::{c_char, CStr, CString};
use std::sync::OnceLock;

use crate::solver::{Learner, Solver, Terminator};

/// Opaque handle (`typedef struct CCaDiCaL CCaDiCaL`).  Actually points to
/// a [`Wrapper`].
#[repr(C)]
pub struct CCaDiCaL {
    _private: [u8; 0],
}

/// `int (*terminate) (void *state)`.
pub type CCaDiCaLTerminate = Option<unsafe extern "C" fn(state: *mut libc::c_void) -> i32>;
/// `void (*learn) (void *state, int *clause)`.
pub type CCaDiCaLLearn = Option<unsafe extern "C" fn(state: *mut libc::c_void, clause: *mut i32)>;

/// The C++ `struct Wrapper` (owning the solver).
pub struct Wrapper {
    pub solver: Solver,
}

/// Terminator forwarding to a C call-back (the `terminator` part of the
/// C++ `Wrapper`).
struct CTerminator {
    state: *mut libc::c_void,
    function: unsafe extern "C" fn(*mut libc::c_void) -> i32,
}

impl Terminator for CTerminator {
    fn terminate(&mut self) -> bool {
        // SAFETY: C call-back with the user provided state.
        unsafe { (self.function)(self.state) != 0 }
    }
}

/// Learner forwarding to a C call-back (the `learner` part of the C++
/// `Wrapper`): collects the literals of a learned clause and passes the
/// zero terminated clause to the call-back.
struct CLearner {
    state: *mut libc::c_void,
    max_length: i32,
    clause: Vec<i32>,
    function: unsafe extern "C" fn(*mut libc::c_void, *mut i32),
}

impl Learner for CLearner {
    fn learning(&mut self, size: i32) -> bool {
        size <= self.max_length
    }

    fn learn(&mut self, lit: i32) {
        self.clause.push(lit);
        if lit != 0 {
            return;
        }
        // SAFETY: C call-back with the user provided state and a zero
        // terminated clause.
        unsafe { (self.function)(self.state, self.clause.as_mut_ptr()) };
        self.clause.clear();
    }
}

#[inline(always)]
fn wrapper<'a>(ptr: *mut CCaDiCaL) -> &'a mut Wrapper {
    debug_assert!(!ptr.is_null());
    // SAFETY: the handle was created by 'ccadical_init'.
    unsafe { &mut *(ptr as *mut Wrapper) }
}

#[inline(always)]
fn solver<'a>(ptr: *mut CCaDiCaL) -> &'a mut Solver {
    &mut wrapper(ptr).solver
}

/// Borrow a C string argument (lossy for non UTF-8 bytes).
fn c_str<'a>(s: *const c_char) -> std::borrow::Cow<'a, str> {
    debug_assert!(!s.is_null());
    // SAFETY: valid zero terminated C string passed by the caller.
    unsafe { CStr::from_ptr(s) }.to_string_lossy()
}

/// Static zero terminated copy of `Solver::signature ()`.
pub(crate) fn signature_c_str() -> *const c_char {
    static SIGNATURE: OnceLock<CString> = OnceLock::new();
    SIGNATURE.get_or_init(|| CString::new(Solver::signature()).unwrap()).as_ptr()
}

/// Name of this library (`"cadical-<version>"`).
#[no_mangle]
pub extern "C" fn ccadical_signature() -> *const c_char {
    signature_c_str()
}

/// Version of this library (Rust addition, `"3.0.1"`).
#[no_mangle]
pub extern "C" fn cadical_rs_version() -> *const c_char {
    static VERSION: OnceLock<CString> = OnceLock::new();
    VERSION.get_or_init(|| CString::new(Solver::version()).unwrap()).as_ptr()
}

/// Create a new solver.
#[no_mangle]
pub extern "C" fn ccadical_init() -> *mut CCaDiCaL {
    Box::into_raw(Box::new(Wrapper { solver: Solver::new() })) as *mut CCaDiCaL
}

/// Delete the solver (and the connected call-back adaptors).
#[no_mangle]
pub extern "C" fn ccadical_release(wrapper: *mut CCaDiCaL) {
    // SAFETY: the handle was created by 'ccadical_init'.
    drop(unsafe { Box::from_raw(wrapper as *mut Wrapper) });
}

/// `Solver::constrain`.
#[no_mangle]
pub extern "C" fn ccadical_constrain(wrapper: *mut CCaDiCaL, lit: i32) {
    solver(wrapper).constrain(lit);
}

/// `Solver::constraint_failed`.
#[no_mangle]
pub extern "C" fn ccadical_constraint_failed(wrapper: *mut CCaDiCaL) -> i32 {
    solver(wrapper).constraint_failed() as i32
}

/// `Solver::set`.
#[no_mangle]
pub extern "C" fn ccadical_set_option(wrapper: *mut CCaDiCaL, name: *const c_char, val: i32) {
    solver(wrapper).set(&c_str(name), val);
}

/// `Solver::limit`.
#[no_mangle]
pub extern "C" fn ccadical_limit(wrapper: *mut CCaDiCaL, name: *const c_char, limit: i32) {
    solver(wrapper).limit(&c_str(name), limit);
}

/// `Solver::get`.
#[no_mangle]
pub extern "C" fn ccadical_get_option(wrapper: *mut CCaDiCaL, name: *const c_char) -> i32 {
    solver(wrapper).get(&c_str(name))
}

/// `Solver::add`.
#[no_mangle]
pub extern "C" fn ccadical_add(wrapper: *mut CCaDiCaL, lit: i32) {
    solver(wrapper).add(lit);
}

/// `Solver::assume`.
#[no_mangle]
pub extern "C" fn ccadical_assume(wrapper: *mut CCaDiCaL, lit: i32) {
    solver(wrapper).assume(lit);
}

/// `Solver::solve`.
#[no_mangle]
pub extern "C" fn ccadical_solve(wrapper: *mut CCaDiCaL) -> i32 {
    solver(wrapper).solve()
}

/// `Solver::simplify` (with the default of 3 rounds).
#[no_mangle]
pub extern "C" fn ccadical_simplify(wrapper: *mut CCaDiCaL) -> i32 {
    solver(wrapper).simplify(3)
}

/// `Solver::val`.
#[no_mangle]
pub extern "C" fn ccadical_val(wrapper: *mut CCaDiCaL, lit: i32) -> i32 {
    solver(wrapper).val(lit)
}

/// `Solver::failed`.
#[no_mangle]
pub extern "C" fn ccadical_failed(wrapper: *mut CCaDiCaL, lit: i32) -> i32 {
    solver(wrapper).failed(lit) as i32
}

/// `Solver::statistics`.
#[no_mangle]
pub extern "C" fn ccadical_print_statistics(wrapper: *mut CCaDiCaL) {
    solver(wrapper).statistics();
}

/// `Solver::terminate`.
#[no_mangle]
pub extern "C" fn ccadical_terminate(wrapper: *mut CCaDiCaL) {
    solver(wrapper).terminate();
}

/// `Solver::active`.
#[no_mangle]
pub extern "C" fn ccadical_active(wrapper: *mut CCaDiCaL) -> i64 {
    solver(wrapper).active() as i64
}

/// `Solver::irredundant`.
#[no_mangle]
pub extern "C" fn ccadical_irredundant(wrapper: *mut CCaDiCaL) -> i64 {
    solver(wrapper).irredundant()
}

/// `Solver::fixed`.
#[no_mangle]
pub extern "C" fn ccadical_fixed(wrapper: *mut CCaDiCaL, lit: i32) -> i32 {
    solver(wrapper).fixed(lit)
}

/// Connect (non-zero `terminate`) or disconnect (zero `terminate`) a
/// terminator call-back.
#[no_mangle]
pub extern "C" fn ccadical_set_terminate(
    wrapper: *mut CCaDiCaL,
    state: *mut libc::c_void,
    terminate: CCaDiCaLTerminate,
) {
    let solver = solver(wrapper);
    if let Some(function) = terminate {
        solver.connect_terminator(Box::new(CTerminator { state, function }));
    } else {
        solver.disconnect_terminator();
    }
}

/// Connect (non-zero `learn`) or disconnect (zero `learn`) a learner
/// call-back receiving learned clauses up to `max_length` literals (zero
/// terminated).
#[no_mangle]
pub extern "C" fn ccadical_set_learn(
    wrapper: *mut CCaDiCaL,
    state: *mut libc::c_void,
    max_length: i32,
    learn: CCaDiCaLLearn,
) {
    let solver = solver(wrapper);
    if let Some(function) = learn {
        solver.connect_learner(Box::new(CLearner {
            state,
            max_length,
            clause: Vec::new(),
            function,
        }));
    } else {
        solver.disconnect_learner();
    }
}

/// `Solver::freeze`.
#[no_mangle]
pub extern "C" fn ccadical_freeze(wrapper: *mut CCaDiCaL, lit: i32) {
    solver(wrapper).freeze(lit);
}

/// `Solver::melt`.
#[no_mangle]
pub extern "C" fn ccadical_melt(wrapper: *mut CCaDiCaL, lit: i32) {
    solver(wrapper).melt(lit);
}

/// `Solver::frozen`.
#[no_mangle]
pub extern "C" fn ccadical_frozen(wrapper: *mut CCaDiCaL, lit: i32) -> i32 {
    solver(wrapper).frozen(lit) as i32
}

/// `Solver::trace_proof (FILE *, const char *)`.
#[no_mangle]
pub extern "C" fn ccadical_trace_proof(
    wrapper: *mut CCaDiCaL,
    file: *mut libc::FILE,
    path: *const c_char,
) -> i32 {
    solver(wrapper).trace_proof_file(file, &c_str(path)) as i32
}

/// `Solver::close_proof_trace`.
#[no_mangle]
pub extern "C" fn ccadical_close_proof(wrapper: *mut CCaDiCaL) {
    solver(wrapper).close_proof_trace(false);
}

/// `Solver::conclude`.
#[no_mangle]
pub extern "C" fn ccadical_conclude(wrapper: *mut CCaDiCaL) {
    solver(wrapper).conclude();
}

/// `Solver::vars`.
#[no_mangle]
pub extern "C" fn ccadical_vars(wrapper: *mut CCaDiCaL) -> i32 {
    solver(wrapper).vars()
}

/// `Solver::declare_more_variables`.
#[no_mangle]
pub extern "C" fn ccadical_declare_more_variables(wrapper: *mut CCaDiCaL, number_of_vars: i32) -> i32 {
    solver(wrapper).declare_more_variables(number_of_vars)
}

/// `Solver::declare_one_more_variable`.
#[no_mangle]
pub extern "C" fn ccadical_declare_one_more_variable(wrapper: *mut CCaDiCaL) -> i32 {
    solver(wrapper).declare_one_more_variable()
}

/// `Solver::phase`.
#[no_mangle]
pub extern "C" fn ccadical_phase(wrapper: *mut CCaDiCaL, lit: i32) {
    solver(wrapper).phase(lit);
}

/// `Solver::unphase`.
#[no_mangle]
pub extern "C" fn ccadical_unphase(wrapper: *mut CCaDiCaL, lit: i32) {
    solver(wrapper).unphase(lit);
}

//! Port of `tracer.hpp`: proof tracer interfaces.
//!
//! The C++ class hierarchy `Tracer` <- `InternalTracer` <- {`StatTracer`,
//! `FileTracer`} is mapped to traits with super-traits.  All event methods
//! have empty default implementations (as the C++ virtual functions).
//!
//! Ownership: connected tracers are owned by `Internal` (as boxes in
//! `tracers`, `stat_tracers` or `file_tracers`, mirroring C++ where
//! `~Internal` deletes still connected tracers); `Proof` keeps raw
//! pointers to them for dispatching events.  Connecting returns a
//! [`TracerRef`] identifying the tracer, which is used to disconnect it
//! again, which returns the box to the caller.

use crate::internal::Internal;

/// `enum ConclusionType`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(i32)]
pub enum ConclusionType {
    CONFLICT = 1,
    ASSUMPTIONS = 2,
    CONSTRAINT = 4,
}

/// Identity of a connected tracer (the address of the boxed tracer
/// object).  Returned by `connect_proof_tracer*` and used by
/// `disconnect_proof_tracer*`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct TracerRef(pub usize);

impl TracerRef {
    /// Identity of a tracer object.
    pub fn of<T: ?Sized>(t: &T) -> TracerRef {
        TracerRef(t as *const T as *const () as usize)
    }
}

pub trait Tracer {
    /*--------------------------------------------------------------------*/
    /*                            Basic Events                            */
    /*--------------------------------------------------------------------*/

    /// `add_original_clause (id, redundant, clause, restored = false)`.
    fn add_original_clause(&mut self, _id: i64, _redundant: bool, _clause: &[i32], _restored: bool) {}

    fn add_derived_clause(
        &mut self,
        _id: i64,
        _redundant: bool,
        _witness: i32,
        _clause: &[i32],
        _chain: &[i64],
    ) {
    }

    fn delete_clause(&mut self, _id: i64, _redundant: bool, _clause: &[i32]) {}

    fn demote_clause(&mut self, _id: u64, _clause: &[i32]) {}

    fn weaken_minus(&mut self, _id: i64, _clause: &[i32]) {}

    fn strengthen(&mut self, _id: i64) {}

    fn report_status(&mut self, _status: i32, _id: i64) {}

    /*--------------------------------------------------------------------*/
    /*                   Specifically non-incremental                     */
    /*--------------------------------------------------------------------*/

    fn finalize_clause(&mut self, _id: i64, _clause: &[i32]) {}

    fn begin_proof(&mut self, _reserved_ids: i64) {}

    /*--------------------------------------------------------------------*/
    /*                      Specifically incremental                      */
    /*--------------------------------------------------------------------*/

    fn solve_query(&mut self) {}

    fn add_assumption(&mut self, _lit: i32) {}

    fn add_constraint(&mut self, _clause: &[i32]) {}

    fn reset_assumptions(&mut self) {}

    fn add_assumption_clause(&mut self, _id: i64, _clause: &[i32], _chain: &[i64]) {}

    fn conclude_unsat(&mut self, _conclusion: ConclusionType, _ids: &[i64]) {}

    fn conclude_sat(&mut self, _model: &[i32]) {}

    fn conclude_unknown(&mut self, _trail: &[i32]) {}

    fn notify_equivalence(&mut self, _lit: i32, _other: i32) {}
}

// Shared ownership of proof tracers (Rust addition): connect a clone of an
// 'Rc<RefCell<T>>' or 'Arc<Mutex<T>>' to keep access to the tracer while
// it is connected (see the call-back notes in 'solver.rs').
crate::solver::impl_shared_callback!(Tracer {
    fn add_original_clause(&mut self, id: i64, redundant: bool, clause: &[i32], restored: bool);
    fn add_derived_clause(&mut self, id: i64, redundant: bool, witness: i32, clause: &[i32], chain: &[i64]);
    fn delete_clause(&mut self, id: i64, redundant: bool, clause: &[i32]);
    fn demote_clause(&mut self, id: u64, clause: &[i32]);
    fn weaken_minus(&mut self, id: i64, clause: &[i32]);
    fn strengthen(&mut self, id: i64);
    fn report_status(&mut self, status: i32, id: i64);
    fn finalize_clause(&mut self, id: i64, clause: &[i32]);
    fn begin_proof(&mut self, reserved_ids: i64);
    fn solve_query(&mut self);
    fn add_assumption(&mut self, lit: i32);
    fn add_constraint(&mut self, clause: &[i32]);
    fn reset_assumptions(&mut self);
    fn add_assumption_clause(&mut self, id: i64, clause: &[i32], chain: &[i64]);
    fn conclude_unsat(&mut self, conclusion: ConclusionType, ids: &[i64]);
    fn conclude_sat(&mut self, model: &[i32]);
    fn conclude_unknown(&mut self, trail: &[i32]);
    fn notify_equivalence(&mut self, lit: i32, other: i32);
});

crate::solver::impl_shared_callback!(InternalTracer {
    fn connect_internal(&mut self, internal: *mut Internal);
});

crate::solver::impl_shared_callback!(StatTracer {
    fn print_stats(&mut self);
});

crate::solver::impl_shared_callback!(FileTracer {
    fn closed(&mut self) -> bool;
    fn close(&mut self, print: bool);
    fn flush(&mut self, print: bool);
});

/// `struct InternalTracer : public Tracer`.
pub trait InternalTracer: Tracer {
    fn connect_internal(&mut self, _internal: *mut Internal) {}
}

/// `class StatTracer : public InternalTracer`.
pub trait StatTracer: InternalTracer {
    fn print_stats(&mut self) {}
}

/// `class FileTracer : public InternalTracer`.
pub trait FileTracer: InternalTracer {
    fn closed(&mut self) -> bool;
    /// `print` defaults to `false` in C++.
    fn close(&mut self, print: bool);
    /// `print` defaults to `false` in C++.
    fn flush(&mut self, print: bool);
}

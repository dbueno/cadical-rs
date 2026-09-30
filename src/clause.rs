//! Port of `clause.hpp` and `clause.cpp`.
//!
//! `Clause` has exactly the C++ memory layout: a 24 byte header followed by
//! the (variadic) literals.  Clauses are referenced through [`CRef`], a
//! `Copy` wrapper around a raw `*mut Clause` which compares by address.

use std::fmt;

use crate::internal::Internal;
use crate::util::align;

/// Number of bits for the `used` counter in the clause header.
pub const USED_SIZE: u32 = 5;

// Bit positions in the flags word ('unsigned used : 5' followed by the
// 'bool ... : 1' flags in declaration order, as laid out by clang/gcc).
const USED_MASK: u32 = (1 << USED_SIZE) - 1;
const CONDITIONED: u32 = 1 << 5;
const COVERED: u32 = 1 << 6;
const ENQUEUED: u32 = 1 << 7;
const FROZEN: u32 = 1 << 8;
const GARBAGE: u32 = 1 << 9;
const GATE: u32 = 1 << 10;
const HYPER: u32 = 1 << 11;
const INSTANTIATED: u32 = 1 << 12;
const MOVED: u32 = 1 << 13;
const REASON: u32 = 1 << 14;
const REDUNDANT: u32 = 1 << 15;
const TRANSRED: u32 = 1 << 16;
const SUBSUME: u32 = 1 << 17;
const SWEPT: u32 = 1 << 18;
const FLUSHED: u32 = 1 << 19;
const VIVIFIED: u32 = 1 << 20;
const VIVIFY: u32 = 1 << 21;

/// The clause header.  See `clause.hpp` for the (long) explanation of the
/// fields.  `id` doubles as the `copy` pointer if the clause is `moved`.
#[repr(C)]
pub struct Clause {
    /// Union of `int64_t id` and `Clause *copy`.
    pub id_or_copy: u64,
    /// `used : 5` plus all the one-bit flags.
    pub bits: u32,
    pub glue: i32,
    /// Actual size of `literals` (at least 2).
    pub size: i32,
    /// Position of last watch replacement [Gent'13].
    pub pos: i32,
    /// Flexible array member.
    pub literals: [i32; 0],
}

const _: () = assert!(std::mem::size_of::<Clause>() == 24);
const _: () = assert!(std::mem::align_of::<Clause>() == 8);

impl Clause {
    /// A zero initialized clause header (used for the static pseudo
    /// reasons `decision_reason` and `external_reason`).
    pub const ZERO: Clause = Clause {
        id_or_copy: 0,
        bits: 0,
        glue: 0,
        size: 0,
        pos: 0,
        literals: [],
    };

    /// Bytes needed for a clause of the given size (8 byte aligned).
    #[inline]
    pub fn bytes_for(size: i32) -> usize {
        debug_assert!(size > 1);
        let header_bytes = std::mem::size_of::<Clause>();
        let actual_literal_bytes = size as usize * std::mem::size_of::<i32>();
        let combined_bytes = header_bytes + actual_literal_bytes;
        align(combined_bytes, std::mem::align_of::<*const Clause>())
    }
}

/// Raw clause handle (`Clause *` in C++).  Null is allowed (`CRef::NULL`).
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct CRef(pub *mut Clause);

impl Default for CRef {
    fn default() -> Self {
        CRef::NULL
    }
}

impl fmt::Debug for CRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "CRef({:p})", self.0)
    }
}

impl fmt::Pointer for CRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Pointer::fmt(&self.0, f)
    }
}

macro_rules! flag_accessors {
    ($($get:ident, $set:ident, $bit:ident;)*) => {
        $(
            #[inline(always)]
            pub fn $get(self) -> bool {
                (self.hdr().bits & $bit) != 0
            }
            #[inline(always)]
            pub fn $set(self, b: bool) {
                let h = self.hdr_mut();
                if b { h.bits |= $bit } else { h.bits &= !$bit }
            }
        )*
    };
}

impl CRef {
    pub const NULL: CRef = CRef(std::ptr::null_mut());

    #[inline(always)]
    pub fn from_ptr(p: *mut Clause) -> CRef {
        CRef(p)
    }
    #[inline(always)]
    pub fn as_ptr(self) -> *mut Clause {
        self.0
    }
    #[inline(always)]
    pub fn is_null(self) -> bool {
        self.0.is_null()
    }
    #[inline(always)]
    pub fn is_some(self) -> bool {
        !self.0.is_null()
    }
    /// Address as integer (for `pointer_rank` and `%p` style logging).
    #[inline(always)]
    pub fn addr(self) -> usize {
        self.0 as usize
    }

    #[inline(always)]
    fn hdr(&self) -> &Clause {
        debug_assert!(!self.0.is_null());
        // SAFETY: a non-null CRef always points to a live clause header.
        unsafe { &*self.0 }
    }
    #[inline(always)]
    #[allow(clippy::mut_from_ref)]
    fn hdr_mut(&self) -> &mut Clause {
        debug_assert!(!self.0.is_null());
        // SAFETY: see 'hdr'.  Clauses are only accessed single threaded.
        unsafe { &mut *self.0 }
    }

    /*--------------------------------------------------------------------*/

    /// Allocate an uninitialized clause of `size` literals with the global
    /// allocator (`new char[bytes]` in C++).  Header fields are zeroed.
    pub fn alloc(size: i32) -> CRef {
        let bytes = Clause::bytes_for(size);
        // SAFETY: 'malloc' returns memory aligned for any fundamental type.
        let p = unsafe { libc::malloc(bytes) } as *mut Clause;
        if p.is_null() {
            crate::message::fatal(format_args!("out of memory allocating clause"));
        }
        // SAFETY: freshly allocated and large enough for a header.
        unsafe { std::ptr::write(p, Clause::ZERO) };
        CRef(p)
    }

    /// Release memory obtained by [`CRef::alloc`] (`delete[] (char*) c`).
    ///
    /// # Safety
    /// The clause must have been allocated with `alloc` (not in the arena)
    /// and must not be used afterwards.
    pub unsafe fn dealloc(self) {
        libc::free(self.0 as *mut libc::c_void)
    }

    /*--------------------------------------------------------------------*/

    #[inline(always)]
    pub fn id(self) -> i64 {
        self.hdr().id_or_copy as i64
    }
    #[inline(always)]
    pub fn set_id(self, id: i64) {
        self.hdr_mut().id_or_copy = id as u64
    }
    /// Only valid if `moved`.
    #[inline(always)]
    pub fn copy(self) -> CRef {
        CRef(self.hdr().id_or_copy as usize as *mut Clause)
    }
    #[inline(always)]
    pub fn set_copy(self, c: CRef) {
        self.hdr_mut().id_or_copy = c.0 as usize as u64
    }

    #[inline(always)]
    pub fn used(self) -> u32 {
        self.hdr().bits & USED_MASK
    }
    /// Stores `u` truncated to `USED_SIZE` bits (like the C++ bit-field).
    #[inline(always)]
    pub fn set_used(self, u: u32) {
        let h = self.hdr_mut();
        h.bits = (h.bits & !USED_MASK) | (u & USED_MASK);
    }

    flag_accessors! {
        conditioned, set_conditioned, CONDITIONED;
        covered, set_covered, COVERED;
        enqueued, set_enqueued, ENQUEUED;
        frozen, set_frozen, FROZEN;
        garbage, set_garbage, GARBAGE;
        gate, set_gate, GATE;
        hyper, set_hyper, HYPER;
        instantiated, set_instantiated, INSTANTIATED;
        moved, set_moved, MOVED;
        reason, set_reason, REASON;
        redundant, set_redundant, REDUNDANT;
        transred, set_transred, TRANSRED;
        subsume, set_subsume, SUBSUME;
        swept, set_swept, SWEPT;
        flushed, set_flushed, FLUSHED;
        vivified, set_vivified, VIVIFIED;
        vivify, set_vivify, VIVIFY;
    }

    #[inline(always)]
    pub fn glue(self) -> i32 {
        self.hdr().glue
    }
    #[inline(always)]
    pub fn set_glue(self, g: i32) {
        self.hdr_mut().glue = g
    }
    #[inline(always)]
    pub fn size(self) -> i32 {
        self.hdr().size
    }
    #[inline(always)]
    pub fn set_size(self, s: i32) {
        self.hdr_mut().size = s
    }
    #[inline(always)]
    pub fn pos(self) -> i32 {
        self.hdr().pos
    }
    #[inline(always)]
    pub fn set_pos(self, p: i32) {
        self.hdr_mut().pos = p
    }

    /*--------------------------------------------------------------------*/

    /// Pointer to the first literal (`c->literals`).
    #[inline(always)]
    pub fn literals_ptr(self) -> *mut i32 {
        debug_assert!(!self.0.is_null());
        // SAFETY: address computation only.
        unsafe { std::ptr::addr_of_mut!((*self.0).literals) as *mut i32 }
    }
    /// `c->literals[i]`.
    #[inline(always)]
    pub fn lit(self, i: usize) -> i32 {
        debug_assert!(i < self.size() as usize || self.size() == 0);
        // SAFETY: index within the clause (checked in debug mode).
        unsafe { *self.literals_ptr().add(i) }
    }
    /// `c->literals[i] = l`.
    #[inline(always)]
    pub fn set_lit(self, i: usize, l: i32) {
        // SAFETY: as in 'lit'.  Writing beyond 'size' but within the
        // originally allocated size is allowed (as in C++).
        unsafe { *self.literals_ptr().add(i) = l }
    }
    /// Swap two literals.
    #[inline(always)]
    pub fn swap_lits(self, i: usize, j: usize) {
        debug_assert!(i < self.size() as usize && j < self.size() as usize);
        // SAFETY: both indices within the clause.
        unsafe { std::ptr::swap(self.literals_ptr().add(i), self.literals_ptr().add(j)) }
    }
    /// The literals as a shared slice.  Never keep this slice alive across
    /// a write to the same clause.
    #[inline(always)]
    pub fn lits<'a>(self) -> &'a [i32] {
        // SAFETY: 'size' literals follow the header.
        unsafe { std::slice::from_raw_parts(self.literals_ptr(), self.size() as usize) }
    }
    /// The literals as a mutable slice (same caveats as `lits`).
    #[inline(always)]
    #[allow(clippy::mut_from_ref)]
    pub fn lits_mut<'a>(self) -> &'a mut [i32] {
        // SAFETY: 'size' literals follow the header.
        unsafe { std::slice::from_raw_parts_mut(self.literals_ptr(), self.size() as usize) }
    }

    /// `c->bytes ()`.
    #[inline(always)]
    pub fn bytes(self) -> usize {
        Clause::bytes_for(self.size())
    }

    /// Check whether this clause is ready to be collected and deleted.
    #[inline(always)]
    pub fn collect(self) -> bool {
        !self.reason() && self.garbage()
    }

    /// Raw header flags word (for copying all flags at once).
    #[inline(always)]
    pub fn bits(self) -> u32 {
        self.hdr().bits
    }
    #[inline(always)]
    pub fn set_bits(self, b: u32) {
        self.hdr_mut().bits = b
    }
}

/// `clause_smaller_size` comparator.
#[inline]
pub fn clause_smaller_size(a: &CRef, b: &CRef) -> bool {
    a.size() < b.size()
}

/// Place literals over the same variable close to each other
/// (`clause_lit_less_than`).
#[inline]
pub fn clause_lit_less_than(a: &i32, b: &i32) -> bool {
    let s = a.abs();
    let t = b.abs();
    s < t || (s == t && a < b)
}

/*------------------------------------------------------------------------*/

// Static pseudo clauses (address used as a sentinel only).

static mut DECISION_REASON_CLAUSE: Clause = Clause::ZERO;
static mut EXTERNAL_REASON_CLAUSE: Clause = Clause::ZERO;

impl Internal {
    /// `Internal::decision_reason`: the address of a static clause is used
    /// as pseudo reason for decisions.
    #[inline(always)]
    pub fn decision_reason() -> CRef {
        // SAFETY: only the address is taken.
        CRef(unsafe { std::ptr::addr_of_mut!(DECISION_REASON_CLAUSE) })
    }
}

/// Address of the static `external_reason_clause` (defined in
/// `internal.cpp`), stored in `Internal::external_reason`.
#[inline(always)]
pub fn external_reason_clause() -> CRef {
    // SAFETY: only the address is taken.
    CRef(unsafe { std::ptr::addr_of_mut!(EXTERNAL_REASON_CLAUSE) })
}

/*------------------------------------------------------------------------*/
// Port of 'clause.cpp'.

#[allow(unused_imports)]
use crate::prelude::*;

impl Internal {
    /*----------------------------------------------------------------------*/

    // Signed marking or unmarking of a clause or the global 'clause'.

    /// C++ overload `Internal::mark` (renamed).
    pub fn mark_clause_literals(&mut self, c: CRef) {
        for i in 0..c.size() as usize {
            let lit = c.lit(i);
            self.mark(lit);
        }
    }

    /// C++ overload `Internal::mark2` (renamed).
    pub fn mark2_clause_literals(&mut self, c: CRef) {
        for i in 0..c.size() as usize {
            let lit = c.lit(i);
            self.mark2(lit);
        }
    }

    /// C++ overload `Internal::unmark` (renamed).
    pub fn unmark_clause_literals(&mut self, c: CRef) {
        for i in 0..c.size() as usize {
            let lit = c.lit(i);
            self.unmark(lit);
        }
    }

    pub fn mark_clause(&mut self) {
        for i in 0..self.clause.len() {
            let lit = self.clause[i];
            self.mark(lit);
        }
    }

    pub fn unmark_clause(&mut self) {
        for i in 0..self.clause.len() {
            let lit = self.clause[i];
            self.unmark(lit);
        }
    }

    /*----------------------------------------------------------------------*/

    /// Mark the variables of an irredundant clause to 'have been removed',
    /// which will trigger these variables to be considered again in the
    /// next bounded variable elimination phase.  This is called from
    /// 'mark_garbage' below.  Note that 'mark_removed (int lit)' will also
    /// mark the blocking flag of '-lit' to trigger reconsidering blocking
    /// clauses on '-lit'.
    ///
    /// `except` defaults to `0` in C++
    pub fn mark_removed(&mut self, c: CRef, except: i32) {
        log!(self, c, "marking removed");
        debug_assert!(!c.redundant());
        for i in 0..c.size() as usize {
            let lit = c.lit(i);
            if lit != except {
                self.mark_removed_lit(lit);
            }
        }
    }

    /// Mark the variables of a (redundant or irredundant) clause to 'have
    /// been added', which triggers clauses with such a variables, to be
    /// considered both as a subsumed or subsuming clause in the next
    /// subsumption phase.  This function is called from 'new_clause' below
    /// as well as in situations where a clause is shrunken (and thus needs
    /// to be at least considered again to subsume a larger clause).  We
    /// also use this to tell 'ternary' preprocessing reconsider clauses on
    /// an added literal as well as trying to block clauses on it.
    ///
    /// C++ overload `Internal::mark_added` (renamed).
    #[inline]
    pub fn mark_added_lit(&mut self, lit: i32, size: i32, redundant: bool) {
        self.mark_subsume(lit);
        if size == 3 {
            self.mark_ternary(lit);
        }
        if !redundant {
            self.mark_block(lit);
        }
        if !redundant || size == 2 {
            self.mark_factor(lit);
        }
    }

    pub fn mark_added(&mut self, c: CRef) {
        log!(self, c, "marking added");
        debug_assert!(self.likely_to_be_kept_clause(c));
        for i in 0..c.size() as usize {
            let lit = c.lit(i);
            self.mark_added_lit(lit, c.size(), c.redundant());
        }
    }

    /*----------------------------------------------------------------------*/

    /// `glue` defaults to `0` in C++
    pub fn new_clause(&mut self, red: bool, glue: i32) -> CRef {
        debug_assert!(self.clause.len() <= i32::MAX as usize);
        let size = self.clause.len() as i32;
        debug_assert!(size >= 2);

        let mut glue = glue;
        if glue > size {
            glue = size;
        }

        let bytes = Clause::bytes_for(size);
        let c = CRef::alloc(size);

        self.clause_id += 1;
        c.set_id(self.clause_id);

        // All flags (including 'used') are cleared.
        c.set_bits(0);
        c.set_conditioned(false);
        c.set_covered(false);
        c.set_enqueued(false);
        c.set_frozen(false);
        c.set_garbage(false);
        c.set_gate(false);
        c.set_hyper(false);
        c.set_instantiated(false);
        c.set_moved(false);
        c.set_reason(false);
        c.set_redundant(red);
        c.set_transred(false);
        c.set_subsume(false);
        c.set_swept(false);
        c.set_flushed(false);
        c.set_vivified(false);
        c.set_vivify(false);
        c.set_used(0);

        c.set_glue(glue);
        c.set_size(size);
        c.set_pos(2);

        for i in 0..size as usize {
            c.set_lit(i, self.clause[i]);
        }

        // Just checking that we did not mess up our sophisticated memory
        // layout.  This might be compiler dependent though. Crucial for
        // correctness.
        //
        debug_assert!(c.bytes() == bytes);
        let _ = bytes;

        self.stats.current.total += 1;
        self.stats.added.total += 1;

        if red {
            self.stats.current.redundant += 1;
            self.stats.added.redundant += 1;
        } else {
            self.stats.irrlits += size as i64;
            self.stats.current.irredundant += 1;
            self.stats.added.irredundant += 1;
        }

        self.clauses.push(c);
        log!(self, c, "new pointer {:p}", c);

        if self.likely_to_be_kept_clause(c) {
            self.mark_added(c);
        }

        c
    }

    /*----------------------------------------------------------------------*/

    pub fn promote_clause(&mut self, c: CRef, new_glue: i32) {
        debug_assert!(c.redundant());
        debug_assert!(new_glue != 0);
        let tier1limit = self.tier1[false as usize];
        let tier2limit = tier1limit.max(self.tier2[false as usize]);
        if !c.redundant() {
            return;
        }
        if c.hyper() {
            return;
        }
        let old_glue = c.glue();
        if new_glue >= old_glue {
            return;
        }
        c.set_used(Internal::MAX_USED);
        if old_glue > tier1limit && new_glue <= tier1limit {
            log!(self, c, "promoting with new glue {} to tier1", new_glue);
            self.stats.promoted1 += 1;
        } else if old_glue > tier2limit && new_glue <= tier2limit {
            log!(self, c, "promoting with new glue {} to tier2", new_glue);
            self.stats.promoted2 += 1;
        } else if old_glue <= tier2limit {
            log!(self, c, "keeping with new glue {} in tier2", new_glue);
        } else {
            log!(self, c, "keeping with new glue {} in tier3", new_glue);
        }
        self.stats.improvedglue += 1;
        c.set_glue(new_glue);
    }

    /*----------------------------------------------------------------------*/

    pub fn promote_clause_glue_only(&mut self, c: CRef, new_glue: i32) {
        debug_assert!(c.redundant());
        debug_assert!(new_glue != 0);
        if c.hyper() {
            return;
        }
        let old_glue = c.glue();
        let tier1limit = self.tier1[false as usize];
        let tier2limit = tier1limit.max(self.tier2[false as usize]);
        if new_glue >= old_glue {
            return;
        }
        if new_glue <= tier1limit {
            log!(self, c, "promoting with new glue {} to tier1", new_glue);
            self.stats.promoted1 += 1;
        } else if old_glue > tier2limit && new_glue <= tier2limit {
            log!(self, c, "promoting with new glue {} to tier2", new_glue);
            self.stats.promoted2 += 1;
        } else if old_glue <= tier2limit {
            log!(self, c, "keeping with new glue {} in tier2", new_glue);
        } else {
            log!(self, c, "keeping with new glue {} in tier3", new_glue);
        }
        self.stats.improvedglue += 1;
        c.set_glue(new_glue);
    }

    /*----------------------------------------------------------------------*/

    /// Shrinking a clause, e.g., removing one or more literals, requires to
    /// fix the 'pos' field, if it exists and points after the new last
    /// literal. We also have adjust the global statistics counter of
    /// irredundant literals for irredundant clauses, and also adjust the
    /// glue value of redundant clauses if the size becomes smaller than the
    /// glue.  Also mark the literals in the resulting clause as 'added'.
    /// The result is the number of (aligned) removed bytes, resulting from
    /// shrinking the clause.
    pub fn shrink_clause(&mut self, c: CRef, new_size: i32) -> usize {
        if self.opts.check != 0 && self.is_external_forgettable(c.id()) {
            self.mark_garbage_external_forgettable(c.id());
        }
        debug_assert!(new_size >= 2);
        let old_size = c.size();
        debug_assert!(new_size < old_size);
        #[cfg(debug_assertions)]
        {
            let mut i = c.size();
            while i < new_size {
                c.set_lit(i as usize, 0);
                i += 1;
            }
        }

        if c.pos() >= new_size {
            c.set_pos(2);
        }

        let old_bytes = c.bytes();
        c.set_size(new_size);
        let new_bytes = c.bytes();
        let res = old_bytes - new_bytes;

        if c.redundant() {
            let g = (c.size() - 1).min(c.glue());
            self.promote_clause_glue_only(c, g);
        } else {
            let delta_size = old_size - new_size;
            debug_assert!(self.stats.irrlits >= delta_size as i64);
            self.stats.irrlits -= delta_size as i64;
        }

        if self.likely_to_be_kept_clause(c) {
            self.mark_added(c);
        }

        res
    }

    /// This is the 'raw' deallocation of a clause.  If the clause is in the
    /// arena nothing happens.  If the clause is not in the arena its memory
    /// is reclaimed immediately.
    pub fn deallocate_clause(&mut self, c: CRef) {
        let p = c.as_ptr() as *const u8;
        if self.arena.contains(p) {
            return;
        }
        log!(self, c, "deallocate pointer {:p}", c);
        // SAFETY: not in the arena, thus allocated with 'CRef::alloc'.
        unsafe { c.dealloc() };
    }

    pub fn delete_clause(&mut self, c: CRef) {
        log!(self, c, "delete pointer {:p}", c);
        let bytes = c.bytes();
        self.stats.collected += bytes as i64;
        if c.garbage() {
            debug_assert!(self.stats.garbage.bytes >= bytes as i64);
            self.stats.garbage.bytes -= bytes as i64;
            debug_assert!(self.stats.garbage.clauses > 0);
            self.stats.garbage.clauses -= 1;
            debug_assert!(self.stats.garbage.literals >= c.size() as i64);
            self.stats.garbage.literals -= c.size() as i64;

            // See the discussion in 'propagate' on avoiding to eagerly trace
            // binary clauses as deleted (produce 'd ...' lines) as soon they
            // are marked garbage.  We avoid this and only trace them as
            // deleted when they are actually deleted here.  This allows the
            // solver to propagate binary garbage clauses without producing
            // incorrect 'd' lines.  The effect from the proof perspective is
            // that the deletion of these binary clauses occurs later in the
            // proof file.
            //
            if c.size() == 2 && !c.flushed() {
                if let Some(proof) = self.proof.as_mut() {
                    proof.delete_clause(c);
                }
            }
        }
        self.deallocate_clause(c);
    }

    /// We want to eagerly update statistics as soon clauses are marked
    /// garbage.  Otherwise 'report' for instance gives wrong numbers after
    /// 'subsume' before the next 'reduce'.  Thus we factored out marking
    /// and accounting for garbage clauses.
    ///
    /// Eagerly deleting clauses instead is problematic, since references to
    /// these clauses need to be flushed, which is too costly to do eagerly.
    ///
    /// We also update garbage statistics at this point.  This helps to
    /// determine whether the garbage collector should be called during for
    /// instance bounded variable elimination, which usually generates lots
    /// of garbage clauses.
    ///
    /// In order not to miss any update to these clause statistics we call
    /// 'check_clause_stats' after garbage collection in debugging mode.
    pub fn mark_garbage(&mut self, c: CRef) {
        debug_assert!(!c.garbage());

        // Delay tracing deletion of binary clauses.  See the discussion
        // above in 'delete_clause' and also in 'propagate'.
        //
        if self.proof.is_some() && (c.size() != 2 || !self.watching()) {
            c.set_flushed(true);
            self.proof.as_mut().unwrap().delete_clause(c);
        }

        // Because of the internal model checking, external forgettable
        // clauses must be marked as removed already upon mark_garbage, can
        // not wait until actual deletion.
        if self.opts.check != 0 && self.is_external_forgettable(c.id()) {
            self.mark_garbage_external_forgettable(c.id());
        }

        debug_assert!(self.stats.current.total > 0);
        self.stats.current.total -= 1;

        let bytes = c.bytes();
        if c.redundant() {
            debug_assert!(self.stats.current.redundant > 0);
            self.stats.current.redundant -= 1;
        } else {
            debug_assert!(self.stats.current.irredundant > 0);
            self.stats.current.irredundant -= 1;
            debug_assert!(self.stats.irrlits >= c.size() as i64);
            self.stats.irrlits -= c.size() as i64;
            self.mark_removed(c, 0);
        }
        self.stats.garbage.bytes += bytes as i64;
        self.stats.garbage.clauses += 1;
        self.stats.garbage.literals += c.size() as i64;
        c.set_garbage(true);
        c.set_used(0);

        log!(self, c, "marked garbage pointer {:p}", c);
    }

    /*----------------------------------------------------------------------*/

    /// Almost the same function as 'search_assign' except that we do not
    /// pretend to learn a new unit clause (which was confusing in log
    /// files).
    pub fn assign_original_unit(&mut self, id: i64, lit: i32) {
        // assert (!level || opts.chrono || external->propagator);
        debug_assert!(!self.unsat);
        let idx = self.vidx(lit);
        debug_assert!(self.val(idx) == 0);
        debug_assert!(!self.flags(idx).eliminated());
        let trail_len = self.trail.len() as i32;
        {
            let v = self.var_mut(idx);
            v.level = 0;
            v.trail = trail_len;
            v.reason = CRef::NULL;
        }
        let tmp = sign(lit) as i8;
        self.set_val(idx, tmp);
        self.trail.push(lit);
        self.num_assigned += 1;
        let uidx = self.vlit(lit);
        if self.lrat || self.frat {
            *self.unit_clauses(uidx as i32) = id;
        }
        log!(self, "original unit assign {}", lit);
        debug_assert!(self.num_assigned == self.trail.len() || self.level != 0);
        self.mark_fixed(lit);
        if self.level != 0 {
            return;
        }
        if self.propagate() {
            return;
        }
        debug_assert!(!self.conflict.is_null());
        log!(self, "propagation of original unit results in conflict");
        self.learn_empty_clause();
    }

    /// New clause added through the API, e.g., while parsing a DIMACS file.
    /// Also used by external_propagate in various different modes.
    /// clause, original, lrat_chain and external->eclause are set.
    /// from_propagator and force_no_backtrack change the behaviour.
    /// sometimes the pointer to the new clause is needed, therefore it is
    /// made sure that newest_clause points to the new clause upon return.
    pub fn add_new_original_clause(&mut self, id: i64) {
        if !self.from_propagator && self.level != 0 && self.opts.ilb == 0 {
            self.backtrack(0);
        } else if self.changed_val != 0 {
            debug_assert!(self.val(self.changed_val) != 0);
            let new_level = self.var(self.changed_val).level - 1;
            debug_assert!(new_level >= 0);
            self.backtrack(new_level);
        }
        debug_assert!(self.changed_val == 0);
        log!(self, &self.original, "original clause");
        debug_assert!(self.clause.is_empty());
        let mut skip = false;
        // Only the size of 'learned_levels' is used ('unordered_set<int>').
        let mut learned_levels: std::collections::HashSet<i32> = std::collections::HashSet::new();
        let mut unassigned: usize = 0;
        self.newest_clause = CRef::NULL;
        let external = self.ext_unbound();
        if self.unsat {
            log!(self, "skipping clause since formula is already inconsistent");
            skip = true;
        } else {
            debug_assert!(self.clause.is_empty());
            for k in 0..self.original.len() {
                let lit = self.original[k];
                let mut tmp = self.marked(lit) as i32;
                if tmp > 0 {
                    log!(self, "removing duplicated literal {}", lit);
                } else if tmp < 0 {
                    log!(self, "tautological since both {} and {} occur", -lit, lit);
                    skip = true;
                } else {
                    self.mark(lit);
                    tmp = self.fixed(lit);
                    if tmp < 0 {
                        log!(self, "removing falsified literal {}", lit);
                        if self.lrat {
                            let elit = self.externalize(lit);
                            let eidx = (elit > 0) as u32 + 2u32 * elit.unsigned_abs();
                            if external.ext_units[eidx as usize] == 0 {
                                let uid = self.unit_id(-lit);
                                self.lrat_chain.push(uid);
                            }
                        }
                    } else if tmp > 0 {
                        log!(self, "satisfied since literal {} true", lit);
                        skip = true;
                    } else {
                        self.clause.push(lit);
                        debug_assert!(self.flags(lit).status != Flags::UNUSED);
                        tmp = self.val(lit) as i32;
                        if tmp != 0 {
                            learned_levels.insert(self.var(lit).level);
                        } else {
                            unassigned += 1;
                        }
                    }
                }
            }
            for k in 0..self.original.len() {
                let lit = self.original[k];
                self.unmark(lit);
            }
        }
        if skip {
            if self.from_propagator {
                self.stats.ext_prop.elearn_conf += 1;

                // In case it was a skipped external forgettable, we need to
                // mark it immediately as removed

                if self.opts.check != 0 && self.is_external_forgettable(id) {
                    self.mark_garbage_external_forgettable(id);
                }
            }
            if let Some(proof) = self.proof.as_mut() {
                proof.delete_external_original_clause(id, false, &external.eclause);
            }
        } else {
            let mut new_id = id;
            let size = self.clause.len();
            if self.original.len() > size {
                self.clause_id += 1;
                new_id = self.clause_id;
                if self.proof.is_some() {
                    if self.lrat {
                        self.lrat_chain.push(id);
                    }
                    let proof = self.proof.as_mut().unwrap();
                    proof.add_derived_clause_lits(new_id, false, &self.clause, &self.lrat_chain);
                    proof.delete_external_original_clause(id, false, &external.eclause);
                }
                external.check_learned_clause();

                if self.from_propagator {
                    // The original form of the added clause is immediately
                    // forgotten TODO: shall we save and check the simplified
                    // form? (one with new_id)
                    if self.opts.check != 0 && self.is_external_forgettable(id) {
                        self.mark_garbage_external_forgettable(id);
                    }
                }
            }
            external.eclause.clear();
            self.lrat_chain.clear();
            if size == 0 {
                if self.from_propagator {
                    self.stats.ext_prop.elearn_conf += 1;
                }
                debug_assert!(!self.unsat);
                if self.original.is_empty() {
                    verbose!(self, 1, "found empty original clause");
                } else {
                    verbose!(self, 1, "found falsified original clause");
                }
                self.unsat = true;
                self.conflict_id = new_id;
                self.marked_failed = true;
                self.conclusion.push(new_id);
            } else if size == 1 {
                self.handle_external_clause(CRef::NULL, new_id);
            } else {
                self.move_literals_to_watch();
                #[cfg(debug_assertions)]
                self.check_watched_literal_invariants();
                let glue = (learned_levels.len() + unassigned) as i32;
                debug_assert!(glue <= self.clause.len() as i32);
                let clause_redundancy = self.from_propagator && self.ext_clause_forgettable;
                let c = self.new_clause(clause_redundancy, glue);
                c.set_id(new_id);
                self.clause_id -= 1;
                self.original.clear();
                self.handle_external_clause(c, 0); // handle_external_clause uses clause
                self.watch_clause(c); // and may change the watched literal
                self.clause.clear(); // therefore it is cleared afterwards
                self.newest_clause = c;
            }
        }
        self.clause.clear();
        self.lrat_chain.clear();
    }

    /// Add learned new clause during conflict analysis and watch it.
    /// Requires that the clause is at least of size 2, and the first two
    /// literals are assigned at the highest decision level.
    pub fn new_learned_redundant_clause(&mut self, glue: i32) -> CRef {
        debug_assert!(self.clause.len() > 1);
        #[cfg(debug_assertions)]
        for i in 2..self.clause.len() {
            debug_assert!(self.var(self.clause[0]).level >= self.var(self.clause[i]).level);
            debug_assert!(self.var(self.clause[1]).level >= self.var(self.clause[i]).level);
        }
        self.external().check_learned_clause();
        let res = self.new_clause(true, glue);
        if let Some(proof) = self.proof.as_mut() {
            proof.add_derived_clause(res, &self.lrat_chain);
        }
        debug_assert!(self.watching());
        self.watch_clause(res);
        res
    }

    /// Add hyper binary resolved clause during 'probing'.
    pub fn new_hyper_binary_resolved_clause(&mut self, red: bool, glue: i32) -> CRef {
        self.external().check_learned_clause();
        let res = self.new_clause(red, glue);
        if let Some(proof) = self.proof.as_mut() {
            proof.add_derived_clause(res, &self.lrat_chain);
        }
        debug_assert!(self.watching());
        self.watch_clause(res);
        res
    }

    /// Add hyper ternary resolved clause during 'ternary'.
    pub fn new_hyper_ternary_resolved_clause(&mut self, red: bool) -> CRef {
        self.external().check_learned_clause();
        let size = self.clause.len();
        let res = self.new_clause(red, size as i32);
        if let Some(proof) = self.proof.as_mut() {
            proof.add_derived_clause(res, &self.lrat_chain);
        }
        debug_assert!(!self.watching());
        res
    }

    pub fn new_factor_clause(&mut self, witness: i32) -> CRef {
        self.external().check_learned_clause();
        self.stats.factor_added += 1;
        self.stats.literals_factored += self.clause.len() as i64;
        let res = self.new_clause(false, 0);
        if self.proof.is_some() {
            if witness != 0 {
                let ew = self.externalize(witness);
                let proof = self.proof.as_mut().unwrap();
                proof.add_derived_rat_clause(res, ew, &self.lrat_chain);
            } else {
                let proof = self.proof.as_mut().unwrap();
                proof.add_derived_clause(res, &self.lrat_chain);
            }
        }
        debug_assert!(!self.watching());
        debug_assert!(self.occurring());
        for i in 0..res.size() as usize {
            let lit = res.lit(i);
            self.occs_mut(lit).push(res);
        }
        res
    }

    /// Add hyper ternary resolved clause during 'congruence' and watch it
    pub fn new_hyper_ternary_resolved_clause_and_watch(&mut self, red: bool, full_watching: bool) -> CRef {
        self.external().check_learned_clause();
        let size = self.clause.len();
        let res = self.new_clause(red, size as i32);
        if let Some(proof) = self.proof.as_mut() {
            proof.add_derived_clause(res, &self.lrat_chain);
        }
        if full_watching {
            debug_assert!(self.watching());
            self.watch_clause(res);
        }
        res
    }

    /// Add a new clause with same glue and redundancy as 'orig' but
    /// literals are assumed to be in 'clause' in 'decompose' and 'vivify'.
    pub fn new_clause_as(&mut self, orig: CRef) -> CRef {
        self.external().check_learned_clause();
        let new_glue = orig.glue();
        let res = self.new_clause(orig.redundant(), new_glue);
        if let Some(proof) = self.proof.as_mut() {
            proof.add_derived_clause(res, &self.lrat_chain);
        }
        debug_assert!(self.watching());
        self.watch_clause(res);
        res
    }

    /// Add resolved clause during resolution, e.g., bounded variable
    /// elimination, but do not connect its occurrences here.
    pub fn new_resolved_irredundant_clause(&mut self) -> CRef {
        self.external().check_learned_clause();
        if let Some(proof) = self.proof.as_mut() {
            proof.add_derived_clause_lits(self.clause_id + 1, false, &self.clause, &self.lrat_chain);
        }
        let res = self.new_clause(false, 0);
        debug_assert!(!self.watching());
        res
    }

    pub fn decay_clauses_upon_incremental_clauses(&mut self) {
        if self.opts.incdecay == 0 {
            return;
        }
        if self.stats.searches == 0 {
            return;
        }
        if self.stats.conflicts < self.lim.incremental_decay {
            return;
        }

        phase!(
            self,
            "decay",
            self.stats.incremental_decay,
            "decaying clauses with next decaying at conflict {}(after the next incremental call)",
            self.lim.incremental_decay
        );

        for i in 0..self.clauses.len() {
            let c = self.clauses[i];
            if c.garbage() {
                continue;
            }
            if !c.redundant() {
                continue;
            }
            if c.id() >= self.last.incremental_decay.last_id {
                continue;
            }
            match self.opts.incdecay {
                1 => {
                    // my intuition
                    c.set_glue(c.glue() + 1);
                }
                2 => {
                    // Armin's idea
                    if c.glue() < self.tier1[false as usize] {
                        c.set_used(1);
                    }
                }
                3 => {
                    if c.glue() < self.tier1[false as usize] {
                        c.set_used(1);
                    }
                    c.set_glue(c.glue() + 1);
                }
                _ => {}
            }
        }

        self.lim.incremental_decay += self.stats.conflicts + self.opts.incdecayint as i64;
        self.stats.incremental_decay += 1;
        self.last.incremental_decay.last_id = self.clause_id;
    }
}

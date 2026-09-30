//! Port of `lratchecker.hpp` and `lratchecker.cpp`: the online LRAT proof
//! checker.

use std::collections::HashMap;

use crate::internal::Internal;
use crate::tracer::{ConclusionType, InternalTracer, StatTracer, Tracer};

#[repr(C)]
pub struct LratCheckerClause {
    /// Collision chain link for hash table.
    pub next: *mut LratCheckerClause,
    /// Previously computed full 64-bit hash.
    pub hash: u64,
    /// Id of clause.
    pub id: i64,
    /// For garbage clauses.
    pub garbage: bool,
    pub size: u32,
    pub used: bool,
    pub tautological: bool,
    /// 'literals' of length 'size'.
    pub literals: [i32; 1],
}

#[derive(Clone, Copy, Debug, Default)]
pub struct LratCheckerStats {
    /// Number of added clauses.
    pub added: i64,
    /// Number of added original clauses.
    pub original: i64,
    /// Number of added derived clauses.
    pub derived: i64,
    /// Number of added rat clauses.
    pub rat: i64,
    /// Number of deleted clauses.
    pub deleted: i64,
    /// Number of finalized clauses.
    pub finalized: i64,
    /// Number of clauses added to hash table.
    pub insertions: i64,
    /// Number of hash collisions in 'find'.
    pub collisions: i64,
    /// Number of searched clauses in 'find'.
    pub searches: i64,
    /// Number of implication checks.
    pub checks: i64,
    /// Garbage collections.
    pub collections: i64,
}

pub const LRAT_CHECKER_NUM_NONCES: usize = 4;

pub struct LratChecker {
    pub internal: *mut Internal,

    /// Number of variables.
    pub size_vars: i64,

    pub checked_lits: Vec<i8>,
    /// Mark bits of literals.
    pub marks: Vec<i8>,
    /// Only 'find' / 'erase' are used (order irrelevant).
    pub clauses_to_reconstruct: HashMap<i64, Vec<i32>>,
    pub assumptions: Vec<i32>,
    pub constraint: Vec<i32>,
    pub concluded: bool,

    /// Number of clauses in hash table.
    pub num_clauses: u64,
    pub num_finalized: u64,
    /// Number of garbage clauses.
    pub num_garbage: u64,
    /// Size of clause hash table.
    pub size_clauses: u64,
    /// Hash table of clauses.
    pub clauses: Vec<*mut LratCheckerClause>,
    /// Linked list of garbage clauses.
    pub garbage: *mut LratCheckerClause,

    /// Original clause for reporting.
    pub imported_clause: Vec<i32>,
    pub assumption_clauses: Vec<i64>,

    /// Random numbers for hashing.
    pub nonces: [u64; LRAT_CHECKER_NUM_NONCES],
    /// Last computed hash value of clause.
    pub last_hash: u64,
    /// Id of the last added/deleted clause.
    pub last_id: i64,
    /// Id of the last added clause.
    pub current_id: i64,

    pub stats: LratCheckerStats,
}

/*------------------------------------------------------------------------*/

#[allow(unused_imports)]
use crate::prelude::*;

use crate::message::{c_stderr, fatal_message_end, fatal_message_start, fputc, fputs};

/// Pointer to the literals of an LRAT checker clause (variadic array).
#[inline(always)]
fn lrat_lits(c: *mut LratCheckerClause) -> *mut i32 {
    // SAFETY: only computes the address of the 'literals' field.
    unsafe { std::ptr::addr_of_mut!((*c).literals) as *mut i32 }
}

/// Literals of an LRAT checker clause as slice.
#[inline(always)]
fn lrat_clause_lits<'a>(c: *mut LratCheckerClause) -> &'a [i32] {
    // SAFETY: 'c' is a live clause with 'size' literals.
    unsafe { std::slice::from_raw_parts(lrat_lits(c), (*c).size as usize) }
}

/// `fatal_message_start (); fputs (msg, stderr); <lits> fputc ('0');
/// fatal_message_end ()`.
fn fatal_with_clause(msg: &str, lits: &[i32]) -> ! {
    fatal_message_start();
    fputs(msg, c_stderr());
    for &lit in lits {
        cfprintf!(c_stderr(), "{} ", lit);
    }
    fputc(b'0' as i32, c_stderr());
    fatal_message_end();
}

impl Tracer for LratChecker {
    fn begin_proof(&mut self, id: i64) {
        self.current_id = id;
    }

    fn add_original_clause(&mut self, id: i64, _redundant: bool, c: &[i32], restore: bool) {
        // SAFETY: back pointer to the owning 'Internal'.
        let internal = unsafe { &mut *self.internal };
        start!(internal, checking);
        log!(self.internal, c, "LRAT CHECKER addition of original clause[{}]", id);
        if restore {
            self.restore_clause(id, c);
        }
        self.stats.added += 1;
        self.stats.original += 1;
        self.import_clause(c);
        self.last_id = id;
        if !restore && id == 1 + self.current_id {
            self.current_id = id;
        }

        if self.size_clauses != 0 && !restore {
            let p = self.find(id);
            // SAFETY: 'p' points to a valid slot.
            let d = unsafe { *p };
            if !d.is_null() {
                fatal_message_start();
                fputs("different clause with id ", c_stderr());
                cfprintf!(c_stderr(), "{}", id);
                fputs(" already present\n", c_stderr());
                fatal_message_end();
            }
        }
        debug_assert!(id != 0);
        self.insert();
        self.imported_clause.clear();
        // SAFETY: see above.
        let internal = unsafe { &mut *self.internal };
        stop!(internal, checking);
    }

    fn add_derived_clause(&mut self, id: i64, _redundant: bool, w: i32, c: &[i32], proof_chain: &[i64]) {
        // SAFETY: back pointer to the owning 'Internal'.
        let internal = unsafe { &mut *self.internal };
        start!(internal, checking);
        log!(self.internal, c, "LRAT CHECKER addition of derived {} clause[{}]", w, id);
        debug_assert!(w == 0 || c[0] == w);
        if w != 0 {
            self.stats.rat += 1;
        }
        self.stats.added += 1;
        self.stats.derived += 1;
        self.import_clause(c);
        self.last_id = id;
        debug_assert!(id == self.current_id + 1);
        debug_assert!(w == 0 || w == c[0]);
        self.current_id = id;
        if self.size_clauses != 0 {
            let p = self.find(id);
            // SAFETY: 'p' points to a valid slot.
            let d = unsafe { *p };
            if !d.is_null() {
                fatal_message_start();
                fputs("different clause with id ", c_stderr());
                cfprintf!(c_stderr(), "{}", id);
                fputs(" already present\n", c_stderr());
                fatal_message_end();
            }
        }
        debug_assert!(id != 0);
        let mut failed = true;
        if self.check(proof_chain.to_vec()) && self.check_resolution(proof_chain.to_vec()) {
            failed = false;
        } else if self.check_blocked(proof_chain.to_vec()) {
            failed = false;
        }
        if failed {
            log!(self.internal, proof_chain, "LRAT CHECKER check failed with chain");
            #[cfg(feature = "logging")]
            {
                for &pid in proof_chain {
                    let aid = pid.abs();
                    let p = self.find(aid);
                    // SAFETY: 'p' points to a valid slot (the C++ code
                    // dereferences 'd' unconditionally too).
                    let d = unsafe { *p };
                    // SAFETY: back pointer to the owning 'Internal'.
                    let i: &Internal = unsafe { &*self.internal };
                    if i.opts.log != 0 {
                        crate::logging::Logger::log_int_array(
                            i,
                            lrat_clause_lits(d),
                            format_args!("clause[{}]", pid),
                        );
                    }
                }
            }
            fatal_with_clause("failed to check derived clause:\n", &self.imported_clause);
        } else {
            self.insert();
        }
        self.imported_clause.clear();
        // SAFETY: see above.
        let internal = unsafe { &mut *self.internal };
        stop!(internal, checking);
    }

    fn delete_clause(&mut self, id: i64, _redundant: bool, c: &[i32]) {
        // SAFETY: back pointer to the owning 'Internal'.
        let internal = unsafe { &mut *self.internal };
        start!(internal, checking);
        log!(self.internal, c, "LRAT CHECKER checking deletion of clause[{}]", id);
        self.stats.deleted += 1;
        self.import_clause(c);
        self.last_id = id;
        let p = self.find(id);
        // SAFETY: 'p' points to a valid slot, 'd' (if non-null) is live.
        unsafe {
            let d = *p;
            if !d.is_null() {
                for k in 0..self.imported_clause.len() {
                    let lit = self.imported_clause[k];
                    *self.mark(lit) = 1;
                }
                let dp = lrat_lits(d);
                for i in 0..(*d).size as usize {
                    let lit = *dp.add(i);
                    if *self.mark(lit) == 0 {
                        // should never happen since ids are unique.
                        fatal_with_clause("deleted clause not in proof:\n", &self.imported_clause);
                    }
                }
                for k in 0..self.imported_clause.len() {
                    let lit = self.imported_clause[k];
                    *self.mark(lit) = 0;
                }

                // Remove from hash table, mark as garbage, connect to
                // garbage list.
                self.num_garbage += 1;
                debug_assert!(self.num_clauses != 0);
                self.num_clauses -= 1;
                *p = (*d).next;
                (*d).next = self.garbage;
                self.garbage = d;
                (*d).garbage = true;

                // If there are enough garbage clauses collect them.
                // TODO: probably can just delete clause directly without
                // specific garbage collection phase.
                if self.num_garbage as f64
                    > 0.5 * std::cmp::max(self.size_clauses as usize, self.size_vars as usize) as f64
                {
                    self.collect_garbage_clauses();
                }
            } else {
                fatal_with_clause("deleted clause not in proof:\n", &self.imported_clause);
            }
        }
        self.imported_clause.clear();
        // SAFETY: see above.
        let internal = unsafe { &mut *self.internal };
        stop!(internal, checking);
    }

    fn weaken_minus(&mut self, id: i64, c: &[i32]) {
        log!(self.internal, c, "LRAT CHECKER saving clause[{}] to restore later", id);
        self.import_clause(c);

        debug_assert!(id <= self.current_id);
        self.last_id = id;
        let p = self.find(id);
        // SAFETY: 'p' points to a valid slot, 'd' (if non-null) is live.
        unsafe {
            let d = *p;
            if !d.is_null() {
                for k in 0..self.imported_clause.len() {
                    let lit = self.imported_clause[k];
                    *self.mark(lit) = 1;
                }
                let dp = lrat_lits(d);
                for i in 0..(*d).size as usize {
                    let lit = *dp.add(i);
                    if *self.mark(lit) == 0 {
                        // should never happen since ids are unique.
                        fatal_with_clause("deleted clause not in proof:\n", &self.imported_clause);
                    }
                }
                for k in 0..self.imported_clause.len() {
                    let lit = self.imported_clause[k];
                    *self.mark(lit) = 0;
                }
            } else {
                fatal_with_clause("weakened clause not in proof:\n", &self.imported_clause);
            }
        }
        self.imported_clause.clear();

        let mut e: Vec<i32> = c.to_vec();
        crate::sort::std_sort_default_arith(&mut e);
        self.clauses_to_reconstruct.insert(id, e);
    }

    fn finalize_clause(&mut self, id: i64, c: &[i32]) {
        // SAFETY: back pointer to the owning 'Internal'.
        let internal = unsafe { &mut *self.internal };
        start!(internal, checking);
        log!(self.internal, c, "LRAT CHECKER checking finalize of clause[{}]", id);
        self.stats.finalized += 1;
        self.num_finalized += 1;
        self.import_clause(c);
        debug_assert!(id <= self.current_id);
        self.last_id = id;
        let p = self.find(id);
        // SAFETY: 'p' points to a valid slot, 'd' (if non-null) is live.
        unsafe {
            let d = *p;
            if !d.is_null() {
                for k in 0..self.imported_clause.len() {
                    let lit = self.imported_clause[k];
                    *self.mark(lit) = 1;
                }
                let dp = lrat_lits(d);
                for i in 0..(*d).size as usize {
                    let lit = *dp.add(i);
                    if *self.mark(lit) == 0 {
                        // should never happen since ids are unique.
                        fatal_with_clause("deleted clause not in proof:\n", &self.imported_clause);
                    }
                }
                for k in 0..self.imported_clause.len() {
                    let lit = self.imported_clause[k];
                    *self.mark(lit) = 0;
                }
            } else {
                fatal_with_clause("deleted clause not in proof:\n", &self.imported_clause);
            }
        }
        self.imported_clause.clear();
        // SAFETY: see above.
        let internal = unsafe { &mut *self.internal };
        stop!(internal, checking);
    }

    fn add_assumption_clause(&mut self, id: i64, c: &[i32], chain: &[i64]) {
        for &lit in c {
            if self.assumptions.contains(&-lit) {
                continue;
            }
            if self.constraint.contains(&-lit) {
                continue;
            }
            fatal_message_start();
            fputs("clause contains non assumptions or constraint literals\n", c_stderr());
            fatal_message_end();
        }
        self.add_derived_clause(id, true, 0, c, chain);
        Tracer::delete_clause(self, id, true, c);
        self.assumption_clauses.push(id);
    }

    fn add_assumption(&mut self, a: i32) {
        self.assumptions.push(a);
    }

    fn add_constraint(&mut self, c: &[i32]) {
        self.constraint.clear();
        for &lit in c {
            debug_assert!(lit != 0);
            if self.constraint.contains(&lit) {
                continue;
            }
            self.constraint.push(lit);
        }
    }

    fn reset_assumptions(&mut self) {
        self.assumption_clauses.clear();
        self.assumptions.clear();
        self.concluded = false;
        // constraint.clear ();
    }

    /// Check if all clauses have been deleted.
    fn report_status(&mut self, _status: i32, _id: i64) {
        // SAFETY: back pointer to the owning 'Internal'.
        let internal = unsafe { &mut *self.internal };
        start!(internal, checking);
        if self.num_finalized == self.num_clauses {
            self.num_finalized = 0;
            log!(
                self.internal,
                "LRAT CHECKER successful finalize check, all clauses have been deleted"
            );
        } else {
            fatal_message_start();
            fputs("finalize check failed ", c_stderr());
            cfprintf!(c_stderr(), "{}", self.num_clauses);
            fputs(" are not finalized", c_stderr());
            fatal_message_end();
        }
        // SAFETY: see above.
        let internal = unsafe { &mut *self.internal };
        stop!(internal, checking);
    }

    fn conclude_unsat(&mut self, conclusion: ConclusionType, ids: &[i64]) {
        if self.concluded {
            fatal_message_start();
            fputs("already concluded\n", c_stderr());
            fatal_message_end();
        }
        self.concluded = true;
        if conclusion == ConclusionType::CONFLICT {
            let p = self.find(*ids.last().unwrap());
            // SAFETY: 'p' points to a valid slot, 'd' (if non-null) is live.
            let d = unsafe { *p };
            if d.is_null() || unsafe { (*d).size } != 0 {
                fatal_message_start();
                fputs("empty clause not in proof\n", c_stderr());
                fatal_message_end();
            }
        } else if conclusion == ConclusionType::ASSUMPTIONS {
            if ids.len() != 1 || self.assumption_clauses.len() != 1 {
                fatal_message_start();
                fputs("expected exactly one assumption clause\n", c_stderr());
                fatal_message_end();
            }
            if ids.last() != self.assumption_clauses.last() {
                fatal_message_start();
                fputs("conclusion is not an assumption clause\n", c_stderr());
                fatal_message_end();
            }
        } else {
            debug_assert!(conclusion == ConclusionType::CONSTRAINT);
            if self.constraint.len() != ids.len() {
                fatal_message_start();
                fputs("not complete conclusion given for constraint\n", c_stderr());
                fputs("The constraint contains the literals: ", c_stderr());
                for &c in &self.constraint {
                    cfprintf!(c_stderr(), "{} ", c);
                }

                fputs("\nThe ids are: ", c_stderr());
                for &c in ids {
                    cfprintf!(c_stderr(), "{} ", c);
                }
                fatal_message_end();
            }
            for id in ids {
                if self.assumption_clauses.contains(id) {
                    continue;
                }
                fatal_message_start();
                fputs("assumption clause for constraint missing\n", c_stderr());
                fatal_message_end();
            }
        }
    }
}

impl InternalTracer for LratChecker {
    fn connect_internal(&mut self, i: *mut Internal) {
        self.internal = i;
        log!(self.internal, "connected to internal");
    }
}

impl StatTracer for LratChecker {
    /// `LratChecker::print_stats` (from 'stats.cpp').
    fn print_stats(&mut self) {
        if self.stats.added == 0 && self.stats.deleted == 0 {
            return;
        }

        // SAFETY: back pointer to the owning 'Internal'.
        let internal = unsafe { &mut *self.internal };
        section!(internal, "lrat checker statistics");

        let s = self.stats;
        let i = self.internal;
        msg!(i, "checks:          {:15}", s.checks);
        msg!(
            i,
            "insertions:      {:15}   {:10.2} %  of all clauses",
            s.insertions,
            percent(s.insertions as f64, s.added as f64)
        );
        msg!(
            i,
            "original:        {:15}   {:10.2} %  of all clauses",
            s.original,
            percent(s.original as f64, s.added as f64)
        );
        msg!(
            i,
            "derived:         {:15}   {:10.2} %  of all clauses",
            s.derived,
            percent(s.derived as f64, s.added as f64)
        );
        msg!(
            i,
            "rat:         {:15}   {:10.2} %  of derived clauses",
            s.rat,
            percent(s.rat as f64, s.derived as f64)
        );
        msg!(
            i,
            "deleted:         {:15}   {:10.2} %  of all clauses",
            s.deleted,
            percent(s.deleted as f64, s.added as f64)
        );
        msg!(
            i,
            "finalized:       {:15}   {:10.2} %  of all clauses",
            s.finalized,
            percent(s.finalized as f64, s.added as f64)
        );
        msg!(
            i,
            "collections:     {:15}   {:10.2}    deleted per collection",
            s.collections,
            relative(s.collections as f64, s.deleted as f64)
        );
        msg!(
            i,
            "collisions:      {:15}   {:10.2}    per search",
            s.collisions,
            relative(s.collisions as f64, s.searches as f64)
        );
        msg!(i, "searches:        {:15}", s.searches);
    }
}

impl LratChecker {
    pub fn new(internal: *mut Internal) -> LratChecker {
        let mut nonces = [0u64; LRAT_CHECKER_NUM_NONCES];
        // Initialize random number table for hash function.
        let mut random = Random::new(42);
        for n in nonces.iter_mut() {
            let mut nonce = random.next();
            if nonce & 1 == 0 {
                nonce = nonce.wrapping_add(1);
            }
            debug_assert!(nonce != 0);
            debug_assert!(nonce & 1 != 0);
            *n = nonce;
        }
        LratChecker {
            internal,
            size_vars: 0,
            checked_lits: Vec::new(),
            marks: Vec::new(),
            clauses_to_reconstruct: HashMap::new(),
            assumptions: Vec::new(),
            constraint: Vec::new(),
            concluded: false,
            num_clauses: 0,
            num_finalized: 0,
            num_garbage: 0,
            size_clauses: 0,
            clauses: Vec::new(),
            garbage: std::ptr::null_mut(),
            imported_clause: Vec::new(),
            assumption_clauses: Vec::new(),
            nonces,
            last_hash: 0,
            last_id: 0,
            current_id: 0,
            stats: LratCheckerStats::default(), // Initialize statistics.
        }
    }
}

impl Drop for LratChecker {
    fn drop(&mut self) {
        log!(self.internal, "LRAT CHECKER delete");
        for i in 0..self.size_clauses as usize {
            let mut c = self.clauses[i];
            while !c.is_null() {
                // SAFETY: 'c' is a live clause of the hash table.
                let next = unsafe { (*c).next };
                self.deallocate_clause(c);
                c = next;
            }
        }
        let mut c = self.garbage;
        while !c.is_null() {
            // SAFETY: 'c' is a live garbage clause.
            let next = unsafe { (*c).next };
            self.deallocate_clause(c);
            c = next;
        }
        self.garbage = std::ptr::null_mut();
    }
}

/*------------------------------------------------------------------------*/

impl LratChecker {
    #[inline]
    pub fn l2u(lit: i32) -> u32 {
        debug_assert!(lit != 0);
        debug_assert!(lit != i32::MIN);
        let mut res = 2 * (lit.abs() - 1) as u32;
        if lit < 0 {
            res += 1;
        }
        res
    }

    pub fn mark(&mut self, lit: i32) -> &mut i8 {
        let u = Self::l2u(lit) as usize;
        debug_assert!(u < self.marks.len());
        &mut self.marks[u]
    }

    pub fn checked_lit(&mut self, lit: i32) -> &mut i8 {
        let u = Self::l2u(lit) as usize;
        debug_assert!(u < self.checked_lits.len());
        &mut self.checked_lits[u]
    }

    /*----------------------------------------------------------------------*/

    pub fn new_clause(&mut self) -> *mut LratCheckerClause {
        let size = self.imported_clause.len();
        debug_assert!(size <= u32::MAX as usize);
        let off = if size != 0 { 1 } else { 0 };
        let bytes = std::mem::size_of::<LratCheckerClause>() + (size - off) * std::mem::size_of::<i32>();
        // SAFETY: allocation of a variadic clause, initialized below.
        let res = unsafe { libc::malloc(bytes) as *mut LratCheckerClause };
        if res.is_null() {
            std::alloc::handle_alloc_error(std::alloc::Layout::from_size_align(bytes, 8).unwrap());
        }
        // SAFETY: 'res' points to 'bytes' writable bytes.
        unsafe {
            (*res).garbage = false;
            (*res).next = std::ptr::null_mut();
            (*res).hash = self.last_hash;
            (*res).id = self.last_id;
            (*res).size = size as u32;
            (*res).used = false;
            (*res).tautological = false;
        }
        let literals = lrat_lits(res);
        #[cfg(debug_assertions)]
        for &b in &self.checked_lits {
            debug_assert!(b == 0); // = false;
        }
        for k in 0..size {
            let lit = self.imported_clause[k];
            // SAFETY: 'k < size'.
            unsafe { *literals.add(k) = lit };
            *self.checked_lit(-lit) = 1;
            if *self.checked_lit(lit) != 0 {
                log!(self.internal, &self.imported_clause, "LRAT CHECKER clause tautological");
                // SAFETY: see above.
                unsafe { (*res).tautological = true };
            }
        }
        for k in 0..size {
            let lit = self.imported_clause[k];
            *self.checked_lit(-lit) = 0;
        }
        self.num_clauses += 1;

        res
    }

    /// C++ overload `LratChecker::delete_clause` (renamed).
    pub fn deallocate_clause(&mut self, c: *mut LratCheckerClause) {
        debug_assert!(!c.is_null());
        // SAFETY: 'c' is a live clause allocated in 'new_clause'.
        unsafe {
            if !(*c).garbage {
                debug_assert!(self.num_clauses != 0);
                self.num_clauses -= 1;
            } else {
                debug_assert!(self.num_garbage != 0);
                self.num_garbage -= 1;
            }
            libc::free(c as *mut libc::c_void);
        }
    }

    pub fn enlarge_clauses(&mut self) {
        debug_assert!(self.num_clauses == self.size_clauses);
        let new_size_clauses: u64 = if self.size_clauses != 0 { 2 * self.size_clauses } else { 1 };
        log!(
            self.internal,
            "LRAT CHECKER enlarging clauses of checker from {} to {}",
            self.size_clauses,
            new_size_clauses
        );
        let mut new_clauses: Vec<*mut LratCheckerClause> = vec![std::ptr::null_mut(); new_size_clauses as usize];
        for i in 0..self.size_clauses as usize {
            let mut c = self.clauses[i];
            while !c.is_null() {
                // SAFETY: 'c' is a live clause of the hash table.
                unsafe {
                    let next = (*c).next;
                    let h = Self::reduce_hash((*c).hash, new_size_clauses) as usize;
                    (*c).next = new_clauses[h];
                    new_clauses[h] = c;
                    c = next;
                }
            }
        }
        self.clauses = new_clauses;
        self.size_clauses = new_size_clauses;
    }

    /// Probably not necessary since we have no watches.
    pub fn collect_garbage_clauses(&mut self) {
        self.stats.collections += 1;

        log!(
            self.internal,
            "LRAT CHECKER collecting {} garbage clauses {:.0}%",
            self.num_garbage,
            percent(self.num_garbage as f64, self.num_clauses as f64)
        );

        let mut c = self.garbage;
        while !c.is_null() {
            // SAFETY: 'c' is a live garbage clause.
            let next = unsafe { (*c).next };
            self.deallocate_clause(c);
            c = next;
        }

        debug_assert!(self.num_garbage == 0);
        self.garbage = std::ptr::null_mut();
    }

    /*----------------------------------------------------------------------*/

    pub fn enlarge_vars(&mut self, idx: i64) {
        debug_assert!(0 < idx);
        debug_assert!(idx <= i32::MAX as i64);

        let mut new_size_vars: i64 = if self.size_vars != 0 { 2 * self.size_vars } else { 2 };
        while idx >= new_size_vars {
            new_size_vars *= 2;
        }
        log!(
            self.internal,
            "LRAT CHECKER enlarging variables of checker from {} to {}",
            self.size_vars,
            new_size_vars
        );

        self.marks.resize(2 * new_size_vars as usize, 0);
        self.checked_lits.resize(2 * new_size_vars as usize, 0);

        debug_assert!(idx < new_size_vars);
        self.size_vars = new_size_vars;
    }

    #[inline]
    pub fn import_literal(&mut self, lit: i32) {
        debug_assert!(lit != 0);
        debug_assert!(lit != i32::MIN);
        let idx = lit.abs();
        if idx as i64 >= self.size_vars {
            self.enlarge_vars(idx as i64);
        }
        self.imported_clause.push(lit);
    }

    pub fn import_clause(&mut self, c: &[i32]) {
        for &lit in c {
            self.import_literal(lit);
        }
    }

    /*----------------------------------------------------------------------*/

    pub fn reduce_hash(hash: u64, size: u64) -> u64 {
        debug_assert!(size > 0);
        let mut shift: u32 = 32;
        let mut res = hash;
        while (1u64 << shift) > size {
            res ^= res >> shift;
            shift >>= 1;
        }
        res &= size.wrapping_sub(1);
        debug_assert!(res < size);
        res
    }

    pub fn compute_hash(&mut self, id: i64) -> u64 {
        debug_assert!(id > 0);
        let j = (id % LRAT_CHECKER_NUM_NONCES as i64) as u32 as usize;
        let tmp = self.nonces[j].wrapping_mul(id as u64);
        self.last_hash = tmp;
        tmp
    }

    /// Returns the address of the hash table slot (as C++).
    pub fn find(&mut self, id: i64) -> *mut *mut LratCheckerClause {
        self.stats.searches += 1;
        let hash = self.compute_hash(id);
        let h = Self::reduce_hash(hash, self.size_clauses) as usize;
        // SAFETY: 'h < size_clauses' and the chain consists of live clauses.
        unsafe {
            let mut res: *mut *mut LratCheckerClause = self.clauses.as_mut_ptr().add(h);
            loop {
                let c = *res;
                if c.is_null() {
                    break;
                }
                if (*c).hash == hash && (*c).id == id {
                    break;
                }
                self.stats.collisions += 1;
                res = &mut (*c).next;
            }
            res
        }
    }

    pub fn insert(&mut self) {
        self.stats.insertions += 1;
        if self.num_clauses == self.size_clauses {
            self.enlarge_clauses();
        }
        let hash = self.compute_hash(self.last_id);
        let h = Self::reduce_hash(hash, self.size_clauses) as usize;
        let c = self.new_clause();
        // SAFETY: 'c' is a fresh clause.
        unsafe { (*c).next = self.clauses[h] };
        self.clauses[h] = c;
    }

    /*----------------------------------------------------------------------*/

    /// "strict" resolution check instead of rup check
    pub fn check_resolution(&mut self, proof_chain: Vec<i64>) -> bool {
        if proof_chain.is_empty() {
            log!(self.internal, "LRAT CHECKER resolution check skipped clause is tautological");
            return true;
        }
        // LOG (imported_clause, "LRAT CHECKER checking clause with resolution");
        #[cfg(debug_assertions)]
        for &b in &self.checked_lits {
            debug_assert!(b == 0); // = false;
        }
        if proof_chain.is_empty() || *proof_chain.last().unwrap() < 0 {
            return false;
        }
        let mut c = {
            let p = self.find(*proof_chain.last().unwrap());
            // SAFETY: 'p' points to a valid slot.
            unsafe { *p }
        };
        debug_assert!(!c.is_null());
        for &lit in lrat_clause_lits(c) {
            *self.checked_lit(lit) = 1;
            debug_assert!(*self.checked_lit(-lit) == 0);
        }
        let mut p = proof_chain.len() as isize - 2;
        while p >= 0 {
            let id = proof_chain[p as usize];
            c = {
                let q = self.find(id);
                // SAFETY: 'q' points to a valid slot.
                unsafe { *q }
            };
            debug_assert!(!c.is_null()); // since this is checked in check already
            for &lit in lrat_clause_lits(c) {
                if *self.checked_lit(-lit) == 0 {
                    *self.checked_lit(lit) = 1;
                } else {
                    *self.checked_lit(-lit) = 0;
                }
            }
            p -= 1;
        }
        for k in 0..self.imported_clause.len() {
            let lit = self.imported_clause[k];
            if *self.checked_lit(-lit) != 0 {
                log!(
                    self.internal,
                    "LRAT CHECKER resolution failed, resolved literal {} in learned clause",
                    lit
                );
                for b in self.checked_lits.iter_mut() {
                    *b = 0; // clearing checking bits
                }
                return false;
            }
            if *self.checked_lit(lit) == 0 {
                // learned clause is subsumed by resolvents
                *self.checked_lit(lit) = 1;
            }
            *self.checked_lit(-lit) = 1;
        }
        let mut failed = false;
        let mut lit: i64 = 1;
        while lit < self.size_vars {
            let l = lit as i32;
            let mut ok = *self.checked_lit(l) != 0 && *self.checked_lit(-l) != 0;
            ok = ok || (*self.checked_lit(l) == 0 && *self.checked_lit(-l) == 0);
            *self.checked_lit(-l) = 0;
            *self.checked_lit(l) = 0;
            if !ok && !failed {
                log!(
                    self.internal,
                    "LRAT CHECKER resolution failed, learned clause does not match on variable {}",
                    lit
                );
                failed = true;
            }
            lit += 1;
        }

        !failed
    }

    /*----------------------------------------------------------------------*/

    pub fn check(&mut self, proof_chain: Vec<i64>) -> bool {
        log!(self.internal, &self.imported_clause, "LRAT CHECKER checking clause");
        self.stats.checks += 1;
        #[cfg(debug_assertions)]
        for &b in &self.checked_lits {
            debug_assert!(b == 0); // = false;
        }
        let mut taut = false;
        for k in 0..self.imported_clause.len() {
            // tautological clauses
            let lit = self.imported_clause[k];
            *self.checked_lit(-lit) = 1;
            if *self.checked_lit(lit) != 0 {
                log!(self.internal, &self.imported_clause, "LRAT CHECKER clause tautological");
                debug_assert!(proof_chain.is_empty()); // would be unnecessary hence a bug
                taut = true;
            }
        }
        // we assume that we can have RUP and ER clauses. One side of the ER
        // clauses are pure, i.e. without any chain, the long clause is
        // blocked, so the chain consists only of negative ids. Therefore
        // these checks are enough to distiguish between RUP and ER
        if taut || proof_chain.is_empty() || *proof_chain.last().unwrap() < 0 {
            for k in 0..self.imported_clause.len() {
                // tautological clauses
                let lit = self.imported_clause[k];
                *self.checked_lit(-lit) = 0;
            }
            return taut;
        }

        let mut used_clauses: Vec<*mut LratCheckerClause> = Vec::new();
        let mut checking = false;
        for &id in &proof_chain {
            let c = {
                let p = self.find(id);
                // SAFETY: 'p' points to a valid slot.
                unsafe { *p }
            };
            if c.is_null() {
                log!(
                    self.internal,
                    "LRAT CHECKER LRAT failed. Did not find clause with id {}",
                    id as u64
                );
                break;
            }
            // SAFETY: 'c' is a live clause.
            if unsafe { (*c).tautological } {
                log!(self.internal, "LRAT CHECKER LRAT failed. Clause with id {} is tautological", id);
                break;
            }
            used_clauses.push(c);
            // SAFETY: 'c' is a live clause.
            if unsafe { (*c).used } {
                log!(self.internal, "LRAT CHECKER LRAT failed. Id {} was used multiple times", id);
                break;
            } else {
                // SAFETY: 'c' is a live clause.
                unsafe { (*c).used = true };
            }
            let mut unit = 0i32;
            for &lit in lrat_clause_lits(c) {
                if *self.checked_lit(-lit) != 0 {
                    continue;
                }
                if unit != 0 && unit != lit {
                    unit = i32::MIN; // multiple unfalsified literals
                    break;
                }
                unit = lit; // potential unit
            }
            if unit == i32::MIN {
                log!(self.internal, "LRAT CHECKER check failed, found non unit clause {}", id);
                break;
            }
            if unit == 0 {
                log!(self.internal, "LRAT CHECKER check succeded, clause falsified {}", id);
                checking = true;
                break;
            }
            // LOG ("LRAT CHECKER found unit clause %" PRIu64 ", assign %d", id,
            // unit);
            *self.checked_lit(unit) = 1;
        }
        for &lc in &used_clauses {
            // SAFETY: used clauses are alive.
            unsafe { (*lc).used = false };
        }
        for b in self.checked_lits.iter_mut() {
            *b = 0;
        }
        if !checking {
            log!(self.internal, "LRAT CHECKER failed, no conflict found");
            return false; // check failed because no empty clause was found
        }
        true
    }

    pub fn check_blocked(&mut self, proof_chain: Vec<i64>) -> bool {
        for k in 0..self.imported_clause.len() {
            let lit = self.imported_clause[k];
            *self.checked_lit(-lit) = 1;
            *self.mark(-lit) = 1;
        }
        for i in 0..self.size_clauses as usize {
            let mut c = self.clauses[i];
            while !c.is_null() {
                // SAFETY: 'c' is a live clause of the hash table.
                let (next, garbage, cid) = unsafe { ((*c).next, (*c).garbage, (*c).id) };
                if garbage {
                    c = next;
                    continue;
                }
                // if c is part of the proof chain its id occurs negatively
                // there.
                if proof_chain.contains(&-cid) {
                    // clause needs to be blocked
                    let mut count = 0u32;
                    let mut candidates: Vec<i32> = Vec::new();
                    for &lit in lrat_clause_lits(c) {
                        if *self.checked_lit(lit) != 0 {
                            count += 1;
                        }
                        if *self.mark(lit) != 0 {
                            candidates.push(lit);
                        }
                    }
                    if count < 2 {
                        // check failed
                        for k in 0..self.imported_clause.len() {
                            let lit = self.imported_clause[k];
                            *self.checked_lit(-lit) = 0;
                            *self.mark(-lit) = 0;
                        }
                        return false;
                    } else {
                        // all literals outside of candidates are not valid
                        // RAT candidates
                        for k in 0..self.imported_clause.len() {
                            let lit = self.imported_clause[k];
                            if *self.mark(-lit) != 0 && !candidates.contains(&-lit) {
                                *self.mark(-lit) = 0;
                            }
                        }
                    }
                } else {
                    // any literal contained in the clause is not a valid RAT
                    // candidate
                    for &lit in lrat_clause_lits(c) {
                        if *self.checked_lit(lit) != 0 {
                            *self.mark(lit) = 0;
                        }
                    }
                }
                c = next;
            }
        }
        let mut success = false;
        for k in 0..self.imported_clause.len() {
            let lit = self.imported_clause[k];
            if *self.mark(-lit) != 0 {
                success = true;
            }
            *self.mark(-lit) = 0;
            *self.checked_lit(-lit) = 0;
        }
        success
    }

    /*----------------------------------------------------------------------*/

    pub fn restore_clause(&mut self, id: i64, c: &[i32]) {
        log!(self.internal, c, "LRAT CHECKER check of restoration of clause[{}]", id);
        if !self.clauses_to_reconstruct.contains_key(&id) {
            fatal_with_clause("restoring clauses not deleted previously:\n", c);
        }
        let mut e: Vec<i32> = c.to_vec();
        crate::sort::std_sort_default_arith(&mut e);
        let d = &self.clauses_to_reconstruct[&id];
        let mut eq = true;
        if c.len() != d.len() {
            eq = false;
        }

        let mut i = 0usize;
        while i < e.len() && eq {
            eq = e[i] == d[i];
            i += 1;
        }

        if !eq {
            fatal_message_start();
            fputs("restoring clause that is different than the one imported:\n", c_stderr());
            for &lit in c {
                cfprintf!(c_stderr(), "{} ", lit);
            }
            fputc(b'0' as i32, c_stderr());
            fputs("vs:\n", c_stderr());
            for &lit in d {
                cfprintf!(c_stderr(), "{} ", lit);
            }
            fputc(b'0' as i32, c_stderr());
            fatal_message_end();
        }

        self.clauses_to_reconstruct.remove(&id);
    }

    pub fn dump(&mut self) {
        let mut max_var = 0i32;
        for i in 0..self.size_clauses as usize {
            let mut c = self.clauses[i];
            while !c.is_null() {
                for &lit in lrat_clause_lits(c) {
                    if lit.abs() > max_var {
                        max_var = lit.abs();
                    }
                }
                // SAFETY: 'c' is a live clause.
                c = unsafe { (*c).next };
            }
        }
        cprintf!("p cnf {} {}\n", max_var, self.num_clauses);
        for i in 0..self.size_clauses as usize {
            let mut c = self.clauses[i];
            while !c.is_null() {
                for &lit in lrat_clause_lits(c) {
                    cprintf!("{} ", lit);
                }
                cprintf!("0\n");
                // SAFETY: 'c' is a live clause.
                c = unsafe { (*c).next };
            }
        }
    }
}

/*------------------------------------------------------------------------*/

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::proof::tests::{child_stdout, expect_fatal};

    fn with_checker(f: impl FnOnce(&mut LratChecker)) {
        let mut internal = Internal::new();
        let ip: *mut Internal = &mut *internal;
        let mut k = LratChecker::new(ip);
        f(&mut k);
        drop(k);
    }

    const PHP: [&[i32]; 9] =
        [&[1, 2], &[3, 4], &[5, 6], &[-1, -3], &[-1, -5], &[-3, -5], &[-2, -4], &[-2, -6], &[-4, -6]];

    /// Same as 'l-valid' in the C++ driver (checkdriver.cpp).
    pub(crate) fn valid_case(k: &mut LratChecker) {
        k.begin_proof(0);
        for (i, c) in PHP.iter().enumerate() {
            k.add_original_clause(i as i64 + 1, false, c, false);
        }
        k.add_derived_clause(10, false, 0, &[-1], &[4, 5, 2, 3, 9]);
        k.add_derived_clause(11, false, 0, &[-3], &[4, 6, 1, 3, 8]);
        k.add_derived_clause(12, false, 0, &[], &[10, 11, 1, 2, 7]);
        for id in [4i64, 5, 6, 7, 8, 9, 10, 11] {
            let c: &[i32] = if id <= 9 {
                PHP[id as usize - 1]
            } else if id == 10 {
                &[-1]
            } else {
                &[-3]
            };
            Tracer::delete_clause(k, id, false, c);
        }
        k.weaken_minus(1, &[2, 1]);
        Tracer::delete_clause(k, 1, false, &[1, 2]);
        k.add_original_clause(1, false, &[2, 1], true);
        k.finalize_clause(1, &[1, 2]);
        k.finalize_clause(2, &[3, 4]);
        k.finalize_clause(3, &[6, 5]);
        k.finalize_clause(12, &[]);
        k.report_status(20, 12);
        k.conclude_unsat(ConclusionType::CONFLICT, &[12]);
    }

    /// Same as 'l-assume' in the C++ driver.
    pub(crate) fn assume_case(k: &mut LratChecker) {
        k.begin_proof(0);
        k.add_original_clause(1, false, &[1, 2], false);
        k.add_original_clause(2, false, &[-1, 2], false);
        k.add_assumption(-2);
        k.add_assumption_clause(3, &[2], &[1, 2]);
        k.conclude_unsat(ConclusionType::ASSUMPTIONS, &[3]);
        k.reset_assumptions();
        k.add_constraint(&[-2, 3, -2]);
        k.add_assumption(-3);
        k.add_derived_clause(4, false, 0, &[2], &[1, 2]);
        k.add_assumption_clause(5, &[2], &[4]);
        k.add_original_clause(6, false, &[-3], false);
        k.add_assumption_clause(7, &[-3], &[6]);
        k.conclude_unsat(ConclusionType::CONSTRAINT, &[5, 7]);
    }

    #[test]
    fn lrat_checker_valid_statistics_match_cpp() {
        with_checker(|k| {
            valid_case(k);
            let s = k.stats;
            assert_eq!(s.checks, 3);
            assert_eq!(s.insertions, 13);
            assert_eq!(s.original, 10);
            assert_eq!(s.derived, 3);
            assert_eq!(s.rat, 0);
            assert_eq!(s.deleted, 9);
            assert_eq!(s.finalized, 4);
            assert_eq!(s.collections, 1);
            assert_eq!(s.collisions, 15);
            assert_eq!(s.searches, 56);
        });
        with_checker(|k| {
            assume_case(k);
            let s = k.stats;
            assert_eq!(s.checks, 4);
            assert_eq!(s.insertions, 7);
            assert_eq!(s.original, 3);
            assert_eq!(s.derived, 4);
            assert_eq!(s.deleted, 3);
            assert_eq!(s.finalized, 0);
            assert_eq!(s.collections, 0);
            assert_eq!(s.collisions, 8);
            assert_eq!(s.searches, 21);
        });
    }

    #[test]
    fn lrat_checker_print_stats_matches_cpp() {
        let out = child_stdout("lratchecker::tests::lrat_checker_print_stats_matches_cpp", || {
            with_checker(|k| {
                valid_case(k);
                k.print_stats();
            });
        });
        let expected = "\
c --- [ lrat checker statistics ] --------------------------------------------
c 
c checks:                        3
c insertions:                   13       100.00 %  of all clauses
c original:                     10        76.92 %  of all clauses
c derived:                       3        23.08 %  of all clauses
c rat:                       0         0.00 %  of derived clauses
c deleted:                       9        69.23 %  of all clauses
c finalized:                     4        30.77 %  of all clauses
c collections:                   1         0.11    deleted per collection
c collisions:                   15         0.27    per search
c searches:                     56
";
        assert!(out.contains(expected), "got:\n{}", out);
    }

    #[test]
    fn lrat_checker_accepts_blocked_clause() {
        with_checker(|k| {
            k.add_original_clause(1, false, &[1, 2], false);
            // Blocked on '3' (ER definition '3 = -1'), empty chain.
            k.add_derived_clause(2, false, 0, &[3, 1], &[]);
            // The other side, with the negative id of the blocking clause.
            k.add_derived_clause(3, false, 0, &[-3, -1], &[-2]);
            assert_eq!(k.num_clauses, 3);
        });
    }

    fn fatal(name: &str, expected: &str, case: impl FnOnce(&mut LratChecker)) {
        let test = format!("lratchecker::tests::{}", name);
        expect_fatal(&test, expected, || with_checker(case));
    }

    #[test]
    fn lrat_fatal_derive() {
        fatal("lrat_fatal_derive", "failed to check derived clause:\n2 4 0", |k| {
            k.add_original_clause(1, false, &[1, 2], false);
            k.add_original_clause(2, false, &[-1, 3], false);
            k.add_original_clause(3, false, &[-2, -4], false);
            k.add_derived_clause(4, false, 0, &[2, 4], &[1, 2]);
        });
    }

    #[test]
    fn lrat_fatal_duplicate_original() {
        fatal("lrat_fatal_duplicate_original", "different clause with id 1 already present\n", |k| {
            k.add_original_clause(1, false, &[1, 2], false);
            k.add_original_clause(1, false, &[1, 3], false);
        });
    }

    #[test]
    fn lrat_fatal_duplicate_derived() {
        fatal("lrat_fatal_duplicate_derived", "different clause with id 1 already present\n", |k| {
            k.add_original_clause(1, false, &[1, 2], false);
            k.add_original_clause(2, false, &[-1, 2], false);
            k.begin_proof(0);
            k.add_derived_clause(1, false, 0, &[2], &[1, 2]);
        });
    }

    #[test]
    fn lrat_fatal_not_finalized() {
        fatal("lrat_fatal_not_finalized", "finalize check failed 2 are not finalized", |k| {
            k.add_original_clause(1, false, &[1, 2], false);
            k.add_original_clause(2, false, &[-1, 2], false);
            k.finalize_clause(1, &[2, 1]);
            k.report_status(10, 0);
        });
    }

    #[test]
    fn lrat_fatal_finalize_missing() {
        fatal("lrat_fatal_finalize_missing", "deleted clause not in proof:\n2 -1 0", |k| {
            k.add_original_clause(1, false, &[1, 2], false);
            k.add_original_clause(2, false, &[-1, 2], false);
            Tracer::delete_clause(k, 2, false, &[-1, 2]);
            k.finalize_clause(2, &[2, -1]);
        });
    }

    #[test]
    fn lrat_fatal_delete_missing() {
        fatal("lrat_fatal_delete_missing", "deleted clause not in proof:\n2 -1 0", |k| {
            k.add_original_clause(1, false, &[1, 2], false);
            Tracer::delete_clause(k, 2, false, &[2, -1]);
        });
    }

    #[test]
    fn lrat_fatal_delete_different() {
        fatal("lrat_fatal_delete_different", "deleted clause not in proof:\n2 -1 0", |k| {
            k.add_original_clause(1, false, &[1, 2], false);
            Tracer::delete_clause(k, 1, false, &[2, -1]);
        });
    }

    #[test]
    fn lrat_fatal_weaken_missing() {
        fatal("lrat_fatal_weaken_missing", "weakened clause not in proof:\n2 -1 0", |k| {
            k.add_original_clause(1, false, &[1, 2], false);
            k.add_original_clause(2, false, &[-1, 2], false);
            Tracer::delete_clause(k, 2, false, &[-1, 2]);
            k.weaken_minus(2, &[2, -1]);
        });
    }

    #[test]
    fn lrat_fatal_restore_missing() {
        fatal("lrat_fatal_restore_missing", "restoring clauses not deleted previously:\n2 1 0", |k| {
            k.add_original_clause(1, false, &[1, 2], false);
            k.add_original_clause(2, false, &[2, 1], true);
        });
    }

    #[test]
    fn lrat_fatal_restore_different() {
        fatal(
            "lrat_fatal_restore_different",
            "restoring clause that is different than the one imported:\n3 1 0vs:\n1 2 0",
            |k| {
                k.add_original_clause(1, false, &[1, 2], false);
                k.weaken_minus(1, &[2, 1]);
                Tracer::delete_clause(k, 1, false, &[1, 2]);
                k.add_original_clause(1, false, &[3, 1], true);
            },
        );
    }

    #[test]
    fn lrat_fatal_concluded_twice() {
        fatal("lrat_fatal_concluded_twice", "already concluded\n", |k| {
            k.add_original_clause(1, false, &[1], false);
            k.add_original_clause(2, false, &[-1], false);
            k.add_derived_clause(3, false, 0, &[], &[1, 2]);
            k.conclude_unsat(ConclusionType::CONFLICT, &[3]);
            k.conclude_unsat(ConclusionType::CONFLICT, &[3]);
        });
    }

    #[test]
    fn lrat_fatal_empty_missing() {
        fatal("lrat_fatal_empty_missing", "empty clause not in proof\n", |k| {
            k.add_original_clause(1, false, &[1], false);
            k.conclude_unsat(ConclusionType::CONFLICT, &[1]);
        });
    }

    #[test]
    fn lrat_fatal_assumption_literals() {
        fatal("lrat_fatal_assumption_literals", "clause contains non assumptions or constraint literals\n", |k| {
            k.add_original_clause(1, false, &[1, 2], false);
            k.add_assumption(-1);
            k.add_assumption_clause(2, &[1, 2], &[1]);
        });
    }

    #[test]
    fn lrat_fatal_assumption_count() {
        fatal("lrat_fatal_assumption_count", "expected exactly one assumption clause\n", |k| {
            k.add_original_clause(1, false, &[1], false);
            k.add_assumption(-1);
            k.add_assumption_clause(2, &[1], &[1]);
            k.conclude_unsat(ConclusionType::ASSUMPTIONS, &[2, 2]);
        });
    }

    #[test]
    fn lrat_fatal_assumption_wrong() {
        fatal("lrat_fatal_assumption_wrong", "conclusion is not an assumption clause\n", |k| {
            k.add_original_clause(1, false, &[1], false);
            k.add_assumption(-1);
            k.add_assumption_clause(2, &[1], &[1]);
            k.conclude_unsat(ConclusionType::ASSUMPTIONS, &[1]);
        });
    }

    #[test]
    fn lrat_fatal_constraint_size() {
        fatal(
            "lrat_fatal_constraint_size",
            "not complete conclusion given for constraint\nThe constraint contains the literals: -1 2 \nThe ids are: 2 ",
            |k| {
                k.add_original_clause(1, false, &[1], false);
                k.add_constraint(&[-1, 2]);
                k.add_assumption_clause(2, &[1], &[1]);
                k.conclude_unsat(ConclusionType::CONSTRAINT, &[2]);
            },
        );
    }

    #[test]
    fn lrat_fatal_constraint_missing() {
        fatal("lrat_fatal_constraint_missing", "assumption clause for constraint missing\n", |k| {
            k.add_original_clause(1, false, &[1], false);
            k.add_constraint(&[-1]);
            k.add_assumption_clause(2, &[1], &[1]);
            k.conclude_unsat(ConclusionType::CONSTRAINT, &[1]);
        });
    }
}

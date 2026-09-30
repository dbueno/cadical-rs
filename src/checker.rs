//! Port of `checker.hpp` and `checker.cpp`: the online DRAT proof checker.

use crate::internal::Internal;
use crate::tracer::{InternalTracer, StatTracer, Tracer};

/// Clauses of the checker (allocated with variadic size as in C++).
#[repr(C)]
pub struct CheckerClause {
    /// Collision chain link for hash table.
    pub next: *mut CheckerClause,
    /// Previously computed full 64-bit hash.
    pub hash: u64,
    /// Zero if this is a garbage clause.
    pub size: u32,
    /// Otherwise 'literals' of length 'size'.
    pub literals: [i32; 2],
}

#[derive(Clone, Copy, Debug)]
pub struct CheckerWatch {
    pub blit: i32,
    pub size: u32,
    pub clause: *mut CheckerClause,
}

impl CheckerWatch {
    pub fn new(b: i32, c: *mut CheckerClause) -> CheckerWatch {
        // SAFETY: 'c' is a live checker clause.
        CheckerWatch { blit: b, size: unsafe { (*c).size }, clause: c }
    }
}

impl Default for CheckerWatch {
    fn default() -> Self {
        CheckerWatch { blit: 0, size: 0, clause: std::ptr::null_mut() }
    }
}

pub type CheckerWatcher = Vec<CheckerWatch>;

#[derive(Clone, Copy, Debug, Default)]
pub struct CheckerStats {
    /// Number of added clauses.
    pub added: i64,
    /// Number of added original clauses.
    pub original: i64,
    /// Number of added derived clauses.
    pub derived: i64,
    /// Number of deleted clauses.
    pub deleted: i64,
    /// Number of assumed literals.
    pub assumptions: i64,
    /// Number of propagated literals.
    pub propagations: i64,
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
    pub units: i64,
}

pub const CHECKER_NUM_NONCES: usize = 4;

pub struct Checker {
    pub internal: *mut Internal,

    /// Number of variables.
    pub size_vars: i64,
    /// Assignment `[-size_vars,size_vars]` (C++ `signed char *vals`
    /// shifted by `size_vars`; index with `lit + size_vars`).
    pub vals: Vec<i8>,

    /// Watchers of literals.
    pub watchers: Vec<CheckerWatcher>,
    /// Mark bits of literals.
    pub marks: Vec<i8>,

    /// Found or added empty clause.
    pub inconsistent: bool,

    /// Number of clauses in hash table.
    pub num_clauses: u64,
    /// Number of garbage clauses.
    pub num_garbage: u64,
    /// Size of clause hash table.
    pub size_clauses: u64,
    /// Hash table of clauses.
    pub clauses: Vec<*mut CheckerClause>,
    /// Linked list of garbage clauses.
    pub garbage: *mut CheckerClause,

    /// Original clause for reporting.
    pub unsimplified: Vec<i32>,
    /// Clause for sorting.
    pub simplified: Vec<i32>,

    /// For propagation.
    pub trail: Vec<i32>,

    /// Next to propagate on trail.
    pub next_to_propagate: u32,

    /// Random numbers for hashing.
    pub nonces: [u64; CHECKER_NUM_NONCES],
    /// Last computed hash value of clause.
    pub last_hash: u64,
    pub last_id: i64,

    pub stats: CheckerStats,
}

/*------------------------------------------------------------------------*/

#[allow(unused_imports)]
use crate::prelude::*;

use crate::message::{c_stderr, c_stdout, fatal_message_end, fatal_message_start, fputc, fputs};

/// Pointer to the literals of a checker clause (variadic array).
#[inline(always)]
fn checker_lits(c: *mut CheckerClause) -> *mut i32 {
    // SAFETY: only computes the address of the 'literals' field.
    unsafe { std::ptr::addr_of_mut!((*c).literals) as *mut i32 }
}

/// Literals of a checker clause as slice (for logging and dumping).
#[inline(always)]
#[allow(dead_code)]
fn checker_clause_lits<'a>(c: *mut CheckerClause) -> &'a [i32] {
    // SAFETY: 'c' is a live clause with 'size' literals.
    unsafe { std::slice::from_raw_parts(checker_lits(c), (*c).size as usize) }
}

/// `LOG (literals, size, fmt, ...)` (the `(const int *, unsigned)`
/// overload of the logger).
macro_rules! log_int_array {
    ($internal:expr, $lits:expr, $fmt:literal $(, $arg:expr)* $(,)?) => {
        #[cfg(feature = "logging")]
        {
            // SAFETY: back pointer to the owning 'Internal'.
            let __internal: &Internal = unsafe { &*$internal };
            if __internal.opts.log != 0 {
                $crate::logging::Logger::log_int_array(__internal, $lits, format_args!($fmt $(, $arg)*));
            }
        }
    };
}

impl Tracer for Checker {
    fn add_original_clause(&mut self, id: i64, _redundant: bool, c: &[i32], _restored: bool) {
        if self.inconsistent {
            return;
        }
        // SAFETY: back pointer to the owning 'Internal'.
        let internal = unsafe { &mut *self.internal };
        start!(internal, checking);
        log!(self.internal, c, "CHECKER addition of original clause");
        self.stats.added += 1;
        self.stats.original += 1;
        self.import_clause(c);
        self.last_id = id;
        if self.tautological() {
            log!(self.internal, "CHECKER ignoring satisfied original clause");
        } else {
            self.add_clause("original");
        }
        self.simplified.clear();
        self.unsimplified.clear();
        // SAFETY: see above.
        let internal = unsafe { &mut *self.internal };
        stop!(internal, checking);
    }

    fn add_derived_clause(&mut self, id: i64, _redundant: bool, _witness: i32, c: &[i32], _chain: &[i64]) {
        if self.inconsistent {
            return;
        }
        // SAFETY: back pointer to the owning 'Internal'.
        let internal = unsafe { &mut *self.internal };
        start!(internal, checking);
        log!(self.internal, c, "CHECKER addition of derived clause");
        self.stats.added += 1;
        self.stats.derived += 1;
        self.import_clause(c);
        self.last_id = id;
        if self.tautological() {
            log!(self.internal, "CHECKER ignoring satisfied derived clause");
        } else if !self.check() && !self.check_blocked() {
            // needed for ER proof support
            fatal_message_start();
            fputs("failed to check derived clause:\n", c_stderr());
            for &lit in &self.unsimplified {
                cfprintf!(c_stderr(), "{} ", lit);
            }
            fputc(b'0' as i32, c_stderr());
            fatal_message_end();
        } else {
            self.add_clause("derived");
        }
        self.simplified.clear();
        self.unsimplified.clear();
        // SAFETY: see above.
        let internal = unsafe { &mut *self.internal };
        stop!(internal, checking);
    }

    fn delete_clause(&mut self, id: i64, _redundant: bool, c: &[i32]) {
        if self.inconsistent {
            return;
        }
        // SAFETY: back pointer to the owning 'Internal'.
        let internal = unsafe { &mut *self.internal };
        start!(internal, checking);
        log!(self.internal, c, "CHECKER checking deletion of clause");
        self.stats.deleted += 1;
        self.simplified.clear(); // Can be non-empty if clause allocation fails.
        self.unsimplified.clear(); // Can be non-empty if clause allocation fails.
        self.import_clause(c);
        self.last_id = id;
        if !self.tautological() {
            let p = self.find();
            // SAFETY: 'p' points to a slot of the hash table or to the
            // 'next' field of a live clause.
            unsafe {
                let d = *p;
                if !d.is_null() {
                    debug_assert!((*d).size > 1);
                    // Remove from hash table, mark as garbage, connect to
                    // garbage list.
                    self.num_garbage += 1;
                    debug_assert!(self.num_clauses != 0);
                    self.num_clauses -= 1;
                    *p = (*d).next;
                    (*d).next = self.garbage;
                    self.garbage = d;
                    (*d).size = 0;
                } else {
                    fatal_message_start();
                    fputs("deleted clause not in proof:\n", c_stderr());
                    for &lit in &self.unsimplified {
                        cfprintf!(c_stderr(), "{} ", lit);
                    }
                    fputc(b'0' as i32, c_stderr());
                    fatal_message_end();
                }
            }
        }
        self.simplified.clear();
        self.unsimplified.clear();
        // SAFETY: see above.
        let internal = unsafe { &mut *self.internal };
        stop!(internal, checking);
    }

    fn finalize_clause(&mut self, _id: i64, _clause: &[i32]) {} // skip
    fn report_status(&mut self, _status: i32, _id: i64) {} // skip
    fn begin_proof(&mut self, _reserved_ids: i64) {} // skip

    fn add_assumption_clause(&mut self, id: i64, c: &[i32], chain: &[i64]) {
        self.add_derived_clause(id, true, 0, c, chain);
        Tracer::delete_clause(self, id, true, c);
    }
}

impl InternalTracer for Checker {
    fn connect_internal(&mut self, i: *mut Internal) {
        self.internal = i;
        log!(self.internal, "CHECKER connected to internal");
    }
}

impl StatTracer for Checker {
    /// `Checker::print_stats` (from 'stats.cpp').
    fn print_stats(&mut self) {
        if self.stats.added == 0 && self.stats.deleted == 0 {
            return;
        }

        // SAFETY: back pointer to the owning 'Internal'.
        let internal = unsafe { &mut *self.internal };
        section!(internal, "checker statistics");

        let s = self.stats;
        let i = self.internal;
        msg!(i, "checks:          {:15}", s.checks);
        msg!(
            i,
            "assumptions:     {:15}   {:10.2}    per check",
            s.assumptions,
            relative(s.assumptions as f64, s.checks as f64)
        );
        msg!(
            i,
            "propagations:    {:15}   {:10.2}    per check",
            s.propagations,
            relative(s.propagations as f64, s.checks as f64)
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
            "deleted:         {:15}   {:10.2} %  of all clauses",
            s.deleted,
            percent(s.deleted as f64, s.added as f64)
        );
        msg!(
            i,
            "insertions:      {:15}   {:10.2} %  of all clauses",
            s.insertions,
            percent(s.insertions as f64, s.added as f64)
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
        msg!(i, "units:           {:15}", s.units);
    }
}

impl Checker {
    pub fn new(internal: *mut Internal) -> Checker {
        let mut nonces = [0u64; CHECKER_NUM_NONCES];
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
        Checker {
            internal,
            size_vars: 0,
            vals: Vec::new(),
            watchers: Vec::new(),
            marks: Vec::new(),
            inconsistent: false,
            num_clauses: 0,
            num_garbage: 0,
            size_clauses: 0,
            clauses: Vec::new(),
            garbage: std::ptr::null_mut(),
            unsimplified: Vec::new(),
            simplified: Vec::new(),
            trail: Vec::new(),
            next_to_propagate: 0,
            nonces,
            last_hash: 0,
            last_id: 0,
            stats: CheckerStats::default(), // Initialize statistics.
        }
    }
}

impl Drop for Checker {
    fn drop(&mut self) {
        log!(self.internal, "CHECKER delete");
        // 'vals' is released with the vector.
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

impl Checker {
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

    #[inline]
    pub fn val(&mut self, lit: i32) -> i8 {
        debug_assert!(lit != 0);
        debug_assert!(lit != i32::MIN);
        debug_assert!((lit.abs() as i64) < self.size_vars);
        debug_assert!(self.vals[(lit as i64 + self.size_vars) as usize] == -self.vals[(-lit as i64 + self.size_vars) as usize]);
        self.vals[(lit as i64 + self.size_vars) as usize]
    }

    /// `vals[lit] = v`.
    #[inline]
    fn set_val(&mut self, lit: i32, v: i8) {
        let idx = (lit as i64 + self.size_vars) as usize;
        self.vals[idx] = v;
    }

    pub fn mark(&mut self, lit: i32) -> &mut i8 {
        let u = Self::l2u(lit) as usize;
        debug_assert!(u < self.marks.len());
        &mut self.marks[u]
    }

    #[inline]
    pub fn watcher(&mut self, lit: i32) -> &mut CheckerWatcher {
        let u = Self::l2u(lit) as usize;
        debug_assert!(u < self.watchers.len());
        &mut self.watchers[u]
    }

    /*----------------------------------------------------------------------*/

    pub fn new_clause(&mut self) -> *mut CheckerClause {
        let size = self.simplified.len();
        debug_assert!(size > 1);
        debug_assert!(size <= u32::MAX as usize);
        let bytes = std::mem::size_of::<CheckerClause>() + (size - 2) * std::mem::size_of::<i32>();
        // SAFETY: allocation of a variadic clause, initialized below.
        let res = unsafe { libc::malloc(bytes) as *mut CheckerClause };
        if res.is_null() {
            std::alloc::handle_alloc_error(std::alloc::Layout::from_size_align(bytes, 8).unwrap());
        }
        // SAFETY: 'res' points to 'bytes' writable bytes.
        unsafe {
            (*res).next = std::ptr::null_mut();
            (*res).hash = self.last_hash;
            (*res).size = size as u32;
        }
        let literals = checker_lits(res);
        for (k, &lit) in self.simplified.iter().enumerate() {
            // SAFETY: 'k < size'.
            unsafe { *literals.add(k) = lit };
        }
        self.num_clauses += 1;

        // First two literals are used as watches and should not be false.
        for i in 0..2usize {
            // SAFETY: indices below 'size'.
            let lit = unsafe { *literals.add(i) };
            if self.val(lit) == 0 {
                continue;
            }
            for j in i + 1..size {
                // SAFETY: indices below 'size'.
                let other = unsafe { *literals.add(j) };
                if self.val(other) != 0 {
                    continue;
                }
                // SAFETY: indices below 'size'.
                unsafe { std::ptr::swap(literals.add(i), literals.add(j)) };
                break;
            }
        }
        // SAFETY: 'size > 1'.
        let (l0, l1) = unsafe { (*literals, *literals.add(1)) };
        debug_assert!(self.val(l0) == 0);
        debug_assert!(self.val(l1) == 0);
        self.watcher(l0).push(CheckerWatch::new(l1, res));
        self.watcher(l1).push(CheckerWatch::new(l0, res));

        res
    }

    /// C++ overload `Checker::delete_clause` (renamed).
    pub fn deallocate_clause(&mut self, c: *mut CheckerClause) {
        // SAFETY: 'c' is a live clause allocated in 'new_clause'.
        unsafe {
            if (*c).size != 0 {
                debug_assert!((*c).size > 1);
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
            "CHECKER enlarging clauses of checker from {} to {}",
            self.size_clauses,
            new_size_clauses
        );
        let mut new_clauses: Vec<*mut CheckerClause> = vec![std::ptr::null_mut(); new_size_clauses as usize];
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

    pub fn clause_satisfied(&mut self, c: *mut CheckerClause) -> bool {
        // SAFETY: 'c' is a live clause.
        let size = unsafe { (*c).size };
        let lits = checker_lits(c);
        for i in 0..size as usize {
            // SAFETY: 'i < size'.
            let lit = unsafe { *lits.add(i) };
            if self.val(lit) > 0 {
                return true;
            }
        }
        false
    }

    // The main reason why we have an explicit garbage collection phase is
    // that removing clauses from watcher lists eagerly might lead to an
    // accumulated quadratic algorithm.  Thus we delay removing garbage
    // clauses from watcher lists until garbage collection (even though we
    // remove garbage clauses on the fly during propagation too).  We also
    // remove satisfied clauses.
    //
    pub fn collect_garbage_clauses(&mut self) {
        self.stats.collections += 1;

        for i in 0..self.size_clauses as usize {
            let mut p: *mut *mut CheckerClause = &mut self.clauses[i];
            // SAFETY: 'p' points to a hash table slot or to the 'next'
            // field of a live clause; the hash table is not reallocated.
            unsafe {
                loop {
                    let c = *p;
                    if c.is_null() {
                        break;
                    }
                    if self.clause_satisfied(c) {
                        (*c).size = 0; // mark as garbage
                        *p = (*c).next;
                        (*c).next = self.garbage;
                        self.garbage = c;
                        self.num_garbage += 1;
                        debug_assert!(self.num_clauses != 0);
                        self.num_clauses -= 1;
                    } else {
                        p = &mut (*c).next;
                    }
                }
            }
        }

        log!(
            self.internal,
            "CHECKER collecting {} garbage clauses {:.0}%",
            self.num_garbage,
            percent(self.num_garbage as f64, self.num_clauses as f64)
        );

        let mut lit = -self.size_vars + 1;
        while lit < self.size_vars {
            if lit == 0 {
                lit += 1;
                continue;
            }
            let ws = self.watcher(lit as i32);
            let end = ws.len();
            let mut j = 0usize;
            for i in 0..end {
                let w = ws[i];
                // SAFETY: watched clauses are alive until collected below.
                if unsafe { (*w.clause).size } != 0 {
                    ws[j] = w;
                    j += 1;
                }
            }
            if j == end {
                lit += 1;
                continue;
            }
            if j == 0 {
                erase_vector(ws);
            } else {
                ws.truncate(j);
            }
            lit += 1;
        }

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

    // The simplicity for accessing 'vals' and 'watchers' directly through a
    // signed integer literal, comes with the price of slightly more complex
    // code in deleting and enlarging the checker data structures.

    pub fn enlarge_vars(&mut self, idx: i64) {
        debug_assert!(0 < idx);
        debug_assert!(idx <= i32::MAX as i64);

        let mut new_size_vars: i64 = if self.size_vars != 0 { 2 * self.size_vars } else { 2 };
        while idx >= new_size_vars {
            new_size_vars *= 2;
        }
        log!(
            self.internal,
            "CHECKER enlarging variables of checker from {} to {}",
            self.size_vars,
            new_size_vars
        );

        let mut new_vals: Vec<i8> = vec![0; 2 * new_size_vars as usize];
        if self.size_vars != 0 {
            let off = (new_size_vars - self.size_vars) as usize;
            let n = 2 * self.size_vars as usize;
            new_vals[off..off + n].copy_from_slice(&self.vals[..n]);
        }
        self.vals = new_vals;
        self.size_vars = new_size_vars;

        self.watchers.resize(2 * new_size_vars as usize, Vec::new());
        self.marks.resize(2 * new_size_vars as usize, 0);

        debug_assert!(idx < new_size_vars);
    }

    #[inline]
    pub fn import_literal(&mut self, lit: i32) {
        debug_assert!(lit != 0);
        debug_assert!(lit != i32::MIN);
        let idx = lit.abs();
        if idx as i64 >= self.size_vars {
            self.enlarge_vars(idx as i64);
        }
        self.simplified.push(lit);
        self.unsimplified.push(lit);
    }

    pub fn import_clause(&mut self, c: &[i32]) {
        for &lit in c {
            self.import_literal(lit);
        }
    }

    pub fn tautological(&mut self) -> bool {
        crate::sort::std_sort(&mut self.simplified, |&a: &i32, &b: &i32| {
            let c = a.abs();
            let d = b.abs();
            if c < d {
                return true;
            }
            if c > d {
                return false;
            }
            a < b
        });
        let end = self.simplified.len();
        let mut j = 0usize;
        let mut prev = 0i32;
        for i in 0..end {
            let lit = self.simplified[i];
            if lit == prev {
                continue; // duplicated literal
            }
            if lit == -prev {
                return true; // tautological clause
            }
            let tmp = self.val(lit);
            if tmp > 0 {
                return true; // satisfied literal and clause
            }
            prev = lit;
            self.simplified[j] = lit;
            j += 1;
        }
        self.simplified.truncate(j);
        false
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

    pub fn compute_hash(&mut self) -> u64 {
        let j = (self.last_id % CHECKER_NUM_NONCES as i64) as u32 as usize;
        let tmp = self.nonces[j].wrapping_mul(self.last_id as u64);
        self.last_hash = tmp;
        tmp
    }

    /// Returns the address of the hash table slot (as C++).
    pub fn find(&mut self) -> *mut *mut CheckerClause {
        self.stats.searches += 1;
        let hash = self.compute_hash();
        let size = self.simplified.len() as u32;
        let h = Self::reduce_hash(hash, self.size_clauses) as usize;
        for k in 0..self.simplified.len() {
            let lit = self.simplified[k];
            *self.mark(lit) = 1;
        }
        // SAFETY: 'h < size_clauses' and the chain consists of live clauses.
        let mut res: *mut *mut CheckerClause = unsafe { self.clauses.as_mut_ptr().add(h) };
        unsafe {
            loop {
                let c = *res;
                if c.is_null() {
                    break;
                }
                if (*c).hash == hash && (*c).size == size {
                    let mut found = true;
                    let literals = checker_lits(c);
                    let mut i = 0u32;
                    while found && i != size {
                        found = *self.mark(*literals.add(i as usize)) != 0;
                        i += 1;
                    }
                    if found {
                        break;
                    }
                }
                self.stats.collisions += 1;
                res = &mut (*c).next;
            }
        }
        for k in 0..self.simplified.len() {
            let lit = self.simplified[k];
            *self.mark(lit) = 0;
        }
        res
    }

    pub fn insert(&mut self) {
        self.stats.insertions += 1;
        if self.num_clauses == self.size_clauses {
            self.enlarge_clauses();
        }
        let hash = self.compute_hash();
        let h = Self::reduce_hash(hash, self.size_clauses) as usize;
        let c = self.new_clause();
        // SAFETY: 'c' is a fresh clause.
        unsafe { (*c).next = self.clauses[h] };
        self.clauses[h] = c;
    }

    /*----------------------------------------------------------------------*/

    #[inline]
    pub fn assign(&mut self, lit: i32) {
        debug_assert!(self.val(lit) == 0);
        self.set_val(lit, 1);
        self.set_val(-lit, -1);
        self.trail.push(lit);
    }

    #[inline]
    pub fn assume(&mut self, lit: i32) {
        let tmp = self.val(lit);
        if tmp > 0 {
            return;
        }
        debug_assert!(tmp == 0);
        self.stats.assumptions += 1;
        self.assign(lit);
    }

    pub fn backtrack(&mut self, previously_propagated: u32) {
        debug_assert!(previously_propagated as usize <= self.trail.len());

        while self.trail.len() > previously_propagated as usize {
            let lit = *self.trail.last().unwrap();
            debug_assert!(self.val(lit) > 0);
            debug_assert!(self.val(-lit) < 0);
            self.set_val(lit, 0);
            self.set_val(-lit, 0);
            self.trail.pop();
        }

        self.trail.truncate(previously_propagated as usize);
        self.next_to_propagate = previously_propagated;
        debug_assert!(self.trail.len() == self.next_to_propagate as usize);
    }

    /*----------------------------------------------------------------------*/

    // This is a standard propagation routine without using blocking
    // literals nor without saving the last replacement position.

    pub fn propagate(&mut self) -> bool {
        let mut res = true;
        while res && (self.next_to_propagate as usize) < self.trail.len() {
            let lit = self.trail[self.next_to_propagate as usize];
            self.next_to_propagate += 1;
            self.stats.propagations += 1;
            debug_assert!(self.val(lit) > 0);
            debug_assert!((lit.abs() as i64) < self.size_vars);
            let ws: *mut CheckerWatcher = self.watcher(-lit);
            // SAFETY: 'watchers' is not resized during propagation and the
            // only other watcher list modified below ('replacement') is a
            // different list (since 'replacement != -lit').
            unsafe {
                let ws: &mut CheckerWatcher = &mut *ws;
                let end = ws.len();
                let mut j = 0usize;
                let mut i = 0usize;
                while res && i != end {
                    let w = ws[i];
                    i += 1;
                    ws[j] = w;
                    j += 1;
                    let blit = w.blit;
                    debug_assert!(blit != -lit);
                    let blit_val = self.val(blit);
                    if blit_val > 0 {
                        continue;
                    }
                    let size = w.size;
                    if size == 2 {
                        // not precise since
                        if blit_val < 0 {
                            res = false; // clause might be garbage
                        } else {
                            self.assign(w.blit); // but still sound
                        }
                    } else {
                        debug_assert!(size > 2);
                        let c = w.clause;
                        if (*c).size == 0 {
                            j -= 1;
                            continue;
                        } // skip garbage clauses
                        debug_assert!(size == (*c).size);
                        let lits = checker_lits(c);
                        let other = *lits ^ *lits.add(1) ^ (-lit);
                        debug_assert!(other != -lit);
                        let other_val = self.val(other);
                        if other_val > 0 {
                            ws[j - 1].blit = other;
                            continue;
                        }
                        *lits = other;
                        *lits.add(1) = -lit;
                        let mut k = 2u32;
                        let mut replacement = 0i32;
                        let mut replacement_val: i8 = -1;
                        while k < size {
                            replacement = *lits.add(k as usize);
                            replacement_val = self.val(replacement);
                            if replacement_val >= 0 {
                                break;
                            }
                            k += 1;
                        }
                        if replacement_val >= 0 {
                            debug_assert!(replacement != -lit);
                            self.watcher(replacement).push(CheckerWatch::new(-lit, c));
                            std::ptr::swap(lits.add(1), lits.add(k as usize));
                            j -= 1;
                        } else if other_val == 0 {
                            self.assign(other);
                        } else {
                            res = false;
                        }
                    }
                }
                while i != end {
                    ws[j] = ws[i];
                    j += 1;
                    i += 1;
                }
                ws.truncate(j);
            }
        }
        res
    }

    pub fn check(&mut self) -> bool {
        self.stats.checks += 1;
        if self.inconsistent {
            return true;
        }
        let previously_propagated = self.next_to_propagate;
        for k in 0..self.simplified.len() {
            let lit = self.simplified[k];
            self.assume(-lit);
        }
        let res = !self.propagate();
        self.backtrack(previously_propagated);
        res
    }

    pub fn check_blocked(&mut self) -> bool {
        for k in 0..self.unsimplified.len() {
            let lit = self.unsimplified[k];
            *self.mark(-lit) = 1;
        }
        let mut not_blocked: Vec<i32> = Vec::new();
        for i in 0..self.size_clauses as usize {
            let mut c = self.clauses[i];
            while !c.is_null() {
                // SAFETY: 'c' is a live clause of the hash table.
                let (next, size) = unsafe { ((*c).next, (*c).size) };
                let lits = checker_lits(c);
                let mut count = 0u32;
                let mut first = 0i32;
                for k in 0..size as usize {
                    // SAFETY: 'k < size'.
                    let lit = unsafe { *lits.add(k) };
                    if self.val(lit) > 0 {
                        log_int_array!(self.internal, checker_clause_lits(c), "satisfied clause");
                        count = 2;
                        break;
                    }
                    if *self.mark(lit) != 0 {
                        count += 1;
                        log_int_array!(self.internal, checker_clause_lits(c), "clause");
                        first = lit;
                    }
                }
                if count == 1 {
                    not_blocked.push(first);
                }
                c = next;
            }
        }
        for &lit in &not_blocked {
            *self.mark(lit) = 0;
        }
        let mut blocked = false;
        for k in 0..self.unsimplified.len() {
            let lit = self.unsimplified[k];
            if *self.mark(-lit) != 0 {
                blocked = true;
            }
            *self.mark(-lit) = 0;
        }
        blocked
    }

    /*----------------------------------------------------------------------*/

    pub fn add_clause(&mut self, type_: &str) {
        let _ = type_;

        // If there are enough garbage clauses collect them first.
        if self.num_garbage as f64
            > 0.5 * std::cmp::max(self.size_clauses as usize, self.size_vars as usize) as f64
        {
            self.collect_garbage_clauses();
        }

        let mut unit = 0i32;
        for k in 0..self.simplified.len() {
            let lit = self.simplified[k];
            let tmp = self.val(lit);
            if tmp < 0 {
                continue;
            }
            debug_assert!(tmp == 0);
            if unit != 0 {
                unit = i32::MIN;
                break;
            }
            unit = lit;
        }

        if self.simplified.is_empty() {
            log!(self.internal, "CHECKER added empty {} clause", type_);
            self.inconsistent = true;
        }
        if unit == 0 {
            log!(self.internal, "CHECKER added and checked falsified {} clause", type_);
            self.inconsistent = true;
        } else if unit != i32::MIN {
            log!(self.internal, "CHECKER added and checked {} unit clause {}", type_, unit);
            self.assign(unit);
            self.stats.units += 1;
            if !self.propagate() {
                log!(self.internal, "CHECKER inconsistent after propagating {} unit", type_);
                self.inconsistent = true;
            }
        } else {
            self.insert();
        }
    }

    pub fn dump(&mut self) {
        let mut max_var = 0i32;
        for i in 0..self.size_clauses as usize {
            let mut c = self.clauses[i];
            while !c.is_null() {
                for &lit in checker_clause_lits(c) {
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
                for &lit in checker_clause_lits(c) {
                    cprintf!("{} ", lit);
                }
                cprintf!("0\n");
                // SAFETY: 'c' is a live clause.
                c = unsafe { (*c).next };
            }
        }
        let _ = c_stdout;
    }
}

/*------------------------------------------------------------------------*/

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::proof::tests::{child_stdout, expect_fatal};

    fn with_checker(f: impl FnOnce(&mut Checker)) {
        let mut internal = Internal::new();
        let ip: *mut Internal = &mut *internal;
        let mut k = Checker::new(ip);
        f(&mut k);
        drop(k);
    }

    /// Same as 'c-valid' in the C++ driver (checkdriver.cpp).
    pub(crate) fn valid_case(k: &mut Checker) {
        k.add_original_clause(1, false, &[1, 2, 3], false);
        k.add_original_clause(2, false, &[-1, 2, 3], false);
        k.add_original_clause(3, false, &[1, -2, 3], false);
        k.add_original_clause(4, false, &[-1, -2, 3], false);
        k.add_original_clause(5, false, &[1, 2, -3, 4], false);
        k.add_original_clause(6, false, &[-4, 5, 1], false);
        k.add_original_clause(7, false, &[-5, 6, 7, 8], false);
        k.add_original_clause(8, false, &[6, 6, -7], false); // duplicate literal
        k.add_original_clause(9, false, &[9, -9], false); // tautology
        k.add_derived_clause(10, true, 0, &[1, 2, 4], &[]);
        k.add_derived_clause(11, true, 0, &[2, 3], &[]);
        k.add_derived_clause(12, true, 0, &[3, 2, 3], &[]); // duplicate
        Tracer::delete_clause(k, 12, true, &[2, 3]);
        k.add_derived_clause(13, true, 0, &[4, -4], &[]); // tautology
        Tracer::delete_clause(k, 10, true, &[4, 2, 1]);
        k.add_assumption_clause(14, &[3, 1], &[]);
        for i in 0..20 {
            k.add_derived_clause(100 + i as i64, true, 0, &[10 + i, 1, 2, 3], &[]); // blocked
        }
        let mut i = 0;
        while i < 20 {
            Tracer::delete_clause(k, 100 + i as i64, true, &[3, 2, 1, 10 + i]);
            i += 2;
        }
        k.add_derived_clause(15, false, 0, &[3], &[]);
        k.add_derived_clause(16, false, 0, &[-1, 3, 5], &[]);
        k.add_derived_clause(17, false, 0, &[6, 7, 8, -5], &[]);
        for i in 0..100 {
            k.add_derived_clause(200 + i as i64, true, 0, &[40 + i % 10, -50 - i % 10, 60 + i / 10], &[]);
        }
        for i in 0..100 {
            Tracer::delete_clause(k, 200 + i as i64, true, &[60 + i / 10, 40 + i % 10, -50 - i % 10]);
        }
        Tracer::delete_clause(k, 7, false, &[-5, 6, 7, 8]);
        k.add_derived_clause(18, false, 0, &[-9], &[]); // blocked since '9' pure
        k.add_derived_clause(19, false, 0, &[7, 8, -5], &[]);
    }

    #[test]
    fn checker_valid_statistics_match_cpp() {
        with_checker(|k| {
            valid_case(k);
            assert!(!k.inconsistent);
            let s = k.stats;
            // Values printed by the C++ checker for the same case.
            assert_eq!(s.checks, 128);
            assert_eq!(s.assumptions, 398);
            assert_eq!(s.propagations, 786);
            assert_eq!(s.original, 9);
            assert_eq!(s.derived, 130);
            assert_eq!(s.deleted, 114);
            assert_eq!(s.insertions, 134);
            assert_eq!(s.collections, 1);
            assert_eq!(s.collisions, 57);
            assert_eq!(s.searches, 114);
            assert_eq!(s.units, 2);
        });
    }

    #[test]
    fn checker_print_stats_matches_cpp() {
        let out = child_stdout("checker::tests::checker_print_stats_matches_cpp", || {
            with_checker(|k| {
                valid_case(k);
                k.print_stats();
            });
        });
        let expected = "\
c --- [ checker statistics ] -------------------------------------------------
c 
c checks:                      128
c assumptions:                 398         3.11    per check
c propagations:                786         6.14    per check
c original:                      9         6.47 %  of all clauses
c derived:                     130        93.53 %  of all clauses
c deleted:                     114        82.01 %  of all clauses
c insertions:                  134        96.40 %  of all clauses
c collections:                   1         0.01    deleted per collection
c collisions:                   57         0.50    per search
c searches:                    114
c units:                         2
";
        assert!(out.contains(expected), "got:\n{}", out);
    }

    #[test]
    fn checker_derives_empty_clause() {
        with_checker(|k| {
            // PHP(3,2) with a RUP refutation.
            let php: [&[i32]; 9] =
                [&[1, 2], &[3, 4], &[5, 6], &[-1, -3], &[-1, -5], &[-3, -5], &[-2, -4], &[-2, -6], &[-4, -6]];
            for (i, c) in php.iter().enumerate() {
                k.add_original_clause(i as i64 + 1, false, c, false);
            }
            assert!(!k.inconsistent);
            k.add_derived_clause(10, false, 0, &[-1, -4], &[]);
            k.add_derived_clause(11, false, 0, &[-1], &[]);
            // After the unit '-1' the formula is refuted by propagation.
            assert!(k.inconsistent);
            k.add_derived_clause(12, false, 0, &[], &[]);
            Tracer::delete_clause(k, 1, false, &[1, 2]);
            assert!(k.inconsistent);
        });
    }

    #[test]
    fn checker_fails_on_underived_clause() {
        expect_fatal(
            "checker::tests::checker_fails_on_underived_clause",
            "failed to check derived clause:\n1 3 0",
            || {
                with_checker(|k| {
                    k.add_original_clause(1, false, &[1, 2], false);
                    k.add_original_clause(2, false, &[-1, 2], false);
                    k.add_original_clause(3, false, &[-3, 2], false);
                    k.add_derived_clause(4, false, 0, &[1, 3], &[]);
                })
            },
        );
    }

    #[test]
    fn checker_fails_on_deleting_missing_clause() {
        expect_fatal(
            "checker::tests::checker_fails_on_deleting_missing_clause",
            "deleted clause not in proof:\n1 3 0",
            || {
                with_checker(|k| {
                    k.add_original_clause(1, false, &[1, 2], false);
                    k.add_original_clause(2, false, &[2, 3], false);
                    Tracer::delete_clause(k, 3, false, &[1, 3]);
                })
            },
        );
    }

    #[test]
    fn checker_hash_reduction() {
        assert_eq!(Checker::reduce_hash(0x1234_5678_9abc_def0, 1), 0);
        let h = 0x1234_5678_9abc_def0u64;
        let mut r = h ^ (h >> 32);
        r ^= r >> 16;
        r ^= r >> 8;
        r ^= r >> 4;
        assert_eq!(Checker::reduce_hash(h, 16), r & 15);
        assert_eq!(Checker::l2u(1), 0);
        assert_eq!(Checker::l2u(-1), 1);
        assert_eq!(Checker::l2u(3), 4);
    }
}

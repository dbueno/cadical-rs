//! Port of `idruptracer.hpp` and `idruptracer.cpp`.

use crate::file::File;
use crate::internal::Internal;
use crate::tracer::{ConclusionType, FileTracer, InternalTracer, Tracer};

#[repr(C)]
pub struct IdrupClause {
    /// Collision chain link for hash table.
    pub next: *mut IdrupClause,
    /// Previously computed full 64-bit hash.
    pub hash: u64,
    /// Id of clause.
    pub id: i64,
    pub size: u32,
    pub literals: [i32; 1],
}

pub const IDRUP_NUM_NONCES: usize = 4;

pub struct IdrupTracer {
    pub internal: *mut Internal,
    pub file: Box<File>,
    pub binary: bool,
    /// The file is a pipe and needs eagerly flushing.
    pub piping: bool,
    /// Number of clauses in hash table.
    pub num_clauses: u64,
    /// Size of clause hash table.
    pub size_clauses: u64,
    /// Hash table of clauses.
    pub clauses: Vec<*mut IdrupClause>,
    pub imported_clause: Vec<i32>,
    pub assumptions: Vec<i32>,

    /// Random numbers for hashing.
    pub nonces: [u64; IDRUP_NUM_NONCES],
    /// Last computed hash value of clause.
    pub last_hash: u64,
    /// Id of the last added clause.
    pub last_id: i64,
    pub last_clause: *mut IdrupClause,
    pub added: i64,
    pub deleted: i64,
    pub weakened: i64,
    pub restore: i64,
    pub original: i64,
    pub solved: i64,
}

impl Tracer for IdrupTracer {
    fn add_derived_clause(&mut self, _id: i64, _redundant: bool, _witness: i32, clause: &[i32], _chain: &[i64]) {
        if self.file.closed() {
            return;
        }
        debug_assert!(self.imported_clause.is_empty());
        log!(self.internal, clause, "IDRUP TRACER tracing addition of derived clause");
        self.idrup_add_derived_clause(clause);
        self.added += 1;
    }

    fn add_assumption_clause(&mut self, id: i64, clause: &[i32], _chain: &[i64]) {
        if self.file.closed() {
            return;
        }
        debug_assert!(self.imported_clause.is_empty());
        log!(self.internal, clause, "IDRUP TRACER tracing addition of assumption clause");
        for &lit in clause {
            self.imported_clause.push(lit);
        }
        self.last_id = id;
        self.insert();
        self.imported_clause.clear();
    }

    fn weaken_minus(&mut self, id: i64, _clause: &[i32]) {
        if self.file.closed() {
            return;
        }
        debug_assert!(self.imported_clause.is_empty());
        log!(self.internal, "IDRUP TRACER tracing weaken minus of clause[{}]", id);
        self.last_id = id;
        self.insert();
        self.weakened += 1;
    }

    fn delete_clause(&mut self, id: i64, _redundant: bool, clause: &[i32]) {
        if self.file.closed() {
            return;
        }
        debug_assert!(self.imported_clause.is_empty());
        log!(self.internal, "IDRUP TRACER tracing deletion of clause[{}]", id);
        self.idrup_delete_clause(id, clause);
    }

    fn add_original_clause(&mut self, id: i64, _redundant: bool, clause: &[i32], restored: bool) {
        if self.file.closed() {
            return;
        }
        if !restored {
            log!(self.internal, clause, "IDRUP TRACER tracing addition of original clause");
            self.original += 1;
            return self.idrup_add_original_clause(clause);
        }
        debug_assert!(restored);
        if self.find_and_delete(id) {
            log!(self.internal, clause, "IDRUP TRACER the clause was not yet weakened, so no restore");
            return;
        }
        log!(self.internal, clause, "IDRUP TRACER tracing addition of restored clause");
        self.idrup_add_restored_clause(clause);
        self.restore += 1;
    }

    fn report_status(&mut self, status: i32, _id: i64) {
        if self.file.closed() {
            return;
        }
        log!(self.internal, "IDRUP TRACER tracing report of status {}", status);
        self.idrup_report_status(status);
    }

    fn conclude_sat(&mut self, model: &[i32]) {
        if self.file.closed() {
            return;
        }
        log!(self.internal, model, "IDRUP TRACER tracing conclusion of model");
        self.idrup_conclude_sat(model);
    }

    fn conclude_unsat(&mut self, _conclusion: ConclusionType, conclusion: &[i64]) {
        if self.file.closed() {
            return;
        }
        debug_assert!(self.imported_clause.is_empty());
        log!(self.internal, conclusion, "IDRUP TRACER tracing conclusion of clause(s)");
        self.idrup_conclude_and_delete(conclusion);
    }

    fn conclude_unknown(&mut self, trail: &[i32]) {
        if self.file.closed() {
            return;
        }
        log!(self.internal, trail, "IDRUP TRACER tracing conclusion of unknown state");
        self.idrup_conclude_unknown(trail);
    }

    fn solve_query(&mut self) {
        if self.file.closed() {
            return;
        }
        log!(self.internal, &self.assumptions, "IDRUP TRACER tracing solve query with assumptions");
        self.idrup_solve_query();
        self.solved += 1;
    }

    fn add_assumption(&mut self, lit: i32) {
        log!(self.internal, "IDRUP TRACER tracing addition of assumption {}", lit);
        self.assumptions.push(lit);
    }

    fn reset_assumptions(&mut self) {
        log!(self.internal, &self.assumptions, "IDRUP TRACER tracing reset of assumptions");
        self.assumptions.clear();
    }

    fn begin_proof(&mut self, _reserved_ids: i64) {}
    fn finalize_clause(&mut self, _id: i64, _clause: &[i32]) {}
    fn strengthen(&mut self, _id: i64) {}
    fn add_constraint(&mut self, _clause: &[i32]) {}
}

impl InternalTracer for IdrupTracer {
    fn connect_internal(&mut self, i: *mut Internal) {
        self.internal = i;
        self.file.connect_internal(self.internal);
        log!(self.internal, "IDRUP TRACER connected to internal");
    }
}

impl FileTracer for IdrupTracer {
    fn closed(&mut self) -> bool {
        self.file.closed()
    }

    fn close(&mut self, print: bool) {
        debug_assert!(!self.closed());
        self.file.close(false);
        if print {
            msg!(self.internal, "IDRUP proof file '{}' closed", self.file.name());
            self.print_statistics();
        }
    }

    fn flush(&mut self, print: bool) {
        debug_assert!(!self.closed());
        self.file.flush();
        if print {
            msg!(self.internal, "IDRUP proof file '{}' flushed", self.file.name());
            self.print_statistics();
        }
    }
}

impl IdrupTracer {
    pub fn new(internal: *mut Internal, mut file: Box<File>, binary: bool) -> IdrupTracer {
        // Initialize random number table for hash function.
        let mut nonces = [0u64; IDRUP_NUM_NONCES];
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
        let piping = file.piping();
        IdrupTracer {
            internal,
            file,
            binary,
            piping,
            num_clauses: 0,
            size_clauses: 0,
            clauses: Vec::new(),
            imported_clause: Vec::new(),
            assumptions: Vec::new(),
            nonces,
            last_hash: 0,
            last_id: 0,
            last_clause: std::ptr::null_mut(),
            added: 0,
            deleted: 0,
            // Not initialized in C++ (only used for statistics).
            weakened: 0,
            restore: 0,
            original: 0,
            solved: 0,
        }
    }
}

impl Drop for IdrupTracer {
    fn drop(&mut self) {
        log!(self.internal, "IDRUP TRACER delete");
        // 'file' is deleted with the box.
        for i in 0..self.size_clauses as usize {
            let mut c = self.clauses[i];
            while !c.is_null() {
                // SAFETY: 'c' is a live clause of the hash table.
                let next = unsafe { (*c).next };
                self.deallocate_clause(c);
                c = next;
            }
        }
    }
}

/*------------------------------------------------------------------------*/

#[allow(unused_imports)]
use crate::prelude::*;

use crate::solver::{SATISFIABLE, UNSATISFIABLE};

/// Pointer to the literals of an IDRUP clause (variadic array).
#[inline(always)]
fn idrup_lits(c: *mut IdrupClause) -> *mut i32 {
    // SAFETY: only computes the address of the 'literals' field.
    unsafe { std::ptr::addr_of_mut!((*c).literals) as *mut i32 }
}

impl IdrupTracer {
    pub fn enlarge_clauses(&mut self) {
        debug_assert!(self.num_clauses == self.size_clauses);
        let new_size_clauses: u64 = if self.size_clauses != 0 { 2 * self.size_clauses } else { 1 };
        log!(
            self.internal,
            "IDRUP Tracer enlarging clauses of tracer from {} to {}",
            self.size_clauses,
            new_size_clauses
        );
        let mut new_clauses: Vec<*mut IdrupClause> = vec![std::ptr::null_mut(); new_size_clauses as usize];
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

    pub fn new_clause(&mut self) -> *mut IdrupClause {
        let size = self.imported_clause.len();
        debug_assert!(size <= u32::MAX as usize);
        // C++: 'off = size ? -1 : 0' and 'bytes = sizeof + (size - off) * 4'.
        let extra = if size != 0 { size + 1 } else { 0 };
        let bytes = std::mem::size_of::<IdrupClause>() + extra * std::mem::size_of::<i32>();
        // SAFETY: allocation of a variadic clause, initialized below.
        let res = unsafe { libc::malloc(bytes) as *mut IdrupClause };
        if res.is_null() {
            std::alloc::handle_alloc_error(std::alloc::Layout::from_size_align(bytes, 8).unwrap());
        }
        // SAFETY: 'res' points to 'bytes' writable bytes.
        unsafe {
            (*res).next = std::ptr::null_mut();
            (*res).hash = self.last_hash;
            (*res).id = self.last_id;
            (*res).size = size as u32;
        }
        let literals = idrup_lits(res);
        for (k, &lit) in self.imported_clause.iter().enumerate() {
            // SAFETY: 'k < size'.
            unsafe { *literals.add(k) = lit };
        }
        self.last_clause = res;
        self.num_clauses += 1;
        res
    }

    /// C++ overload `IdrupTracer::delete_clause` (renamed).
    pub fn deallocate_clause(&mut self, c: *mut IdrupClause) {
        debug_assert!(!c.is_null());
        self.num_clauses -= 1;
        // SAFETY: allocated with 'malloc' in 'new_clause'.
        unsafe { libc::free(c as *mut libc::c_void) };
    }

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
        let j = (id % IDRUP_NUM_NONCES as i64) as u32 as usize;
        let tmp = self.nonces[j].wrapping_mul(id as u64);
        self.last_hash = tmp;
        tmp
    }

    pub fn find_and_delete(&mut self, id: i64) -> bool {
        if self.num_clauses == 0 {
            return false;
        }
        let hash = self.compute_hash(id);
        let h = Self::reduce_hash(hash, self.size_clauses) as usize;
        // SAFETY: 'h < size_clauses' and the chain consists of live clauses.
        unsafe {
            let mut res: *mut *mut IdrupClause = self.clauses.as_mut_ptr().add(h);
            let mut c: *mut IdrupClause;
            loop {
                c = *res;
                if c.is_null() {
                    break;
                }
                if (*c).hash == hash && (*c).id == id {
                    break;
                }
                if (*c).next.is_null() {
                    return false;
                }
                res = &mut (*c).next;
            }
            if c.is_null() {
                return false;
            }
            *res = (*c).next;
            let begin = idrup_lits(c);
            for i in 0..(*c).size as usize {
                self.imported_clause.push(*begin.add(i));
            }
            self.deallocate_clause(c);
        }
        true
    }

    pub fn insert(&mut self) {
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

    #[inline]
    pub fn flush_if_piping(&mut self) {
        if self.piping {
            self.file.flush();
        }
    }

    #[inline]
    pub fn put_binary_zero(&mut self) {
        debug_assert!(self.binary);
        self.file.put_char(0);
    }

    #[inline]
    pub fn put_binary_lit(&mut self, lit: i32) {
        debug_assert!(self.binary);
        debug_assert!(lit != i32::MIN);
        let mut x: u32 = 2u32.wrapping_mul(lit.unsigned_abs()).wrapping_add((lit < 0) as u32);
        let mut ch: u8;
        while x & !0x7f != 0 {
            ch = ((x & 0x7f) | 0x80) as u8;
            self.file.put_char(ch);
            x >>= 7;
        }
        ch = x as u8;
        self.file.put_char(ch);
    }

    /// `can_be_negative` defaults to `false` in C++
    #[inline]
    pub fn put_binary_id(&mut self, id: i64, can_be_negative: bool) {
        debug_assert!(self.binary);
        let mut x: u64 = id.unsigned_abs();
        if can_be_negative {
            x = 2u64.wrapping_mul(x).wrapping_add((id < 0) as u64);
        }
        let mut ch: u8;
        while x & !0x7f != 0 {
            ch = ((x & 0x7f) | 0x80) as u8;
            self.file.put_char(ch);
            x >>= 7;
        }
        ch = x as u8;
        self.file.put_char(ch);
    }

    /// `<tag> <lits> 0` shared by several line types.
    #[inline]
    fn put_tagged_lits(&mut self, binary_tag: u8, ascii_tag: &str, lits: &[i32]) {
        if self.binary {
            self.file.put_char(binary_tag);
        } else {
            self.file.put_str(ascii_tag);
        }
        for &lit in lits {
            if self.binary {
                self.put_binary_lit(lit);
            } else {
                self.file.put_int(lit);
                self.file.put_char(b' ');
            }
        }
        if self.binary {
            self.put_binary_zero();
        } else {
            self.file.put_str("0\n");
        }
    }

    /*----------------------------------------------------------------------*/

    pub fn idrup_add_restored_clause(&mut self, clause: &[i32]) {
        self.put_tagged_lits(b'r', "r ", clause);
        // flush_if_piping ();
    }

    pub fn idrup_add_derived_clause(&mut self, clause: &[i32]) {
        self.put_tagged_lits(b'l', "l ", clause);
        // flush_if_piping ();
    }

    pub fn idrup_add_original_clause(&mut self, clause: &[i32]) {
        self.put_tagged_lits(b'i', "i ", clause);
        // flush_if_piping ();
    }

    pub fn idrup_delete_clause(&mut self, id: i64, clause: &[i32]) {
        if self.find_and_delete(id) {
            debug_assert!(self.imported_clause.is_empty());
            if self.binary {
                self.file.put_char(b'w');
            } else {
                self.file.put_str("w ");
            }
            self.weakened += 1;
        } else {
            if self.binary {
                self.file.put_char(b'd');
            } else {
                self.file.put_str("d ");
            }
            self.deleted += 1;
        }
        for &external_lit in clause {
            if self.binary {
                self.put_binary_lit(external_lit);
            } else {
                self.file.put_int(external_lit);
                self.file.put_char(b' ');
            }
        }
        if self.binary {
            self.put_binary_zero();
        } else {
            self.file.put_str("0\n");
        }
        // flush_if_piping ();
    }

    pub fn idrup_conclude_and_delete(&mut self, conclusion: &[i64]) {
        let size = conclusion.len() as u64;
        if size > 1 {
            if self.binary {
                self.file.put_char(b'U');
                self.put_binary_id(size as i64, false);
            } else {
                self.file.put_str("U ");
                self.file.put_u64(size);
                self.file.put_str("\n");
            }
        }
        for &id in conclusion {
            if self.binary {
                self.file.put_char(b'u');
            } else {
                self.file.put_str("u ");
            }
            let _ = self.find_and_delete(id);
            for k in 0..self.imported_clause.len() {
                let external_lit = self.imported_clause[k];
                // flip sign...
                let not_elit = -external_lit;
                if self.binary {
                    self.put_binary_lit(not_elit);
                } else {
                    self.file.put_int(not_elit);
                    self.file.put_char(b' ');
                }
            }
            if self.binary {
                self.put_binary_zero();
            } else {
                self.file.put_str("0\n");
            }
            self.imported_clause.clear();
        }
        self.flush_if_piping();
    }

    pub fn idrup_report_status(&mut self, status: i32) {
        if self.binary {
            self.file.put_char(b's');
        } else {
            self.file.put_str("s ");
        }
        if status == SATISFIABLE {
            self.file.put_str("SATISFIABLE");
        } else if status == UNSATISFIABLE {
            self.file.put_str("UNSATISFIABLE");
        } else {
            self.file.put_str("UNKNOWN");
        }
        if !self.binary {
            self.file.put_str("\n");
        }
        self.flush_if_piping();
    }

    pub fn idrup_conclude_sat(&mut self, model: &[i32]) {
        self.put_tagged_lits(b'm', "m ", model);
        self.flush_if_piping();
    }

    pub fn idrup_conclude_unknown(&mut self, trail: &[i32]) {
        self.put_tagged_lits(b'e', "e ", trail);
        self.flush_if_piping();
    }

    pub fn idrup_solve_query(&mut self) {
        if self.binary {
            self.file.put_char(b'q');
        } else {
            self.file.put_str("q ");
        }
        for k in 0..self.assumptions.len() {
            let lit = self.assumptions[k];
            if self.binary {
                self.put_binary_lit(lit);
            } else {
                self.file.put_int(lit);
                self.file.put_char(b' ');
            }
        }
        if self.binary {
            self.put_binary_zero();
        } else {
            self.file.put_str("0\n");
        }
        self.flush_if_piping();
    }

    /*----------------------------------------------------------------------*/

    pub fn print_statistics(&mut self) {
        // TODO complete this.
        let bytes = self.file.bytes();
        let total = (self.added + self.deleted + self.weakened + self.restore + self.original) as u64;
        msg!(
            self.internal,
            "LIDRUP {} original clauses {:.2}%",
            self.original,
            percent(self.original as f64, total as f64)
        );
        msg!(
            self.internal,
            "LIDRUP {} learned clauses {:.2}%",
            self.added,
            percent(self.added as f64, total as f64)
        );
        msg!(
            self.internal,
            "LIDRUP {} deleted clauses {:.2}%",
            self.deleted,
            percent(self.deleted as f64, total as f64)
        );
        msg!(
            self.internal,
            "LIDRUP {} weakened clauses {:.2}%",
            self.weakened,
            percent(self.weakened as f64, total as f64)
        );
        msg!(
            self.internal,
            "LIDRUP {} restored clauses {:.2}%",
            self.restore,
            percent(self.restore as f64, total as f64)
        );
        msg!(
            self.internal,
            "LIDRUP {} queries {:.2}",
            self.solved,
            relative(self.solved as f64, total as f64)
        );
        msg!(
            self.internal,
            "IDRUP {} bytes ({:.2} MB)",
            bytes,
            bytes as f64 / (1u64 << 20) as f64
        );
    }
}

//! Port of `veripbtracer.hpp` and `veripbtracer.cpp`.

use crate::file::File;
use crate::internal::Internal;
use crate::tracer::{FileTracer, InternalTracer, Tracer};

#[repr(C)]
pub struct HashId {
    /// Collision chain link for hash table.
    pub next: *mut HashId,
    /// Previously computed full 64-bit hash.
    pub hash: u64,
    /// Id of clause.
    pub id: i64,
}

pub const VERIPB_NUM_NONCES: usize = 4;

pub struct VeripbTracer {
    pub internal: *mut Internal,
    pub file: Box<File>,
    #[cfg(debug_assertions)]
    pub binary: bool,
    pub with_antecedents: bool,
    pub checked_deletions: bool,
    /// Number of clauses in hash table.
    pub num_clauses: u64,
    /// Size of clause hash table.
    pub size_clauses: u64,
    /// Hash table of clauses.
    pub clauses: Vec<*mut HashId>,
    /// Random numbers for hashing.
    pub nonces: [u64; VERIPB_NUM_NONCES],
    /// Last computed hash value of clause.
    pub last_hash: u64,
    /// Id of the last added clause.
    pub last_id: i64,
    pub last_clause: *mut HashId,
    pub added: i64,
    pub deleted: i64,
    pub delete_ids: Vec<i64>,
}

impl Tracer for VeripbTracer {
    fn begin_proof(&mut self, id: i64) {
        if self.file.closed() {
            return;
        }
        log!(self.internal, "VERIPB TRACER tracing start of proof with {}original clauses", id);
        self.veripb_begin_proof(id);
    }

    fn add_original_clause(&mut self, _id: i64, _redundant: bool, _clause: &[i32], _restored: bool) {} // skip

    fn add_derived_clause(&mut self, id: i64, redundant: bool, witness: i32, clause: &[i32], chain: &[i64]) {
        if self.file.closed() {
            return;
        }
        log!(self.internal, "VERIPB TRACER tracing addition of derived clause[{}]", id);
        if witness != 0 {
            self.veripb_add_derived_clause_witness(id, redundant, witness, clause);
        } else if self.with_antecedents {
            self.veripb_add_derived_clause_chain(id, redundant, clause, chain);
        } else {
            self.veripb_add_derived_clause(id, redundant, clause);
        }
        self.added += 1;
    }

    fn delete_clause(&mut self, id: i64, redundant: bool, _clause: &[i32]) {
        if self.file.closed() {
            return;
        }
        log!(self.internal, "VERIPB TRACER tracing deletion of clause[{}]", id);
        self.veripb_delete_clause(id, redundant);
        self.deleted += 1;
    }

    fn finalize_clause(&mut self, _id: i64, _clause: &[i32]) {} // skip

    fn report_status(&mut self, status: i32, conflict_id: i64) {
        if self.file.closed() {
            return;
        }
        #[cfg(feature = "logging")]
        if conflict_id != 0 {
            log!(
                self.internal,
                "VERIPB TRACER tracing finalization of proof with empty clause[{}]",
                conflict_id
            );
        }
        self.veripb_report_status(status == UNSATISFIABLE, conflict_id);
    }

    fn weaken_minus(&mut self, id: i64, _clause: &[i32]) {
        if !self.checked_deletions {
            return;
        }
        if self.file.closed() {
            return;
        }
        log!(self.internal, "VERIPB TRACER tracing weaken minus of clause[{}]", id);
        self.last_id = id;
        self.insert();
    }

    fn strengthen(&mut self, id: i64) {
        if self.file.closed() {
            return;
        }
        log!(self.internal, "VERIPB TRACER tracing strengthen of clause[{}]", id);
        self.veripb_strengthen(id);
    }
}

impl InternalTracer for VeripbTracer {
    fn connect_internal(&mut self, i: *mut Internal) {
        self.internal = i;
        self.file.connect_internal(self.internal);
        log!(self.internal, "VERIPB TRACER connected to internal");
    }
}

impl FileTracer for VeripbTracer {
    fn closed(&mut self) -> bool {
        self.file.closed()
    }

    fn close(&mut self, print: bool) {
        debug_assert!(!self.closed());
        self.file.close(false);
        if print {
            msg!(self.internal, "VeriPB proof file '{}' closed", self.file.name());
            self.print_statistics();
        }
    }

    fn flush(&mut self, print: bool) {
        debug_assert!(!self.closed());
        self.file.flush();
        if print {
            msg!(self.internal, "VeriPB proof file '{}' flushed", self.file.name());
            self.print_statistics();
        }
    }
}

impl VeripbTracer {
    /// Owns and deletes 'file'.
    pub fn new(
        internal: *mut Internal,
        file: Box<File>,
        binary: bool,
        antecedents: bool,
        check_deletions: bool,
    ) -> VeripbTracer {
        // Initialize random number table for hash function.
        let mut nonces = [0u64; VERIPB_NUM_NONCES];
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
        #[cfg(not(debug_assertions))]
        let _ = binary;
        VeripbTracer {
            internal,
            file,
            #[cfg(debug_assertions)]
            binary,
            with_antecedents: antecedents,
            checked_deletions: check_deletions,
            num_clauses: 0,
            size_clauses: 0,
            clauses: Vec::new(),
            nonces,
            last_hash: 0,
            last_id: 0,
            last_clause: std::ptr::null_mut(),
            added: 0,
            deleted: 0,
            delete_ids: Vec::new(),
        }
    }
}

impl Drop for VeripbTracer {
    fn drop(&mut self) {
        log!(self.internal, "VERIPB TRACER delete");
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

use crate::solver::UNSATISFIABLE;

impl VeripbTracer {
    pub fn enlarge_clauses(&mut self) {
        debug_assert!(self.num_clauses == self.size_clauses);
        let new_size_clauses: u64 = if self.size_clauses != 0 { 2 * self.size_clauses } else { 1 };
        log!(
            self.internal,
            "VeriPB Tracer enlarging clauses from {} to {}",
            self.size_clauses,
            new_size_clauses
        );
        let mut new_clauses: Vec<*mut HashId> = vec![std::ptr::null_mut(); new_size_clauses as usize];
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

    pub fn new_clause(&mut self) -> *mut HashId {
        let res = Box::into_raw(Box::new(HashId {
            next: std::ptr::null_mut(),
            hash: self.last_hash,
            id: self.last_id,
        }));
        self.last_clause = res;
        self.num_clauses += 1;
        res
    }

    /// C++ overload `VeripbTracer::delete_clause` (renamed).
    pub fn deallocate_clause(&mut self, c: *mut HashId) {
        debug_assert!(!c.is_null());
        self.num_clauses -= 1;
        // SAFETY: allocated with 'Box' in 'new_clause'.
        drop(unsafe { Box::from_raw(c) });
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
        let j = (id % VERIPB_NUM_NONCES as i64) as u32 as usize; // Dont know if this is a good
        let tmp = self.nonces[j].wrapping_mul(id as u64); // hash funktion or even better
        self.last_hash = tmp; // than just using id.
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
            let mut res: *mut *mut HashId = self.clauses.as_mut_ptr().add(h);
            let mut c: *mut HashId;
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
    pub fn put_binary_zero(&mut self) {
        #[cfg(debug_assertions)]
        debug_assert!(self.binary);
        self.file.put_char(0);
    }

    #[inline]
    pub fn put_binary_lit(&mut self, lit: i32) {
        #[cfg(debug_assertions)]
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
        #[cfg(debug_assertions)]
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

    /*----------------------------------------------------------------------*/

    /// `1 [~]x<var> ` for each literal.
    #[inline]
    fn put_pb_lits(&mut self, clause: &[i32]) {
        for &external_lit in clause {
            self.file.put_str("1 ");
            if external_lit < 0 {
                self.file.put_char(b'~');
            }
            self.file.put_char(b'x');
            self.file.put_int(external_lit.abs());
            self.file.put_char(b' ');
        }
    }

    /// C++ overload `VeripbTracer::veripb_add_derived_clause` (renamed).
    pub fn veripb_add_derived_clause_witness(&mut self, id: i64, redundant: bool, witness: i32, clause: &[i32]) {
        debug_assert!(witness == clause[0]);
        self.file.put_str("red ");
        self.put_pb_lits(clause);
        self.file.put_str(">= 1 : ");
        self.file.put_char(b'x');
        self.file.put_int(witness.abs());
        self.file.put_str(" -> ");
        if witness < 0 {
            self.file.put_str("0");
        } else {
            self.file.put_str("1");
        }
        self.file.put_str(";\n");
        if !redundant && self.checked_deletions {
            self.file.put_str("core id ");
            self.file.put_i64(id);
            self.file.put_str(";\n");
        }
    }

    /// C++ overload `VeripbTracer::veripb_add_derived_clause` (renamed).
    pub fn veripb_add_derived_clause_chain(&mut self, id: i64, redundant: bool, clause: &[i32], chain: &[i64]) {
        self.file.put_str("pol ");
        let mut first = true;
        debug_assert!(!chain.is_empty());
        for &cid in chain.iter().rev() {
            if first {
                first = false;
                self.file.put_i64(cid);
            } else {
                self.file.put_char(b' ');
                self.file.put_i64(cid);
                self.file.put_str(" + s");
            }
        }
        self.file.put_str(";\n");
        self.file.put_str("e ");
        self.put_pb_lits(clause);
        self.file.put_str(">= 1 : ");
        self.file.put_i64(id);
        self.file.put_str(";\n");
        if !redundant && self.checked_deletions {
            self.file.put_str("core id ");
            self.file.put_i64(id);
            self.file.put_str(";\n");
        }
    }

    pub fn veripb_add_derived_clause(&mut self, id: i64, redundant: bool, clause: &[i32]) {
        self.file.put_str("rup ");
        self.put_pb_lits(clause);
        self.file.put_str(">= 1;\n");
        if !redundant && self.checked_deletions {
            self.file.put_str("core id ");
            self.file.put_i64(id);
            self.file.put_str(";\n");
        }
    }

    pub fn veripb_begin_proof(&mut self, reserved_ids: i64) {
        self.file.put_str("pseudo-Boolean proof version 3.0\n");
        self.file.put_str("f ");
        self.file.put_i64(reserved_ids);
        self.file.put_str(";\n");
    }

    pub fn veripb_delete_clause(&mut self, id: i64, redundant: bool) {
        if !redundant && self.checked_deletions && self.find_and_delete(id) {
            return;
        }
        if redundant || !self.checked_deletions {
            self.file.put_str("del id ");
        } else {
            self.file.put_str("delc ");
        }
        self.file.put_i64(id);
        self.file.put_str(";\n");
    }

    pub fn veripb_report_status(&mut self, unsat: bool, conflict_id: i64) {
        self.file.put_str("output NONE;\n");
        if unsat {
            self.file.put_str("conclusion UNSAT : ");
            self.file.put_i64(conflict_id);
            self.file.put_str(";\n");
        } else {
            self.file.put_str("conclusion NONE;\n");
        }
        self.file.put_str("end pseudo-Boolean proof;\n");
    }

    pub fn veripb_strengthen(&mut self, id: i64) {
        if !self.checked_deletions {
            return;
        }
        self.file.put_str("core id ");
        self.file.put_i64(id);
        self.file.put_str(";\n");
    }

    /*----------------------------------------------------------------------*/

    pub fn print_statistics(&mut self) {
        // TODO complete
        let bytes = self.file.bytes();
        let total = (self.added + self.deleted) as u64;
        msg!(
            self.internal,
            "VeriPB {} added clauses {:.2}%",
            self.added,
            percent(self.added as f64, total as f64)
        );
        msg!(
            self.internal,
            "VeriPB {} deleted clauses {:.2}%",
            self.deleted,
            percent(self.deleted as f64, total as f64)
        );
        msg!(
            self.internal,
            "VeriPB {} bytes ({:.2} MB)",
            bytes,
            bytes as f64 / (1u64 << 20) as f64
        );
    }
}

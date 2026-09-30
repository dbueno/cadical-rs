//! Port of `frattracer.hpp` and `frattracer.cpp`.

use crate::file::File;
use crate::internal::Internal;
use crate::tracer::{FileTracer, InternalTracer, Tracer};

pub struct FratTracer {
    pub internal: *mut Internal,
    pub file: Box<File>,
    pub binary: bool,
    pub with_antecedents: bool,
    pub added: i64,
    pub deleted: i64,
    pub finalized: i64,
    pub original: i64,
    pub delete_ids: Vec<i64>,
}

impl Tracer for FratTracer {
    fn begin_proof(&mut self, _reserved_ids: i64) {} // skip

    fn add_original_clause(&mut self, id: i64, _redundant: bool, clause: &[i32], _restored: bool) {
        if self.file.closed() {
            return;
        }
        log!(self.internal, "FRAT TRACER tracing addition of original clause");
        self.frat_add_original_clause(id, clause);
    }

    fn add_derived_clause(&mut self, id: i64, _redundant: bool, _witness: i32, clause: &[i32], chain: &[i64]) {
        if self.file.closed() {
            return;
        }
        log!(self.internal, "FRAT TRACER tracing addition of derived clause");
        if self.with_antecedents {
            self.frat_add_derived_clause_with_chain(id, clause, chain);
        } else {
            self.frat_add_derived_clause(id, clause);
        }
        self.added += 1;
    }

    fn delete_clause(&mut self, id: i64, _redundant: bool, clause: &[i32]) {
        if self.file.closed() {
            return;
        }
        log!(self.internal, "FRAT TRACER tracing deletion of clause");
        self.frat_delete_clause(id, clause);
        self.deleted += 1;
    }

    fn finalize_clause(&mut self, id: i64, clause: &[i32]) {
        if self.file.closed() {
            return;
        }
        log!(self.internal, "FRAT TRACER tracing finalization of clause");
        self.frat_finalize_clause(id, clause);
    }

    fn report_status(&mut self, _status: i32, _id: i64) {} // skip
}

impl InternalTracer for FratTracer {
    fn connect_internal(&mut self, i: *mut Internal) {
        self.internal = i;
        self.file.connect_internal(self.internal);
        log!(self.internal, "FRAT TRACER connected to internal");
    }
}

impl FileTracer for FratTracer {
    fn closed(&mut self) -> bool {
        self.file.closed()
    }

    fn close(&mut self, print: bool) {
        debug_assert!(!self.closed());
        self.file.close(false);
        if print {
            msg!(self.internal, "FRAT proof file '{}' closed", self.file.name());
            self.print_statistics();
        }
    }

    fn flush(&mut self, print: bool) {
        debug_assert!(!self.closed());
        self.file.flush();
        if print {
            msg!(self.internal, "FRAT proof file '{}' flushed", self.file.name());
            self.print_statistics();
        }
    }
}

impl FratTracer {
    /// Owns and deletes 'file'.
    pub fn new(internal: *mut Internal, file: Box<File>, binary: bool, antecedents: bool) -> FratTracer {
        FratTracer {
            internal,
            file,
            binary,
            with_antecedents: antecedents,
            added: 0,
            deleted: 0,
            finalized: 0,
            original: 0,
            delete_ids: Vec::new(),
        }
    }
}

impl Drop for FratTracer {
    fn drop(&mut self) {
        log!(self.internal, "FRAT TRACER delete");
        // 'file' is deleted with the box.
    }
}

/*------------------------------------------------------------------------*/

#[allow(unused_imports)]
use crate::prelude::*;

impl FratTracer {
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

    /*----------------------------------------------------------------------*/

    /// Common part: `<tag> <id>  <lits> 0` (without the terminating zero).
    #[inline]
    fn put_tag_id_lits(&mut self, binary_tag: u8, ascii_tag: &str, id: i64, clause: &[i32]) {
        if self.binary {
            self.file.put_char(binary_tag);
        } else {
            self.file.put_str(ascii_tag);
        }
        if self.binary {
            self.put_binary_id(id, false);
        } else {
            self.file.put_i64(id);
            self.file.put_str("  ");
        }
        for &external_lit in clause {
            if self.binary {
                self.put_binary_lit(external_lit);
            } else {
                self.file.put_int(external_lit);
                self.file.put_char(b' ');
            }
        }
    }

    pub fn frat_add_original_clause(&mut self, id: i64, clause: &[i32]) {
        self.put_tag_id_lits(b'o', "o ", id, clause);
        if self.binary {
            self.put_binary_zero();
        } else {
            self.file.put_str("0\n");
        }
    }

    pub fn frat_add_derived_clause(&mut self, id: i64, clause: &[i32]) {
        self.put_tag_id_lits(b'a', "a ", id, clause);
        if self.binary {
            self.put_binary_zero();
        } else {
            self.file.put_str("0\n");
        }
    }

    /// C++ overload `FratTracer::frat_add_derived_clause` (renamed).
    pub fn frat_add_derived_clause_with_chain(&mut self, id: i64, clause: &[i32], chain: &[i64]) {
        self.put_tag_id_lits(b'a', "a ", id, clause);
        if self.binary {
            self.put_binary_zero();
            self.file.put_char(b'l');
        } else {
            self.file.put_str("0  l ");
        }
        for &c in chain {
            if self.binary {
                self.put_binary_id(c, true); // LRAT can have negative ids
            } else {
                self.file.put_i64(c);
                self.file.put_char(b' '); // in proof chain, so they get
            }
        }
        if self.binary {
            self.put_binary_zero(); // since cadical has no rat-steps
        } else {
            self.file.put_str("0\n"); // this is just 2c here
        }
    }

    pub fn frat_delete_clause(&mut self, id: i64, clause: &[i32]) {
        self.put_tag_id_lits(b'd', "d ", id, clause);
        if self.binary {
            self.put_binary_zero();
        } else {
            self.file.put_str("0\n");
        }
    }

    pub fn frat_finalize_clause(&mut self, id: i64, clause: &[i32]) {
        self.put_tag_id_lits(b'f', "f ", id, clause);
        if self.binary {
            self.put_binary_zero();
        } else {
            self.file.put_str("0\n");
        }
    }

    /*----------------------------------------------------------------------*/

    pub fn print_statistics(&mut self) {
        let bytes = self.file.bytes();
        let total = (self.original + self.added + self.deleted + self.finalized) as u64;
        msg!(
            self.internal,
            "FRAT {} original clauses {:.2}%",
            self.original,
            percent(self.original as f64, total as f64)
        );
        msg!(
            self.internal,
            "FRAT {} added clauses {:.2}%",
            self.added,
            percent(self.added as f64, total as f64)
        );
        msg!(
            self.internal,
            "FRAT {} deleted clauses {:.2}%",
            self.deleted,
            percent(self.deleted as f64, total as f64)
        );
        msg!(
            self.internal,
            "FRAT {} finalized clauses {:.2}%",
            self.finalized,
            percent(self.finalized as f64, total as f64)
        );
        msg!(
            self.internal,
            "FRAT {} bytes ({:.2} MB)",
            bytes,
            bytes as f64 / (1u64 << 20) as f64
        );
    }
}

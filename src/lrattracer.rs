//! Port of `lrattracer.hpp` and `lrattracer.cpp`.

use crate::file::File;
use crate::internal::Internal;
use crate::tracer::{FileTracer, InternalTracer, Tracer};

pub struct LratTracer {
    pub internal: *mut Internal,
    pub file: Box<File>,
    pub binary: bool,
    pub added: i64,
    pub deleted: i64,
    pub latest_id: i64,
    pub delete_ids: Vec<i64>,
}

impl Tracer for LratTracer {
    fn begin_proof(&mut self, id: i64) {
        if self.file.closed() {
            return;
        }
        log!(self.internal, "LRAT TRACER tracing begin of proof");
        self.latest_id = id;
    }

    fn add_original_clause(&mut self, _id: i64, _redundant: bool, _clause: &[i32], _restored: bool) {} // skip

    fn add_derived_clause(&mut self, id: i64, _redundant: bool, _witness: i32, clause: &[i32], chain: &[i64]) {
        if self.file.closed() {
            return;
        }
        log!(self.internal, "LRAT TRACER tracing addition of derived clause");
        self.lrat_add_clause(id, clause, chain);
        self.added += 1;
    }

    fn delete_clause(&mut self, id: i64, _redundant: bool, _clause: &[i32]) {
        if self.file.closed() {
            return;
        }
        log!(self.internal, "LRAT TRACER tracing deletion of clause");
        self.lrat_delete_clause(id);
        self.deleted += 1;
    }

    fn finalize_clause(&mut self, _id: i64, _clause: &[i32]) {} // skip
    fn report_status(&mut self, _status: i32, _id: i64) {} // skip
}

impl InternalTracer for LratTracer {
    fn connect_internal(&mut self, i: *mut Internal) {
        self.internal = i;
        self.file.connect_internal(self.internal);
        log!(self.internal, "LRAT TRACER connected to internal");
    }
}

impl FileTracer for LratTracer {
    fn closed(&mut self) -> bool {
        self.file.closed()
    }

    fn close(&mut self, print: bool) {
        debug_assert!(!self.closed());
        self.file.close(false);
        if print {
            msg!(self.internal, "LRAT proof file '{}' closed", self.file.name());
            self.print_statistics();
        }
    }

    fn flush(&mut self, print: bool) {
        debug_assert!(!self.closed());
        self.file.flush();
        if print {
            msg!(self.internal, "LRAT proof file '{}' flushed", self.file.name());
            self.print_statistics();
        }
    }
}

impl LratTracer {
    /// Owns and deletes 'file'.
    pub fn new(internal: *mut Internal, file: Box<File>, binary: bool) -> LratTracer {
        LratTracer { internal, file, binary, added: 0, deleted: 0, latest_id: 0, delete_ids: Vec::new() }
    }
}

impl Drop for LratTracer {
    fn drop(&mut self) {
        log!(self.internal, "LRAT TRACER delete");
        // 'file' is deleted with the box.
    }
}

/*------------------------------------------------------------------------*/

#[allow(unused_imports)]
use crate::prelude::*;

impl LratTracer {
    #[inline]
    pub fn put_binary_zero(&mut self) {
        debug_assert!(self.binary);
        self.file.put_char(0);
    }

    #[inline]
    pub fn put_binary_lit(&mut self, lit: i32) {
        debug_assert!(self.binary);
        debug_assert!(lit != i32::MIN);
        let idx = lit.unsigned_abs();
        debug_assert!(idx < (1u32 << 31));
        let mut x: u32 = 2u32.wrapping_mul(idx).wrapping_add((lit < 0) as u32);
        let mut ch: u8;
        while x & !0x7f != 0 {
            ch = ((x & 0x7f) | 0x80) as u8;
            self.file.put_char(ch);
            x >>= 7;
        }
        ch = x as u8;
        self.file.put_char(ch);
    }

    #[inline]
    pub fn put_binary_id(&mut self, id: i64) {
        debug_assert!(self.binary);
        let mut x: u64 = id.unsigned_abs();
        x = 2u64.wrapping_mul(x).wrapping_add((id < 0) as u64);
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

    pub fn lrat_add_clause(&mut self, id: i64, clause: &[i32], chain: &[i64]) {
        if !self.delete_ids.is_empty() {
            if !self.binary {
                self.file.put_i64(self.latest_id);
                self.file.put_str(" ");
            }
            if self.binary {
                self.file.put_char(b'd');
            } else {
                self.file.put_str("d ");
            }
            for k in 0..self.delete_ids.len() {
                let did = self.delete_ids[k];
                if self.binary {
                    self.put_binary_id(did);
                } else {
                    self.file.put_i64(did);
                    self.file.put_str(" ");
                }
            }
            if self.binary {
                self.put_binary_zero();
            } else {
                self.file.put_str("0\n");
            }
            self.delete_ids.clear();
        }
        self.latest_id = id;

        if self.binary {
            self.file.put_char(b'a');
            self.put_binary_id(id);
        } else {
            self.file.put_i64(id);
            self.file.put_str(" ");
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
            self.file.put_str("0 ");
        }
        for &c in chain {
            if self.binary {
                self.put_binary_id(c);
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

    pub fn lrat_delete_clause(&mut self, id: i64) {
        self.delete_ids.push(id); // pushing off deletion for later
    }

    /*----------------------------------------------------------------------*/

    pub fn print_statistics(&mut self) {
        let bytes = self.file.bytes();
        let total = (self.added + self.deleted) as u64;
        msg!(
            self.internal,
            "LRAT {} added clauses {:.2}%",
            self.added,
            percent(self.added as f64, total as f64)
        );
        msg!(
            self.internal,
            "LRAT {} deleted clauses {:.2}%",
            self.deleted,
            percent(self.deleted as f64, total as f64)
        );
        msg!(
            self.internal,
            "LRAT {} bytes ({:.2} MB)",
            bytes,
            bytes as f64 / (1u64 << 20) as f64
        );
    }
}

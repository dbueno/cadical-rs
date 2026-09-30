//! Port of `drattracer.hpp` and `drattracer.cpp`.

use crate::file::File;
use crate::internal::Internal;
use crate::tracer::{FileTracer, InternalTracer, Tracer};

pub struct DratTracer {
    pub internal: *mut Internal,
    pub file: Box<File>,
    pub binary: bool,
    pub added: i64,
    pub deleted: i64,
}

impl Tracer for DratTracer {
    fn begin_proof(&mut self, _reserved_ids: i64) {} // skip
    fn add_original_clause(&mut self, _id: i64, _redundant: bool, _clause: &[i32], _restored: bool) {} // skip

    fn add_derived_clause(&mut self, _id: i64, _redundant: bool, _witness: i32, clause: &[i32], _chain: &[i64]) {
        if self.file.closed() {
            return;
        }
        log!(self.internal, "DRAT TRACER tracing addition of derived clause");
        self.drat_add_clause(clause);
        self.added += 1;
    }

    fn delete_clause(&mut self, _id: i64, _redundant: bool, clause: &[i32]) {
        if self.file.closed() {
            return;
        }
        log!(self.internal, "DRAT TRACER tracing deletion of clause");
        self.drat_delete_clause(clause);
        self.deleted += 1;
    }

    fn finalize_clause(&mut self, _id: i64, _clause: &[i32]) {} // skip
    fn report_status(&mut self, _status: i32, _id: i64) {} // skip
}

impl InternalTracer for DratTracer {
    fn connect_internal(&mut self, i: *mut Internal) {
        self.internal = i;
        self.file.connect_internal(self.internal);
        log!(self.internal, "DRAT TRACER connected to internal");
    }
}

impl FileTracer for DratTracer {
    fn closed(&mut self) -> bool {
        self.file.closed()
    }

    fn close(&mut self, print: bool) {
        debug_assert!(!self.closed());
        self.file.close(false);
        if print {
            msg!(self.internal, "DRAT proof file '{}' closed", self.file.name());
            self.print_statistics();
        }
    }

    fn flush(&mut self, print: bool) {
        debug_assert!(!self.closed());
        self.file.flush();
        if print {
            msg!(self.internal, "DRAT proof file '{}' flushed", self.file.name());
            self.print_statistics();
        }
    }
}

impl DratTracer {
    /// Owns and deletes 'file'.
    pub fn new(internal: *mut Internal, file: Box<File>, binary: bool) -> DratTracer {
        DratTracer { internal, file, binary, added: 0, deleted: 0 }
    }
}

impl Drop for DratTracer {
    fn drop(&mut self) {
        log!(self.internal, "DRAT TRACER delete");
        // 'file' is deleted with the box.
    }
}

/*------------------------------------------------------------------------*/

#[allow(unused_imports)]
use crate::prelude::*;

impl DratTracer {
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

    /*----------------------------------------------------------------------*/

    pub fn drat_add_clause(&mut self, clause: &[i32]) {
        if self.binary {
            self.file.put_char(b'a');
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
    }

    pub fn drat_delete_clause(&mut self, clause: &[i32]) {
        if self.binary {
            self.file.put_char(b'd');
        } else {
            self.file.put_str("d ");
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
    }

    /*----------------------------------------------------------------------*/

    pub fn print_statistics(&mut self) {
        let bytes = self.file.bytes();
        let total = (self.added + self.deleted) as u64;
        msg!(
            self.internal,
            "DRAT {} added clauses {:.2}%",
            self.added,
            percent(self.added as f64, total as f64)
        );
        msg!(
            self.internal,
            "DRAT {} deleted clauses {:.2}%",
            self.deleted,
            percent(self.deleted as f64, total as f64)
        );
        msg!(
            self.internal,
            "DRAT {} bytes ({:.2} MB)",
            bytes,
            bytes as f64 / (1u64 << 20) as f64
        );
    }
}

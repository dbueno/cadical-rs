//! Port of `occs.hpp` and `occs.cpp`.
//!
//! Full occurrence lists used in a one-watch scheme for all clauses in
//! subsumption checking and for irredundant clauses in variable elimination.

use crate::clause::CRef;
use crate::internal::Internal;
use crate::util::{erase_vector, shrink_vector};

pub type Occs = Vec<CRef>;

#[inline]
pub fn shrink_occs(os: &mut Occs) {
    shrink_vector(os)
}
#[inline]
pub fn erase_occs(os: &mut Occs) {
    erase_vector(os)
}

/// Remove the (unique) occurrence of `c` from `os`, keeping the order.
#[inline]
pub fn remove_occs(os: &mut Occs, c: CRef) {
    let end = os.len();
    let mut i = 0;
    for j in 0..end {
        let d = os[j];
        os[i] = d;
        i += 1;
        if c == d {
            i -= 1;
        }
    }
    debug_assert!(i + 1 == end);
    os.truncate(i);
}

impl Internal {
    pub fn init_occs(&mut self) {
        if self.otab.len() < 2 * self.vsize {
            self.otab.resize(2 * self.vsize, Occs::new());
        }
        log!(self, "initialized occurrence lists");
    }

    pub fn reset_occs(&mut self) {
        debug_assert!(self.occurring());
        erase_vector(&mut self.otab);
        log!(self, "reset occurrence lists");
    }

    pub fn clear_occs(&mut self) {
        debug_assert!(self.occurring());
        for occ in self.otab.iter_mut() {
            occ.clear();
        }
        log!(self, "clear occurrence lists");
    }

    /*--------------------------------------------------------------------*/

    // One-sided occurrence counter (each literal has its own counter).

    pub fn init_noccs(&mut self) {
        debug_assert!(self.ntab.is_empty());
        if self.ntab.len() < 2 * self.vsize {
            self.ntab.resize(2 * self.vsize, 0);
        }
        log!(self, "initialized two-sided occurrence counters");
    }

    pub fn clear_noccs(&mut self) {
        debug_assert!(!self.ntab.is_empty());
        for nt in self.ntab.iter_mut() {
            *nt = 0;
        }
        log!(self, "clear two-sided occurrence counters");
    }

    pub fn reset_noccs(&mut self) {
        debug_assert!(self.max_var == 0 || !self.ntab.is_empty());
        erase_vector(&mut self.ntab);
        log!(self, "reset two-sided occurrence counters");
    }
}

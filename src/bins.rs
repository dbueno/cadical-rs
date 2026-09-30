//! Port of `bins.hpp` and `bins.cpp` (binary implication graph lists).

use crate::internal::Internal;
use crate::util::{erase_vector, shrink_vector};

#[derive(Clone, Copy, Debug, Default)]
pub struct Bin {
    pub lit: i32,
    pub id: i64,
}

pub type Bins = Vec<Bin>;

#[inline]
pub fn shrink_bins(bs: &mut Bins) {
    shrink_vector(bs)
}
#[inline]
pub fn erase_bins(bs: &mut Bins) {
    erase_vector(bs)
}

impl Internal {
    pub fn init_bins(&mut self) {
        debug_assert!(self.big.is_empty());
        if self.big.len() < 2 * self.vsize {
            self.big.resize(2 * self.vsize, Bins::new());
        }
        log!(self, "initialized binary implication graph");
    }

    pub fn reset_bins(&mut self) {
        debug_assert!(!self.big.is_empty());
        erase_vector(&mut self.big);
        log!(self, "reset binary implication graph");
    }
}

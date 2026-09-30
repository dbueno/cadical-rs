//! Port of `range.hpp`: safe iteration over variables `1..=max_var`
//! (`Range`) and literals `-1,1,-2,2,...,-max_var,max_var` (`Sange`).
//!
//! As in C++ range-based `for` loops the bounds are evaluated once when
//! the iterator is created (a snapshot of `max_var`), so the iterator does
//! not borrow the solver and the loop body may modify it.

/// Iterates `1, ..., n` (safe for `n == 0` and `n == INT_MAX`).
#[derive(Clone, Copy, Debug)]
pub struct Range {
    idx: u32,
    end: u32,
}

impl Range {
    #[inline]
    pub fn new(n: i32) -> Range {
        debug_assert!(n >= 0);
        Range { idx: 1, end: (n as u32).wrapping_add(1) }
    }
    /// Reverse iteration from `n` down to `1`.
    #[inline]
    pub fn reversed(n: i32) -> RangeRev {
        debug_assert!(n >= 0);
        RangeRev { idx: n as u32, end: 0 }
    }
}

impl Iterator for Range {
    type Item = i32;
    #[inline]
    fn next(&mut self) -> Option<i32> {
        if self.idx == self.end {
            return None;
        }
        let res = self.idx as i32;
        self.idx = self.idx.wrapping_add(1);
        Some(res)
    }
}

/// Reverse `Range` (`rbegin ()` / `rend ()`).
#[derive(Clone, Copy, Debug)]
pub struct RangeRev {
    idx: u32,
    end: u32,
}

impl Iterator for RangeRev {
    type Item = i32;
    #[inline]
    fn next(&mut self) -> Option<i32> {
        if self.idx == self.end {
            return None;
        }
        let res = self.idx as i32;
        self.idx = self.idx.wrapping_sub(1);
        Some(res)
    }
}

/// Iterates over literals `-1, 1, -2, 2, ..., -n, n`.
#[derive(Clone, Copy, Debug)]
pub struct Sange {
    lit: u32,
    end: u32,
}

impl Sange {
    #[inline(always)]
    fn inc(u: u32) -> u32 {
        (!u).wrapping_add(u >> 31)
    }
    #[inline]
    pub fn new(n: i32) -> Sange {
        debug_assert!(n >= 0);
        Sange { lit: Sange::inc(0), end: Sange::inc(n as u32) }
    }
}

impl Iterator for Sange {
    type Item = i32;
    #[inline]
    fn next(&mut self) -> Option<i32> {
        if self.lit == self.end {
            return None;
        }
        let res = self.lit as i32;
        self.lit = Sange::inc(self.lit);
        Some(res)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn ranges() {
        assert_eq!(Range::new(3).collect::<Vec<_>>(), vec![1, 2, 3]);
        assert_eq!(Range::new(0).count(), 0);
        assert_eq!(Range::reversed(3).collect::<Vec<_>>(), vec![3, 2, 1]);
        assert_eq!(Sange::new(2).collect::<Vec<_>>(), vec![-1, 1, -2, 2]);
        assert_eq!(Sange::new(0).count(), 0);
    }
}

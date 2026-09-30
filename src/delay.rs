//! Port of `delay.hpp`.
//!
//! Note that `delay.hpp` is not included anywhere in CaDiCaL 3.0.1 (the
//! `Delay` used by `Internal` is the one in `limit.hpp`, see
//! [`crate::limit::Delay`]).  It is ported for completeness.

#[derive(Clone, Copy, Debug, Default)]
pub struct Delay {
    pub count: u32,
    pub current: u32,
}

impl Delay {
    pub fn new() -> Delay {
        Delay { count: 0, current: 0 }
    }
    #[inline]
    pub fn delay(&mut self) -> bool {
        if self.count != 0 {
            self.count -= 1;
            true
        } else {
            false
        }
    }
    #[inline]
    pub fn bump_delay(&mut self) {
        self.current += (self.current < u32::MAX) as u32;
        self.count = self.current;
    }
    #[inline]
    pub fn reduce_delay(&mut self) {
        if self.current == 0 {
            return;
        }
        self.current /= 2;
        self.count = self.current;
    }
}

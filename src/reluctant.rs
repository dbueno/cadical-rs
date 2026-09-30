//! Port of `reluctant.hpp`: Donald Knuth's version of the Luby restart
//! sequence ('reluctant doubling').

#[derive(Clone, Copy, Debug, Default)]
pub struct Reluctant {
    u: u64,
    v: u64,
    limit: u64,
    period: u64,
    countdown: u64,
    trigger: bool,
    limited: bool,
}

impl Reluctant {
    pub fn new() -> Reluctant {
        Reluctant::default()
    }

    pub fn enable(&mut self, p: i32, l: i64) {
        debug_assert!(p > 0);
        self.u = 1;
        self.v = 1;
        self.period = p as u64;
        self.countdown = p as u64;
        self.trigger = false;
        if l <= 0 {
            self.limited = false;
        } else {
            self.limited = true;
            self.limit = l as u64;
        }
    }

    pub fn disable(&mut self) {
        self.period = 0;
        self.trigger = false;
    }

    /// Increments the count until the 'period' is hit.  Then it performs
    /// the actual increment of reluctant doubling.
    pub fn tick(&mut self) {
        if self.period == 0 {
            return; // disabled
        }
        if self.trigger {
            return; // already triggered
        }
        self.countdown = self.countdown.wrapping_sub(1);
        if self.countdown != 0 {
            return; // not there yet
        }
        if (self.u & self.u.wrapping_neg()) == self.v {
            self.u = self.u.wrapping_add(1);
            self.v = 1;
        } else {
            self.v = self.v.wrapping_mul(2); // (DK)
        }
        if self.limited && self.v >= self.limit {
            self.u = 1;
            self.v = 1;
        }
        self.countdown = self.v.wrapping_mul(self.period);
        self.trigger = true;
    }

    /// `operator bool ()`: returns and clears the trigger.
    pub fn triggered(&mut self) -> bool {
        if !self.trigger {
            return false;
        }
        self.trigger = false;
        true
    }
}

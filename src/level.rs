//! Port of `level.hpp`.
//!
//! For each new decision we increase the decision level and push a `Level`
//! on the `control` stack.  The information gathered here is used in
//! `reuse_trail` and for early aborts in clause minimization.

#[derive(Clone, Copy, Debug, Default)]
pub struct LevelSeen {
    /// How many variables seen during 'analyze'.
    pub count: i32,
    /// Smallest trail position seen on this level.
    pub trail: i32,
}

#[derive(Clone, Copy, Debug, Default)]
pub struct Level {
    /// Decision literal of this level.
    pub decision: i32,
    /// Trail start of this level.
    pub trail: i32,
    pub seen: LevelSeen,
}

impl Level {
    #[inline]
    pub fn reset(&mut self) {
        self.seen.count = 0;
        self.seen.trail = i32::MAX;
    }
    /// `Level (int d, int t)`.
    #[inline]
    pub fn new(d: i32, t: i32) -> Level {
        let mut l = Level { decision: d, trail: t, seen: LevelSeen::default() };
        l.reset();
        l
    }
}

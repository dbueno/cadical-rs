//! Port of `score.hpp` and `score.cpp` (EVSIDS scores heap).

use crate::heap::{Heap, HeapLess};
use crate::internal::Internal;
use crate::random::Random;

/// `score_smaller` (defined in `internal.hpp` since it needs `Internal`).
#[derive(Clone, Copy, Debug)]
pub struct score_smaller {
    pub internal: *mut Internal,
}

impl score_smaller {
    pub fn new(i: *mut Internal) -> Self {
        score_smaller { internal: i }
    }
}

impl HeapLess for score_smaller {
    #[inline]
    fn less(&self, a: u32, b: u32) -> bool {
        // SAFETY: the heap lives inside 'Internal' which outlives it.
        let internal = unsafe { &*self.internal };
        // Avoid computing twice 'abs' in 'score ()'.
        debug_assert!(1 <= a);
        debug_assert!(a <= internal.max_var as u32);
        debug_assert!(1 <= b);
        debug_assert!(b <= internal.max_var as u32);
        let s = internal.stab[a as usize];
        let t = internal.stab[b as usize];
        if s < t {
            return true;
        }
        if s > t {
            return false;
        }
        a > b
    }
}

pub type ScoreSchedule = Heap<score_smaller>;

/*------------------------------------------------------------------------*/

// Port of 'score.cpp'.

impl Internal {
    /// This initializes variables on the binary 'scores' heap also with
    /// smallest variable index first (thus picked first) and larger indices
    /// at the end.
    pub fn init_scores(&mut self, old_max_var: i32, new_max_var: i32) {
        log!(self, "initializing EVSIDS scores from {} to {}", old_max_var + 1, new_max_var);
        for i in old_max_var..new_max_var {
            self.scores.push_back((i + 1) as u32);
        }
    }

    /// Shuffle the EVSIDS heap.
    pub fn shuffle_scores(&mut self) {
        if self.opts.shuffle == 0 {
            return;
        }
        if self.opts.shufflescores == 0 {
            return;
        }
        debug_assert!(self.level == 0);
        self.stats.shuffled += 1;
        log!(self, "shuffling scores");
        let mut shuffle: Vec<i32> = Vec::new();
        if self.opts.shufflerandom != 0 {
            self.scores.erase();
            let mut idx = self.max_var;
            while idx != 0 {
                shuffle.push(idx);
                idx -= 1;
            }
            let mut random = Random::new(self.opts.seed as u64); // global seed
            random += self.stats.shuffled as u64; // different every time
            let max_var = self.max_var;
            let mut i = 0;
            while i <= max_var - 2 {
                let j = random.pick_int(i, max_var - 1);
                shuffle.swap(i as usize, j as usize);
                i += 1;
            }
        } else {
            while !self.scores.empty() {
                let idx = self.scores.front() as i32;
                let _ = self.scores.pop_front();
                shuffle.push(idx);
            }
        }
        self.score_inc = 0.0;
        for &idx in &shuffle {
            self.stab[idx as usize] = self.score_inc;
            self.score_inc += 1.0;
            self.scores.push_back(idx as u32);
        }
    }
}

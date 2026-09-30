//! Port of `averages.hpp` and `averages.cpp`.

use crate::ema::EMA;
use crate::internal::Internal;

#[derive(Clone, Copy, Debug, Default)]
pub struct AveragesFastSlow {
    /// Average fast (small window) moving value.
    pub fast: EMA,
    /// Average slow (large window) moving value.
    pub slow: EMA,
}

#[derive(Clone, Copy, Debug, Default)]
pub struct AveragesSet {
    /// Glucose level.
    pub glue: AveragesFastSlow,
    /// Trail level.
    pub trail: AveragesFastSlow,
    pub decisions: EMA,
    /// Average learned clause size.
    pub size: EMA,
    /// Average (potential non-chronological) back-jump level.
    pub jump: EMA,
    /// Average back track level after conflict.
    pub level: EMA,
}

#[derive(Clone, Copy, Debug, Default)]
pub struct Averages {
    pub swapped: i64,
    pub current: AveragesSet,
    pub saved: AveragesSet,
}

impl Internal {
    pub fn init_averages(&mut self) {
        log!(self, "initializing averages");
        init_ema!(self, averages.current.jump, self.opts.emajump);
        init_ema!(self, averages.current.level, self.opts.emalevel);
        init_ema!(self, averages.current.size, self.opts.emasize);
        init_ema!(self, averages.current.glue.fast, self.opts.emagluefast);
        init_ema!(self, averages.current.glue.slow, self.opts.emaglueslow);
        init_ema!(self, averages.current.decisions, self.opts.emadecisions);
        init_ema!(self, averages.current.trail.fast, self.opts.ematrailfast);
        init_ema!(self, averages.current.trail.slow, self.opts.ematrailslow);
        debug_assert!(self.averages.swapped == 0);
    }

    pub fn swap_averages(&mut self) {
        log!(self, "saving current averages");
        std::mem::swap(&mut self.averages.current, &mut self.averages.saved);
        if self.averages.swapped == 0 {
            self.init_averages();
        } else {
            log!(self, "swapping in previously saved averages");
        }
        self.averages.swapped += 1;
    }
}

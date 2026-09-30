//! Port of `var.hpp` and `var.cpp`.

use crate::clause::CRef;
use crate::internal::Internal;

/// Data associated with an assigned variable.  None of these members is
/// valid unless the variable is assigned.  During unassigning a variable we
/// do not reset it.
#[derive(Clone, Copy, Debug, Default)]
#[repr(C)]
pub struct Var {
    /// Decision level.
    pub level: i32,
    /// Trail height at assignment.
    pub trail: i32,
    /// Implication graph edge during search.
    pub reason: CRef,
}

impl Internal {
    pub fn reset_subsume_bits(&mut self) {
        log!(self, "marking all variables as not subsume");
        for idx in self.vars() {
            self.flags_mut(idx).subsume = false;
        }
    }

    pub fn check_var_stats(&mut self) {
        #[cfg(debug_assertions)]
        {
            let (mut fixed, mut eliminated, mut substituted, mut pure, mut unused) =
                (0i64, 0i64, 0i64, 0i64, 0i64);
            for idx in self.vars() {
                let f = self.flags(idx);
                if f.active() {
                    continue;
                }
                if f.fixed() {
                    fixed += 1;
                }
                if f.eliminated() {
                    eliminated += 1;
                }
                if f.substituted() {
                    substituted += 1;
                }
                if f.unused() {
                    unused += 1;
                }
                if f.pure() {
                    pure += 1;
                }
            }
            debug_assert!(self.stats.now.fixed == fixed);
            debug_assert!(self.stats.now.eliminated == eliminated);
            debug_assert!(self.stats.now.substituted == substituted);
            debug_assert!(self.stats.now.pure == pure);
            let inactive = unused + fixed + eliminated + substituted + pure;
            debug_assert!(self.stats.inactive == inactive);
            debug_assert!(self.max_var as i64 == self.stats.active + self.stats.inactive);
        }
    }
}

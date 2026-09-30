//! Port of `phases.hpp` and `phases.cpp`.

use crate::internal::Internal;
use crate::util::sign;

#[derive(Clone, Debug, Default)]
pub struct Phases {
    /// The current largest trail phase.
    pub best: Vec<i8>,
    /// Forced through 'phase'.
    pub forced: Vec<i8>,
    /// Previous during local search.
    pub prev: Vec<i8>,
    /// The actual saved phase.
    pub saved: Vec<i8>,
    /// The current target phase.
    pub target: Vec<i8>,
}

/// Selects one of the phase vectors in [`Phases`].  The C++ functions
/// `copy_phases`, `save_assigned_phases` and `clear_phases` take a
/// `vector<signed char> &` which is always one of the members of
/// `Internal::phases`.  To avoid aliasing `&mut self` with a field we pass
/// a selector instead.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PhaseKind {
    Best,
    Forced,
    Prev,
    Saved,
    Target,
}

impl Phases {
    #[inline]
    pub fn get(&self, k: PhaseKind) -> &Vec<i8> {
        match k {
            PhaseKind::Best => &self.best,
            PhaseKind::Forced => &self.forced,
            PhaseKind::Prev => &self.prev,
            PhaseKind::Saved => &self.saved,
            PhaseKind::Target => &self.target,
        }
    }
    #[inline]
    pub fn get_mut(&mut self, k: PhaseKind) -> &mut Vec<i8> {
        match k {
            PhaseKind::Best => &mut self.best,
            PhaseKind::Forced => &mut self.forced,
            PhaseKind::Prev => &mut self.prev,
            PhaseKind::Saved => &mut self.saved,
            PhaseKind::Target => &mut self.target,
        }
    }
}

/*------------------------------------------------------------------------*/

// Port of 'phases.cpp'.

impl Internal {
    /// Copy 'saved' to the selected phases (`copy_phases (dst)`).
    pub fn copy_phases(&mut self, dst: PhaseKind) {
        start!(self, copy);
        for i in self.vars() {
            let tmp = self.phases.saved[i as usize];
            if tmp != 0 {
                self.phases.get_mut(dst)[i as usize] = tmp;
            }
        }
        stop!(self, copy);
    }

    /// Save assigned literals to the selected phases.
    pub fn save_assigned_phases(&mut self, dst: PhaseKind) {
        start!(self, copy);
        for i in self.vars() {
            let v = self.val(i);
            if v != 0 {
                self.phases.get_mut(dst)[i as usize] = v;
            }
        }
        stop!(self, copy);
    }

    /// Reset the selected phases to zero.
    pub fn clear_phases(&mut self, dst: PhaseKind) {
        start!(self, copy);
        for i in self.vars() {
            self.phases.get_mut(dst)[i as usize] = 0;
        }
        stop!(self, copy);
    }

    pub fn phase(&mut self, lit: i32) {
        let idx = self.vidx(lit);
        let old_forced_phase = self.phases.forced[idx as usize];
        let new_forced_phase = sign(lit) as i8;
        if old_forced_phase == new_forced_phase {
            log!(self, "forced phase remains at {}", old_forced_phase as i32 * idx);
            return;
        }
        if old_forced_phase != 0 {
            log!(self, "overwriting old forced phase {}", old_forced_phase as i32 * idx);
        }
        log!(self, "new forced phase {}", new_forced_phase as i32 * idx);
        self.phases.forced[idx as usize] = new_forced_phase;
    }

    pub fn unphase(&mut self, lit: i32) {
        let idx = self.vidx(lit);
        let old_forced_phase = self.phases.forced[idx as usize];
        if old_forced_phase == 0 {
            log!(self, "forced phase of {} already reset", lit);
            return;
        }
        log!(self, "clearing old forced phase {}", old_forced_phase as i32 * idx);
        self.phases.forced[idx as usize] = 0;
    }
}

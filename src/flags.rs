//! Port of `flags.hpp` and `flags.cpp` (variable and literal flags).
//!
//! The C++ bit-fields are plain fields here.  The two bit wide fields
//! (`marked_signed`, `factor`, `block`, `skip`, `assumed`, `failed`) are
//! `u8` holding values in `0..=3` (bit `1` for the positive and bit `2`
//! for the negative literal, see `bign`), `status` holds `0..=5`.

use crate::internal::Internal;

#[derive(Clone, Copy, Debug)]
pub struct Flags {
    // The first set of flags is related to 'analyze' and 'minimize'.
    /// Seen in generating first UIP clause in 'analyze'.
    pub seen: bool,
    /// Keep in learned clause in 'minimize'.
    pub keep: bool,
    /// Can not be removed in 'minimize'.
    pub poison: bool,
    /// Can be removed in 'minimize'.
    pub removable: bool,
    /// Can be removed in 'shrink'.
    pub shrinkable: bool,
    /// Has already been added to lrat_chain (in 'minimize').
    pub added: bool,

    // These three variable flags are used to schedule clauses in
    // subsumption ('subsume'), variables in bounded variable elimination
    // ('elim') and in hyper ternary resolution ('ternary').
    /// Removed since last 'elim' round (*).
    pub elim: bool,
    /// Added since last 'subsume' round (*).
    pub subsume: bool,
    /// Added in ternary clause since last 'ternary' (*).
    pub ternary: bool,
    pub sweep: bool,
    pub blockable: bool,

    /// Generate correct LRAT chains in decompose (2 bits).
    pub marked_signed: u8,
    /// 2 bits.
    pub factor: u8,

    // These literal flags are used by blocked clause elimination ('block').
    /// Removed since last 'block' round (*) (2 bits).
    pub block: u8,
    /// Skip this literal as blocking literal (2 bits).
    pub skip: u8,

    pub backbone1: bool,
    pub backbone0: bool,

    // Bits for handling assumptions.
    /// 2 bits.
    pub assumed: u8,
    /// 0 if not part of failure, 1 if positive lit is in failure, 2 if
    /// negated lit is in failure (2 bits).
    pub failed: u8,

    pub factored_but_on_reconstruction_stack: bool,

    /// One of `UNUSED`, `ACTIVE`, `FIXED`, `ELIMINATED`, `SUBSTITUTED`,
    /// `PURE` (3 bits).
    pub status: u8,
}

impl Flags {
    pub const UNUSED: u8 = 0;
    pub const ACTIVE: u8 = 1;
    pub const FIXED: u8 = 2;
    pub const ELIMINATED: u8 = 3;
    pub const SUBSTITUTED: u8 = 4;
    pub const PURE: u8 = 5;

    /// Initialized explicitly in 'Internal::init' through this function.
    pub fn new() -> Flags {
        Flags {
            seen: false,
            keep: false,
            poison: false,
            removable: false,
            shrinkable: false,
            added: false,
            elim: true,
            subsume: true,
            ternary: true,
            sweep: false,
            // Not initialized in the C++ constructor (bit-field storage is
            // zero initialized by 'vector::resize' value-initialization of
            // the enclosing storage in practice).
            blockable: false,
            marked_signed: 0,
            factor: 0,
            block: 3,
            skip: 0,
            backbone1: false,
            backbone0: false,
            assumed: 0,
            failed: 0,
            // Also not initialized in the C++ constructor.
            factored_but_on_reconstruction_stack: false,
            status: Flags::UNUSED,
        }
    }

    #[inline(always)]
    pub fn unused(&self) -> bool {
        self.status == Flags::UNUSED
    }
    #[inline(always)]
    pub fn active(&self) -> bool {
        self.status == Flags::ACTIVE
    }
    #[inline(always)]
    pub fn fixed(&self) -> bool {
        self.status == Flags::FIXED
    }
    #[inline(always)]
    pub fn eliminated(&self) -> bool {
        self.status == Flags::ELIMINATED
    }
    #[inline(always)]
    pub fn substituted(&self) -> bool {
        self.status == Flags::SUBSTITUTED
    }
    #[inline(always)]
    pub fn pure(&self) -> bool {
        self.status == Flags::PURE
    }

    /// The flags marked with '(*)' are copied during 'External::copy_flags',
    /// which in essence means they are reset in the copy if they were
    /// clear.  This avoids the effort of fruitless preprocessing the copy.
    pub fn copy(&self, dst: &mut Flags) {
        dst.elim = self.elim;
        dst.subsume = self.subsume;
        dst.ternary = self.ternary;
        dst.block = self.block;
        dst.sweep = self.sweep;
        dst.backbone0 = self.backbone0;
        dst.backbone1 = self.backbone1;
        dst.added = self.added;
        dst.factor = self.factor;
        // seen, keep, poison, removable, shrinkable are unused
    }
}

impl Default for Flags {
    fn default() -> Self {
        Flags::new()
    }
}

/*------------------------------------------------------------------------*/

// Port of 'flags.cpp'.

impl Internal {
    pub fn mark_fixed(&mut self, lit: i32) {
        if self.external().fixed_listener.is_some() {
            let elit = self.externalize(lit);
            debug_assert!(elit != 0);
            let eidx = elit.abs();
            let external = self.external();
            if !external.ervars[eidx as usize] {
                if let Some(listener) = external.fixed_listener.as_mut() {
                    listener.notify_fixed_assignment(elit);
                }
            }
        }
        {
            let f = self.flags_mut(lit);
            debug_assert!(f.status == Flags::ACTIVE);
            f.status = Flags::FIXED;
        }
        log!(self, "fixed {}", lit.abs());
        self.stats.all.fixed += 1;
        self.stats.now.fixed += 1;
        self.stats.inactive += 1;
        debug_assert!(self.stats.active != 0);
        self.stats.active -= 1;
        debug_assert!(!self.active(lit));
        debug_assert!(self.flags(lit).fixed());
        if self.external_prop && self.private_steps {
            // If pre/inprocessing found a fixed assignment, we want the
            // propagator to know about it.  But at that point it is not
            // guaranteed to be already on the trail, so notification will
            // happen only later.
            debug_assert!(self.level == 0 || self.in_mode(crate::internal::Mode::BACKBONE));
        }
    }

    pub fn mark_eliminated(&mut self, lit: i32) {
        {
            let f = self.flags_mut(lit);
            debug_assert!(f.status == Flags::ACTIVE);
            f.status = Flags::ELIMINATED;
        }
        log!(self, "eliminated {}", lit.abs());
        self.stats.all.eliminated += 1;
        self.stats.now.eliminated += 1;
        self.stats.inactive += 1;
        debug_assert!(self.stats.active != 0);
        self.stats.active -= 1;
        debug_assert!(!self.active(lit));
        debug_assert!(self.flags(lit).eliminated());
    }

    pub fn mark_pure(&mut self, lit: i32) {
        {
            let f = self.flags_mut(lit);
            debug_assert!(f.status == Flags::ACTIVE);
            f.status = Flags::PURE;
        }
        log!(self, "pure {}", lit.abs());
        self.stats.all.pure += 1;
        self.stats.now.pure += 1;
        self.stats.inactive += 1;
        debug_assert!(self.stats.active != 0);
        self.stats.active -= 1;
        debug_assert!(!self.active(lit));
        debug_assert!(self.flags(lit).pure());
    }

    pub fn mark_substituted(&mut self, lit: i32) {
        {
            let f = self.flags_mut(lit);
            debug_assert!(f.status == Flags::ACTIVE);
            f.status = Flags::SUBSTITUTED;
        }
        log!(self, "substituted {}", lit.abs());
        self.stats.all.substituted += 1;
        self.stats.now.substituted += 1;
        self.stats.inactive += 1;
        debug_assert!(self.stats.active != 0);
        self.stats.active -= 1;
        debug_assert!(!self.active(lit));
        debug_assert!(self.flags(lit).substituted());
    }

    pub fn mark_active(&mut self, lit: i32) {
        {
            let f = self.flags_mut(lit);
            debug_assert!(f.status == Flags::UNUSED);
            f.status = Flags::ACTIVE;
        }
        log!(self, "activate {} previously unused", lit.abs());
        debug_assert!(self.stats.inactive != 0);
        self.stats.inactive -= 1;
        debug_assert!(self.stats.unused != 0);
        self.stats.unused -= 1;
        self.stats.active += 1;
        debug_assert!(self.active(lit));
    }

    pub fn reactivate(&mut self, lit: i32) {
        debug_assert!(!self.active(lit));
        let status = self.flags(lit).status;
        debug_assert!(status != Flags::FIXED);
        debug_assert!(status != Flags::UNUSED);
        #[cfg(feature = "logging")]
        let msg: &str;
        match status {
            Flags::SUBSTITUTED => {
                #[cfg(feature = "logging")]
                {
                    msg = "substituted";
                }
                debug_assert!(self.stats.now.substituted > 0);
                self.stats.now.substituted -= 1;
            }
            Flags::PURE => {
                #[cfg(feature = "logging")]
                {
                    msg = "pure literal";
                }
                debug_assert!(self.stats.now.pure > 0);
                self.stats.now.pure -= 1;
            }
            _ => {
                debug_assert!(status == Flags::ELIMINATED);
                debug_assert!(self.stats.now.eliminated > 0);
                self.stats.now.eliminated -= 1;
                #[cfg(feature = "logging")]
                {
                    msg = "eliminated";
                }
            }
        }
        log!(self, "reactivate previously {} {}", msg, lit.abs());
        {
            let f = self.flags_mut(lit);
            f.status = Flags::ACTIVE;
            f.sweep = false;
        }
        debug_assert!(self.active(lit));
        self.stats.reactivated += 1;
        debug_assert!(self.stats.inactive > 0);
        self.stats.inactive -= 1;
        self.stats.active += 1;
    }
}

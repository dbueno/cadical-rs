//! Port of `internal.hpp` (the `Internal` solver state and all inline
//! member functions) and of the constructor / destructor and
//! `enlarge_vals` from `internal.cpp`.  All other functions of
//! `internal.cpp` are at the end of this file.
//!
//! See "Internal layout" in `PORTING.md` for the design decisions.

use std::sync::atomic::{AtomicBool, Ordering::Relaxed};
use std::sync::Arc;

use crate::arena::Arena;
use crate::averages::Averages;
use crate::bins::Bins;
use crate::clause::{external_reason_clause, CRef, Clause};
use crate::external::External;
use crate::flags::Flags;
use crate::format::Format;
use crate::kitten::Kitten;
use crate::level::Level;
use crate::limit::{Delay, Inc, Last, Limit};
use crate::occs::Occs;
use crate::options::Options;
use crate::phases::Phases;
use crate::profile::Profiles;
use crate::proof::Proof;
use crate::queue::{Link, Links, Queue};
use crate::range::{Range, Sange};
use crate::reap::Reap;
use crate::reluctant::Reluctant;
use crate::score::{score_smaller, ScoreSchedule};
use crate::stats::Stats;
use crate::tracer::{FileTracer, StatTracer, Tracer};
use crate::util::{bign, relative, sign};
use crate::var::Var;
use crate::watch::{remove_watch, Watch, Watches};

/// `struct CubesWithStatus` (result of `generate_cubes`).
#[derive(Clone, Debug, Default)]
pub struct CubesWithStatus {
    pub status: i32,
    pub cubes: Vec<Vec<i32>>,
}

/// `Internal::Mode`: the internal state of the solver (bit masks).
#[allow(non_snake_case)]
pub struct Mode;

impl Mode {
    pub const BLOCK: i32 = 1 << 0;
    pub const CONDITION: i32 = 1 << 1;
    pub const CONGRUENCE: i32 = 1 << 2;
    pub const COVER: i32 = 1 << 3;
    pub const DECOMP: i32 = 1 << 4;
    pub const DEDUP: i32 = 1 << 5;
    pub const ELIM: i32 = 1 << 6;
    pub const FACTOR: i32 = 1 << 7;
    pub const LUCKY: i32 = 1 << 8;
    pub const PROBE: i32 = 1 << 9;
    pub const SEARCH: i32 = 1 << 10;
    pub const SIMPLIFY: i32 = 1 << 11;
    pub const SUBSUME: i32 = 1 << 12;
    pub const SWEEP: i32 = 1 << 13;
    pub const TERNARY: i32 = 1 << 14;
    pub const TRANSRED: i32 = 1 << 15;
    pub const VIVIFY: i32 = 1 << 16;
    pub const WALK: i32 = 1 << 17;
    pub const BACKBONE: i32 = 1 << 18;
}

/// Anything that gives access to the `Internal` solver (used by the
/// `log!`, `msg!`, `verbose!`, `phase!` and `warning!` macros, so that
/// their first argument can be `self` in `Internal` methods, `self` in
/// `External` methods, or a raw `*mut Internal` back pointer as kept by
/// `Proof`, the tracers, `Closure`, `Sweeper`, ...).
pub trait InternalRef {
    fn internal_ref(&self) -> &Internal;
}

impl InternalRef for Internal {
    #[inline(always)]
    fn internal_ref(&self) -> &Internal {
        self
    }
}

impl InternalRef for *mut Internal {
    #[inline(always)]
    fn internal_ref(&self) -> &Internal {
        // SAFETY: back pointers to the owning 'Internal' are always valid
        // while the object holding them is alive.
        unsafe { &**self }
    }
}

impl InternalRef for *const Internal {
    #[inline(always)]
    fn internal_ref(&self) -> &Internal {
        // SAFETY: see above.
        unsafe { &**self }
    }
}

impl InternalRef for External {
    #[inline(always)]
    fn internal_ref(&self) -> &Internal {
        // SAFETY: see above.
        unsafe { &*self.internal }
    }
}

pub struct Internal {
    /*----------------------------------------------------------------------*/

    /// Current internal state (see [`Mode`]).
    pub mode: i32,
    /// tier1 limit for 0=focused, 1=stable; aka `tier1[stable]`
    pub tier1: [i32; 2],
    /// tier2 limit for 0=focused, 1=stable; aka `tier1[stable]`
    pub tier2: [i32; 2],
    /// Empty clause found or learned.
    pub unsat: bool,
    /// Report learned unit ('i' line).
    pub iterating: bool,
    /// True during local search.
    pub localsearching: bool,
    /// True during look ahead.
    pub lookingahead: bool,
    /// True during preprocessing.
    pub preprocessing: bool,
    /// Referenced reasons are protected.
    pub protected_reasons: bool,
    /// Force saved phase in decision.
    pub force_saved_phase: bool,
    /// During 'lucky_phases'.
    pub searching_lucky_phases: bool,
    /// True during stabilization phase.
    pub stable: bool,
    /// Reported in this solving call.
    pub reported: bool,
    /// True if an external propagator is connected.
    pub external_prop: bool,
    /// True if ext. propagation happened.
    pub did_external_prop: bool,
    /// True if the external propagator is lazy.
    pub external_prop_is_lazy: bool,
    /// External propagator can force backtracking.
    pub forced_backt_allowed: bool,
    /// No notification of ext. prop during these steps.
    pub private_steps: bool,
    /// Lowest out-of-order level to fix.
    pub out_of_order_level: i32,
    /// Highest out-of-order literal on the trail.
    pub out_of_order_trail: i32,
    /// Last type of resetting phases (C++ `char`).
    pub rephased: u8,
    /// Restart counter in stable mode.
    pub reluctant: Reluctant,
    /// Actually allocated variable data size.
    pub vsize: usize,
    /// Internal maximum variable index.
    pub max_var: i32,
    /// Last used id for clauses.
    pub clause_id: i64,
    /// Ids for original clauses to produce LRAT.
    pub original_id: i64,
    /// Number of reserved ids for original clauses.
    pub reserved_ids: i64,
    /// Store conflict id for finalize (frat).
    pub conflict_id: i64,
    /// To compute decision rate average.
    pub saved_decisions: i64,
    /// Keeps track of conclude.
    pub concluded: bool,
    /// Store ids of conclusion clauses.
    pub conclusion: Vec<i64>,
    /// Keep track of unit_clauses (LRAT/FRAT).
    pub unit_clauses_idx: Vec<i64>,
    /// Create LRAT in solver: option lratdirect.
    pub lrat_chain: Vec<i64>,
    /// Used to create LRAT in minimize.
    pub mini_chain: Vec<i64>,
    /// Used to create LRAT in minimize.
    pub minimize_chain: Vec<i64>,
    /// Used to avoid duplicate units.
    pub unit_chain: Vec<i64>,
    /// For LRAT in instantiate.
    pub inst_chain: Vec<CRef>,
    /// Only used if opts.probehbr=false.
    pub probehbr_chains: Vec<Vec<Vec<i64>>>,
    /// Generate LRAT internally.
    pub lrat: bool,
    /// Finalize non-deleted clauses in proof.
    pub frat: bool,
    /// Decision level ('control.size () - 1').
    pub level: i32,
    /// Saved, target and best phases.
    pub phases: Phases,
    /// Assignment `[-max_var,max_var]`: points into `vals_storage` at
    /// offset `vsize` (of the allocation), so `*vals.offset (lit)` is the
    /// value of `lit`.  Use `val (lit)` / `set_val (lit, v)`.
    pub vals: *mut i8,
    /// Owning storage of `vals` (size `2 * vsize` of the allocation).
    pub vals_storage: Vec<i8>,
    /// Signed marks `[1,max_var]`.
    pub marks: Vec<i8>,
    /// Frozen counters `[1,max_var]`.
    pub frozentab: Vec<u32>,
    /// Maps internal 'idx' to external 'lit'.
    pub i2e: Vec<i32>,
    /// Reference counts for observed variables.
    pub relevanttab: Vec<u32>,
    /// Variable move to front decision queue.
    pub queue: Queue,
    /// Table of links for decision queue.
    pub links: Links,
    /// Current score increment.
    pub score_inc: f64,
    /// Score based decision priority queue.
    pub scores: ScoreSchedule,
    /// Table of variable scores `[1,max_var]`.
    pub stab: Vec<f64>,
    /// Variable table `[1,max_var]`.
    pub vtab: Vec<Var>,
    /// Parent literals during probing.
    pub parents: Vec<i32>,
    /// Variable and literal flags.
    pub ftab: Vec<Flags>,
    /// Enqueue time stamps for queue.
    pub btab: Vec<i64>,
    /// Time stamp table to recompute glue.
    pub gtab: Vec<i64>,
    /// Table of occurrences for all literals.
    pub otab: Vec<Occs>,
    /// Table of redundant occurrences.
    pub rtab: Vec<Occs>,
    /// Table for caching probing attempts.
    pub ptab: Vec<i32>,
    /// Number of one-sided occurrences table.
    pub ntab: Vec<i64>,
    /// Binary implication graph.
    pub big: Vec<Bins>,
    /// Table of watches for all literals.
    pub wtab: Vec<Watches>,
    /// Set in 'propagation', reset in 'analyze'.
    pub conflict: CRef,
    /// Ignored during 'vivify_propagate'.
    pub ignore: CRef,
    /// Dummy binary clause for subsumption.
    pub dummy_binary: CRef,
    /// Used as reason at external propagations.
    pub external_reason: CRef,
    /// Used in external_propagate.
    pub newest_clause: CRef,
    /// For new clauses with external propagator.
    pub force_no_backtrack: bool,
    /// Differentiate new clauses...
    pub from_propagator: bool,
    /// Is new clause from propagator forgettable.
    pub ext_clause_forgettable: bool,
    /// Used for ILB.
    pub changed_val: i32,
    /// Next trail position to notify external prop.
    pub notified: usize,
    /// Current level of external prop.
    pub notified_level: i32,
    /// Set during probing.
    pub probe_reason: CRef,
    /// Next trail position to propagate.
    pub propagated: usize,
    /// Next binary trail position to propagate.
    pub propagated2: usize,
    /// Propagated without blocking literals.
    pub propergated: usize,
    /// Best maximum assigned ever.
    pub best_assigned: usize,
    /// Maximum assigned without conflict.
    pub target_assigned: usize,
    /// Largest trail prefix without conflict.
    pub no_conflict_until: usize,
    /// Currently assigned literals.
    pub trail: Vec<i32>,
    /// Simplified in parsing & learning.
    pub clause: Vec<i32>,
    /// Assumed literals.
    pub assumptions: Vec<i32>,
    /// Literals of the constraint.
    pub constraint: Vec<i32>,
    /// Constraint used for unsatisfiability?
    pub unsat_constraint: bool,
    /// Are the failed assumptions marked?
    pub marked_failed: bool,
    /// Original added literals.
    pub original: Vec<i32>,
    /// Decision levels in learned clause.
    pub levels: Vec<i32>,
    /// Analyzed literals in 'analyze'.
    pub analyzed: Vec<i32>,
    /// To avoid duplicate units in lrat_chain.
    pub unit_analyzed: Vec<i32>,
    /// Literals skipped in 'decompose'.
    pub sign_marked: Vec<i32>,
    /// Removable or poison in 'minimize'.
    pub minimized: Vec<i32>,
    /// Removable or poison in 'shrink'.
    pub shrinkable: Vec<i32>,
    /// Radix heap for shrink.
    pub reap: Reap,
    /// Boolean indicated that we have done the resize 1.
    pub factorcheckdone: bool,

    /// Remember sweep varibles to reschedule.
    pub sweep_schedule: Vec<i32>,
    /// Sweep.
    pub sweep_incomplete: bool,
    pub randomized_deciding: u64,

    /// `kitten *citten`.
    pub citten: Option<Box<Kitten>>,

    /// Check for satisfied.
    pub num_assigned: usize,

    /// Remaining scheduled probes.
    pub probes: Vec<i32>,
    /// 'level + 1 == control.size ()'.
    pub control: Vec<Level>,
    /// Ordered collection of all clauses.
    pub clauses: Vec<CRef>,
    /// Glue, size, jump moving averages.
    pub averages: Averages,
    /// Delay certain functions.
    pub delay: [Delay; 2],
    /// Delay congruence if not successful recently.
    pub congruence_delay: Delay,
    /// Limits for various phases.
    pub lim: Limit,
    /// Statistics at last occurrence.
    pub last: Last,
    /// Increments on limits.
    pub inc: Inc,

    pub delaying_vivify_irredundant: Delay,
    pub delaying_sweep: Delay,

    /// Abstraction layer between solver and tracers.
    pub proof: Option<Box<Proof>>,
    /// Proof tracing objects (ie interpolant calculator).  Owned (C++
    /// deletes still connected tracers in `~Internal`).
    pub tracers: Vec<Box<dyn Tracer>>,
    /// File proof tracers (ie DRAT, LRAT...).
    pub file_tracers: Vec<Box<dyn FileTracer>>,
    /// Checkers.
    pub stat_tracers: Vec<Box<dyn StatTracer>>,

    /// Run-time options.
    pub opts: Options,
    /// Statistics.
    pub stats: Stats,
    /// Time profiles for various functions.
    pub profiles: Profiles,
    /// Force 'phase (...)' messages.
    pub force_phase_messages: bool,
    /// Memory arena for moving garbage collector.
    pub arena: Arena,
    /// Provide persistent error message.
    pub error_message: Format,
    /// Verbose messages prefix.
    pub prefix: String,

    // 'Internal *internal' (proxy to 'this' in macros) is not needed: the
    // Rust macros take the internal explicitly (usually 'self').
    /// Proxy to 'external' buddy in 'Solver'.
    pub external: *mut External,

    /*----------------------------------------------------------------------*/

    /// Asynchronous termination flag written by 'terminate' and read by
    /// 'terminated_asynchronously'.  Shared (`Arc`) so that a
    /// [`crate::solver::TerminationHandle`] can set it from another thread.
    pub termination_forced: Arc<AtomicBool>,
}

impl Internal {
    /// Must fit into the header of the clause!
    pub const MAX_USED: u32 = 31;

    /*----------------------------------------------------------------------*/

    /// `Internal ()` (from 'internal.cpp').  Boxed since several members
    /// keep a back pointer to the `Internal`.
    pub fn new() -> Box<Internal> {
        // Two phase initialization: members with back pointers are
        // initialized with a null pointer first and then patched.
        let null: *mut Internal = std::ptr::null_mut();
        let mut internal = Box::new(Internal {
            mode: Mode::SEARCH,
            tier1: [2, 2],
            tier2: [6, 6],
            unsat: false,
            iterating: false,
            localsearching: false,
            lookingahead: false,
            preprocessing: false,
            protected_reasons: false,
            force_saved_phase: false,
            searching_lucky_phases: false,
            stable: false,
            reported: false,
            external_prop: false,
            did_external_prop: false,
            external_prop_is_lazy: true,
            forced_backt_allowed: false,
            private_steps: false,
            out_of_order_level: -1,
            out_of_order_trail: -1,
            rephased: 0,
            reluctant: Reluctant::new(),
            vsize: 0,
            max_var: 0,
            clause_id: 0,
            original_id: 0,
            reserved_ids: 0,
            conflict_id: 0,
            saved_decisions: 0,
            concluded: false,
            conclusion: Vec::new(),
            unit_clauses_idx: Vec::new(),
            lrat_chain: Vec::new(),
            mini_chain: Vec::new(),
            minimize_chain: Vec::new(),
            unit_chain: Vec::new(),
            inst_chain: Vec::new(),
            probehbr_chains: Vec::new(),
            lrat: false,
            frat: false,
            level: 0,
            phases: Phases::default(),
            vals: std::ptr::null_mut(),
            vals_storage: Vec::new(),
            marks: Vec::new(),
            frozentab: Vec::new(),
            i2e: Vec::new(),
            relevanttab: Vec::new(),
            queue: Queue::default(),
            links: Vec::new(),
            score_inc: 1.0,
            scores: ScoreSchedule::new(score_smaller::new(null)),
            stab: Vec::new(),
            vtab: Vec::new(),
            parents: Vec::new(),
            ftab: Vec::new(),
            btab: Vec::new(),
            gtab: Vec::new(),
            otab: Vec::new(),
            rtab: Vec::new(),
            ptab: Vec::new(),
            ntab: Vec::new(),
            big: Vec::new(),
            wtab: Vec::new(),
            conflict: CRef::NULL,
            ignore: CRef::NULL,
            dummy_binary: CRef::NULL,
            external_reason: external_reason_clause(),
            newest_clause: CRef::NULL,
            force_no_backtrack: false,
            from_propagator: false,
            ext_clause_forgettable: false,
            changed_val: 0,
            notified: 0,
            notified_level: 0,
            probe_reason: CRef::NULL,
            propagated: 0,
            propagated2: 0,
            propergated: 0,
            best_assigned: 0,
            target_assigned: 0,
            no_conflict_until: 0,
            trail: Vec::new(),
            clause: Vec::new(),
            assumptions: Vec::new(),
            constraint: Vec::new(),
            unsat_constraint: false,
            marked_failed: true,
            original: Vec::new(),
            levels: Vec::new(),
            analyzed: Vec::new(),
            unit_analyzed: Vec::new(),
            sign_marked: Vec::new(),
            minimized: Vec::new(),
            shrinkable: Vec::new(),
            reap: Reap::new(),
            factorcheckdone: false,
            sweep_schedule: Vec::new(),
            sweep_incomplete: false,
            randomized_deciding: 0,
            citten: None,
            num_assigned: 0,
            probes: Vec::new(),
            control: Vec::new(),
            clauses: Vec::new(),
            averages: Averages::default(),
            delay: [Delay::default(); 2],
            congruence_delay: Delay::default(),
            lim: Limit::new(),
            last: Last::new(),
            inc: Inc::new(),
            delaying_vivify_irredundant: Delay::default(),
            delaying_sweep: Delay::default(),
            proof: None,
            tracers: Vec::new(),
            file_tracers: Vec::new(),
            stat_tracers: Vec::new(),
            opts: Options::new(null),
            stats: Stats::new(),
            profiles: Profiles::new(null),
            force_phase_messages: false,
            arena: Arena::new(null),
            error_message: Format::new(),
            prefix: String::from("c "),
            external: std::ptr::null_mut(),
            termination_forced: Arc::new(AtomicBool::new(false)),
        });
        let this: *mut Internal = &mut *internal;
        internal.scores.less.internal = this;
        internal.opts.internal = this;
        internal.profiles.internal = this;
        internal.arena.internal = this;

        internal.control.push(Level::new(0, 0));

        // The 'dummy_binary' is used in 'try_to_subsume_clause' to fake a
        // real clause (which then can be used to subsume or strengthen the
        // given clause in one routine for both binary and non binary
        // clauses) and in walk (which is only used as a placeholder in the
        // watch lists when logging is off, since the clause is not
        // accessed).  This fake binary clause is always kept non-redundant
        // (and not-moved etc.) due to the following zero initialization.
        // Only literals will be changed.
        let bytes = Clause::bytes_for(2);
        // SAFETY: allocation of a zeroed binary clause.
        let p = unsafe { libc::calloc(1, bytes) } as *mut Clause;
        if p.is_null() {
            crate::message::fatal(format_args!("out of memory allocating dummy binary"));
        }
        let dummy = CRef(p);
        dummy.set_size(2);
        internal.dummy_binary = dummy;

        debug_assert!(Internal::MAX_USED == (1 << crate::clause::USED_SIZE) - 1);
        internal
    }

    /*----------------------------------------------------------------------*/

    /// Values in 'vals' can be accessed in the range '[-max_var,max_var]'
    /// that is directly by a literal.  This is crucial for performance.
    pub fn enlarge_vals(&mut self, new_vsize: usize) {
        let bytes = 2 * new_vsize;
        let mut new_storage: Vec<i8> = vec![0; bytes];
        // SAFETY: 'new_vsize' is within the new allocation.
        let new_vals = unsafe { new_storage.as_mut_ptr().add(new_vsize) };
        if !self.vals.is_null() {
            let mv = self.max_var as usize;
            // SAFETY: both ranges '[-max_var,max_var]' are valid.
            unsafe {
                std::ptr::copy_nonoverlapping(self.vals.sub(mv), new_vals.sub(mv), 2 * mv + 1);
            }
        } else {
            debug_assert!(self.vsize == 0);
        }
        self.vals_storage = new_storage;
        self.vals = new_vals;
    }

    /*----------------------------------------------------------------------*/

    /// Back pointer to the `External` buddy in `Solver`.
    #[inline(always)]
    #[allow(clippy::mut_from_ref)]
    pub fn external(&self) -> &mut External {
        debug_assert!(!self.external.is_null());
        // SAFETY: 'External' is owned by the same 'Solver' and lives at a
        // stable address as long as this 'Internal'.
        unsafe { &mut *self.external }
    }

    /// Safe variable iteration `1..=max_var` (snapshot of 'max_var').
    #[inline(always)]
    pub fn vars(&self) -> Range {
        Range::new(self.max_var)
    }

    /// Safe literal iteration `-1,1,...,-max_var,max_var`.
    #[inline(always)]
    pub fn lits(&self) -> Sange {
        Sange::new(self.max_var)
    }

    /*----------------------------------------------------------------------*/

    #[inline(always)]
    pub fn in_mode(&self, m: i32) -> bool {
        (self.mode & m) != 0
    }
    #[inline(always)]
    pub fn set_mode(&mut self, m: i32) {
        debug_assert!(self.mode & m == 0);
        self.mode |= m;
    }
    #[inline(always)]
    pub fn reset_mode(&mut self, m: i32) {
        debug_assert!(self.mode & m != 0);
        self.mode &= !m;
    }
    #[inline(always)]
    pub fn require_mode(&self, m: i32) {
        debug_assert!(self.mode & m != 0);
        let _ = m;
    }

    /*----------------------------------------------------------------------*/

    /// A variable is 'active' if it is not eliminated nor fixed.
    #[inline(always)]
    pub fn active(&self, lit: i32) -> bool {
        self.flags(lit).active()
    }

    /// C++ overload `int active () const` (number of active variables).
    #[inline]
    pub fn active_count(&self) -> i32 {
        let res = self.stats.active as i32;
        #[cfg(debug_assertions)]
        {
            let mut tmp = self.max_var as i64;
            tmp -= self.stats.unused;
            tmp -= self.stats.now.fixed;
            tmp -= self.stats.now.eliminated;
            tmp -= self.stats.now.substituted;
            tmp -= self.stats.now.pure;
            debug_assert!(tmp >= 0);
            debug_assert!(tmp == res as i64);
        }
        res
    }

    /// Currently remaining active redundant clauses.
    #[inline(always)]
    pub fn redundant(&self) -> i64 {
        self.stats.current.redundant
    }

    /// Currently remaining active irredundant clauses.
    #[inline(always)]
    pub fn irredundant(&self) -> i64 {
        self.stats.current.irredundant
    }

    #[inline]
    pub fn clause_variable_ratio(&self) -> f64 {
        relative(self.irredundant() as f64, self.active_count() as f64)
    }

    /// Unsigned literals (abs) with checks.
    #[inline(always)]
    pub fn vidx(&self, lit: i32) -> i32 {
        debug_assert!(lit != 0);
        debug_assert!(lit != i32::MIN);
        let idx = lit.abs();
        debug_assert!(idx <= self.max_var);
        idx
    }

    /// Unsigned version with LSB denoting sign.  This is used in indexing
    /// arrays by literals.
    #[inline(always)]
    pub fn vlit(&self, lit: i32) -> u32 {
        (lit < 0) as u32 + 2u32 * self.vidx(lit) as u32
    }

    #[inline(always)]
    pub fn u2i(&self, u: u32) -> i32 {
        debug_assert!(u > 1);
        let mut res = (u / 2) as i32;
        debug_assert!(res <= self.max_var);
        if u & 1 != 0 {
            res = -res;
        }
        res
    }

    #[inline(always)]
    pub fn citten2lit(&self, ulit: u32) -> i32 {
        let mut res = (ulit / 2) as i32 + 1;
        debug_assert!(res <= self.max_var);
        if ulit & 1 != 0 {
            res = -res;
        }
        res
    }

    #[inline(always)]
    pub fn lit2citten(&self, lit: i32) -> u32 {
        let idx = self.vidx(lit) - 1;
        (lit < 0) as u32 + 2u32 * idx as u32
    }

    #[inline]
    pub fn unit_id(&self, lit: i32) -> i64 {
        debug_assert!(self.lrat || self.frat);
        debug_assert!(self.val(lit) > 0);
        let uidx = self.vlit(lit);
        let id = self.unit_clauses_idx[uidx as usize];
        debug_assert!(id != 0);
        id
    }

    /// `int64_t &unit_clauses (int uidx)`.
    #[inline]
    pub fn unit_clauses(&mut self, uidx: i32) -> &mut i64 {
        debug_assert!(self.lrat || self.frat);
        debug_assert!(uidx > 0);
        debug_assert!((uidx as usize) < self.unit_clauses_idx.len());
        &mut self.unit_clauses_idx[uidx as usize]
    }

    // Helper functions to access variable and literal data.  The C++
    // functions return non-const references, the Rust port has a shared
    // and a '_mut' version of each.

    #[inline(always)]
    pub fn var(&self, lit: i32) -> &Var {
        &self.vtab[self.vidx(lit) as usize]
    }
    #[inline(always)]
    pub fn var_mut(&mut self, lit: i32) -> &mut Var {
        let idx = self.vidx(lit) as usize;
        &mut self.vtab[idx]
    }
    #[inline(always)]
    pub fn link(&self, lit: i32) -> &Link {
        &self.links[self.vidx(lit) as usize]
    }
    #[inline(always)]
    pub fn link_mut(&mut self, lit: i32) -> &mut Link {
        let idx = self.vidx(lit) as usize;
        &mut self.links[idx]
    }
    #[inline(always)]
    pub fn flags(&self, lit: i32) -> &Flags {
        &self.ftab[self.vidx(lit) as usize]
    }
    #[inline(always)]
    pub fn flags_mut(&mut self, lit: i32) -> &mut Flags {
        let idx = self.vidx(lit) as usize;
        &mut self.ftab[idx]
    }
    #[inline(always)]
    pub fn bumped(&self, lit: i32) -> i64 {
        self.btab[self.vidx(lit) as usize]
    }
    #[inline(always)]
    pub fn bumped_mut(&mut self, lit: i32) -> &mut i64 {
        let idx = self.vidx(lit) as usize;
        &mut self.btab[idx]
    }
    #[inline(always)]
    pub fn propfixed(&self, lit: i32) -> i32 {
        self.ptab[self.vlit(lit) as usize]
    }
    #[inline(always)]
    pub fn propfixed_mut(&mut self, lit: i32) -> &mut i32 {
        let idx = self.vlit(lit) as usize;
        &mut self.ptab[idx]
    }
    #[inline(always)]
    pub fn score(&self, lit: i32) -> f64 {
        self.stab[self.vidx(lit) as usize]
    }
    #[inline(always)]
    pub fn score_mut(&mut self, lit: i32) -> &mut f64 {
        let idx = self.vidx(lit) as usize;
        &mut self.stab[idx]
    }

    #[inline(always)]
    pub fn occurring(&self) -> bool {
        !self.otab.is_empty()
    }
    #[inline(always)]
    pub fn watching(&self) -> bool {
        !self.wtab.is_empty()
    }

    #[inline(always)]
    pub fn bins(&self, lit: i32) -> &Bins {
        &self.big[self.vlit(lit) as usize]
    }
    #[inline(always)]
    pub fn bins_mut(&mut self, lit: i32) -> &mut Bins {
        let idx = self.vlit(lit) as usize;
        &mut self.big[idx]
    }
    #[inline(always)]
    pub fn occs(&self, lit: i32) -> &Occs {
        &self.otab[self.vlit(lit) as usize]
    }
    #[inline(always)]
    pub fn occs_mut(&mut self, lit: i32) -> &mut Occs {
        let idx = self.vlit(lit) as usize;
        &mut self.otab[idx]
    }
    #[inline(always)]
    pub fn noccs(&self, lit: i32) -> i64 {
        self.ntab[self.vlit(lit) as usize]
    }
    #[inline(always)]
    pub fn noccs_mut(&mut self, lit: i32) -> &mut i64 {
        let idx = self.vlit(lit) as usize;
        &mut self.ntab[idx]
    }
    #[inline(always)]
    pub fn watches(&self, lit: i32) -> &Watches {
        &self.wtab[self.vlit(lit) as usize]
    }
    #[inline(always)]
    pub fn watches_mut(&mut self, lit: i32) -> &mut Watches {
        let idx = self.vlit(lit) as usize;
        &mut self.wtab[idx]
    }

    /// Variable bumping through exponential VSIDS (EVSIDS) as in MiniSAT.
    #[inline(always)]
    pub fn use_scores(&self) -> bool {
        self.opts.score != 0 && self.stable
    }

    /*----------------------------------------------------------------------*/

    // Marking variables with a sign (positive or negative).

    #[inline(always)]
    pub fn marked(&self, lit: i32) -> i8 {
        let mut res = self.marks[self.vidx(lit) as usize];
        if lit < 0 {
            res = res.wrapping_neg();
        }
        res
    }
    #[inline(always)]
    pub fn mark(&mut self, lit: i32) {
        debug_assert!(self.marked(lit) == 0);
        let idx = self.vidx(lit) as usize;
        self.marks[idx] = sign(lit) as i8;
        debug_assert!(self.marked(lit) > 0);
        debug_assert!(self.marked(-lit) < 0);
    }
    #[inline(always)]
    pub fn unmark(&mut self, lit: i32) {
        let idx = self.vidx(lit) as usize;
        self.marks[idx] = 0;
        debug_assert!(self.marked(lit) == 0);
    }

    /// Use only bits 6 and 7 to store the sign or zero.  The remaining bits
    /// can be used as additional flags.
    #[inline(always)]
    pub fn marked67(&self, lit: i32) -> i8 {
        let mut res = self.marks[self.vidx(lit) as usize] >> 6;
        if lit < 0 {
            res = res.wrapping_neg();
        }
        res
    }
    #[inline(always)]
    pub fn mark67(&mut self, lit: i32) {
        let idx = self.vidx(lit) as usize;
        let mask: i8 = 0x3f;
        let m = self.marks[idx];
        #[cfg(debug_assertions)]
        let bits = m & mask;
        self.marks[idx] = (m & mask) | ((sign(lit) << 6) as i8);
        debug_assert!(self.marked(lit) > 0);
        debug_assert!(self.marked(-lit) < 0);
        #[cfg(debug_assertions)]
        debug_assert!((self.marks[idx] & mask) == bits);
        debug_assert!(self.marked67(lit) > 0);
        debug_assert!(self.marked67(-lit) < 0);
    }
    #[inline(always)]
    pub fn unmark67(&mut self, lit: i32) {
        let idx = self.vidx(lit) as usize;
        let mask: i8 = 0x3f;
        #[cfg(debug_assertions)]
        let bits = self.marks[idx] & mask;
        self.marks[idx] &= mask;
        #[cfg(debug_assertions)]
        debug_assert!((self.marks[idx] & mask) == bits);
    }

    /// C++ overload `unmark (vector<int> &lits)`.
    #[inline]
    pub fn unmark_lits(&mut self, lits: &[i32]) {
        for &lit in lits {
            self.unmark(lit);
        }
    }

    /// The other 6 bits of the 'marks' bytes can be used as additional
    /// (unsigned) marking bits.
    #[inline(always)]
    pub fn getbit(&self, lit: i32, bit: i32) -> bool {
        debug_assert!(0 <= bit && bit < 6);
        (self.marks[self.vidx(lit) as usize] & (1 << bit)) != 0
    }
    #[inline(always)]
    pub fn setbit(&mut self, lit: i32, bit: i32) {
        debug_assert!(0 <= bit && bit < 6);
        debug_assert!(!self.getbit(lit, bit));
        let idx = self.vidx(lit) as usize;
        self.marks[idx] |= 1 << bit;
        debug_assert!(self.getbit(lit, bit));
    }
    #[inline(always)]
    pub fn unsetbit(&mut self, lit: i32, bit: i32) {
        debug_assert!(0 <= bit && bit < 6);
        debug_assert!(self.getbit(lit, bit));
        let idx = self.vidx(lit) as usize;
        self.marks[idx] &= !(1 << bit);
        debug_assert!(!self.getbit(lit, bit));
    }

    /// Marking individual literals.
    #[inline(always)]
    pub fn marked2(&self, lit: i32) -> bool {
        let res = self.marks[self.vidx(lit) as usize] as u32;
        debug_assert!(res <= 3);
        let bit = bign(lit);
        (res & bit) != 0
    }
    #[inline(always)]
    pub fn mark2(&mut self, lit: i32) {
        let idx = self.vidx(lit) as usize;
        self.marks[idx] |= bign(lit) as i8;
        debug_assert!(self.marked2(lit));
    }

    /// Marks bits 1,2,3 and 4,5,6 depending on fact and sign of lit.
    #[inline(always)]
    pub fn getfact(&self, lit: i32, fact: i32) -> bool {
        debug_assert!(fact == 1 || fact == 2 || fact == 4);
        let mut res = self.marks[self.vidx(lit) as usize] as i32;
        if lit < 0 {
            res >>= 3;
        } else {
            res &= 7;
        }
        (res & fact) != 0
    }
    #[inline(always)]
    pub fn markfact(&mut self, lit: i32, fact: i32) {
        debug_assert!(fact == 1 || fact == 2 || fact == 4);
        debug_assert!(!self.getfact(lit, fact));
        #[cfg(debug_assertions)]
        let before = self.getfact(-lit, fact);
        let idx = self.vidx(lit) as usize;
        let mut res = self.marks[idx] as i32;
        if lit < 0 {
            res |= fact << 3;
        } else {
            res |= fact;
        }
        self.marks[idx] = res as i8;
        debug_assert!(self.getfact(lit, fact));
        #[cfg(debug_assertions)]
        debug_assert!(self.getfact(-lit, fact) == before);
    }
    #[inline(always)]
    pub fn unmarkfact(&mut self, lit: i32, fact: i32) {
        debug_assert!(fact == 1 || fact == 2 || fact == 4);
        debug_assert!(self.getfact(lit, fact));
        let idx = self.vidx(lit) as usize;
        let mut res = self.marks[idx] as i32;
        if lit < 0 {
            res &= !(fact << 3);
        } else {
            res &= !fact;
        }
        self.marks[idx] = res as i8;
        debug_assert!(!self.getfact(lit, fact));
    }

    /*----------------------------------------------------------------------*/

    /// Watch literal 'lit' in clause with blocking literal 'blit'.
    /// Inlined here, since it occurs in the tight inner loop of
    /// 'propagate'.
    #[inline(always)]
    pub fn watch_literal(&mut self, lit: i32, blit: i32, c: CRef) {
        debug_assert!(lit != blit);
        self.watches_mut(lit).push(Watch::new(blit, c));
        debug_assert!(c.lit(0) == lit || c.lit(1) == lit);
        log!(self, c, "watch {} blit {} in", lit, blit);
    }

    /// Watch literal 'lit' in binary clause with blocking literal 'blit'.
    #[inline(always)]
    pub fn watch_binary_literal(&mut self, lit: i32, blit: i32, c: CRef) {
        debug_assert!(lit != blit);
        self.watches_mut(lit).push(Watch::new_binary(blit, c));
        log!(self, c, "watch binary {} blit {} in", lit, blit);
    }

    /// Add two watches to a clause.  This is used initially during
    /// allocation of a clause and during connecting back all watches after
    /// preprocessing.
    #[inline(always)]
    pub fn watch_clause(&mut self, c: CRef) {
        let l0 = c.lit(0);
        let l1 = c.lit(1);
        self.watch_literal(l0, l1, c);
        self.watch_literal(l1, l0, c);
    }

    #[inline(always)]
    pub fn unwatch_clause(&mut self, c: CRef) {
        let l0 = c.lit(0);
        let l1 = c.lit(1);
        remove_watch(self.watches_mut(l0), c);
        remove_watch(self.watches_mut(l1), c);
    }

    /// Update queue to point to last potentially still unassigned
    /// variable.  All variables after 'queue.unassigned' in bump order are
    /// assumed to be assigned.  Then update the 'queue.bumped' field and
    /// log it.
    #[inline(always)]
    pub fn update_queue_unassigned(&mut self, idx: i32) {
        debug_assert!(0 < idx);
        debug_assert!(idx <= self.max_var);
        self.queue.unassigned = idx;
        self.queue.bumped = self.btab[idx as usize];
        log!(self, "queue unassigned now {} bumped {}", idx, self.btab[idx as usize]);
    }

    /// `int64_t cache_lines (size_t bytes)`.
    #[inline(always)]
    pub fn cache_lines(&self, bytes: usize) -> i64 {
        ((bytes + 127) / 128) as i64
    }

    /// C++ overload `int64_t cache_lines (size_t n, size_t bytes)`.
    #[inline(always)]
    pub fn cache_lines_n(&self, n: usize, bytes: usize) -> i64 {
        self.cache_lines(n * bytes)
    }

    /*----------------------------------------------------------------------*/

    /// We monitor the maximum size and glue of clauses during 'reduce' and
    /// thus can predict if a redundant extended clause is likely to be
    /// kept in the next 'reduce' phase.
    #[inline]
    pub fn likely_to_be_kept_clause(&self, c: CRef) -> bool {
        if !c.redundant() {
            return true;
        }
        if c.glue() <= self.tier2[0] {
            return true;
        }
        if c.glue() > self.lim.keptglue {
            return false;
        }
        if c.size() > self.lim.keptsize {
            return false;
        }
        true
    }

    #[inline]
    pub fn mark_subsume(&mut self, lit: i32) {
        if self.flags(lit).subsume {
            return;
        }
        log!(self, "marking {} as subsuming literal candidate", lit.abs());
        self.stats.mark.subsume += 1;
        self.flags_mut(lit).subsume = true;
    }

    #[inline]
    pub fn mark_ternary(&mut self, lit: i32) {
        if self.flags(lit).ternary {
            return;
        }
        log!(self, "marking {} as ternary resolution literal candidate", lit.abs());
        self.stats.mark.ternary += 1;
        self.flags_mut(lit).ternary = true;
    }

    #[inline]
    pub fn mark_factor(&mut self, lit: i32) {
        let bit = bign(lit) as u8;
        if self.flags(lit).factor & bit != 0 {
            return;
        }
        log!(self, "marking {} as factor literal candidate", lit);
        self.stats.mark.factor += 1;
        self.flags_mut(lit).factor |= bit;
    }

    #[inline(always)]
    pub fn marked_subsume(&self, lit: i32) -> bool {
        self.flags(lit).subsume
    }

    /// If irredundant clauses are removed or literals in clauses are
    /// removed, then variables in such clauses should be reconsidered to be
    /// eliminated through bounded variable elimination.
    #[inline]
    pub fn mark_elim(&mut self, lit: i32) {
        if self.flags(lit).elim {
            return;
        }
        log!(self, "marking {} as elimination literal candidate", lit);
        self.stats.mark.elim += 1;
        self.flags_mut(lit).elim = true;
    }

    #[inline]
    pub fn mark_block(&mut self, lit: i32) {
        let bit = bign(lit) as u8;
        if self.flags(lit).block & bit != 0 {
            return;
        }
        log!(self, "marking {} as blocking literal candidate", lit);
        self.stats.mark.block += 1;
        self.flags_mut(lit).block |= bit;
    }

    /// C++ overload `mark_removed (int lit)`.
    #[inline]
    pub fn mark_removed_lit(&mut self, lit: i32) {
        self.mark_elim(lit);
        self.mark_block(-lit);
    }

    /// Only used for testing & debugging.
    #[inline]
    pub fn marked_block(&self, lit: i32) -> bool {
        let bit = bign(lit) as u8;
        (self.flags(lit).block & bit) != 0
    }

    #[inline]
    pub fn unmark_block(&mut self, lit: i32) {
        let bit = bign(lit) as u8;
        self.flags_mut(lit).block &= !bit;
    }

    /// During scheduling literals for blocked clause elimination we skip
    /// those literals which occur negated in a too large clause.
    #[inline]
    pub fn mark_skip(&mut self, lit: i32) {
        let bit = bign(lit) as u8;
        if self.flags(lit).skip & bit != 0 {
            return;
        }
        log!(self, "marking {} to be skipped as blocking literal", lit);
        self.flags_mut(lit).skip |= bit;
    }

    #[inline]
    pub fn marked_skip(&self, lit: i32) -> bool {
        let bit = bign(lit) as u8;
        (self.flags(lit).skip & bit) != 0
    }

    /// During decompose ignore literals where we already built LRAT chains.
    #[inline]
    pub fn mark_decomposed(&mut self, lit: i32) {
        let bit = bign(lit) as u8;
        debug_assert!((self.flags(lit).marked_signed & bit) == 0);
        self.sign_marked.push(lit);
        self.flags_mut(lit).marked_signed |= bit;
    }

    #[inline]
    pub fn unmark_decomposed(&mut self, lit: i32) {
        let bit = bign(lit) as u8;
        self.flags_mut(lit).marked_signed &= !bit;
    }

    #[inline]
    pub fn marked_decomposed(&self, lit: i32) -> bool {
        let bit = bign(lit) as u8;
        (self.flags(lit).marked_signed & bit) != 0
    }

    /// Marked as assumption.
    #[inline]
    pub fn assumed(&self, lit: i32) -> bool {
        let bit = bign(lit) as u8;
        (self.flags(lit).assumed & bit) != 0
    }

    /*----------------------------------------------------------------------*/

    #[inline]
    pub fn terminate(&mut self) {
        log!(self, "forcing asynchronous termination");
        self.termination_forced.store(true, Relaxed);
    }

    /*----------------------------------------------------------------------*/

    /// Accumulated time (process or real time depending on 'realtime').
    #[inline]
    pub fn time(&self) -> f64 {
        if self.opts.realtime != 0 {
            self.real_time()
        } else {
            self.process_time()
        }
    }

    /// Get the value of an internal literal: -1=false, 0=unassigned,
    /// 1=true.
    #[inline(always)]
    pub fn val(&self, lit: i32) -> i8 {
        debug_assert!(-self.max_var <= lit);
        debug_assert!(lit != 0);
        debug_assert!(lit <= self.max_var);
        // SAFETY: 'vals' covers '[-max_var,max_var]' (asserted).
        unsafe { *self.vals.offset(lit as isize) }
    }

    /// Setting and resetting the value of a literal.
    #[inline(always)]
    pub fn set_val(&mut self, lit: i32, val: i8) {
        debug_assert!(-1 <= val);
        debug_assert!(val <= 1);
        debug_assert!(-self.max_var <= lit);
        debug_assert!(lit != 0);
        debug_assert!(lit <= self.max_var);
        // SAFETY: 'vals' covers '[-max_var,max_var]' (asserted).
        unsafe {
            *self.vals.offset(lit as isize) = val;
            *self.vals.offset(-(lit as isize)) = -val;
        }
    }

    /// As 'val' but restricted to the root-level value of a literal.
    #[inline]
    pub fn fixed(&self, lit: i32) -> i32 {
        debug_assert!(-self.max_var <= lit);
        debug_assert!(lit != 0);
        debug_assert!(lit <= self.max_var);
        let idx = self.vidx(lit);
        // SAFETY: 'idx' is within '[1,max_var]'.
        let mut res = unsafe { *self.vals.offset(idx as isize) } as i32;
        if res != 0 && self.vtab[idx as usize].level != 0 {
            res = 0;
        }
        if lit < 0 {
            res = -res;
        }
        res
    }

    /// Map back an internal literal to an external.
    #[inline]
    pub fn externalize(&self, lit: i32) -> i32 {
        debug_assert!(lit != i32::MIN);
        let idx = lit.abs();
        debug_assert!(idx != 0);
        debug_assert!(idx <= self.max_var);
        let mut res = self.i2e[idx as usize];
        if lit < 0 {
            res = -res;
        }
        res
    }

    /// Explicit freezing of variables.
    pub fn freeze(&mut self, lit: i32) {
        let idx = self.vidx(lit);
        if idx as usize >= self.frozentab.len() {
            let mut new_vsize = if self.vsize != 0 { 2 * self.vsize } else { 1 + self.max_var as usize };
            while new_vsize <= self.max_var as usize {
                new_vsize *= 2;
            }
            self.frozentab.resize(new_vsize, 0);
        }
        let r = self.frozentab[idx as usize];
        if r < u32::MAX {
            self.frozentab[idx as usize] = r + 1;
            log!(self, "variable {} frozen {} times", idx, r + 1);
        } else {
            log!(self, "variable {} remains frozen forever", idx);
        }
    }

    /// Explicit melting of variables.
    pub fn melt(&mut self, lit: i32) {
        let idx = self.vidx(lit) as usize;
        let r = self.frozentab[idx];
        if r < u32::MAX {
            self.frozentab[idx] = r - 1;
            if self.frozentab[idx] == 0 {
                if self.relevanttab[idx] != 0 {
                    log!(self, "variable {} is observed, can not be completely molten", idx);
                    self.frozentab[idx] += 1;
                } else {
                    log!(self, "variable {} completely molten", idx);
                }
            } else {
                log!(
                    self,
                    "variable {} melted once but remains frozen {} times",
                    lit,
                    self.frozentab[idx]
                );
            }
        } else {
            log!(self, "variable {} remains frozen forever", idx);
        }
    }

    #[inline]
    pub fn frozen(&self, lit: i32) -> bool {
        (self.vidx(lit) as usize) < self.frozentab.len() && self.frozentab[self.vidx(lit) as usize] > 0
    }

    /*----------------------------------------------------------------------*/

    /// We want to have termination checks inlined, particularly the first
    /// function which appears in preprocessor loops.
    ///
    /// `factor` defaults to `1` in C++.
    #[inline]
    pub fn terminated_asynchronously(&mut self, factor: i32) -> bool {
        // First way of asynchronous termination is through 'terminate' or
        // 'catch_signal' which sets the 'termination_forced' flag directly.
        if self.termination_forced.load(Relaxed) {
            log!(self, "termination asynchronously forced");
            return true;
        }

        // This is only for testing and debugging asynchronous termination
        // calls.
        if self.lim.terminate.forced != 0 {
            debug_assert!(self.lim.terminate.forced > 0);
            let forced = self.lim.terminate.forced;
            self.lim.terminate.forced -= 1;
            if forced == 1 {
                log!(self, "internally forcing termination");
                self.termination_forced.store(true, Relaxed);
                return true;
            }
            log!(
                self,
                "decremented internal forced termination limit to {}",
                self.lim.terminate.forced
            );
        }

        // The second way of asynchronous termination is through registering
        // and calling an external 'Terminator' object.
        if self.external().terminator.is_some() {
            let check = self.lim.terminate.check;
            self.lim.terminate.check -= 1;
            if check == 0 {
                debug_assert!(factor > 0);
                debug_assert!(i32::MAX / factor > self.opts.terminateint);
                self.lim.terminate.check = factor * self.opts.terminateint;
                let terminate = match self.external().terminator.as_mut() {
                    Some(t) => t.terminate(),
                    None => false,
                };
                if terminate {
                    self.termination_forced.store(true, Relaxed); // Cache it.
                    log!(self, "connected terminator forces termination");
                    return true;
                }
            }
        }

        false
    }

    #[inline]
    pub fn search_limits_hit(&self) -> bool {
        debug_assert!(!self.preprocessing);
        debug_assert!(!self.localsearching);

        if self.lim.conflicts >= 0 && self.stats.conflicts >= self.lim.conflicts {
            log!(self, "conflict limit {} reached", self.lim.conflicts);
            return true;
        }

        if self.lim.decisions >= 0 && self.stats.decisions >= self.lim.decisions {
            log!(self, "decision limit {} reached", self.lim.decisions);
            return true;
        }

        if self.lim.ticks >= 0 && self.stats.ticks.search[0] + self.stats.ticks.search[1] >= self.lim.ticks {
            log!(self, "ticks limit {} reached", self.lim.ticks);
            return true;
        }

        false
    }
}

impl Drop for Internal {
    /// `~Internal ()` (from 'internal.cpp').
    fn drop(&mut self) {
        // If a memory exception ocurred a profile might still be active.
        for i in 0..self.profiles.profs.len() {
            let p = self.profiles.profs[i];
            if p.level <= self.opts.profile && p.active {
                let t = self.time();
                self.stop_profiling(crate::profile::ProfileId::ALL[i], t);
            }
        }
        // SAFETY: allocated with 'calloc' in 'Internal::new'.
        unsafe { libc::free(self.dummy_binary.as_ptr() as *mut libc::c_void) };
        let clauses = std::mem::take(&mut self.clauses);
        for c in clauses {
            self.delete_clause(c);
        }
        self.proof = None;
        self.tracers.clear();
        self.file_tracers.clear();
        self.stat_tracers.clear();
        // 'vals' is released with 'vals_storage'.
    }
}

/*------------------------------------------------------------------------*/
// Port of the remaining functions of 'internal.cpp'.

#[allow(unused_imports)]
use crate::prelude::*;

impl Internal {
    /// Back pointer to the `External` buddy with an unbounded lifetime, so
    /// that fields of `External` can be passed as arguments together with
    /// (disjoint) fields of `Internal` (as C++ does with 'external->...').
    #[inline(always)]
    #[allow(clippy::mut_from_ref)]
    pub fn ext_unbound<'a>(&self) -> &'a mut External {
        debug_assert!(!self.external.is_null());
        // SAFETY: see 'external ()'.  'External' is a separate heap object.
        unsafe { &mut *self.external }
    }

    pub fn enlarge(&mut self, new_max_var: i32) {
        // New variables can be created that can invoke enlarge anytime (via
        // calls during ipasir-up call-backs), thus assuming (!level) is not
        // correct
        let mut new_vsize = if self.vsize != 0 { 2 * self.vsize } else { 1 + new_max_var as usize };
        while new_vsize <= new_max_var as usize {
            new_vsize *= 2;
        }
        log!(self, "enlarge internal size from {} to new size {}", self.vsize, new_vsize);
        // Ordered in the size of allocated memory (larger block first).
        if self.lrat || self.frat {
            enlarge_zero(&mut self.unit_clauses_idx, 2 * new_vsize);
        }
        enlarge_only(&mut self.wtab, 2 * new_vsize);
        enlarge_only(&mut self.vtab, new_vsize);
        enlarge_zero(&mut self.parents, new_vsize);
        enlarge_only(&mut self.links, new_vsize);
        enlarge_zero(&mut self.btab, new_vsize);
        enlarge_zero(&mut self.gtab, new_vsize);
        enlarge_zero(&mut self.stab, new_vsize);
        enlarge_init(&mut self.ptab, 2 * new_vsize, -1);
        enlarge_only(&mut self.ftab, new_vsize);
        self.enlarge_vals(new_vsize);
        self.vsize = new_vsize;
        if !self.external.is_null() {
            enlarge_zero(&mut self.relevanttab, new_vsize);
        }
        let val: i8 = if self.opts.phase != 0 { 1 } else { -1 };
        enlarge_init(&mut self.phases.saved, new_vsize, val);
        enlarge_zero(&mut self.phases.forced, new_vsize);
        enlarge_zero(&mut self.phases.target, new_vsize);
        enlarge_zero(&mut self.phases.best, new_vsize);
        enlarge_zero(&mut self.phases.prev, new_vsize);
        enlarge_zero(&mut self.marks, new_vsize);
    }

    pub fn init_vars(&mut self, new_max_var: i32) {
        if new_max_var <= self.max_var {
            return;
        }
        // New variables can be created that can invoke enlarge anytime (via
        // calls during ipasir-up call-backs), thus assuming (!level) is not
        // correct
        log!(
            self,
            "initializing {} internal variables from {} to {}",
            new_max_var - self.max_var,
            self.max_var + 1,
            new_max_var
        );
        if new_max_var as usize >= self.vsize {
            self.enlarge(new_max_var);
        }
        #[cfg(debug_assertions)]
        {
            let mut i = -(new_max_var as i64);
            while i < -(self.max_var as i64) {
                // SAFETY: 'vals' covers '[-vsize+1,vsize-1]' of the allocation.
                debug_assert!(unsafe { *self.vals.offset(i as isize) } == 0);
                i += 1;
            }
            for i in (self.max_var as u32 + 1)..=(new_max_var as u32) {
                // SAFETY: see above.
                debug_assert!(unsafe { *self.vals.offset(i as isize) } == 0);
                debug_assert!(self.btab[i as usize] == 0);
                debug_assert!(self.gtab[i as usize] == 0);
            }
            let mut i = 2 * (self.max_var as u64 + 1);
            while i <= 2 * new_max_var as u64 + 1 {
                debug_assert!(self.ptab[i as usize] == -1);
                i += 1;
            }
        }
        debug_assert!(self.btab[0] == 0);
        let old_max_var = self.max_var;
        self.max_var = new_max_var;
        self.init_queue(old_max_var, new_max_var);
        self.init_scores(old_max_var, new_max_var);
        let initialized = new_max_var - old_max_var;
        self.stats.vars += initialized as i64;
        self.stats.unused += initialized as i64;
        self.stats.inactive += initialized as i64;
        log!(self, "finished initializing {} internal variables", initialized);
    }

    pub fn add_original_lit(&mut self, lit: i32) {
        debug_assert!(lit.abs() <= self.max_var);
        if lit != 0 {
            self.original.push(lit);
        } else {
            let id = if self.original_id < self.reserved_ids {
                self.original_id += 1;
                self.original_id
            } else {
                self.clause_id += 1;
                self.clause_id
            };
            let external = self.ext_unbound();
            if let Some(proof) = self.proof.as_mut() {
                // Use the external form of the clause for printing in proof
                // Externalize(internalized literal) != external literal
                debug_assert!(self.original.is_empty() || !external.eclause.is_empty());
                proof.add_external_original_clause(id, false, &external.eclause, false);
            }
            if self.opts.check != 0 && (self.opts.checkwitness != 0 || self.opts.checkfailed != 0) {
                let forgettable = self.from_propagator && self.ext_clause_forgettable;
                if forgettable && self.opts.check != 0 {
                    debug_assert!(self.original.is_empty() || !external.eclause.is_empty());

                    // First integer is the presence-flag (even if the clause
                    // is empty)
                    let entry = external.forgettable_original.entry(id as u64).or_default();
                    *entry = vec![1];
                    for &elit in external.eclause.iter() {
                        entry.push(elit);
                    }

                    log!(self, &external.eclause, "clause added to external forgettable map:");
                }
            }

            self.add_new_original_clause(id);
            self.original.clear();
        }
    }

    /// `restore` defaults to `false` in C++
    pub fn finish_added_clause_with_id(&mut self, id: i64, restore: bool) {
        let external = self.ext_unbound();
        if let Some(proof) = self.proof.as_mut() {
            // Use the external form of the clause for printing in proof
            // Externalize(internalized literal) != external literal
            debug_assert!(self.original.is_empty() || !external.eclause.is_empty());
            proof.add_external_original_clause(id, false, &external.eclause, restore);
        }
        self.add_new_original_clause(id);
        self.original.clear();
    }

    /*----------------------------------------------------------------------*/

    pub fn reserve_ids(&mut self, number: i32) {
        // return;
        log!(self, "reserving {} ids", number);
        debug_assert!(number >= 0);
        debug_assert!(self.clause_id == 0 && self.reserved_ids == 0 && self.original_id == 0);
        self.reserved_ids = number as i64;
        self.clause_id = self.reserved_ids;
        if let Some(proof) = self.proof.as_mut() {
            proof.begin_proof(self.reserved_ids);
        }
    }

    /*----------------------------------------------------------------------*/

    // 'PROFILE_MODE' is not ported, thus the wrappers are the plain
    // functions (as the '#define's in 'internal.hpp').

    #[inline(always)]
    pub fn propagate_wrapper(&mut self) -> bool {
        self.propagate()
    }

    #[inline(always)]
    pub fn analyze_wrapper(&mut self) {
        self.analyze()
    }

    #[inline(always)]
    pub fn decide_wrapper(&mut self) -> i32 {
        self.decide()
    }

    /*----------------------------------------------------------------------*/

    /// This is the main CDCL loop with interleaved inprocessing.
    pub fn cdcl_loop_with_inprocessing(&mut self) -> i32 {
        let mut res = 0;

        start!(self, search);

        if self.stable {
            start!(self, stable);
            self.report(b'[', 0);
        } else {
            start!(self, unstable);
            self.report(b'{', 0);
        }

        while res == 0 {
            if self.unsat {
                res = 20;
            } else if self.unsat_constraint {
                res = 20;
            } else if !self.propagate_wrapper() {
                self.analyze_wrapper(); // propagate and analyze
            } else if self.iterating {
                self.iterate(); // report learned unit
            } else if self.terminated_asynchronously(1) {
                // externally terminated
                break;
            } else if !self.external_propagate() || self.unsat {
                // external propagation
                if self.unsat {
                    continue;
                } else {
                    self.analyze();
                }
            } else if self.satisfied() {
                // found model
                if !self.external_check_solution() || self.unsat {
                    if self.unsat {
                        continue;
                    } else {
                        self.analyze();
                    }
                } else if self.satisfied() {
                    res = 10;
                }
            } else if self.search_limits_hit() {
                break; // decision or conflict limit
            } else if self.terminated_asynchronously(1) {
                // externally terminated
                break;
            } else if self.restarting() {
                self.restart(); // restart by backtracking
            } else if self.rephasing() {
                self.rephase(); // reset variable phases
            } else if self.reducing() {
                self.reduce(); // collect useless clauses
            } else if self.inprobing() {
                self.inprobe(true); // schedule of inprocessing
            } else if self.ineliminating() {
                self.elim(true); // variable elimination
            } else if self.compacting() {
                self.compact(); // collect variables
            } else if self.conditioning() {
                self.condition(true); // globally blocked clauses
            } else {
                res = self.decide_wrapper(); // next decision
            }
        }

        if self.stable {
            stop!(self, stable);
            self.report(b']', 0);
        } else {
            stop!(self, unstable);
            self.report(b'}', 0);
        }

        stop!(self, search);

        res
    }

    pub fn propagate_assumptions(&mut self) -> i32 {
        if let Some(proof) = self.proof.as_mut() {
            proof.solve_query();
        }
        if self.opts.ilb != 0 {
            self.sort_and_reuse_assumptions();
            debug_assert!(self.opts.ilb == 2 || self.level as usize <= self.assumptions.len());
            self.stats.ilbtriggers += 1;
            self.stats.ilbsuccess += (self.level > 0) as i64;
            self.stats.levelsreused += self.level as i64;
            if self.level != 0 {
                debug_assert!(self.control.len() > 1);
                self.stats.literalsreused += self.num_assigned as i64 - self.control[1].trail as i64;
            }
        }
        self.init_search_limits();
        self.init_report_limits();

        let mut res = self.already_solved(); // root-level propagation is done here

        let mut last_assumption_level = self.assumptions.len() as i32;
        if !self.constraint.is_empty() {
            last_assumption_level += 1;
        }

        if res == 0 {
            self.restore_clauses();
            while res == 0 {
                if self.unsat {
                    res = 20;
                } else if self.unsat_constraint {
                    res = 20;
                } else if !self.propagate() {
                    // let analyze run to get failed assumptions
                    self.analyze();
                } else if !self.external_propagate() || self.unsat {
                    // external propagation
                    if self.unsat {
                        continue;
                    } else {
                        self.analyze();
                    }
                } else if self.satisfied() {
                    // found model
                    if !self.external_check_solution() || self.unsat {
                        if self.unsat {
                            continue;
                        } else {
                            self.analyze();
                        }
                    } else if self.satisfied() {
                        res = 10;
                    }
                } else if self.search_limits_hit() {
                    break; // decision or conflict limit
                } else if self.terminated_asynchronously(1) {
                    // externally terminated
                    break;
                } else {
                    if self.level >= last_assumption_level {
                        break;
                    }
                    res = self.decide();
                }
            }
        }

        if self.unsat || self.unsat_constraint {
            res = 20;
        }

        if res == 0 && self.satisfied() {
            res = 10;
        }

        self.finalize(res);
        self.reset_solving();
        self.report_solving(res);

        res
    }

    pub fn implied(&mut self, entrailed: &mut Vec<i32>) {
        let mut last_assumption_level = self.assumptions.len() as i32;
        if !self.constraint.is_empty() {
            last_assumption_level += 1;
        }

        let mut trail_limit = self.trail.len();
        if self.level > last_assumption_level {
            trail_limit = self.control[(last_assumption_level + 1) as usize].trail as usize;
        }

        for i in 0..trail_limit {
            entrailed.push(self.trail[i]);
        }
    }

    /*----------------------------------------------------------------------*/

    // Most of the limits are only initialized in the first 'solve' call and
    // increased as in a stand-alone non-incremental SAT call except for
    // those explicitly marked as being reset below.

    pub fn init_report_limits(&mut self) {
        self.reported = false;
        self.lim.report = 0;
        self.lim.recompute_tier = 5000;
    }

    pub fn init_preprocessing_limits(&mut self) {
        let incremental = self.lim.initialized;
        if incremental {
            log!(self, "reinitializing preprocessing limits incrementally");
        } else {
            log!(self, "initializing preprocessing limits and increments");
        }

        #[allow(unused_assignments)]
        let mut mode: &str = "";

        /*--------------------------------------------------------------------*/

        if incremental {
            mode = "keeping";
        } else {
            self.last.elim.marked = -1;
            self.lim.elim = (self.stats.conflicts as f64 + self.scale(self.opts.elimint as f64)) as i64;
            mode = "initial";
        }
        log!(
            self,
            "{} elim limit {} after {} conflicts",
            mode,
            self.lim.elim,
            self.lim.elim - self.stats.conflicts
        );

        // Initialize and reset elimination bounds in any case.

        self.lim.elimbound = self.opts.elimboundmin as i64;
        log!(self, "elimination bound {}", self.lim.elimbound);

        /*--------------------------------------------------------------------*/

        if !incremental {
            self.last.ternary.marked = -1; // TODO this should not be necessary...

            self.lim.compact = self.stats.conflicts + self.opts.compactint as i64;
            log!(
                self,
                "initial compact limit {} increment {}",
                self.lim.compact,
                self.lim.compact - self.stats.conflicts
            );
        }

        /*--------------------------------------------------------------------*/

        if incremental {
            mode = "keeping";
        } else {
            let mut delta = ((self.stats.added.irredundant + 10) as f64).log10();
            delta = delta * delta;
            self.lim.inprobe = (self.stats.conflicts as f64 + self.opts.inprobeint as f64 * delta) as i64;
            mode = "initial";
        }
        log!(
            self,
            "{} probe limit {} after {} conflicts",
            mode,
            self.lim.inprobe,
            self.lim.inprobe - self.stats.conflicts
        );

        /*--------------------------------------------------------------------*/

        if incremental {
            mode = "keeping";
        } else {
            self.lim.condition = self.stats.conflicts + self.opts.conditionint as i64;
            mode = "initial";
        }
        log!(
            self,
            "{} condition limit {} increment {}",
            mode,
            self.lim.condition,
            self.lim.condition - self.stats.conflicts
        );
        let _ = mode;

        /*--------------------------------------------------------------------*/

        // Initial preprocessing rounds.

        if self.inc.preprocessing <= 0 {
            self.lim.preprocessing = 0;
            log!(self, "no preprocessing");
        } else {
            self.lim.preprocessing = self.inc.preprocessing;
            log!(self, "limiting to {} preprocessing rounds", self.lim.preprocessing);
        }
    }

    pub fn init_search_limits(&mut self) {
        let incremental = self.lim.initialized;
        if incremental {
            log!(self, "reinitializing search limits incrementally");
        } else {
            log!(self, "initializing search limits and increments");
        }

        #[allow(unused_assignments)]
        let mut mode: &str = "";

        /*--------------------------------------------------------------------*/

        if incremental {
            mode = "keeping";
        } else {
            self.last.reduce.conflicts = -1;
            self.lim.reduce = self.stats.conflicts + self.opts.reduceinit as i64;
            mode = "initial";
        }
        log!(
            self,
            "{} reduce limit {} after {} conflicts",
            mode,
            self.lim.reduce,
            self.lim.reduce - self.stats.conflicts
        );

        /*--------------------------------------------------------------------*/

        if incremental {
            mode = "keeping";
        } else {
            self.lim.flush = self.opts.flushint as i64;
            self.inc.flush = self.opts.flushint as i64;
            mode = "initial";
        }
        log!(self, "{} flush limit {} interval {}", mode, self.lim.flush, self.inc.flush);

        /*--------------------------------------------------------------------*/

        // Initialize or reset 'rephase' limits in any case.

        self.lim.rephase = self.stats.conflicts + self.opts.rephaseint as i64;
        self.lim.rephased[0] = 0;
        self.lim.rephased[1] = 0;
        self.last.stabilize.rephased = 0;
        log!(
            self,
            "new rephase limit {} after {} conflicts",
            self.lim.rephase,
            self.lim.rephase - self.stats.conflicts
        );

        /*--------------------------------------------------------------------*/

        // Initialize or reset 'restart' limits in any case.

        self.lim.restart = self.stats.conflicts + self.opts.restartint as i64;
        log!(
            self,
            "new restart limit {} increment {}",
            self.lim.restart,
            self.lim.restart - self.stats.conflicts
        );

        /*--------------------------------------------------------------------*/

        if !incremental {
            self.stable = self.opts.stabilize != 0 && self.opts.stabilizeonly != 0;
            if self.stable {
                log!(self, "starting in always forced stable phase");
            } else {
                log!(self, "starting in default non-stable phase");
            }
            self.init_averages();
        } else if self.opts.stabilize != 0 && self.opts.stabilizeonly != 0 {
            log!(self, "keeping always forced stable phase");
            debug_assert!(self.stable);
        } else if self.stable {
            log!(self, "switching back to default non-stable phase");
            self.stable = false;
            self.swap_averages();
        } else {
            log!(self, "keeping non-stable phase");
        }

        self.inc.stabilize = 0;
        self.last.stabilize.conflicts = self.stats.conflicts;
        self.lim.stabilize = self.stats.conflicts + self.opts.stabilizeinit as i64;
        self.last.stabilize.ticks = self.stats.ticks.search[0];
        self.stats.stabphases = 0;
        log!(
            self,
            "new ticks-based stabilize limit {} after {} conflicts",
            self.lim.stabilize,
            self.opts.stabilizeinit as i32
        );

        if self.opts.stabilize != 0 && self.opts.reluctant != 0 && self.opts.reluctantint != 0 {
            log!(self, "new restart reluctant doubling sequence period {}", self.opts.reluctant);
            self.reluctant.enable(self.opts.reluctantint, self.opts.reluctantmax as i64);
        } else {
            self.reluctant.disable();
        }

        /*--------------------------------------------------------------------*/

        // Conflict and decision limits.

        if self.inc.conflicts < 0 {
            self.lim.conflicts = -1;
            log!(self, "no limit on conflicts");
        } else {
            self.lim.conflicts = self.stats.conflicts + self.inc.conflicts;
            log!(
                self,
                "conflict limit after {} conflicts at {} conflicts",
                self.inc.conflicts,
                self.lim.conflicts
            );
        }

        if self.inc.decisions < 0 {
            self.lim.decisions = -1;
            log!(self, "no limit on decisions");
        } else {
            self.lim.decisions = self.stats.decisions + self.inc.decisions;
            log!(
                self,
                "decision limit after {} decisions at {} decisions",
                self.inc.decisions,
                self.lim.decisions
            );
        }

        if self.inc.ticks < 0 {
            self.lim.ticks = -1;
            log!(self, "no limit on ticks");
        } else {
            self.lim.ticks = self.stats.ticks.search[0] + self.stats.ticks.search[1] + self.inc.ticks;
            log!(self, "ticks limit after {} ticks at {} ticks", self.inc.ticks, self.lim.ticks);
        }

        /*--------------------------------------------------------------------*/

        // Initial preprocessing rounds.

        if self.inc.localsearch <= 0 {
            self.lim.localsearch = 0;
            log!(self, "no local search");
        } else {
            self.lim.localsearch = self.inc.localsearch;
            log!(self, "limiting to {} local search rounds", self.lim.localsearch);
        }

        /*--------------------------------------------------------------------*/
        // tier 1 and tier 2 limits
        if incremental && self.opts.recomputetier != 0 {
            for m in [true, false] {
                for u in self.stats.used[m as usize].iter_mut() {
                    *u = 0;
                }
            }
            for u in self.stats.bump_used.iter_mut() {
                *u = 0;
            }
            for u in [true, false] {
                let t1 = if self.opts.tier1minglue != 0 { self.opts.tier1minglue } else { 2 };
                let t2 = if self.opts.tier2minglue != 0 { self.opts.tier2minglue } else { 6 };
                self.tier1[u as usize] = self.tier1[u as usize].max(t1);
                self.tier2[u as usize] = self.tier2[u as usize].max(t2);
            }
            self.stats.tierecomputed = 0;
        }

        /*--------------------------------------------------------------------*/
        // clause decaying
        if incremental {
            self.last.incremental_decay.last_id = 0;
        } else {
            self.lim.incremental_decay = self.opts.incdecayint as i64;
        }

        /*--------------------------------------------------------------------*/

        if incremental {
            mode = "keeping";
        } else {
            self.lim.random_decision = self.stats.conflicts + self.opts.randecinit as i64;
            mode = "initial";
        }
        log!(
            self,
            "{} randomize decision limit {} after {} conflicts",
            mode,
            self.lim.random_decision,
            self.lim.random_decision - self.stats.conflicts
        );
        let _ = mode;

        /*--------------------------------------------------------------------*/

        self.lim.initialized = true;
    }

    /*----------------------------------------------------------------------*/

    pub fn preprocess_round(&mut self, round: i32) -> bool {
        let _ = round;
        if self.unsat {
            return false;
        }
        if self.max_var == 0 {
            return false;
        }
        if self.terminated_asynchronously(1) {
            return false;
        }
        start!(self, preprocess);
        let before_vars = self.active_count() as i64;
        let before_clauses = self.stats.current.irredundant;
        self.stats.preprocessings += 1;
        debug_assert!(!self.preprocessing);
        self.preprocessing = true;
        phase!(
            self,
            "preprocessing",
            self.stats.preprocessings,
            "starting round {} with {} variables and {} clauses",
            round,
            before_vars,
            before_clauses
        );
        let old_elimbound = self.lim.elimbound as i32;
        if self.opts.inprobing != 0 {
            self.inprobe(false);
        }
        if self.opts.elim != 0 {
            self.elim(false);
        }
        if self.opts.condition != 0 {
            self.condition(false);
        }

        let after_vars = self.active_count() as i64;
        let after_clauses = self.stats.current.irredundant;
        debug_assert!(self.preprocessing);
        self.preprocessing = false;
        phase!(
            self,
            "preprocessing",
            self.stats.preprocessings,
            "finished round {} with {} variables and {} clauses",
            round,
            after_vars,
            after_clauses
        );
        stop!(self, preprocess);
        self.report(b'P', 0);
        if self.unsat {
            return false;
        }
        if after_vars < before_vars {
            return true;
        }
        if (old_elimbound as i64) < self.lim.elimbound {
            return true;
        }
        false
    }

    /// for now counts as one of the preprocessing rounds TODO: change this?
    pub fn preprocess_quickly(&mut self, always: bool) {
        if self.unsat {
            return;
        }
        if self.max_var == 0 {
            return;
        }
        if self.terminated_asynchronously(1) {
            return;
        }
        if self.opts.preprocesslight == 0 {
            return;
        }
        if !always && self.stats.searches > 1 {
            return;
        }
        start!(self, preprocess);
        let before_vars = self.active_count() as i64;
        let before_clauses = self.stats.current.irredundant;
        // stats.preprocessings++;
        debug_assert!(!self.preprocessing);
        self.preprocessing = true;
        self.report(b'(', 0);
        phase!(
            self,
            "preprocessing",
            self.stats.preprocessings,
            "starting with {} variables and {} clauses",
            before_vars,
            before_clauses
        );

        if self.extract_gates(true) {
            self.decompose();
        }
        self.binary_clauses_backbone();

        if self.sweep() {
            self.decompose();
        }

        if self.opts.factor != 0 {
            self.factor();
        }

        if self.opts.fastelim != 0 {
            self.elimfast();
        }
        // if (opts.condition)
        // condition (false);
        let after_vars = self.active_count() as i64;
        let after_clauses = self.stats.current.irredundant;
        debug_assert!(self.preprocessing);
        self.preprocessing = false;
        phase!(
            self,
            "preprocessing",
            self.stats.preprocessings,
            "finished with {} variables and {} clauses",
            after_vars,
            after_clauses
        );
        stop!(self, preprocess);
        self.report(b'P', 0);
    }

    pub fn preprocess(&mut self, always: bool) -> i32 {
        let mut res = 0;
        if self.level == 0 && !self.unsat && self.opts.luckyearly != 0 {
            res = self.lucky_phases();
        }
        if res != 0 {
            return res;
        }

        if self.opts.deduplicateallinit != 0 && self.stats.deduplicatedinitrounds == 0 {
            self.deduplicate_all_clauses();
        }

        self.preprocess_quickly(always);
        let mut i: i64 = 0;
        while i < self.lim.preprocessing {
            if !self.preprocess_round(i as i32) {
                break;
            }
            i += 1;
        }
        self.report(b')', 0);
        if self.unsat {
            return 20;
        }
        0
    }

    /*----------------------------------------------------------------------*/

    pub fn try_to_satisfy_formula_by_saved_phases(&mut self) -> i32 {
        log!(self, "satisfying formula by saved phases");
        debug_assert!(self.level == 0);
        debug_assert!(!self.force_saved_phase);
        debug_assert!(self.propagated == self.trail.len());
        self.force_saved_phase = true;
        if self.external_prop {
            debug_assert!(self.level == 0);
            log!(self, "external notifications are turned off during preprocessing.");
            self.private_steps = true;
        }
        let mut res = 0;
        while res == 0 {
            if self.satisfied() {
                log!(self, "formula indeed satisfied by saved phases");
                res = 10;
            } else if self.decide() != 0 {
                log!(self, "inconsistent assumptions with redundant clauses and phases");
                res = 20;
            } else if !self.propagate() {
                log!(self, "saved phases do not satisfy redundant clauses");
                debug_assert!(self.level > 0);
                self.backtrack(0);
                self.conflict = CRef::NULL; // ignore conflict
                debug_assert!(res == 0);
                break;
            }
        }
        debug_assert!(self.force_saved_phase);
        self.force_saved_phase = false;
        if self.external_prop {
            self.private_steps = false;
            log!(self, "external notifications are turned back on.");
            if self.level == 0 {
                self.notify_assignments(); // In case fixed assignments were found.
            } else {
                self.renotify_trail_after_local_search();
            }
        }
        res
    }

    /*----------------------------------------------------------------------*/

    pub fn produce_failed_assumptions(&mut self) {
        log!(self, "producing failed assumptions");
        debug_assert!(self.level == 0);
        debug_assert!(!self.assumptions.is_empty());
        while !self.unsat {
            debug_assert!(!self.satisfied());
            self.notify_assignments();
            if self.decide() != 0 {
                break;
            }
            while !self.unsat && !self.propagate() {
                self.analyze();
            }
        }
        self.notify_assignments();
        if self.unsat {
            log!(self, "formula is actually unsatisfiable unconditionally");
        } else {
            log!(self, "assumptions indeed failing");
        }
    }

    /*----------------------------------------------------------------------*/

    pub fn local_search_round(&mut self, round: i32) -> i32 {
        debug_assert!(round > 0);

        if self.unsat {
            return 0;
        }
        if self.max_var == 0 {
            return 0;
        }

        start_outer_walk!(self);
        debug_assert!(!self.localsearching);
        self.localsearching = true;

        // Determine propagation limit quadratically scaled with rounds.
        //
        let mut limit: i64 = self.opts.walkmineff as i64;
        limit *= round as i64;
        if i64::MAX / round as i64 > limit {
            limit *= round as i64;
        } else {
            limit = i64::MAX;
        }

        let res = if self.opts.walkfullocc != 0 {
            self.walk_full_occs_round(limit, true)
        } else {
            self.walk_round(limit, true)
        };

        debug_assert!(self.localsearching);
        self.localsearching = false;
        stop_outer_walk!(self);

        self.report(b'L', 0);

        res
    }

    pub fn local_search(&mut self) -> i32 {
        if self.unsat {
            return 0;
        }
        if self.max_var == 0 {
            return 0;
        }
        if self.opts.walk == 0 {
            return 0;
        }
        if !self.constraint.is_empty() {
            return 0;
        }

        let mut res = 0;

        let mut i: i64 = 1;
        while res == 0 && i <= self.lim.localsearch {
            res = self.local_search_round(i as i32);
            i += 1;
        }

        if res == 10 {
            log!(self, "local search determined formula to be satisfiable");
            debug_assert!(self.stats.walk.minimum == 0);
            res = self.try_to_satisfy_formula_by_saved_phases();
        } else if res == 20 {
            log!(self, "local search determined assumptions to be inconsistent");
            debug_assert!(!self.assumptions.is_empty());
            self.produce_failed_assumptions();
        }

        res
    }

    /*----------------------------------------------------------------------*/

    /// if preprocess_only is false and opts.ilb is true we do not preprocess
    /// such that we do not have to backtrack to level 0.
    ///
    /// `preprocess_only` defaults to `false` in C++
    pub fn solve(&mut self, preprocess_only: bool) -> i32 {
        debug_assert!(self.clause.is_empty());
        self.stats.searches += 1;
        start!(self, solve);
        if let Some(proof) = self.proof.as_mut() {
            proof.solve_query();
        }
        if self.opts.ilb != 0 {
            self.sort_and_reuse_assumptions();
            debug_assert!(self.opts.ilb != 0 || self.level as usize <= self.assumptions.len());
            self.stats.ilbtriggers += 1;
            self.stats.ilbsuccess += (self.level > 0) as i64;
            self.stats.levelsreused += self.level as i64;
            if self.level != 0 {
                debug_assert!(self.control.len() > 1);
                self.stats.literalsreused += self.num_assigned as i64 - self.control[1].trail as i64;
            }
            if self.external().propagator.is_some() {
                self.renotify_trail_after_ilb();
            }
        }
        if preprocess_only {
            log!(self, "internal solving in preprocessing only mode");
        } else {
            log!(self, "internal solving in full mode");
        }
        self.init_report_limits();
        let mut res = self.already_solved();
        if res == 0 && preprocess_only && self.level != 0 {
            self.backtrack(0);
        }
        if res == 0 {
            res = self.restore_clauses();
        }
        if res == 0 || (res == 10 && self.external_prop) {
            self.init_preprocessing_limits();
            if !preprocess_only {
                self.init_search_limits();
            }
        }
        if !preprocess_only {
            if res == 0 && self.level == 0 {
                res = self.local_search();
            }
        }
        if res == 0 && self.level == 0 {
            res = self.preprocess(preprocess_only);
        }
        if !preprocess_only {
            if res == 0 && self.level == 0 && self.opts.luckylate != 0 {
                res = self.lucky_phases();
            }
            if res == 0 && self.level == 0 {
                res = self.local_search();
            }
            if res == 0 {
                self.decay_clauses_upon_incremental_clauses();
            }
            if res == 0 || (res == 10 && self.external_prop) {
                if res == 10 && self.external_prop && self.level != 0 {
                    self.backtrack(0);
                }
                res = self.cdcl_loop_with_inprocessing();
            }
        }
        self.finalize(res);
        self.reset_solving();
        self.report_solving(res);
        stop!(self, solve);
        res
    }

    pub fn already_solved(&mut self) -> i32 {
        let mut res = 0;
        if self.unsat || self.unsat_constraint {
            log!(self, "already inconsistent");
            res = 20;
        } else {
            if self.level != 0 && self.opts.ilb == 0 {
                self.backtrack(0);
            }
            if self.level == 0 && !self.propagate() {
                log!(self, "root level propagation produces conflict");
                self.learn_empty_clause();
                res = 20;
            }
            if self.max_var == 0 && res == 0 {
                res = 10;
            }
        }
        res
    }

    pub fn report_solving(&mut self, res: i32) {
        if res == 10 {
            self.report(b'1', 0);
        } else if res == 20 {
            self.report(b'0', 0);
        } else {
            self.report(b'?', 0);
        }
    }

    pub fn reset_solving(&mut self) {
        if self.termination_forced.load(Relaxed) {
            // TODO this leads potentially to a data race if the external
            // user is calling 'terminate' twice within one 'solve' call.
            // A proper solution would be to guard / protect setting the
            // 'termination_forced' flag and only allow it during solving and
            // ignore it otherwise thus also the second time it is called
            // during a 'solve' call.  We could move resetting it also the
            // start of 'solve'.
            //
            self.termination_forced.store(false, Relaxed);

            log!(self, "reset forced termination");
        }
    }

    pub fn restore_clauses(&mut self) -> i32 {
        let mut res = 0;
        if self.opts.restoreall <= 1 && self.external().tainted.is_empty() {
            log!(self, "no tainted literals and nothing to restore");
            self.report(b'*', 0);
        } else {
            self.report(b'+', 0);
            // remove_garbage_binaries ();
            self.external().restore_clauses();
            self.report(b'r', 0);
            if !self.unsat && self.level == 0 && !self.propagate() {
                log!(self, "root level propagation after restore produces conflict");
                self.learn_empty_clause();
                res = 20;
            }
        }
        res
    }

    pub fn lookahead(&mut self) -> i32 {
        debug_assert!(self.clause.is_empty());
        start!(self, lookahead);
        debug_assert!(!self.lookingahead);
        self.lookingahead = true;
        if self.external_prop {
            if self.level != 0 {
                // Combining lookahead with external propagator is limited
                // Note that lookahead_probing (); would also force backtrack
                // anyway
                self.backtrack(0);
            }
            log!(self, "external notifications are turned off during preprocessing.");
            self.private_steps = true;
        }
        let mut tmp = self.already_solved();
        if tmp == 0 {
            tmp = self.restore_clauses();
        }
        let mut res = 0;
        if tmp == 0 {
            res = self.lookahead_probing();
        }
        if res == i32::MIN {
            res = 0;
        }
        self.reset_solving();
        self.report_solving(tmp);
        debug_assert!(self.lookingahead);
        self.lookingahead = false;
        stop!(self, lookahead);
        if self.external_prop {
            self.private_steps = false;
            log!(self, "external notifications are turned back on.");
            self.notify_assignments(); // In case fixed assignments were found.
        }
        res
    }

    /*----------------------------------------------------------------------*/

    pub fn finalize(&mut self, res: i32) {
        if self.proof.is_none() {
            return;
        }
        log!(self, "finalizing");
        // finalize external units
        if self.frat {
            let external = self.ext_unbound();
            for evar in external.vars() {
                debug_assert!(evar > 0);
                let eidx = 2 * evar as usize;
                let mut sign = 1;
                let mut id = external.ext_units[eidx];
                if id == 0 {
                    sign = -1;
                    id = external.ext_units[eidx + 1];
                }
                if id != 0 {
                    self.proof.as_mut().unwrap().finalize_external_unit(id, evar * sign);
                }
            }
            // finalize internal units
            for lit in self.lits() {
                let elit = self.externalize(lit);
                if elit != 0 {
                    let eidx = (elit < 0) as u32 + 2u32 * elit.unsigned_abs();
                    let id = external.ext_units[eidx as usize];
                    if id != 0 {
                        debug_assert!(*self.unit_clauses(self.vlit(lit) as i32) == id);
                        continue;
                    }
                }
                let uidx = self.vlit(lit) as i32;
                let id = *self.unit_clauses(uidx);
                if id == 0 {
                    continue;
                }
                self.proof.as_mut().unwrap().finalize_unit(id, lit);
            }
            // See the discussion in 'propagate' on why garbage binary
            // clauses stick around.
            for i in 0..self.clauses.len() {
                let c = self.clauses[i];
                if !c.garbage() || (c.size() == 2 && !c.flushed()) {
                    self.proof.as_mut().unwrap().finalize_clause(c);
                }
            }

            // finalize conflict and proof
            if self.conflict_id != 0 {
                let conflict_id = self.conflict_id;
                self.proof.as_mut().unwrap().finalize_clause_lits(conflict_id, &[]);
            }
        }
        let conflict_id = self.conflict_id;
        self.proof.as_mut().unwrap().report_status(res, conflict_id);
        if res == 10 {
            self.external().conclude_sat();
        } else if res == 20 {
            self.conclude_unsat();
        } else if res == 0 {
            self.external().conclude_unknown();
        }
    }

    /*----------------------------------------------------------------------*/

    pub fn print_statistics(&mut self) {
        Stats::print(self);
        for st in self.stat_tracers.iter_mut() {
            st.print_stats();
        }
    }

    /*----------------------------------------------------------------------*/

    // Only useful for debugging purposes.

    /// C++ overload `Internal::dump` (renamed).
    pub fn dump_clause(&mut self, c: CRef) {
        for &lit in c.lits() {
            cprintf!("{} ", lit);
        }
        cprintf!("0\n");
    }

    pub fn dump(&mut self) {
        let mut m = self.assumptions.len() as i64;
        for idx in self.vars() {
            if self.fixed(idx) != 0 {
                m += 1;
            }
        }
        for &c in self.clauses.iter() {
            if !c.garbage() {
                m += 1;
            }
        }
        cprintf!("p cnf {} {}\n", self.max_var, m);
        for idx in self.vars() {
            let tmp = self.fixed(idx);
            if tmp != 0 {
                cprintf!("{} 0\n", if tmp < 0 { -idx } else { idx });
            }
        }
        for i in 0..self.clauses.len() {
            let c = self.clauses[i];
            if !c.garbage() {
                self.dump_clause(c);
            }
        }
        for &lit in self.assumptions.iter() {
            cprintf!("{} 0\n", lit);
        }
        crate::message::fflush(crate::message::c_stdout());
    }

    /*----------------------------------------------------------------------*/

    pub fn traverse_constraint(&mut self, it: &mut dyn ClauseIterator) -> bool {
        if self.constraint.is_empty() && !self.unsat_constraint {
            return true;
        }

        let mut eclause: Vec<i32> = Vec::new();
        if self.unsat {
            return it.clause(&eclause);
        }

        log!(self, &self.constraint, "traversing constraint");
        let mut satisfied = false;
        for &ilit in self.constraint.iter() {
            let tmp = self.fixed(ilit);
            if tmp > 0 {
                satisfied = true;
                break;
            }
            if tmp < 0 {
                continue;
            }
            let elit = self.externalize(ilit);
            eclause.push(elit);
        }
        if !satisfied && !it.clause(&eclause) {
            return false;
        }

        true
    }

    /*----------------------------------------------------------------------*/

    pub fn traverse_clauses(&mut self, it: &mut dyn ClauseIterator) -> bool {
        let mut eclause: Vec<i32> = Vec::new();
        if self.unsat {
            return it.clause(&eclause);
        }
        for &c in self.clauses.iter() {
            if c.garbage() {
                continue;
            }
            if c.redundant() {
                continue;
            }
            let mut satisfied = false;
            for &ilit in c.lits() {
                let tmp = self.fixed(ilit);
                if tmp > 0 {
                    satisfied = true;
                    break;
                }
                if tmp < 0 {
                    continue;
                }
                let elit = self.externalize(ilit);
                eclause.push(elit);
            }
            if !satisfied && !it.clause(&eclause) {
                return false;
            }
            eclause.clear();
        }
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn construct_internal_and_external() {
        let mut internal = Internal::new();
        let ip: *mut Internal = &mut *internal;
        let external = External::new(ip);
        assert!(std::ptr::eq(internal.external, &*external));
        assert_eq!(internal.max_var, 0);
        assert_eq!(internal.control.len(), 1);
        assert_eq!(internal.dummy_binary.size(), 2);
        assert_eq!(internal.opts.arenatype, 3);
        internal.enlarge_vals(4);
        internal.vsize = 4;
        internal.max_var = 3;
        internal.set_val(2, 1);
        assert_eq!(internal.val(2), 1);
        assert_eq!(internal.val(-2), -1);
        assert_eq!(internal.vars().collect::<Vec<_>>(), vec![1, 2, 3]);
        // The message macros accept 'Internal', 'External' and raw pointers.
        verbose!(ip, 3, "suppressed {}", 1);
        verbose!(external, 3, "suppressed {}", 2);
        verbose!(&mut *internal, 3, "suppressed");
        log!(ip, "not logged {}", 3);
        log!(external, "not logged {}", 4);
        log!(ip, &internal.clause, "not logged");
        drop(internal);
        drop(external);
    }
}

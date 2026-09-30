//! Port of `walk_full_occs.cpp`: random walk local search based on
//! 'ProbSAT' ideas with full occurrence lists (Kissat style).

use crate::clause::CRef;
use crate::internal::Internal;
use crate::random::Random;

/// `struct Tagged` (bit-field `binary : 1`, `counter_pos : 31`).
#[derive(Clone, Copy, Debug)]
pub struct Tagged {
    pub binary: bool,
    pub counter_pos: u32,
    #[cfg(debug_assertions)]
    pub c: CRef,
}

impl Tagged {
    pub fn new(d: CRef, pos: u32) -> Tagged {
        debug_assert!((pos & (1 << 31)) == 0);
        Tagged {
            binary: d.size() == 2,
            counter_pos: pos,
            #[cfg(debug_assertions)]
            c: d,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Counter {
    /// Number of false literals.
    pub count: u32,
    /// Pos in the broken clauses.
    pub pos: u32,
    /// Pointer to the clause itself.
    pub clause: CRef,
}

impl Counter {
    pub fn new(c: u32, p: u32, d: CRef) -> Counter {
        Counter { count: c, pos: p, clause: d }
    }
    pub fn new_unbroken(c: u32, d: CRef) -> Counter {
        Counter { count: c, pos: u32::MAX, clause: d }
    }
}

pub type TOccs = Vec<Tagged>;

/// `struct WalkerFO` (declared in 'walk_full_occs.cpp').
pub struct WalkerFO {
    pub internal: *mut Internal,
    /// Local random number generator.
    pub random: Random,
    /// Ticks to approximate run time.
    pub ticks: i64,
    /// Limit on number of propagations.
    pub limit: i64,
    /// Currently unsatisfied clauses.
    pub broken: Vec<Tagged>,
    /// Smallest considered score.
    pub epsilon: f64,
    /// Break value to score table.
    pub table: Vec<f64>,
    /// Scores of candidate literals.
    pub scores: Vec<f64>,
    /// Remember the flips compared to the last best saved model.
    pub flips: Vec<i32>,
    pub best_trail_pos: i32,
    pub minimum: i64,
    /// Best model found so far.
    pub best_values: Vec<i8>,
    pub tclauses: Vec<Counter>,
    pub tcounters: Vec<Vec<Tagged>>,
}

/*------------------------------------------------------------------------*/
// Port of the functions defined in 'walk_full_occs.cpp'.

#[allow(unused_imports)]
use crate::prelude::*;
use crate::format::fmt_f;
#[allow(unused_imports)]
use crate::util::{percent, relative, sign};

impl WalkerFO {
    pub const INVALID_POSITION: u32 = u32::MAX;

    /// `WalkerFO (Internal *, double size, int64_t limit)`.
    pub fn new(internal: *mut Internal, size: f64, limit: i64) -> WalkerFO {
        // SAFETY: 'internal' is the valid solver creating this walker.
        let i = unsafe { &mut *internal };
        let mut random = Random::new(i.opts.seed as u64); // global random seed
        random += i.stats.walk.count as u64; // different seed every time
        let mut flips = Vec::new();
        flips.reserve((i.max_var / 4) as usize);
        let mut w = WalkerFO {
            internal,
            random,
            ticks: 0,
            limit,
            broken: Vec::new(),
            epsilon: 0.0,
            table: Vec::new(),
            scores: Vec::new(),
            flips,
            best_trail_pos: -1,
            minimum: i64::MAX,
            best_values: vec![0; (i.max_var + 1) as usize],
            tclauses: Vec::new(),
            tcounters: Vec::new(),
        };
        w.tcounters.resize_with((i.max_var * 2 + 2) as usize, Vec::new);

        // This is the magic constant in ProbSAT (also called 'CB'), which we
        // pick according to the average size every second invocation and
        // otherwise just the default '2.0', which turns into the base '0.5'.
        //
        let use_size_based_cb = (i.stats.walk.count & 1) != 0;
        let cb = if use_size_based_cb { fitcbval(size) } else { 2.0 };
        debug_assert!(cb != 0.0);
        let base = 1.0 / cb; // scores are 'base^0,base^1,base^2,...

        let mut next: f64 = 1.0;
        w.epsilon = next;
        while next != 0.0 {
            w.epsilon = next;
            w.table.push(w.epsilon);
            next = w.epsilon * base;
        }

        phase!(
            internal,
            "walk",
            i.stats.walk.count,
            "CB {} with inverse {} as base and table size {}",
            fmt_f(cb, 2),
            fmt_f(base, 2),
            w.table.len()
        );
        w
    }

    /// Unbounded mutable access to the solver (C++ 'internal->').
    #[inline(always)]
    #[allow(clippy::mut_from_ref)]
    fn internal_mut<'a>(&self) -> &'a mut Internal {
        // SAFETY: the walker is a local object of 'walk_full_occs_round' and
        // does not outlive the solver it points to.
        unsafe { &mut *self.internal }
    }

    #[inline]
    fn internal(&self) -> &Internal {
        // SAFETY: the walker does not outlive the solver.
        unsafe { &*self.internal }
    }

    pub fn occs(&mut self, lit: i32) -> &mut TOccs {
        let idx = self.internal().vlit(lit) as usize;
        debug_assert!(idx < self.tcounters.len());
        &mut self.tcounters[idx]
    }

    pub fn occs_ref(&self, lit: i32) -> &TOccs {
        let idx = self.internal().vlit(lit) as usize;
        debug_assert!(idx < self.tcounters.len());
        &self.tcounters[idx]
    }

    /// C++ overload `connect_clause (int lit, Clause *, unsigned pos)`.
    pub fn connect_clause_lit(&mut self, lit: i32, clause: CRef, pos: u32) {
        debug_assert!((pos as usize) < self.tclauses.len());
        debug_assert!(self.tclauses[pos as usize].clause == clause);
        log!(
            self.internal(),
            clause,
            "connecting clause on {} with already in occurrences {}",
            lit,
            self.occs_ref(lit).len()
        );
        self.occs(lit).push(Tagged::new(clause, pos));
    }

    /// C++ overload `connect_clause (Clause *, unsigned pos)`.
    pub fn connect_clause(&mut self, clause: CRef, pos: u32) {
        debug_assert!((pos as usize) < self.tclauses.len());
        debug_assert!(self.tclauses[pos as usize].clause == clause);
        for i in 0..clause.size() as usize {
            let lit = clause.lit(i);
            self.connect_clause_lit(lit, clause, pos);
        }
    }

    pub fn check_occs(&self) {
        #[cfg(debug_assertions)]
        {
            let internal = self.internal();
            for lit in internal.lits() {
                for w in self.occs_ref(lit) {
                    debug_assert!((w.counter_pos as usize) < self.tclauses.len());
                }
            }
            let mut unsatisfied = 0usize;
            for c in self.tclauses.iter() {
                let mut count = 0u32;
                log!(internal, c.clause, "checking clause with counter {}:", c.count);
                for &lit in c.clause.lits() {
                    if internal.val(lit) > 0 {
                        count += 1;
                    }
                }
                debug_assert!(count == c.count);
                if count == 0 {
                    unsatisfied += 1;
                }
            }
            debug_assert!(self.broken.len() == unsatisfied);
        }
    }

    pub fn check_broken(&self) {
        #[cfg(debug_assertions)]
        {
            let internal = self.internal();
            for t in self.broken.iter() {
                debug_assert!(!t.c.is_null());
                debug_assert!((t.counter_pos as usize) < self.tclauses.len());
                debug_assert!(self.tclauses[t.counter_pos as usize].clause == t.c);
                for &lit in t.c.lits() {
                    debug_assert!(internal.val(lit) < 0);
                }
            }
        }
    }

    pub fn check_all(&self) {
        self.check_broken();
        self.check_occs();
    }


    pub fn push_flipped(&mut self, flipped: i32) {
        log!(self.internal, "push literal {} on the flips", loglit!(self.internal, flipped));
        debug_assert!(flipped != 0);
        if self.best_trail_pos < 0 {
            log!(
                self.internal,
                "not pushing flipped {} to already invalid trail",
                loglit!(self.internal, flipped)
            );
            return;
        }

        let size_trail = self.flips.len();
        let limit = (self.internal().max_var / 4 + 1) as usize;
        if size_trail < limit {
            self.flips.push(flipped);
            log!(
                self.internal,
                "pushed flipped {} to trail which now has size {}",
                loglit!(self.internal, flipped),
                size_trail + 1
            );
            return;
        }

        if self.best_trail_pos != 0 {
            log!(
                self.internal,
                "trail reached limit {} but has best position {}",
                limit,
                self.best_trail_pos
            );
            self.save_walker_trail(true);
            self.flips.push(flipped);
            log!(
                self.internal,
                "pushed flipped {} to trail which now has size {}",
                loglit!(self.internal, flipped),
                self.flips.len()
            );
        } else {
            log!(self.internal, "trail reached limit {} without best position", limit);
            self.flips.clear();
            log!(
                self.internal,
                "not pushing {} to invalidated trail",
                loglit!(self.internal, flipped)
            );
            self.best_trail_pos = -1;
            log!(self.internal, "best trail position becomes invalid");
        }
    }

    pub fn save_walker_trail(&mut self, keep: bool) {
        debug_assert!(self.best_trail_pos != -1);
        debug_assert!(self.best_trail_pos as usize <= self.flips.len());
        #[cfg(feature = "logging")]
        let size_trail = self.flips.len();
        let kept: i32 = self.flips.len() as i32 - self.best_trail_pos;
        log!(
            self.internal,
            "saving {} values of flipped literals on trail of size {}",
            self.best_trail_pos,
            size_trail
        );

        let begin = 0usize;
        let best = self.best_trail_pos as usize;
        let end = self.flips.len();

        let mut it = begin;
        while it != best {
            let lit = self.flips[it];
            debug_assert!(lit != 0);
            let value = sign(lit) as i8;
            let idx = lit.abs();
            self.best_values[idx as usize] = value;
            it += 1;
        }
        if !keep {
            log!(self.internal, "no need to shift and keep remaining {} literals", kept as u32);
            return;
        }

        #[cfg(debug_assertions)]
        {
            let internal = self.internal();
            for v in internal.vars() {
                if internal.active(v) {
                    debug_assert!(self.best_values[v as usize] == internal.phases.saved[v as usize]);
                }
            }
        }
        log!(
            self.internal,
            "flushed {} literals {}% from trail",
            self.best_trail_pos as u32,
            fmt_f(percent(self.best_trail_pos as f64, size_trail as f64), 0)
        );
        debug_assert!(it == best);
        let mut jt = begin;
        while it != end {
            debug_assert!(jt <= it);
            debug_assert!(it < end);
            self.flips[jt] = self.flips[it];
            it += 1;
            jt += 1;
        }

        debug_assert!((end - jt) as i32 == self.best_trail_pos);
        debug_assert!((jt - begin) as i32 == kept);
        self.flips.resize(kept as usize, 0);
        log!(
            self.internal,
            "keeping {} literals {}% on trail",
            kept as u32,
            fmt_f(percent(kept as f64, size_trail as f64), 0)
        );
        log!(self.internal, "reset best trail position to 0");
        self.best_trail_pos = 0;
    }

    /// Finally export the final minimum.
    pub fn save_final_minimum(&mut self, old_init_minimum: i64) {
        debug_assert!(self.minimum <= old_init_minimum);
        let _ = old_init_minimum;

        if self.best_trail_pos == 0 || self.best_trail_pos == -1 {
            log!(self.internal, "minimum already saved");
        } else {
            self.save_walker_trail(false);
        }

        let internal = self.internal_mut();
        internal.stats.walk.improved += 1;
        for v in internal.vars() {
            if self.best_values[v as usize] != 0 {
                internal.phases.saved[v as usize] = self.best_values[v as usize];
            } else {
                debug_assert!(!internal.active(v));
            }
        }
        internal.copy_phases(PhaseKind::Prev);
    }

    /// Compute score from break count.  The scores are tabulated for faster
    /// computation (to avoid 'pow').
    #[inline]
    pub fn score(&mut self, i: u32) -> f64 {
        let res = if (i as usize) < self.table.len() { self.table[i as usize] } else { self.epsilon };
        log!(self.internal, "break {} mapped to score {}", i, crate::format::fmt_g(res));
        res
    }

    /*--------------------------------------------------------------------*/

    pub fn walk_full_occs_pick_clause(&mut self) -> u32 {
        self.internal().require_mode(Mode::WALK);
        debug_assert!(!self.broken.is_empty());
        let mut size = self.broken.len() as i64;
        if size > i32::MAX as i64 {
            size = i32::MAX as i64;
        }
        let pos = self.random.pick_int(0, (size - 1) as i32);
        let res = self.broken[pos as usize].counter_pos;
        log!(self.internal, self.tclauses[res as usize].clause, "picking random position {}", pos);
        res
    }

    /*--------------------------------------------------------------------*/

    /// Compute the number of clauses which would be become unsatisfied if
    /// 'lit' is flipped and set to false.  This is called the
    /// 'break-count' of 'lit'.
    pub fn walk_full_occs_break_value(&mut self, lit: i32) -> u32 {
        let internal = self.internal_mut();
        internal.require_mode(Mode::WALK);
        debug_assert!(internal.val(lit) > 0);
        start!(internal, walkbreak);

        let old = self.ticks as u64;
        let mut res: u32 = 0; // The computed break-count of 'lit'.
        self.ticks +=
            1 + internal.cache_lines_n(self.occs_ref(lit).len(), std::mem::size_of::<*const Clause>());

        for w in self.occs_ref(lit).iter() {
            let r = w.counter_pos as usize;
            debug_assert!(r < self.tclauses.len());
            res += (self.tclauses[r].count == 1) as u32;
        }

        internal.stats.ticks.walkbreak =
            (internal.stats.ticks.walkbreak as u64).wrapping_add((self.ticks as u64).wrapping_sub(old)) as i64;
        stop!(internal, walkbreak);
        res
    }

    /*--------------------------------------------------------------------*/

    /// Given an unsatisfied clause 'c', in which we want to flip a literal,
    /// we first determine the exponential score based on the break-count of
    /// its literals and then sample the literals based on these scores (see
    /// 'walk.cpp').
    pub fn walk_full_occs_pick_lit(&mut self, c: CRef) -> i32 {
        let internal = self.internal_mut();
        start!(internal, walkpick);
        log!(internal, "picking literal by break-count");
        debug_assert!(self.scores.is_empty());
        self.ticks += 1;
        let old = self.ticks;
        let mut sum: f64 = 0.0;
        let mut propagations: i64 = 0;
        let size = c.size() as usize;
        for k in 0..size {
            let lit = c.lit(k);
            debug_assert!(internal.active(lit));
            if internal.var(lit).level == 1 {
                log!(internal, "skipping assumption {} for scoring", -lit);
                continue;
            }
            propagations += 1;
            let tmp = self.walk_full_occs_break_value(-lit);
            let score = self.score(tmp);
            log!(internal, "literal {} break-count {} score {}", lit, tmp, crate::format::fmt_g(score));
            self.scores.push(score);
            sum += score;
        }
        let _ = propagations; // TODO unused?
        log!(internal, "scored {} literals", self.scores.len());
        debug_assert!(!self.scores.is_empty());
        debug_assert!(self.scores.len() <= c.size() as usize);
        let lim = sum * self.random.generate_double();
        log!(
            internal,
            "score sum {} limit {}",
            crate::format::fmt_g(sum),
            crate::format::fmt_g(lim)
        );

        let end = c.size() as usize;
        let mut i = 0usize;
        let mut j = 0usize;
        let mut res;
        loop {
            debug_assert!(i != end);
            res = c.lit(i);
            i += 1;
            if internal.var(res).level > 1 {
                break;
            }
            log!(internal, "skipping assumption {} without score", -res);
        }
        sum = self.scores[j];
        j += 1;
        while sum <= lim && i != end {
            res = c.lit(i);
            i += 1;
            if internal.var(res).level == 1 {
                log!(internal, "skipping assumption {} without score", -res);
                continue;
            }
            sum += self.scores[j];
            j += 1;
        }
        self.scores.clear();
        log!(internal, "picking literal {} by break-count", res);
        internal.stats.ticks.walkpick += self.ticks - old;
        stop!(internal, walkpick);
        res
    }

    /*--------------------------------------------------------------------*/

    pub fn make_clause(&mut self, t: Tagged) {
        let tp = t.counter_pos as usize;
        debug_assert!(tp < self.tclauses.len());
        // TODO invalidate position in 'unsatisfied'
        let count = self.tclauses[tp].count;
        self.tclauses[tp].count = count.wrapping_add(1);
        if count != 0 {
            log!(
                self.internal,
                self.tclauses[tp].clause,
                "already made with counter {} at position {}",
                self.tclauses[tp].count as i32,
                self.tclauses[tp].pos as i32
            );
            #[cfg(debug_assertions)]
            debug_assert!(self.tclauses[tp].clause == t.c);
            debug_assert!(self.tclauses[tp].pos == WalkerFO::INVALID_POSITION);
            return;
        }
        log!(
            self.internal,
            self.tclauses[tp].clause,
            "make with counter {} at position {}",
            self.tclauses[tp].count as i32,
            self.tclauses[tp].pos as i32
        );
        debug_assert!(self.tclauses[tp].pos != WalkerFO::INVALID_POSITION);
        debug_assert!((self.tclauses[tp].pos as usize) < self.broken.len());
        self.ticks += 1;
        let last = *self.broken.last().unwrap();
        #[cfg(debug_assertions)]
        {
            debug_assert!(self.tclauses[tp].clause == t.c);
            debug_assert!((last.counter_pos as usize) < self.tclauses.len());
            debug_assert!(self.tclauses[last.counter_pos as usize].clause == last.c);
        }
        let pos = self.tclauses[tp].pos;
        debug_assert!((pos as usize) < self.broken.len());
        self.broken[pos as usize] = last;
        // the order is important
        self.tclauses[last.counter_pos as usize].pos = pos;
        self.tclauses[tp].pos = WalkerFO::INVALID_POSITION;
        self.broken.pop();
    }

    pub fn make_clauses_along_occurrences(&mut self, lit: i32) {
        let internal = self.internal_mut();
        let oidx = internal.vlit(lit) as usize;
        log!(
            internal,
            "making clauses with {} along {} occurrences",
            loglit!(internal, lit),
            self.tcounters[oidx].len()
        );
        debug_assert!(internal.val(lit) > 0);
        let mut made: usize = 0;
        self.ticks += 1 + internal
            .cache_lines_n(self.tcounters[oidx].len(), std::mem::size_of::<*const Clause>());

        // 'make_clause' does not touch the occurrence lists.
        let n = self.tcounters[oidx].len();
        for k in 0..n {
            let c = self.tcounters[oidx][k];
            self.make_clause(c);
            made += 1;
        }
        log!(
            internal,
            "made {} clauses by flipping {}, still {} broken",
            made,
            lit,
            self.broken.len()
        );
        log!(internal, "made {} clauses with flipped {}", made, loglit!(internal, lit));
        let _ = made;
    }

    pub fn make_clauses_along_unsatisfied(&mut self, lit: i32) {
        let internal = self.internal_mut();
        log!(
            internal,
            "making clauses with {} along {} unsatisfied",
            loglit!(internal, lit),
            self.broken.len()
        );
        debug_assert!(internal.val(lit) > 0);
        let mut made: usize = 0;
        // TODO flush made clauses from 'unsatisfied' directly.
        // TODO 'stats.make_visited++', 'made++' appropriately.
        // (Faithfully ported: the outer 'j' is shadowed by the loop variable
        // in C++ and thus stays zero.)
        let j_outer: usize = 0;
        let size = self.broken.len();
        self.ticks +=
            1 + internal.cache_lines_n(self.broken.len(), std::mem::size_of::<*const Clause>());
        let mut i = 0usize;
        let mut j = 0usize;
        while i < size {
            debug_assert!(i >= j);
            let c = self.broken[i];
            let dpos = c.counter_pos as usize;
            self.broken[j] = self.broken[i];
            j += 1;
            debug_assert!(self.tclauses[dpos].pos != WalkerFO::INVALID_POSITION);
            let dclause = self.tclauses[dpos].clause;
            for k in 0..dclause.size() as usize {
                let other = dclause.lit(k);
                if lit == other {
                    made += 1;
                    j -= 1;
                    self.tclauses[dpos].count = self.tclauses[dpos].count.wrapping_add(1);
                    log!(internal, dclause, "made with count {}", self.tclauses[dpos].count as i32);
                    self.tclauses[dpos].pos = WalkerFO::INVALID_POSITION;
                    break;
                }
            }
            if self.tclauses[dpos].pos != WalkerFO::INVALID_POSITION {
                log!(internal, dclause, "still broken");
            }
            debug_assert!(made + j == i + 1); // assertions holds after incrementing 'i'
            i += 1;
        }
        debug_assert!(j_outer <= size);
        self.broken.resize(
            j_outer,
            Tagged {
                binary: false,
                counter_pos: 0,
                #[cfg(debug_assertions)]
                c: CRef::NULL,
            },
        );
        log!(internal, "made {} clauses with flipped {}", made, loglit!(internal, lit));
        let _ = made;
    }

    pub fn make_clauses(&mut self, lit: i32) {
        let internal = self.internal_mut();
        start!(internal, walkflipWL);
        let old = self.ticks;
        // In babywalk this work because there are not counter
        // if (this->occs(lit).size() > broken.size())
        //   make_clauses_along_unsatisfied(lit);
        // else
        self.make_clauses_along_occurrences(lit);
        internal.stats.ticks.walkflipWL += self.ticks - old;
        stop!(internal, walkflipWL);
    }

    pub fn break_clauses(&mut self, lit: i32) {
        let internal = self.internal_mut();
        start!(internal, walkflipbroken);
        let old = self.ticks;
        log!(internal, "breaking clauses on {}", loglit!(internal, lit));
        // Finally add all new unsatisfied (broken) clauses.

        #[cfg(feature = "logging")]
        let mut broken: i64 = 0;
        let oidx = internal.vlit(lit) as usize;
        self.ticks += 1 + internal
            .cache_lines_n(self.tcounters[oidx].len(), std::mem::size_of::<*const Clause>());

        log!(internal, "trying to break {} clauses", self.tcounters[oidx].len());

        let n = self.tcounters[oidx].len();
        for k in 0..n {
            let w = self.tcounters[oidx][k];
            let pos = w.counter_pos as usize;
            #[cfg(debug_assertions)]
            log!(internal, self.tclauses[pos].clause, "trying to break");
            self.tclauses[pos].count = self.tclauses[pos].count.wrapping_sub(1);
            if self.tclauses[pos].count != 0 {
                continue;
            }
            self.tclauses[pos].pos = self.broken.len() as u32;
            self.ticks += 1;
            self.broken.push(w);
            #[cfg(feature = "logging")]
            {
                broken += 1;
            }
        }
        log!(internal, "broken {} clauses by flipping {}", broken, lit);
        internal.stats.ticks.walkflipbroken += self.ticks - old;
        stop!(internal, walkflipbroken);
    }

    pub fn walk_full_occs_flip_lit(&mut self, lit: i32) {
        let internal = self.internal_mut();
        internal.require_mode(Mode::WALK);
        log!(internal, "flipping assign {}", lit);
        debug_assert!(internal.val(lit) < 0);
        let old = self.ticks;

        // First flip the literal value.
        //
        let tmp = sign(lit);
        let idx = lit.abs();
        internal.set_val(idx, tmp as i8);
        debug_assert!(internal.val(lit) > 0);

        self.make_clauses(lit);
        self.break_clauses(-lit);

        if !self.broken.is_empty() {
            self.check_all();
        }
        internal.stats.ticks.walkflip += self.ticks - old;
    }
}

// These are in essence the CB values from Adrian Balint's thesis.  They
// denote the inverse 'cb' of the base 'b' of the (probability) weight
// 'b^-i' for picking a literal with the break value 'i' (first column is
// the 'size', second the 'CB' value).

static CBVALS: [[f64; 2]; 6] = [
    [0.0, 2.00],
    [3.0, 2.50],
    [4.0, 2.85],
    [5.0, 3.70],
    [6.0, 5.10],
    [7.0, 7.40], // Adrian has '5.4', but '7.4' looks better.
];

const NCBVALS: usize = CBVALS.len();

/// Interpolate the CB values for uniform random SAT formula to the non
/// integer situation of average clause size by piecewise linear functions.
#[inline]
fn fitcbval(size: f64) -> f64 {
    let mut i = 0usize;
    while i + 2 < NCBVALS && (CBVALS[i][0] > size || CBVALS[i + 1][0] < size) {
        i += 1;
    }
    let x2 = CBVALS[i + 1][0];
    let x1 = CBVALS[i][0];
    let y2 = CBVALS[i + 1][1];
    let y1 = CBVALS[i][1];
    let dx = x2 - x1;
    let dy = y2 - y1;
    debug_assert!(dx != 0.0);
    let res = dy * (size - x1) / dx + y1;
    debug_assert!(res > 0.0);
    res
}

/*------------------------------------------------------------------------*/

impl Internal {
    /// Check whether to save the current phases as new global minimum.
    #[inline]
    pub fn walk_full_occs_save_minimum(&mut self, walker: &mut WalkerFO) {
        let broken = walker.broken.len() as i64;
        if broken >= walker.minimum {
            return;
        }
        if broken <= self.stats.walk.minimum {
            self.stats.walk.minimum = broken;
            verbose!(self, 3, "new global minimum {}", broken);
        } else {
            verbose!(self, 3, "new walk minimum {}", broken);
        }

        walker.minimum = broken;

        #[cfg(debug_assertions)]
        for i in self.vars() {
            let tmp = self.val(i);
            if tmp != 0 {
                self.phases.saved[i as usize] = tmp;
            }
        }

        if walker.best_trail_pos == -1 {
            for i in self.vars() {
                let tmp = self.val(i);
                if tmp != 0 {
                    walker.best_values[i as usize] = tmp;
                    #[cfg(debug_assertions)]
                    debug_assert!(tmp == self.phases.saved[i as usize]);
                }
            }
            walker.best_trail_pos = 0;
        } else {
            walker.best_trail_pos = walker.flips.len() as i32;
            log!(self, "new best trail position {}", walker.best_trail_pos as u32);
        }
    }

    /*--------------------------------------------------------------------*/

    pub fn walk_full_occs_round(&mut self, limit: i64, prev: bool) -> i32 {
        self.stats.walk.count += 1;

        self.reset_watches();

        // Remove all fixed variables first (assigned at decision level
        // zero).
        //
        if self.last.collect.fixed < self.stats.all.fixed {
            self.garbage_collection();
        }

        // We want to see more messages during initial local search.
        //
        if self.localsearching {
            debug_assert!(!self.force_phase_messages);
            self.force_phase_messages = true;
        }

        phase!(self, "walk", self.stats.walk.count, "random walk limit of {} propagations", limit);

        // First compute the average clause size for picking the CB constant.
        //
        let mut size: f64 = 0.0;
        let mut n: i64 = 0;
        for ci in 0..self.clauses.len() {
            let c = self.clauses[ci];
            if c.garbage() {
                continue;
            }
            if c.redundant() {
                if self.opts.walkredundant == 0 {
                    continue;
                }
                if !self.likely_to_be_kept_clause(c) {
                    continue;
                }
            }
            size += c.size() as f64;
            n += 1;
        }
        let average_size = relative(size, n as f64);

        phase!(
            self,
            "walk",
            self.stats.walk.count,
            "{} clauses average size {} over {} variables",
            n,
            fmt_f(average_size, 2),
            self.active_count()
        );

        // Instantiate data structures for this local search round.
        //
        let mut walker = WalkerFO::new(self as *mut Internal, average_size, limit);

        let mut failed = false; // Inconsistent assumptions?

        self.level = 1; // Assumed variables assigned at level 1.

        if self.assumptions.is_empty() {
            log!(self, "no assumptions so assigning all variables to decision phase");
        } else {
            log!(self, "assigning assumptions to their forced phase first");
            for k in 0..self.assumptions.len() {
                let lit = self.assumptions[k];
                let mut tmp = self.val(lit);
                if tmp > 0 {
                    continue;
                }
                if tmp < 0 {
                    log!(self, "inconsistent assumption {}", lit);
                    failed = true;
                    break;
                }
                if !self.active(lit) {
                    continue;
                }
                tmp = sign(lit) as i8;
                let idx = lit.abs();
                log!(self, "initial assign {} to assumption phase", if tmp < 0 { -idx } else { idx });
                self.set_val(idx, tmp);
                debug_assert!(self.level == 1);
                self.var_mut(idx).level = 1;
            }
            if !failed {
                log!(self, "now assigning remaining variables to their decision phase");
            }
        }

        self.level = 2; // All other non assumed variables assigned at level 2.

        if !failed {
            let target = if self.opts.warmup != 0 {
                false
            } else {
                self.stable || self.opts.target == 2
            };
            for idx in self.vars() {
                if !self.active(idx) {
                    log!(self, "skipping inactive variable {}", idx);
                    continue;
                }
                if self.val(idx) != 0 {
                    debug_assert!(self.var(idx).level == 1);
                    log!(self, "skipping assumed variable {}", idx);
                    continue;
                }
                let mut tmp: i32 = 0;
                if prev {
                    tmp = self.phases.prev[idx as usize] as i32;
                }
                if tmp == 0 {
                    tmp = sign(self.decide_phase(idx, target));
                }
                debug_assert!(tmp == 1 || tmp == -1);
                self.set_val(idx, tmp as i8);
                debug_assert!(self.level == 2);
                self.var_mut(idx).level = 2;
                walker.best_values[idx as usize] = tmp as i8;
                log!(self, "initial assign {} to decision phase", if tmp < 0 { -idx } else { idx });
            }

            log!(self, "watching satisfied and registering broken clauses");
            #[cfg(feature = "logging")]
            let mut watched: i64 = 0;
            for ci in 0..self.clauses.len() {
                let c = self.clauses[ci];

                if c.garbage() {
                    continue;
                }
                if c.redundant() {
                    if self.opts.walkredundant == 0 {
                        continue;
                    }
                    if !self.likely_to_be_kept_clause(c) {
                        continue;
                    }
                }

                let mut satisfiable = false; // contains not only assumptions
                let mut satisfied: i32 = 0; // clause satisfied?

                let size = c.size();

                // Move to front satisfied literals and determine whether
                // there is at least one (non-assumed) literal that can be
                // flipped.
                //
                for i in 0..size {
                    let lit = c.lit(i as usize);
                    debug_assert!(self.active(lit)); // Due to garbage collection.
                    if self.val(lit) > 0 {
                        c.swap_lits(satisfied as usize, i as usize);
                        let was = satisfied;
                        satisfied += 1;
                        if was == 0 {
                            log!(self, "first satisfying literal {}", lit);
                        }
                    } else if !satisfiable && self.var(lit).level > 1 {
                        log!(self, "non-assumption potentially satisfying literal {}", lit);
                        satisfiable = true;
                    }
                }

                if satisfied == 0 && !satisfiable {
                    log!(self, c, "due to assumptions unsatisfiable");
                    log!(self, "stopping local search since assumptions falsify a clause");
                    failed = true;
                    break;
                }

                let pos = walker.tclauses.len() as u32;
                walker.tclauses.push(Counter::new_unbroken(satisfied as u32, c));
                walker.connect_clause(c, pos);

                if satisfied == 0 {
                    debug_assert!(satisfiable); // at least one non-assumed variable ...
                    log!(self, c, "broken");
                    walker.tclauses[pos as usize].pos = walker.broken.len() as u32;
                    walker.broken.push(Tagged::new(c, pos));
                } else {
                    #[cfg(feature = "logging")]
                    {
                        watched += 1; // to be able to compare the number with walk
                    }
                }
            }
            #[cfg(feature = "logging")]
            if !failed {
                let broken = walker.broken.len() as i64;
                let total = watched + broken;
                msg!(
                    self,
                    "watching {} clauses {}% out of {} (watched and broken)",
                    watched,
                    fmt_f(percent(watched as f64, total as f64), 0),
                    total
                );
            }
        }
        walker.check_all();
        let res: i32; // Tells caller to continue with local search.

        if !failed {
            let mut broken = walker.broken.len() as i64;
            let initial_minimum = broken;

            phase!(
                self,
                "walk",
                self.stats.walk.count,
                "starting with {} unsatisfied clauses ({}% out of {})",
                broken,
                fmt_f(percent(broken as f64, self.stats.current.irredundant as f64), 0),
                self.stats.current.irredundant
            );

            self.walk_full_occs_save_minimum(&mut walker);
            debug_assert!(self.stats.walk.minimum <= walker.minimum);

            let mut minimum = broken;
            let mut flips: i64 = 0;
            while !self.terminated_asynchronously(1)
                && !walker.broken.is_empty()
                && walker.ticks < walker.limit
            {
                flips += 1;
                self.stats.walk.flips += 1;
                self.stats.walk.broken += broken;
                let pos = walker.walk_full_occs_pick_clause();
                let c = walker.tclauses[pos as usize].clause;
                let lit = walker.walk_full_occs_pick_lit(c);
                walker.walk_full_occs_flip_lit(lit);
                walker.push_flipped(lit);
                broken = walker.broken.len() as i64;
                log!(self, "now have {} broken clauses in total", broken);
                if broken >= minimum {
                    continue;
                }
                minimum = broken;
                verbose!(self, 3, "new phase minimum {} after {} flips", minimum, flips);
                self.walk_full_occs_save_minimum(&mut walker);
            }

            walker.save_final_minimum(initial_minimum);
            if minimum == initial_minimum {
                phase!(
                    self,
                    "walk",
                    self.stats.walk.count,
                    "{}no improvement {}{} in {} flips and {} ticks",
                    crate::terminal::tout().bright_yellow_code(),
                    minimum,
                    crate::terminal::tout().normal_code(),
                    flips,
                    walker.ticks
                );
            } else {
                phase!(
                    self,
                    "walk",
                    self.stats.walk.count,
                    "best phase minimum {} in {} flips and {} ticks",
                    minimum,
                    flips,
                    walker.ticks
                );
            }

            if self.opts.profile >= 2 {
                let started = self.profiles[ProfileId::walk].started;
                phase!(
                    self,
                    "walk",
                    self.stats.walk.count,
                    "{} million ticks per second",
                    fmt_f(1e-6 * relative(walker.ticks as f64, self.time() - started), 2)
                );

                phase!(
                    self,
                    "walk",
                    self.stats.walk.count,
                    "{} thousand flips per second",
                    fmt_f(relative(1e-3 * flips as f64, self.time() - started), 2)
                );
            } else {
                phase!(
                    self,
                    "walk",
                    self.stats.walk.count,
                    "{} ticks",
                    fmt_f(1e-6 * walker.ticks as f64, 2)
                );

                phase!(
                    self,
                    "walk",
                    self.stats.walk.count,
                    "{} thousand flips",
                    fmt_f(1e-3 * flips as f64, 2)
                );
            }

            if minimum > 0 {
                log!(self, "minimum {} non-zero thus potentially continue", minimum);
                res = 0;
            } else {
                log!(self, "minimum is zero thus stop local search");
                res = 10;
            }
        } else {
            res = 20;

            phase!(self, "walk", self.stats.walk.count, "aborted due to inconsistent assumptions");
        }

        for idx in self.vars() {
            if self.active(idx) {
                self.set_val(idx, 0);
            }
        }

        debug_assert!(self.level == 2);
        self.level = 0;

        self.init_watches();
        self.connect_watches(false);

        if self.localsearching {
            debug_assert!(self.force_phase_messages);
            self.force_phase_messages = false;
        }
        self.stats.ticks.walk += walker.ticks;
        res
    }

    pub fn walk_full_occs(&mut self) {
        start_inner_walk!(self);

        self.backtrack(0);
        if self.propagated < self.trail.len() && !self.propagate() {
            log!(self, "empty clause after root level propagation");
            self.learn_empty_clause();
            stop_inner_walk!(self);
            return;
        }

        let mut res = 0;
        if self.opts.warmup != 0 {
            res = self.warmup();
        }
        if res != 0 {
            log!(self, "stopping walk due to warmup");
            stop_inner_walk!(self);
            return;
        }
        let ticks = self.stats.ticks.search[0] + self.stats.ticks.search[1];
        let mut limit = ticks - self.last.walk.ticks;
        verbose!(
            self,
            2,
            "walk scheduling: last {} current {} delta {}",
            self.last.walk.ticks,
            ticks,
            limit
        );
        self.last.walk.ticks = ticks;
        limit = (limit as f64 * (1e-3 * self.opts.walkeffort as f64)) as i64;
        if limit < self.opts.walkmineff as i64 {
            limit = self.opts.walkmineff as i64;
        }
        // local search is very cache friendly, so we actually really go over
        // a lot of ticks
        if limit as f64 > 1e3 * self.opts.walkmaxeff as f64 {
            msg!(self, "reached maximum efficiency {}", limit);
            limit = (1e3 * self.opts.walkmaxeff as f64) as i64;
        }
        let _ = self.walk_full_occs_round(limit, false);
        stop_inner_walk!(self);
        debug_assert!(!self.unsat);
    }
}

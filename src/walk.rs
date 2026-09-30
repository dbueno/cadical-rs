//! Port of `walk.hpp` and `walk.cpp`: ProbSAT/WalkSAT style local search.

use crate::clause::CRef;
use crate::internal::Internal;
use crate::random::Random;

/// A binary clause in the broken list (the clause pointer is only kept for
/// logging and checking).
#[derive(Clone, Copy, Debug)]
pub struct TaggedBinary {
    pub lit: i32,
    pub other: i32,
    #[cfg(any(feature = "logging", debug_assertions))]
    pub d: CRef,
}

impl TaggedBinary {
    /// `TaggedBinary (Clause *c, int clit, int cother)`.
    #[inline]
    pub fn new(c: CRef, clit: i32, cother: i32) -> TaggedBinary {
        #[cfg(feature = "logging")]
        {
            debug_assert!(c.lit(0) == clit || c.lit(1) == clit);
            debug_assert!(c.lit(0) == cother || c.lit(1) == cother);
        }
        let _ = c;
        TaggedBinary {
            lit: clit,
            other: cother,
            #[cfg(any(feature = "logging", debug_assertions))]
            d: c,
        }
    }
    /// `TaggedBinary (Clause *c)`.
    #[inline]
    pub fn from_clause(c: CRef) -> TaggedBinary {
        debug_assert!(c.size() == 2);
        TaggedBinary {
            lit: c.lit(0),
            other: c.lit(1),
            #[cfg(any(feature = "logging", debug_assertions))]
            d: c,
        }
    }
}

/// Hand rolled `std::variant <Clause*, TaggedBinary>`.
#[derive(Clone, Copy, Debug)]
pub enum ClauseOrBinary {
    Clause(CRef),
    Binary(TaggedBinary),
}

impl Default for ClauseOrBinary {
    fn default() -> Self {
        ClauseOrBinary::Clause(CRef::NULL)
    }
}

impl ClauseOrBinary {
    #[inline]
    pub fn is_binary(&self) -> bool {
        matches!(self, ClauseOrBinary::Binary(_))
    }
    #[inline]
    pub fn clause(&self) -> CRef {
        match self {
            ClauseOrBinary::Clause(c) => *c,
            ClauseOrBinary::Binary(_) => {
                debug_assert!(false);
                CRef::NULL
            }
        }
    }
    #[inline]
    pub fn tagged_binary(&mut self) -> &mut TaggedBinary {
        match self {
            ClauseOrBinary::Binary(b) => b,
            ClauseOrBinary::Clause(_) => panic!("not a binary"),
        }
    }
}

/// `struct Walker` (declared in 'walk.cpp').
pub struct Walker {
    pub internal: *mut Internal,
    /// Local random number generator.
    pub random: Random,
    /// Ticks to approximate run time.
    pub ticks: i64,
    /// Limit on number of propagations.
    pub limit: i64,
    /// Currently unsatisfied clauses.
    pub broken: Vec<ClauseOrBinary>,
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
    /// Best model stored so far.
    pub best_values: Vec<i8>,
    /// Best model found so far.
    #[cfg(debug_assertions)]
    pub current_best_model: Vec<i8>,
}


/*------------------------------------------------------------------------*/

#[allow(unused_imports)]
use crate::prelude::*;
use crate::format::fmt_f;
#[allow(unused_imports)]
use crate::util::{percent, relative, sign};

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

// We interpolate the CB values for uniform random SAT formula to the non
// integer situation of average clause size by piecewise linear functions.
//
//   y2 - y1
//   ------- * (x - x1) + y1
//   x2 - x1
//
// where 'x' is the average size of clauses and 'y' the CB value.

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

impl Walker {
    #[inline(always)]
    fn internal(&self) -> &mut Internal {
        // SAFETY: the walker is a local object of 'walk_round' and does not
        // outlive the solver it points to.
        unsafe { &mut *self.internal }
    }

    /// `Walker (Internal *, int64_t limit)`: initialize the data structures
    /// for one local search round.
    pub fn new(internal: *mut Internal, limit: i64) -> Walker {
        // SAFETY: 'internal' is the valid solver creating this walker.
        let i = unsafe { &mut *internal };
        let mut random = Random::new(i.opts.seed as u64); // global random seed
        random += i.stats.walk.count as u64; // different seed every time
        let mut flips = Vec::new();
        flips.reserve((i.max_var / 4) as usize);
        Walker {
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
            #[cfg(debug_assertions)]
            current_best_model: vec![0; (i.max_var + 1) as usize],
        }
    }

    pub fn populate_table(&mut self, size: f64) {
        // This is the magic constant in ProbSAT (also called 'CB'), which we
        // pick according to the average size every second invocation and
        // otherwise just the default '2.0', which turns into the base '0.5'.
        //
        let use_size_based_cb = (self.internal().stats.walk.count & 1) != 0;
        let cb = if use_size_based_cb { fitcbval(size) } else { 2.0 };
        debug_assert!(cb != 0.0);
        let base = 1.0 / cb; // scores are 'base^0,base^1,base^2,...

        let mut next: f64 = 1.0;
        self.epsilon = next;
        while next != 0.0 {
            self.epsilon = next;
            self.table.push(self.epsilon);
            next = self.epsilon * base;
        }

        phase!(
            self.internal,
            "walk",
            self.internal().stats.walk.count,
            "CB {} with inverse {} as base and table size {}",
            fmt_f(cb, 2),
            fmt_f(base, 2),
            self.table.len()
        );
    }

    /// Add the literal to flip to the queue.
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
            self.flips.len()
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
                    debug_assert!(self.best_values[v as usize] == self.current_best_model[v as usize]);
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

        let internal = self.internal();
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
}

/*------------------------------------------------------------------------*/

impl Internal {
    pub fn walk_pick_clause(&mut self, walker: &mut Walker) -> ClauseOrBinary {
        self.require_mode(Mode::WALK);
        debug_assert!(!walker.broken.is_empty());
        let mut size = walker.broken.len() as i64;
        if size > i32::MAX as i64 {
            size = i32::MAX as i64;
        }
        let pos = walker.random.pick_int(0, (size - 1) as i32);
        let res = walker.broken[pos as usize];
        #[cfg(feature = "logging")]
        {
            let c = match res {
                ClauseOrBinary::Clause(c) => c,
                ClauseOrBinary::Binary(b) => b.d,
            };
            log!(self, c, "picking random position {}", pos);
        }
        res
    }

    /*--------------------------------------------------------------------*/

    /// Compute the number of clauses which would be become unsatisfied if
    /// 'lit' is flipped and set to false.  This is called the 'break-count'
    /// of 'lit'.
    pub fn walk_break_value(&mut self, lit: i32, ticks: &mut i64) -> u32 {
        self.require_mode(Mode::WALK);
        start!(self, walkbreak);
        debug_assert!(self.val(lit) > 0);
        let oldticks = *ticks;

        let mut res: u32 = 0; // The computed break-count of 'lit'.
        *ticks += 1 + self.cache_lines_n(self.watches(lit).len(), std::mem::size_of::<*const Clause>());

        let nws = self.watches(lit).len();
        for k in 0..nws {
            let w = self.watches(lit)[k];
            debug_assert!(w.blit != lit);
            if self.val(w.blit) > 0 {
                continue;
            }
            if w.binary() {
                res += 1;
                continue;
            }

            let c = w.clause;
            #[cfg(feature = "logging")]
            debug_assert!(c != self.dummy_binary);
            *ticks += 1;

            debug_assert!(lit == c.lit(0));

            // Now try to find a second satisfied literal starting at
            // 'literals[1]' shifting all the traversed literals to right by
            // one position in order to move such a second satisfying literal
            // to 'literals[1]'.  This move to front strategy improves the
            // chances to find the second satisfying literal earlier in
            // subsequent break-count computations.
            //
            let begin = 1usize;
            let end = c.size() as usize;
            let mut i = begin;
            let mut prev = 0i32;
            while i != end {
                let other = c.lit(i);
                c.set_lit(i, prev);
                i += 1;
                prev = other;
                if self.val(other) < 0 {
                    continue;
                }

                // Found 'other' as second satisfying literal.

                self.watches_mut(lit)[k].blit = other; // Update 'blit'
                c.set_lit(begin, other); // and move to front.

                break;
            }

            if i != end {
                continue; // Double satisfied!
            }

            // Otherwise restore literals (undo shift to the right).
            //
            while i != begin {
                i -= 1;
                let other = c.lit(i);
                c.set_lit(i, prev);
                prev = other;
            }
            res += 1; // Literal 'lit' single satisfies clause 'c'.
        }
        self.stats.ticks.walkbreak += *ticks - oldticks;
        stop!(self, walkbreak);

        res
    }

    /*--------------------------------------------------------------------*/

    /// Given an unsatisfied clause 'c', in which we want to flip a literal,
    /// we first determine the exponential score based on the break-count of
    /// its literals and then sample the literals based on these scores.
    /// The CB value is smaller than one and thus the score is exponentially
    /// decreasing with the break-count increasing.  The sampling works as
    /// in 'ProbSAT' and 'YalSAT' by summing up the scores and then picking
    /// a random limit in the range of zero to the sum, then summing up the
    /// scores again and picking the first literal which reaches the limit.
    /// Note, that during incremental SAT solving we can not flip assumed
    /// variables.  Those are assigned at decision level one, while the
    /// other variables are assigned at two.
    ///
    /// C++ overload `Internal::walk_pick_lit` (renamed).
    pub fn walk_pick_lit_clause(&mut self, walker: &mut Walker, c: CRef) -> i32 {
        log!(self, "picking literal by break-count");
        debug_assert!(walker.scores.is_empty());
        let old = walker.ticks;
        walker.ticks += 1;
        let mut sum: f64 = 0.0;
        let mut propagations: i64 = 0;
        let size = c.size() as usize;
        for k in 0..size {
            let lit = c.lit(k);
            debug_assert!(self.active(lit));
            if self.var(lit).level == 1 {
                log!(self, "skipping assumption {} for scoring", -lit);
                continue;
            }
            debug_assert!(self.active(lit));
            propagations += 1;
            let tmp = self.walk_break_value(-lit, &mut walker.ticks);
            let score = walker.score(tmp);
            log!(self, "literal {} break-count {} score {}", lit, tmp, crate::format::fmt_g(score));
            walker.scores.push(score);
            sum += score;
        }
        let _ = propagations; // TODO actually unused?
        log!(self, "scored {} literals", walker.scores.len());
        debug_assert!(!walker.scores.is_empty());
        debug_assert!(walker.scores.len() <= c.size() as usize);
        let lim = sum * walker.random.generate_double();
        log!(
            self,
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
            if self.var(res).level > 1 {
                break;
            }
            log!(self, "skipping assumption {} without score", -res);
        }
        sum = walker.scores[j];
        j += 1;
        while sum <= lim && i != end {
            res = c.lit(i);
            i += 1;
            if self.var(res).level == 1 {
                log!(self, "skipping assumption {} without score", -res);
                continue;
            }
            sum += walker.scores[j];
            j += 1;
        }
        walker.scores.clear();
        log!(self, "picking literal {} by break-count", res);
        self.stats.ticks.walkpick += walker.ticks - old;
        res
    }

    pub fn walk_pick_lit(&mut self, walker: &mut Walker, c: ClauseOrBinary) -> i32 {
        match c {
            ClauseOrBinary::Binary(b) => self.walk_pick_lit_binary(walker, b),
            ClauseOrBinary::Clause(c) => self.walk_pick_lit_clause(walker, c),
        }
    }

    /// C++ overload `Internal::walk_pick_lit` (renamed).
    pub fn walk_pick_lit_binary(&mut self, walker: &mut Walker, c: TaggedBinary) -> i32 {
        log!(
            self,
            "picking literal by break-count on binary clause [{}]{} {}",
            c.d.id() as u64,
            loglit!(self, c.lit),
            loglit!(self, c.other)
        );
        debug_assert!(walker.scores.is_empty());
        let old = walker.ticks;
        let mut sum: f64 = 0.0;
        let mut propagations: i64 = 0;
        let clause: [i32; 2] = [c.lit, c.other];
        for &lit in clause.iter() {
            debug_assert!(self.active(lit));
            if self.var(lit).level == 1 {
                log!(self, "skipping assumption {} for scoring", -lit);
                continue;
            }
            debug_assert!(self.active(lit));
            debug_assert!(self.val(lit) < 0);
            propagations += 1;
            let tmp = self.walk_break_value(-lit, &mut walker.ticks);
            let score = walker.score(tmp);
            log!(self, "literal {} break-count {} score {}", lit, tmp, crate::format::fmt_g(score));
            walker.scores.push(score);
            sum += score;
        }
        let _ = propagations; // TODO unused?
        log!(self, "scored {} literals", walker.scores.len());
        debug_assert!(!walker.scores.is_empty());
        debug_assert!(walker.scores.len() <= 2);
        let lim = sum * walker.random.generate_double();
        log!(
            self,
            "score sum {} limit {}",
            crate::format::fmt_g(sum),
            crate::format::fmt_g(lim)
        );
        let end = clause.len();
        let mut i = 0usize;
        let mut j = 0usize;
        let mut res;
        loop {
            debug_assert!(i != end);
            res = clause[i];
            i += 1;
            if self.var(res).level > 1 {
                break;
            }
            log!(self, "skipping assumption {} without score", -res);
        }
        sum = walker.scores[j];
        j += 1;
        while sum <= lim && i != end {
            res = clause[i];
            i += 1;
            if self.var(res).level == 1 {
                log!(self, "skipping assumption {} without score", -res);
                continue;
            }
            sum += walker.scores[j];
            j += 1;
        }
        debug_assert!(res != 0);
        walker.scores.clear();
        log!(self, "picking literal {} by break-count", res);
        self.stats.ticks.walkpick += walker.ticks - old;
        res
    }

    /*--------------------------------------------------------------------*/

    /// Flips a literal unless we run out of ticks.
    pub fn walk_flip_lit(&mut self, walker: &mut Walker, lit: i32) -> bool {
        start!(self, walkflip);
        let old = walker.ticks;
        self.require_mode(Mode::WALK);
        log!(self, "flipping assign {}", lit);
        debug_assert!(self.val(lit) < 0);

        // First flip the literal value.
        //
        let tmp = sign(lit);
        let idx = lit.abs();
        self.set_val(idx, tmp as i8);
        debug_assert!(self.val(lit) > 0);

        // (C++ prefetches the first watch of '-lit' here.)

        // Then remove 'c' and all other now satisfied (made) clauses.
        {
            // Simply go over all unsatisfied (broken) clauses.

            log!(self, "trying to make {} broken clauses", walker.broken.len());

            let eou = walker.broken.len();
            // broken is in cache given how central it is... but not always
            // (see the ncc problems). Value was heuristically determined to
            // give reasonnable values.
            walker.ticks +=
                1 + self.cache_lines_n(walker.broken.len(), std::mem::size_of::<*const Clause>());
            let mut j = 0usize;
            let mut i = 0usize;
            #[cfg(any(feature = "logging", debug_assertions))]
            let mut made: i64 = 0;

            while i != eou {
                let tagged = walker.broken[i];
                walker.broken[j] = tagged;
                i += 1;
                j += 1;

                if let ClauseOrBinary::Binary(b) = tagged {
                    let clit = b.lit;
                    let other = b.other;
                    debug_assert!(self.val(clit) < 0 || self.val(other) < 0);
                    #[cfg(feature = "logging")]
                    {
                        debug_assert!(b.d.lit(0) == clit || b.d.lit(1) == clit);
                        debug_assert!(b.d.lit(0) == other || b.d.lit(1) == other);
                    }
                    if clit == lit || other == lit {
                        log!(self, b.d, "made");
                        let first_lit = lit;
                        let second_lit = clit ^ lit ^ other;
                        #[cfg(feature = "logging")]
                        self.watch_binary_literal(first_lit, second_lit, b.d);
                        #[cfg(not(feature = "logging"))]
                        {
                            // placeholder for the clause, does not matter
                            let dummy = self.dummy_binary;
                            self.watch_binary_literal(first_lit, second_lit, dummy);
                        }

                        walker.ticks += 1;
                        #[cfg(any(feature = "logging", debug_assertions))]
                        {
                            made += 1;
                        }
                        j -= 1;
                    } else {
                        log!(self, b.d, "still broken");
                        debug_assert!(self.val(clit) < 0 && self.val(other) < 0);
                    }
                    continue;
                }

                // now the expansive part
                let d = tagged.clause();
                walker.ticks += 1;
                log!(self, d, "search for replacement");
                let mut prev = 0i32;
                // Find 'lit' in 'd'.
                //
                let size = d.size();
                for i in 0..size as usize {
                    let other = d.lit(i);
                    debug_assert!(self.active(other));
                    d.set_lit(i, prev);
                    prev = other;
                    if other == lit {
                        break;
                    }
                    debug_assert!(self.val(other) < 0);
                }
                // If 'lit' is in 'd' then move it to the front to watch it.
                //
                if prev == lit {
                    d.set_lit(0, lit);
                    log!(self, d, "made");
                    let (l0, l1) = (d.lit(0), d.lit(1));
                    self.watch_literal(l0, l1, d);
                    walker.ticks += 1;
                    #[cfg(any(feature = "logging", debug_assertions))]
                    {
                        made += 1;
                    }
                    j -= 1;
                } else {
                    // Otherwise the clause is not satisfied, undo shift.

                    let mut i = size - 1;
                    while i >= 0 {
                        let other = d.lit(i as usize);
                        d.set_lit(i as usize, prev);
                        prev = other;
                        i -= 1;
                    }
                }
                log!(self, d, "clause after undoing shift");
            }
            #[cfg(any(feature = "logging", debug_assertions))]
            debug_assert!(j as i64 + made == walker.broken.len() as i64);
            walker.broken.truncate(j);
            log!(
                self,
                "made {} clauses by flipping {}, still {} broken",
                made,
                lit,
                walker.broken.len()
            );
            #[cfg(debug_assertions)]
            for d in walker.broken.iter() {
                match d {
                    ClauseOrBinary::Binary(b) => {
                        debug_assert!(self.val(b.lit) < 0 && self.val(b.other) < 0);
                    }
                    ClauseOrBinary::Clause(c) => {
                        for &lit in c.lits() {
                            debug_assert!(self.val(lit) < 0);
                        }
                    }
                }
            }
            if walker.ticks > walker.limit {
                stop!(self, walkflip);
                return false;
            }
        }

        self.stats.ticks.walkflipbroken += walker.ticks - old;

        let old_after_broken = walker.ticks;

        // Finally add all new unsatisfied (broken) clauses.
        {
            #[cfg(feature = "logging")]
            let mut broken: i64 = 0;
            // probably still in cache
            walker.ticks +=
                1 + self.cache_lines_n(self.watches(-lit).len(), std::mem::size_of::<*const Clause>());

            log!(self, "trying to break {} watched clauses", self.watches(-lit).len());

            // The watch list of '-lit' is not modified in the loop (new
            // watches are only added to other literals), so re-indexing is
            // equivalent to the C++ range based loop.
            let nws = self.watches(-lit).len();
            for k in 0..nws {
                let w = self.watches(-lit)[k];
                let d = w.clause;
                let binary = w.binary();
                if binary {
                    let other = w.blit;
                    debug_assert!(w.blit != -lit);
                    if self.val(other) > 0 {
                        log!(self, d, "unwatch {} in", -lit);
                        self.watch_binary_literal(other, -lit, d);
                        walker.ticks += 1;
                        continue;
                    }
                    log!(self, d, "broken");
                    #[cfg(feature = "logging")]
                    debug_assert!(d != self.dummy_binary);
                    walker.broken.push(ClauseOrBinary::Binary(TaggedBinary::new(d, -lit, other)));
                    walker.ticks += 1;
                    #[cfg(feature = "logging")]
                    {
                        broken += 1;
                    }
                    continue;
                }

                if walker.ticks > walker.limit {
                    stop!(self, walkflip);
                    return false;
                }
                // now the expansive part
                debug_assert!(d.size() != 2);
                walker.ticks += 1;
                let mut replacement = 0i32;
                let mut prev = -lit;
                debug_assert!(d.size() == w.size);
                let size = d.size();
                debug_assert!(d.lit(0) == -lit);

                for i in 1..size as usize {
                    let other = d.lit(i);
                    debug_assert!(self.active(other));
                    d.set_lit(i, prev); // shift all to right
                    prev = other;
                    let tmp = self.val(other);
                    if tmp < 0 {
                        continue;
                    }
                    replacement = other; // satisfying literal
                    break;
                }
                if replacement != 0 {
                    debug_assert!(-lit != replacement);
                    d.set_lit(1, -lit);
                    d.set_lit(0, replacement);
                    self.watch_literal(replacement, -lit, d);
                    walker.ticks += 1;
                    log!(self, d, "found replacement");
                } else {
                    let mut i = size - 1;
                    while i > 0 {
                        // undo shift
                        let other = d.lit(i as usize);
                        d.set_lit(i as usize, prev);
                        prev = other;
                        i -= 1;
                    }

                    debug_assert!(d.lit(0) == -lit);
                    log!(self, d, "broken");
                    walker.broken.push(ClauseOrBinary::Clause(d));
                    walker.ticks += 1;
                    #[cfg(feature = "logging")]
                    {
                        broken += 1;
                    }
                }
            }
            log!(self, "broken {} clauses by flipping {}", broken, lit);
            self.watches_mut(-lit).clear();
        }
        stop!(self, walkflip);
        self.stats.ticks.walkflipWL += walker.ticks - old_after_broken;
        self.stats.ticks.walkflip += walker.ticks - old;
        true
    }

    /*--------------------------------------------------------------------*/

    /// Check whether to save the current phases as new global minimum.
    #[inline]
    pub fn walk_save_minimum(&mut self, walker: &mut Walker) {
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
        {
            for i in self.vars() {
                let tmp = self.val(i);
                if tmp != 0 {
                    walker.current_best_model[i as usize] = tmp;
                }
            }
            if walker.minimum == 0 {
                for &c in self.clauses.iter() {
                    if c.garbage() {
                        continue;
                    }
                    if c.redundant() {
                        continue;
                    }
                    let mut satisfied = 0;
                    for &lit in c.lits() {
                        let tmp = self.val(lit);
                        if tmp > 0 {
                            log!(self, c, "satisfied literal {} in", lit);
                            satisfied += 1;
                        }
                    }
                    debug_assert!(satisfied != 0);
                }
            }
        }
        if walker.best_trail_pos == -1 {
            verbose!(self, 3, "saving the new walk minimum {}", broken);
            for i in self.vars() {
                let tmp = self.val(i);
                if tmp != 0 {
                    walker.best_values[i as usize] = tmp;
                    #[cfg(debug_assertions)]
                    debug_assert!(tmp == walker.current_best_model[i as usize]);
                } else {
                    debug_assert!(!self.active(i));
                }
            }
            walker.best_trail_pos = 0;
        } else {
            walker.best_trail_pos = walker.flips.len() as i32;
            log!(self, "new best trail position {}", walker.best_trail_pos as u32);
        }
    }

    /*--------------------------------------------------------------------*/

    pub fn walk_round(&mut self, limit: i64, prev: bool) -> i32 {
        self.stats.walk.count += 1;

        self.clear_watches();

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

        phase!(self, "walk", self.stats.walk.count, "random walk limit of {} ticks", limit);

        // Instantiate data structures for this local search round.
        //
        let mut walker = Walker::new(self as *mut Internal, limit);
        // (C++ 'int old_global_minimum = stats.walk.minimum' truncates.)
        let old_global_minimum: i32 = self.stats.walk.minimum as i32;

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
            // warmup stores the result in phases, not in target
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
                log!(self, "initial assign {} to decision phase", if tmp < 0 { -idx } else { idx });
            }

            log!(self, "watching satisfied and registering broken clauses");
            #[cfg(feature = "logging")]
            let mut watched: i64 = 0;

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

                let mut satisfiable = false; // contains not only assumptions
                let mut satisfied: i32 = 0; // clause satisfied?

                size += c.size() as f64;
                n += 1;
                let size = c.size();

                // Move to front satisfied literals and determine whether
                // there is at least one (non-assumed) literal that can be
                // flipped.
                //
                let mut i = 0;
                while satisfied < 2 && i < size {
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
                    i += 1;
                }

                if satisfied == 0 && !satisfiable {
                    log!(self, c, "due to assumptions unsatisfiable");
                    log!(self, "stopping local search since assumptions falsify a clause");
                    failed = true;
                    break;
                }

                if satisfied != 0 {
                    log!(self, c, "pushing to satisfied");
                    let (l0, l1) = (c.lit(0), c.lit(1));
                    if c.size() == 2 {
                        self.watch_binary_literal(l0, l1, c);
                    } else {
                        self.watch_literal(l0, l1, c);
                    }
                    #[cfg(feature = "logging")]
                    {
                        watched += 1;
                    }
                } else {
                    debug_assert!(satisfiable); // at least one non-assumed variable ...
                    log!(self, c, "broken");
                    debug_assert!(c.size() == size);
                    if size == 2 {
                        walker.broken.push(ClauseOrBinary::Binary(TaggedBinary::from_clause(c)));
                    } else {
                        walker.broken.push(ClauseOrBinary::Clause(c));
                    }
                }
            }

            let average_size = relative(size, n as f64);
            walker.populate_table(average_size);
            phase!(
                self,
                "walk",
                self.stats.walk.count,
                "{} clauses average size {} over {} variables",
                n,
                fmt_f(average_size, 2),
                self.active_count()
            );

            #[cfg(feature = "logging")]
            if !failed {
                let broken = walker.broken.len() as i64;
                let total = watched + broken;
                log!(
                    self,
                    "watching {} clauses {}% out of {} (watched and broken)",
                    watched,
                    fmt_f(percent(watched as f64, total as f64), 0),
                    total
                );
            }
        }

        debug_assert!(failed || !walker.table.is_empty());

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

            self.walk_save_minimum(&mut walker);
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
                let c = self.walk_pick_clause(&mut walker);
                let lit = self.walk_pick_lit(&mut walker, c);
                let finished = self.walk_flip_lit(&mut walker, lit);
                if !finished {
                    break;
                }
                walker.push_flipped(lit);
                broken = walker.broken.len() as i64;
                log!(self, "now have {} broken clauses in total", broken);
                if broken >= minimum {
                    continue;
                }
                minimum = broken;
                verbose!(self, 3, "new phase minimum {} after {} flips", minimum, flips);
                self.walk_save_minimum(&mut walker);
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
            } else if minimum < old_global_minimum as i64 {
                phase!(
                    self,
                    "walk",
                    self.stats.walk.count,
                    "{}new global minimum {}{} in {} flips and {} ticks",
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

        self.clear_watches();
        self.connect_watches(false);

        if self.localsearching {
            debug_assert!(self.force_phase_messages);
            self.force_phase_messages = false;
        }
        self.stats.ticks.walk += walker.ticks;
        res
    }

    pub fn walk(&mut self) {
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
        let _ = self.walk_round(limit, false);
        stop_inner_walk!(self);
        debug_assert!(!self.unsat);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Differential check of the break value table against the C++ code
    /// (reference output computed with clang 21 from the 'walk.cpp' code).
    #[test]
    fn populate_table_matches_cpp() {
        let expected = include_str!("../tests/data/walk_cb_table.txt");
        let mut internal = Internal::new();
        let ip: *mut Internal = &mut *internal;
        for line in expected.lines() {
            let f: Vec<&str> = line.split_whitespace().collect();
            let use_size: i64 = f[0].parse().unwrap();
            let size: f64 = f[1].parse().unwrap();
            let len: usize = f[2].parse().unwrap();
            let hash: u64 = f[3].parse().unwrap();
            let eps: u64 = f[4].parse().unwrap();
            internal.stats.walk.count = use_size;
            let mut walker = Walker::new(ip, 0);
            walker.populate_table(size);
            let mut h: u64 = 0;
            for d in walker.table.iter() {
                h = h.wrapping_mul(1000003).wrapping_add(d.to_bits());
            }
            assert_eq!(walker.table.len(), len, "size {}", size);
            assert_eq!(h, hash, "size {}", size);
            assert_eq!(walker.epsilon.to_bits(), eps, "size {}", size);
        }
    }
}

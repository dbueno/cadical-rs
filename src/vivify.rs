//! Port of `vivify.hpp` and `vivify.cpp`: vivification.

use crate::clause::CRef;
use crate::internal::Internal;
use crate::util::erase_vector;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Vivify_Mode {
    TIER1,
    TIER2,
    TIER3,
    IRREDUNDANT,
}

pub const COUNTREF_COUNTS: usize = 2;

#[derive(Clone, Copy, Debug, Default)]
pub struct vivify_ref {
    pub vivify: bool,
    pub size: usize,
    pub count: [u64; COUNTREF_COUNTS],
    pub clause: CRef,
}

/// In the vivifier structure, we put the schedules in an array in order to
/// be able to iterate over them.  The C++ references `schedule_tier1`,
/// `schedule_tier2`, `schedule_tier3` and `schedule_irred` are accessor
/// methods here.
pub struct Vivifier {
    pub refs_schedule: Vec<vivify_ref>,
    pub schedules: [Vec<CRef>; 4],
    pub sorted: Vec<i32>,
    pub tier: Vivify_Mode,
    /// C++ `char`.
    pub tag: u8,
    pub tier1_limit: i32,
    pub tier2_limit: i32,
    pub ticks: i64,
    pub lrat_stack: Vec<(i32, CRef, bool)>,
}

impl Vivifier {
    pub fn new(mode_tier: Vivify_Mode) -> Vivifier {
        Vivifier {
            refs_schedule: Vec::new(),
            schedules: Default::default(),
            sorted: Vec::new(),
            tier: mode_tier,
            tag: 0,
            tier1_limit: 0,
            tier2_limit: 0,
            ticks: 0,
            lrat_stack: Vec::new(),
        }
    }
    #[inline]
    pub fn schedule_tier1(&mut self) -> &mut Vec<CRef> {
        &mut self.schedules[0]
    }
    #[inline]
    pub fn schedule_tier2(&mut self) -> &mut Vec<CRef> {
        &mut self.schedules[1]
    }
    #[inline]
    pub fn schedule_tier3(&mut self) -> &mut Vec<CRef> {
        &mut self.schedules[2]
    }
    #[inline]
    pub fn schedule_irred(&mut self) -> &mut Vec<CRef> {
        &mut self.schedules[3]
    }
    pub fn erase(&mut self) {
        erase_vector(&mut self.sorted);
    }
}
/*------------------------------------------------------------------------*/
// Port of 'vivify.cpp'.

#[allow(unused_imports)]
use crate::prelude::*;
use crate::util::shrink_vector;
use crate::watch::Watches;

// Vivification is a special case of asymmetric tautology elimination (ATE)
// and asymmetric literal elimination (ALE).  It strengthens and removes
// clauses proven redundant through unit propagation.
//
// The original algorithm is due to a paper by Piette, Hamadi and Sais
// published at ECAI'08.  We have an inprocessing version, e.g., it does not
// necessarily run-to-completion.  Our version also performs conflict
// analysis and uses a new heuristic for selecting clauses to vivify.
//
// See the C++ source for the full explanation of the heuristics.

/*------------------------------------------------------------------------*/

// Check whether a literal occurs less often.  In the implementation below
// (search for 'int64_t score = ...' or '@4') we actually compute a
// weighted occurrence count similar to the Jeroslow Wang heuristic.

#[inline]
fn vivify_more_noccs(internal: &Internal, a: i32, b: i32) -> bool {
    let n = internal.noccs(a);
    let m = internal.noccs(b);
    if n > m {
        return true; // larger occurrences / score first
    }
    if n < m {
        return false; // smaller occurrences / score last
    }
    if a == -b {
        return a > 0; // positive literal first
    }
    a.abs() < b.abs() // smaller index first
}

#[inline]
fn vivify_more_noccs_kissat(internal: &Internal, a: i32, b: i32) -> bool {
    let s = internal.noccs(a) as u32;
    let t = internal.noccs(b) as u32;
    ((t.wrapping_sub(s)) | ((internal.vlit(a).wrapping_sub(internal.vlit(b))) & !(s.wrapping_sub(t))))
        >> 31
        != 0
}

/*------------------------------------------------------------------------*/

// Attempting on-the-fly subsumption during sorting when the last line
// is turned out to be trouble some for identical clauses.  This is
// the single point where sorting is not asymmetric and would require
// 'stable' sorting for determinism.  It can also not be made
// 'complete' on-the-fly.  Instead of on-the-fly subsumption, we
// (optionnaly) thus go over the sorted scheduled in a linear scan
// again and remove certain subsumed clauses (the subsuming clause is
// syntactically a prefix of the subsumed clause), which includes
// those troublesome syntactically identical clauses.

#[inline]
fn vivify_flush_smaller(a: CRef, b: CRef) -> bool {
    let la = a.lits();
    let lb = b.lits();
    let (eoa, eob) = (la.len(), lb.len());
    let (mut i, mut j) = (0usize, 0usize);
    while i != eoa && j != eob {
        if la[i] != lb[j] {
            return la[i] < lb[j];
        }
        i += 1;
        j += 1;
    }
    j == eob && i != eoa
}

/*------------------------------------------------------------------------*/

// In a strengthened clause the idea is to move non-false literals to the
// front, followed by false literals.  Literals are further sorted by
// reverse assignment order.  The goal is to use watches which require to
// backtrack as few as possible decision levels.

#[inline]
fn vivify_better_watch(internal: &Internal, a: i32, b: i32) -> bool {
    let av = internal.val(a);
    let bv = internal.val(b);

    if av >= 0 && bv < 0 {
        return true;
    }
    if av < 0 && bv >= 0 {
        return false;
    }

    internal.var(a).trail > internal.var(b).trail
}

/*------------------------------------------------------------------------*/

/// `std::stable_partition` (the result is uniquely determined).
fn stable_partition<T: Copy, P: FnMut(&T) -> bool>(v: &mut [T], mut pred: P) {
    let mut yes: Vec<T> = Vec::with_capacity(v.len());
    let mut no: Vec<T> = Vec::new();
    for &x in v.iter() {
        if pred(&x) {
            yes.push(x);
        } else {
            no.push(x);
        }
    }
    let n = yes.len();
    v[..n].copy_from_slice(&yes);
    v[n..].copy_from_slice(&no);
}

fn create_ref(internal: &Internal, c: CRef) -> vivify_ref {
    log!(internal, c, "creating vivify_refs of clause");
    let mut r = vivify_ref { vivify: c.vivify(), size: c.size() as usize, count: [0; COUNTREF_COUNTS], clause: c };
    let mut lits: [i32; COUNTREF_COUNTS] = [0; COUNTREF_COUNTS];
    let n = std::cmp::min(COUNTREF_COUNTS as i32, c.size());
    let mut i: i32 = 0;
    while i != n {
        let iu = i as usize;
        let mut best: i32 = 0;
        let mut best_count: u32 = 0;
        'next_literal: for &lit in c.lits() {
            log!(
                internal,
                "to find best number of occurrences for literal {}, looking at literal {}",
                i,
                lit
            );
            for j in 0..iu {
                log!(internal, "comparing {} with literal {}", lit, lits[j]);
                if lits[j] == lit {
                    continue 'next_literal;
                }
            }
            {
                let lit_count: i64 = internal.noccs(lit);
                debug_assert!(lit_count != 0);
                log!(
                    internal,
                    "checking literal {} with {} occurrences",
                    loglit!(internal, lit),
                    lit_count
                );
                if lit_count <= best_count as i64 {
                    continue;
                }
                best_count = lit_count as u32;
                best = lit;
            }
        }
        debug_assert!(best != 0);
        debug_assert!(best_count != 0);
        debug_assert!(best_count < u32::MAX);
        r.count[iu] = ((best_count as u64) << 32).wrapping_add(internal.vlit(best) as u64);
        log!(
            internal,
            "final count at position {} is {} - {}: {}",
            i,
            loglit!(internal, best),
            best_count,
            r.count[iu]
        );
        lits[iu] = best;
        i += 1;
    }
    r
}

#[inline]
fn current_schedule_index(tier: Vivify_Mode) -> usize {
    match tier {
        Vivify_Mode::TIER1 => 0,
        Vivify_Mode::TIER2 => 1,
        Vivify_Mode::TIER3 => 2,
        Vivify_Mode::IRREDUNDANT => 3,
    }
}

#[inline]
fn vivify_refcount_rank(offset: usize, a: &vivify_ref) -> u64 {
    debug_assert!(offset < COUNTREF_COUNTS);
    a.count[offset]
}

#[inline]
fn vivify_refcount_smaller(offset: usize, a: &vivify_ref, b: &vivify_ref) -> bool {
    let s = vivify_refcount_rank(offset, a);
    let t = vivify_refcount_rank(offset, b);
    s < t
}

#[inline]
fn vivify_inversesize_rank(a: &vivify_ref) -> u64 {
    !(a.size as u64)
}

#[inline]
fn vivify_inversesize_smaller(a: &vivify_ref, b: &vivify_ref) -> bool {
    let s = vivify_inversesize_rank(a);
    let t = vivify_inversesize_rank(b);
    s < t
}

fn set_vivifier_mode(vivifier: &mut Vivifier, tier: Vivify_Mode) {
    vivifier.tier = tier;
    vivifier.tag = match tier {
        Vivify_Mode::TIER1 => b'u',
        Vivify_Mode::TIER2 => b'v',
        Vivify_Mode::TIER3 => b'w',
        Vivify_Mode::IRREDUNDANT => b'x',
    };
}

impl Internal {
    /*--------------------------------------------------------------------*/

    // Candidate clause 'subsumed' is subsumed by 'subsuming'.

    pub fn vivify_subsume_clause(&mut self, subsuming: CRef, subsumed: CRef) {
        debug_assert!(subsumed != subsuming);
        self.stats.subsumed += 1;
        self.stats.vivifysubs += 1;
        #[cfg(debug_assertions)]
        {
            debug_assert!(subsuming.is_some());
            debug_assert!(subsumed.is_some());
            debug_assert!(subsuming != subsumed);
            debug_assert!(!subsumed.garbage());
            // size after removeing units;
            let mut real_size_subsuming = 0;
            let mut real_size_subsumed = 0;
            for &lit in subsuming.lits() {
                if self.val(lit) == 0 || self.var(lit).level != 0 {
                    real_size_subsuming += 1;
                } else {
                    debug_assert!(self.val(lit) < 0);
                }
            }
            for &lit in subsumed.lits() {
                if self.val(lit) == 0 || self.var(lit).level != 0 {
                    real_size_subsumed += 1;
                } else {
                    debug_assert!(self.val(lit) < 0);
                }
            }
            debug_assert!(real_size_subsuming <= real_size_subsumed);
        }
        log!(self, subsumed, "subsumed to be deleted");
        log!(self, subsuming, "subsuming to be (un)deleted");
        if subsumed.redundant() && subsuming.redundant() && subsuming.glue() < subsumed.glue() {
            self.promote_clause(subsuming, subsumed.glue());
        }
        if subsumed.redundant() {
            self.stats.subred += 1;
            self.stats.vivifysubred += 1;
        } else {
            self.stats.subirr += 1;
            self.stats.vivifysubirr += 1;
        }
        if subsuming.garbage() {
            debug_assert!(subsuming.size() == 2);
            log!(self, subsuming, "binary subsuming clause was already deleted, so undeleting");
            subsuming.set_garbage(false);
            subsuming.set_glue(1);
            self.stats.current.total += 1;
            if subsuming.redundant() {
                self.stats.current.redundant += 1;
            } else {
                self.stats.current.irredundant += 1;
                self.stats.irrlits += subsuming.size() as i64;
            }
            self.stats.garbage.literals -= subsuming.size() as i64;
            self.stats.garbage.clauses -= 1;
        }
        if subsumed.redundant() || !subsuming.redundant() {
            self.mark_garbage(subsumed);
            return;
        }
        log!(self, "turning redundant subsuming clause into irredundant clause");
        subsuming.set_redundant(false);
        if let Some(proof) = self.proof.as_mut() {
            proof.strengthen(subsuming.id());
        }
        self.mark_garbage(subsumed);
        self.mark_added(subsuming);
        self.stats.current.irredundant += 1;
        self.stats.added.irredundant += 1;
        self.stats.irrlits += subsuming.size() as i64;
        debug_assert!(self.stats.current.redundant > 0);
        self.stats.current.redundant -= 1;
        debug_assert!(self.stats.added.redundant > 0);
        self.stats.added.redundant -= 1;
        // ... and keep 'stats.added.total'.
    }

    // demoting a clause (opposite is promote from subsume.cpp)
    //
    // This turned out to not be useful, but we kept it for the API call in
    // the proof tracers.
    pub fn demote_clause(&mut self, c: CRef) {
        self.stats.subsumed += 1;
        self.stats.vivifydemote += 1;
        log!(self, c, "demoting");
        debug_assert!(!c.redundant());
        self.mark_removed(c, 0);
        c.set_redundant(true);
        debug_assert!(self.stats.current.irredundant > 0);
        self.stats.current.irredundant -= 1;
        debug_assert!(self.stats.added.irredundant > 0);
        self.stats.added.irredundant -= 1;
        self.stats.irrlits -= c.size() as i64;
        self.stats.current.redundant += 1;
        self.stats.added.redundant += 1;
        c.set_glue(c.size() - 1);
        // ... and keep 'stats.added.total'.
    }

    /*--------------------------------------------------------------------*/
    // For vivification we have a separate dedicated propagation routine,
    // which prefers to propagate binary clauses first.  It also uses its
    // own assignment procedure 'vivify_assign', which does not mess with
    // phase saving during search nor the conflict and other statistics and
    // further can be inlined separately here.  The propagation routine
    // needs to ignore (large) clauses which are currently vivified.

    #[inline]
    pub fn vivify_assign(&mut self, lit: i32, reason: CRef) {
        self.require_mode(Mode::VIVIFY);
        let idx = self.vidx(lit);
        debug_assert!(self.val(idx) == 0);
        debug_assert!(!self.flags(idx).eliminated() || reason.is_null());
        let level = self.level;
        let trail_size = self.trail.len() as i32;
        {
            let v = self.var_mut(idx);
            v.level = level; // required to reuse decisions
            v.trail = trail_size; // used in 'vivify_better_watch'
        }
        debug_assert!((self.num_assigned as i32) < self.max_var);
        self.num_assigned += 1;
        self.var_mut(idx).reason = if level != 0 { reason } else { CRef::NULL }; // for conflict analysis
        if level == 0 {
            self.learn_unit_clause(lit);
        }
        let tmp = sign(lit) as i8;
        self.set_val(idx, tmp);
        debug_assert!(self.val(lit) > 0);
        debug_assert!(self.val(-lit) < 0);
        self.trail.push(lit);
        log!(self, reason, "vivify assign {}", lit);
    }

    // Assume negated literals in candidate clause.

    pub fn vivify_assume(&mut self, lit: i32) {
        self.require_mode(Mode::VIVIFY);
        self.level += 1;
        let t = self.trail.len() as i32;
        self.control.push(Level::new(lit, t));
        log!(self, "vivify decide {}", lit);
        debug_assert!(self.level > 0);
        debug_assert!(self.propagated == self.trail.len());
        self.vivify_assign(lit, CRef::NULL);
    }

    // Dedicated routine similar to 'propagate' in 'propagate.cpp' and
    // 'probe_propagate' with 'probe_propagate2' in 'probe.cpp'.  Please
    // refer to that code for more explanation on how propagation is
    // implemented.

    pub fn vivify_propagate(&mut self, ticks: &mut i64) -> bool {
        self.require_mode(Mode::VIVIFY);
        debug_assert!(!self.unsat);
        start!(self, propagate);
        self.propagated2 = self.propagated;
        let before = self.propagated2 as i64;
        loop {
            if self.propagated2 != self.trail.len() {
                let lit = -self.trail[self.propagated2];
                self.propagated2 += 1;
                log!(self, "vivify propagating {} over binary clauses", -lit);
                let widx = self.vlit(lit) as usize;
                let n = self.wtab[widx].len();
                *ticks += 1 + self.cache_lines_n(n, std::mem::size_of::<*const Watch>());
                // The watch list of 'lit' is not modified in this loop
                // ('vivify_assign' and 'build_chain_for_units' do not touch
                // watches), so indexing is equivalent to the C++ iteration.
                for k in 0..n {
                    let w = self.wtab[widx][k];
                    if !w.binary() {
                        continue;
                    }
                    let b = self.val(w.blit);
                    if b > 0 {
                        continue;
                    }
                    if b < 0 {
                        self.conflict = w.clause; // but continue
                    } else {
                        *ticks += 1;
                        self.build_chain_for_units(w.blit, w.clause, false);
                        self.vivify_assign(w.blit, w.clause);
                        self.lrat_chain.clear();
                    }
                }
            } else if self.conflict.is_null() && self.propagated != self.trail.len() {
                let lit = -self.trail[self.propagated];
                self.propagated += 1;
                log!(self, "vivify propagating {} over large clauses", -lit);
                let widx = self.vlit(lit) as usize;
                let wsp: *mut Watches = &mut self.wtab[widx];
                // SAFETY: 'wsp' points into 'wtab' which is not resized
                // during propagation.  Only watch lists of other literals
                // ('r' below, which is unassigned while 'lit' is false) are
                // pushed to, so this watch list is neither reallocated nor
                // accessed through another path while we use it.
                macro_rules! ws {
                    () => {
                        unsafe { &mut *wsp }
                    };
                }
                let eow = ws!().len();
                let mut i = 0usize;
                *ticks += 1 + self.cache_lines_n(eow, std::mem::size_of::<Watch>());
                let mut j = 0usize;
                while i != eow {
                    let w = ws!()[i];
                    ws!()[j] = w;
                    j += 1;
                    i += 1;
                    if w.binary() {
                        continue;
                    }
                    if self.val(w.blit) > 0 {
                        continue;
                    }
                    *ticks += 1;
                    let c = w.clause;
                    if c.garbage() {
                        j -= 1;
                        continue;
                    }
                    let other = c.lit(0) ^ c.lit(1) ^ lit;
                    let u = self.val(other);
                    if u > 0 {
                        ws!()[j - 1].blit = other;
                    } else {
                        let size = c.size() as usize;
                        let middle = c.pos() as usize;
                        let mut k = middle;
                        let mut v: i8 = -1;
                        let mut r: i32 = 0;
                        while k != size {
                            r = c.lit(k);
                            v = self.val(r);
                            if v >= 0 {
                                break;
                            }
                            k += 1;
                        }
                        if v < 0 {
                            k = 2;
                            debug_assert!(c.pos() <= c.size());
                            while k != middle {
                                r = c.lit(k);
                                v = self.val(r);
                                if v >= 0 {
                                    break;
                                }
                                k += 1;
                            }
                        }
                        c.set_pos(k as i32);
                        debug_assert!(2 <= k);
                        debug_assert!(k <= size);
                        if v > 0 {
                            ws!()[j - 1].blit = r;
                        } else if v == 0 {
                            log!(self, c, "unwatch {} in", r);
                            c.set_lit(0, other);
                            c.set_lit(1, r);
                            c.set_lit(k, lit);
                            *ticks += 1;
                            self.watch_literal(r, lit, c);
                            j -= 1;
                        } else if u == 0 {
                            if c == self.ignore {
                                log!(self, "ignoring propagation due to clause to vivify");
                                continue;
                            }
                            *ticks += 1;
                            debug_assert!(v < 0);
                            self.vivify_chain_for_units(other, c);
                            self.vivify_assign(other, c);
                            self.lrat_chain.clear();
                        } else {
                            if c == self.ignore {
                                log!(self, "ignoring conflict due to clause to vivify");
                                continue;
                            }
                            debug_assert!(u < 0);
                            debug_assert!(v < 0);
                            self.conflict = c;
                            break;
                        }
                    }
                }
                if j != i {
                    while i != eow {
                        let w = ws!()[i];
                        ws!()[j] = w;
                        j += 1;
                        i += 1;
                    }
                    ws!().truncate(j);
                }
            } else {
                break;
            }
        }
        let delta = self.propagated2 as i64 - before;
        self.stats.propagations.vivify += delta;
        if self.conflict.is_some() {
            log!(self, self.conflict, "conflict");
        }
        stop!(self, propagate);
        self.conflict.is_null()
    }

    /*--------------------------------------------------------------------*/

    pub fn flush_vivification_schedule(&mut self, schedule: &mut Vec<CRef>, ticks: &mut i64) {
        *ticks += 1 + 3 * self.cache_lines_n(schedule.len(), std::mem::size_of::<CRef>());
        // we cannot use msort here, as we cannot calculate a score
        schedule.sort_by(|&a, &b| {
            if vivify_flush_smaller(a, b) {
                std::cmp::Ordering::Less
            } else if vivify_flush_smaller(b, a) {
                std::cmp::Ordering::Greater
            } else {
                std::cmp::Ordering::Equal
            }
        });
        let end = schedule.len();
        let mut j = 0usize;
        let mut i = 0usize;

        let mut prev = CRef::NULL;
        let mut subsumed: i64 = 0;
        while i != end {
            *ticks += 1;
            let c = schedule[i];
            schedule[j] = c;
            j += 1;
            i += 1;
            if prev.is_null() || c.size() < prev.size() {
                prev = c;
                continue;
            }
            let eop = prev.size() as usize;
            let mut k = 0usize;
            while k != eop {
                if prev.lit(k) != c.lit(k) {
                    break;
                }
                k += 1;
            }
            if k == eop {
                log!(self, c, "found subsumed");
                log!(self, prev, "subsuming");
                debug_assert!(!c.garbage());
                debug_assert!(!prev.garbage());
                debug_assert!(c.redundant() || !prev.redundant());
                self.mark_garbage(c);
                subsumed += 1;
                j -= 1;
            } else {
                prev = c;
            }
        }

        if subsumed != 0 {
            phase!(self, "vivify", self.stats.vivifications, "flushed {} subsumed scheduled clauses", subsumed);
        }

        self.stats.vivifysubs += subsumed;
        self.stats.vivifyflushed += subsumed;

        if subsumed != 0 {
            schedule.truncate(j);
            shrink_vector(schedule);
        } else {
            debug_assert!(j == end);
        }
    }

    /*--------------------------------------------------------------------*/

    // Depending on whether we try to vivify redundant or irredundant
    // clauses, we schedule a clause to be vivified.  For redundant clauses
    // we initially only try to vivify them if they are likely to survive
    // the next 'reduce' operation, but this left the last schedule empty
    // most of the time.
    pub fn consider_to_vivify_clause(&mut self, c: CRef) -> bool {
        if c.garbage() {
            return false;
        }
        if self.opts.vivifyonce >= 1 && c.redundant() && c.vivified() {
            return false;
        }
        if self.opts.vivifyonce >= 2 && !c.redundant() && c.vivified() {
            return false;
        }
        if !c.redundant() {
            return true;
        }
        debug_assert!(c.redundant());

        // likely_to_be_kept_clause is too aggressive at removing tier-3
        // clauses
        true
    }

    /*--------------------------------------------------------------------*/

    // Common code to actually strengthen a candidate clause.  The resulting
    // strengthened clause is communicated through the global 'clause'.

    pub fn vivify_strengthen(&mut self, c: CRef, ticks: &mut i64) {
        debug_assert!(!self.clause.is_empty());

        if self.clause.len() == 1 {
            self.backtrack_without_updating_phases(0);
            let unit = self.clause[0];
            log!(self, c, "vivification shrunken to unit {}", unit);
            debug_assert!(self.val(unit) == 0);
            self.assign_unit(unit);
            // lrat_chain.clear ();   done in search_assign
            self.stats.vivifyunits += 1;

            let ok = self.vivify_propagate(ticks);
            if !ok {
                self.learn_empty_clause();
            }
        } else {
            // See explanation before 'vivify_better_watch' above.
            //
            // The comparator does not read 'clause', so temporarily moving
            // it out of 'self' is safe.
            let mut clause = std::mem::take(&mut self.clause);
            crate::sort::std_sort(&mut clause, |&a, &b| vivify_better_watch(self, a, b));
            self.clause = clause;

            let mut new_level = self.level;

            let lit0 = self.clause[0];
            let val0 = self.val(lit0);
            if val0 < 0 {
                let level0 = self.var(lit0).level;
                log!(self, "1st watch {} negative at level {}", lit0, level0);
                new_level = level0 - 1;
            }

            let lit1 = self.clause[1];
            let val1 = self.val(lit1);
            if val1 < 0 && !(val0 > 0 && self.var(lit0).level <= self.var(lit1).level) {
                let level1 = self.var(lit1).level;
                log!(self, "2nd watch {} negative at level {}", lit1, level1);
                new_level = level1 - 1;
            }

            debug_assert!(new_level >= 0);
            if new_level < self.level {
                self.backtrack(new_level);
            }

            debug_assert!(self.val(lit0) >= 0);
            debug_assert!(
                self.val(lit1) >= 0
                    || (self.val(lit0) > 0
                        && self.val(lit1) < 0
                        && self.var(lit0).level <= self.var(lit1).level)
            );

            let d = self.new_clause_as(c);
            log!(self, c, "before vivification");
            log!(self, d, "after vivification");
            let _ = d;
        }
        self.clause.clear();
        self.mark_garbage(c);
        self.lrat_chain.clear();
        self.stats.vivifystrs += 1;
    }

    // When shortening clauses, we have to update the watched literals.
    // Actually we don't do it, and instead simply backtrack back enough.
    pub fn vivify_sort_watched(&mut self, c: CRef) {
        crate::sort::std_sort(c.lits_mut(), |&a, &b| vivify_better_watch(self, a, b));

        let mut new_level = self.level;

        let lit0 = c.lit(0);
        let val0 = self.val(lit0);
        if val0 < 0 {
            let level0 = self.var(lit0).level;
            log!(self, "1st watch {} negative at level {}", lit0, level0);
            new_level = level0 - 1;
        }

        let lit1 = c.lit(1);
        let val1 = self.val(lit1);
        if val1 < 0 && !(val0 > 0 && self.var(lit0).level <= self.var(lit1).level) {
            let level1 = self.var(lit1).level;
            log!(self, "2nd watch {} negative at level {}", lit1, level1);
            new_level = level1 - 1;
        }

        debug_assert!(new_level >= 0);
        if new_level < self.level {
            self.backtrack_without_updating_phases(new_level);
        }

        debug_assert!(self.val(lit0) >= 0);
        debug_assert!(
            self.val(lit1) >= 0
                || (self.val(lit0) > 0 && self.val(lit1) < 0 && self.var(lit0).level <= self.var(lit1).level)
        );
    }

    /*--------------------------------------------------------------------*/

    // Conflict analysis from 'start' which learns a decision only clause.
    //
    // We cannot use the stack-based implementation of Kissat, because we
    // need to iterate over the conflict in topological ordering to produce
    // a valid LRAT proof
    pub fn vivify_analyze(
        &mut self,
        start: CRef,
        subsumes: &mut bool,
        subsuming: &mut CRef,
        candidate: CRef,
        implied: i32,
        redundant: &mut bool,
    ) {
        // normal trail, so next_trail is wrong
        let mut i = self.trail.len() as i32; // Start at end-of-trail.
        let mut reason = start;
        debug_assert!(reason.is_some());
        debug_assert!(!self.trail.is_empty());
        let mut uip = *self.trail.last().unwrap();
        let mut mark_implied = implied != 0;

        while i >= 0 {
            if reason.is_some() {
                *redundant = *redundant || reason.redundant();
                *subsumes = start != reason && reason.size() <= start.size();
                log!(self, reason, "resolving on {} with", uip);
                for k in 0..reason.size() as usize {
                    let other = reason.lit(k);
                    let v = *self.var(other);
                    if !self.marked2(other) && v.level != 0 {
                        log!(self, "not subsuming due to lit {}", other);
                        *subsumes = false;
                    }
                    if self.val(other) == 0 {
                        log!(self, "skipping unset lit {}", other);
                        continue;
                    }
                    if other == uip {
                        continue;
                    }
                    if v.level == 0 {
                        if self.flags(other).seen || !self.lrat || reason == start {
                            continue;
                        }
                        log!(self, "unit reason for {}", other);
                        let id = self.unit_id(-other);
                        log!(self, "adding unit reason {} for {}", id, loglit!(self, other));
                        self.unit_chain.push(id);
                        self.flags_mut(other).seen = true;
                        self.analyzed.push(other);
                        continue;
                    }
                    if mark_implied && other != implied {
                        log!(self, "skipping non-implied literal {} on current level", other);
                        continue;
                    }

                    debug_assert!(self.val(other) != 0);
                    if self.flags(other).seen {
                        continue;
                    }
                    log!(self, "pushing lit {}", other);
                    self.analyzed.push(other);
                    self.flags_mut(other).seen = true;
                }
                if reason != start && reason.redundant() {
                    let new_glue = self.recompute_glue(reason);
                    self.promote_clause(reason, new_glue);
                }
                if *subsumes {
                    debug_assert!(reason.is_some());
                    log!(self, reason, "clause found subsuming");
                    log!(self, candidate, "clause found subsumed");
                    *subsuming = reason;
                    return;
                }
            } else {
                log!(self, "vivify analyzed decision {}", uip);
                self.clause.push(-uip);
            }
            mark_implied = false;

            uip = 0;
            while uip == 0 && i > 0 {
                debug_assert!(i > 0);
                i -= 1;
                let lit = self.trail[i as usize];
                if self.var(lit).level == 0 {
                    continue;
                }
                if self.flags(lit).seen {
                    uip = lit;
                }
            }
            if uip == 0 {
                break;
            }
            log!(self, "uip is {}", uip);
            reason = self.var(uip).reason;
            if self.lrat && reason.is_some() {
                self.lrat_chain.push(reason.id());
            }
        }
        let _ = candidate;
    }

    /*--------------------------------------------------------------------*/
    // First decide which clause (candidate or conflict) to analyze and
    // how to do it. We also prepare the clause by removing units.
    pub fn vivify_deduce(
        &mut self,
        candidate: CRef,
        conflict: CRef,
        implied: i32,
        subsuming: &mut CRef,
        redundant: &mut bool,
    ) {
        debug_assert!(self.lrat_chain.is_empty());
        // Uninitialized in C++ if 'implied' (then always written by
        // 'vivify_analyze' before being read).
        let mut subsumes = false;
        let reason: CRef;

        debug_assert!(self.clause.is_empty());
        if implied != 0 {
            reason = candidate;
            self.mark2_clause_literals(candidate);
            let not_implied = -implied;
            debug_assert!(self.var(not_implied).level != 0);
            self.flags_mut(not_implied).seen = true;
            log!(self, "pushing implied lit {}", not_implied);
            self.analyzed.push(not_implied);
            self.clause.push(implied);
        } else {
            reason = if conflict.is_some() { conflict } else { candidate };
            debug_assert!(reason.is_some());
            debug_assert!(!reason.garbage() || reason.size() == 2);
            self.mark2_clause_literals(candidate);
            subsumes = candidate != reason;
            *redundant = reason.redundant();
            log!(self, reason, "resolving with");
            if self.lrat {
                self.lrat_chain.push(reason.id());
            }
            for k in 0..reason.size() as usize {
                let lit = reason.lit(k);
                let vlevel = self.var(lit).level;
                debug_assert!(self.val(lit) < 0);
                if vlevel == 0 {
                    if !self.lrat {
                        continue;
                    }
                    log!(self, "adding unit {}", lit);
                    if !self.flags(lit).seen {
                        // nevertheless we can use var (l) as if l was still
                        // assigned because var is updated lazily
                        let id = self.unit_id(-lit);
                        log!(self, "adding unit reason {} for {}", id, loglit!(self, lit));
                        self.unit_chain.push(id);
                    }
                    self.flags_mut(lit).seen = true;
                    self.analyzed.push(lit);
                    continue;
                }
                debug_assert!(vlevel != 0);
                if !self.marked2(lit) {
                    log!(self, "lit {} is not marked", lit);
                    subsumes = false;
                }
                log!(self, "analyzing lit {}", lit);
                log!(self, "pushing lit {}", lit);
                self.analyzed.push(lit);
                self.flags_mut(lit).seen = true;
            }
            if reason != candidate && reason.redundant() {
                let new_glue = self.recompute_glue(reason);
                self.promote_clause(reason, new_glue);
            }
            if subsumes {
                debug_assert!(candidate != reason);
                #[cfg(debug_assertions)]
                {
                    let mut nonfalse_reason = 0;
                    for &lit in reason.lits() {
                        if self.fixed(lit) == 0 {
                            nonfalse_reason += 1;
                        }
                    }

                    let mut nonfalse_candidate = 0;
                    for &lit in candidate.lits() {
                        if self.fixed(lit) == 0 {
                            nonfalse_candidate += 1;
                        }
                    }

                    debug_assert!(nonfalse_reason <= nonfalse_candidate);
                }
                log!(self, candidate, "vivify subsumed 0");
                log!(self, reason, "vivify subsuming 0");
                *subsuming = reason;
                self.unmark_clause_literals(candidate);
                if self.lrat {
                    self.lrat_chain.clear();
                }
                return;
            }
        }

        self.vivify_analyze(reason, &mut subsumes, subsuming, candidate, implied, redundant);
        self.unmark_clause_literals(candidate);
        if subsumes {
            debug_assert!(subsuming.is_some());
            log!(self, candidate, "vivify subsumed");
            log!(self, *subsuming, "vivify subsuming");
            if self.lrat {
                self.lrat_chain.clear();
            }
        }
    }

    /*--------------------------------------------------------------------*/

    // checks whether the clause can be strengthen or not.
    pub fn vivify_shrinkable(&mut self, sorted: &[i32], conflict: CRef) -> bool {
        let mut count_implied: u32 = 0;
        for &lit in sorted {
            let value = self.val(lit);
            if value == 0 {
                log!(self, "vivification unassigned {}", lit);
                return true;
            }
            if value > 0 {
                log!(self, "vivification implied satisfied {}", lit);
                if conflict.is_some() {
                    return true;
                }
                let old = count_implied;
                count_implied += 1;
                if old != 0 {
                    log!(self, "at least one implied literal with conflict thus shrinking");
                    return true;
                }
            } else {
                debug_assert!(value < 0);
                let v = self.var(lit);
                let f = self.flags(lit);
                if v.level == 0 {
                    continue;
                }
                if !f.seen {
                    log!(self, "vivification non-analyzed {}", lit);
                    return true;
                }
                if v.reason.is_some() {
                    log!(self, "vivification implied falsified {}", lit);
                    return true;
                }
            }
        }
        false
    }

    /*--------------------------------------------------------------------*/

    #[inline]
    pub fn vivify_increment_stats(&mut self, vivifier: &Vivifier) {
        match vivifier.tier {
            Vivify_Mode::TIER1 => self.stats.vivifystred1 += 1,
            Vivify_Mode::TIER2 => self.stats.vivifystred2 += 1,
            Vivify_Mode::TIER3 => self.stats.vivifystred3 += 1,
            Vivify_Mode::IRREDUNDANT => self.stats.vivifystrirr += 1,
        }
    }

    /*--------------------------------------------------------------------*/
    // instantiate last literal (see the description of the hack track
    // 2023), fix the watches and backtrack two level back to make sure
    // the watches are correct.
    pub fn vivify_instantiate(
        &mut self,
        sorted: &[i32],
        c: CRef,
        lrat_stack: &mut Vec<(i32, CRef, bool)>,
        ticks: &mut i64,
    ) -> bool {
        log!(self, "now trying instantiation");
        self.conflict = CRef::NULL;
        let lit = *sorted.last().unwrap();
        log!(self, "vivify instantiation");
        debug_assert!(self.var(lit).reason.is_null());
        debug_assert!(self.var(lit).level != 0);
        debug_assert!(self.val(lit) != 0);
        let l = self.level - 1;
        self.backtrack_without_updating_phases(l);
        debug_assert!(self.val(lit) == 0);
        self.stats.vivifydecs += 1;
        self.vivify_assume(lit);
        let ok = self.vivify_propagate(ticks);
        if !ok {
            log!(self, c, "instantiate success with literal {} in", lit);
            self.stats.vivifyinst += 1;
            // strengthen clause
            if self.lrat {
                self.clear_analyzed_literals();
                debug_assert!(self.lrat_chain.is_empty());
                self.vivify_build_lrat(0, c, lrat_stack);
                let conflict = self.conflict;
                self.vivify_build_lrat(0, conflict, lrat_stack);
                self.clear_analyzed_literals();
            }
            let remove = lit;
            self.conflict = CRef::NULL;
            self.unwatch_clause(c);
            let l = self.level - 2;
            self.backtrack_without_updating_phases(l);
            self.strengthen_clause(c, remove);
            self.vivify_sort_watched(c);
            self.watch_clause(c);
            debug_assert!(self.conflict.is_null());
            true
        } else {
            log!(self, "vivify instantiation failed");
            false
        }
    }

    /*--------------------------------------------------------------------*/

    // Main function: try to vivify this candidate clause in the given mode.

    pub fn vivify_clause(&mut self, vivifier: &mut Vivifier, c: CRef) -> bool {
        debug_assert!(c.size() > 2); // see (NO-BINARY) below
        debug_assert!(self.analyzed.is_empty());
        debug_assert!(self.ignore.is_null());

        c.set_vivify(false); // mark as checked / tried
        c.set_vivified(true); // and globally remember

        debug_assert!(!c.garbage());

        vivifier.ticks += 1;

        // First check whether the candidate clause is already satisfied and
        // at the same time copy its non fixed literals to 'sorted'.  The
        // literals in the candidate clause might not be sorted anymore due
        // to replacing watches during propagation, even though we sorted
        // them initially while pushing the clause onto the schedule and
        // sorting the schedule.
        //
        vivifier.sorted.clear();

        for k in 0..c.size() as usize {
            let lit = c.lit(k);
            let tmp = self.fixed(lit);
            if tmp > 0 {
                log!(self, c, "satisfied by propagated unit {}", lit);
                self.mark_garbage(c);
                return false;
            } else if tmp == 0 {
                vivifier.sorted.push(lit);
            }
        }

        debug_assert!(vivifier.sorted.len() > 1);
        if vivifier.sorted.len() == 2 {
            log!(self, "skipping actual binary");
            return false;
        }

        crate::sort::std_sort(&mut vivifier.sorted, |&a, &b| vivify_more_noccs_kissat(self, a, b));
        #[cfg(debug_assertions)]
        {
            let s = &vivifier.sorted;
            for k in 1..s.len() {
                debug_assert!(!vivify_more_noccs(self, s[k], s[k - 1]));
            }
        }

        // The actual vivification checking is performed here, by assuming
        // the negation of each of the remaining literals of the clause in
        // turn and propagating it.  If a conflict occurs or another literal
        // in the clause becomes assigned during propagation, we can stop.
        //
        log!(self, c, "vivification checking");
        self.stats.vivifychecks += 1;

        // If the decision 'level' is non-zero, then we can reuse decisions
        // for the previous candidate, and avoid re-propagating them.  In
        // preliminary experiments this saved between 30%-50% decisions (and
        // thus propagations), which in turn lets us also vivify more clauses
        // within the same propagation bounds, or terminate earlier if vivify
        // runs to completion.
        //
        if self.level != 0 {
            #[cfg(feature = "logging")]
            let orig_level = self.level;
            // First check whether this clause is actually a reason for
            // forcing one of its literals to true and then backtrack one
            // level before that happened.  Otherwise this clause might be
            // incorrectly considered to be redundant or if this situation is
            // checked then redundancy by other clauses using this forced
            // literal becomes impossible.
            //
            let mut forced = 0;

            // This search could be avoided if we would eagerly set the
            // 'reason' boolean flag of clauses, which however we do not want
            // to do for binary clauses (during propagation) and thus would
            // still require a version of 'protect_reason' for binary clauses
            // during 'reduce' (well binary clauses are not collected during
            // 'reduce', but again this exception from the exception is pretty
            // complex and thus a simply search here is probably easier to
            // understand).

            for &lit in c.lits() {
                let tmp = self.val(lit);
                if tmp < 0 {
                    continue;
                }
                if tmp > 0 && self.var(lit).reason == c {
                    forced = lit;
                }
                break;
            }
            if forced != 0 {
                log!(self, "clause is reason forcing {}", forced);
                debug_assert!(self.var(forced).level != 0);
                let l = self.var(forced).level - 1;
                self.backtrack_without_updating_phases(l);
            }

            // As long the (remaining) literals of the sorted clause match
            // decisions on the trail we just reuse them.
            //
            if self.level != 0 {
                let mut l: i32 = 1; // This is the decision level we want to reuse.

                for k in 0..vivifier.sorted.len() {
                    let lit = vivifier.sorted[k];
                    debug_assert!(self.fixed(lit) == 0);
                    let decision = self.control[l as usize].decision;
                    if -lit == decision {
                        log!(self, "reusing decision {} at decision level {}", decision, l);
                        self.stats.vivifyreused += 1;
                        l += 1;
                        if l > self.level {
                            break;
                        }
                    } else {
                        log!(
                            self,
                            "literal {} does not match decision {} at decision level {}",
                            lit,
                            decision,
                            l
                        );
                        self.backtrack_without_updating_phases(l - 1);
                        break;
                    }
                }
            }

            log!(self, "reused {} decision levels from {}", self.level, orig_level);
        }

        log!(self, &vivifier.sorted, "sorted size {} probing schedule", vivifier.sorted.len());

        // Make sure to ignore this clause during propagation.  This is not
        // that easy for binary clauses (NO-BINARY), e.g., ignoring binary
        // clauses, without changing 'propagate'. Actually, we do not want to
        // remove binary clauses which are subsumed.  Those are hyper binary
        // resolvents and should be kept as learned clauses instead, unless
        // they are transitive in the binary implication graph, which in turn
        // is detected during transitive reduction in 'transred'.
        //
        self.ignore = c;

        let mut subsume: i32 = 0; // determined to be redundant / subsumed

        // If the candidate is redundant, i.e., we are in redundant mode, the
        // clause is subsumed (in one of the two cases below where 'subsume'
        // is assigned) and further all reasons involved are only binary
        // clauses, then this redundant clause is what we once called a
        // hidden tautology, and even for redundant clauses it makes sense to
        // remove the candidate.  It does not add anything to propagation
        // power of the formula.  This is the same argument as removing
        // transitive clauses in the binary implication graph during
        // transitive reduction.
        //

        // Go over the literals in the candidate clause in sorted order.
        //
        for k in 0..vivifier.sorted.len() {
            let lit = vivifier.sorted[k];

            // Exit loop as soon a literal is positively implied (case '@5'
            // below) or propagation of the negation of a literal fails
            // ('@6').
            //
            if subsume != 0 {
                break;
            }

            // We keep on assigning literals, even though we know already
            // that we can remove one (was negatively implied), since we
            // either might run into the 'subsume' case above or more false
            // literals become implied.  In any case this might result in
            // stronger vivified clauses.  As a consequence continue with
            // this loop even if 'remove' is non-zero.

            let tmp = self.val(lit);

            if tmp != 0 {
                // literal already assigned

                let v = *self.var(lit);
                debug_assert!(v.level != 0);
                if v.reason.is_null() {
                    log!(self, "skipping decision {}", lit);
                    continue;
                }

                if tmp < 0 {
                    debug_assert!(v.level != 0);
                    log!(self, "literal {} is already false and can be removed", lit);
                    continue;
                }

                debug_assert!(tmp > 0);
                log!(self, "subsumed since literal {} already true", lit);
                subsume = lit; // will be able to subsume candidate '@5'
                break;
            }

            debug_assert!(tmp == 0);

            self.stats.vivifydecs += 1;
            self.vivify_assume(-lit);
            log!(self, "negated decision {} score {}", lit, self.noccs(lit));

            if !self.vivify_propagate(&mut vivifier.ticks) {
                break; // hot-spot
            }
        }

        if subsume != 0 {
            let mut better_subsume_trail = self.var(subsume).trail;
            for k in 0..vivifier.sorted.len() {
                let lit = vivifier.sorted[k];
                if self.val(lit) <= 0 {
                    continue;
                }
                let v = *self.var(lit);
                if v.trail < better_subsume_trail {
                    log!(
                        self,
                        "improving subsume from {} at {} to {} at {}",
                        subsume,
                        better_subsume_trail,
                        lit,
                        v.trail
                    );
                    better_subsume_trail = v.trail;
                    subsume = lit;
                }
            }
        }

        let mut subsuming = CRef::NULL;
        let mut redundant = false;
        let level_after_assumptions = self.level;
        debug_assert!(level_after_assumptions != 0);
        let conflict = self.conflict;
        self.vivify_deduce(c, conflict, subsume, &mut subsuming, &mut redundant);

        let res: bool;

        // reverse lrat_chain. We could probably work with reversed
        // iterators (views) to be more efficient but we would have to
        // distinguish in proof
        //
        if self.lrat {
            for k in 0..self.unit_chain.len() {
                let id = self.unit_chain[k];
                self.lrat_chain.push(id);
            }
            self.unit_chain.clear();
            self.lrat_chain.reverse();
        }

        // For an explanation of the code, see our POS'25 paper ``Revisiting
        // Clause Vivification'' (although for the experiments we focused on
        // Kissat instead of CaDiCaL)
        if subsuming.is_some() {
            debug_assert!(c != subsuming);
            self.vivify_subsume_clause(subsuming, c);
            res = false;
        } else if self.vivify_shrinkable(&vivifier.sorted, self.conflict) {
            self.vivify_increment_stats(vivifier);
            log!(self, "vivify succeeded, learning new clause");
            self.clear_analyzed_literals();
            log!(self, &self.lrat_chain, "lrat");
            log!(self, &self.clause, "learning clause");
            self.conflict = CRef::NULL; // TODO dup from below
            self.vivify_strengthen(c, &mut vivifier.ticks);
            res = true;
        } else if subsume != 0 && c.redundant() {
            log!(self, c, "vivification implied");
            self.mark_garbage(c);
            self.stats.vivifyimplied += 1;
            res = true;
        } else if (self.conflict.is_some() || subsume != 0) && !c.redundant() && !redundant {
            if self.opts.vivifydemote != 0 {
                log!(self, "demote clause from irredundant to redundant");
                self.demote_clause(c);
                let new_glue = self.recompute_glue(c);
                self.promote_clause(c, new_glue);
                res = false;
            } else {
                self.mark_garbage(c);
                self.stats.vivifyimplied += 1;
                res = true;
            }
        } else if subsume != 0 {
            log!(self, c, "no vivification instantiation with implied literal {}", subsume);
            debug_assert!(!c.redundant());
            debug_assert!(redundant);
            res = false;
            self.stats.vivifyimplied += 1;
        } else {
            debug_assert!(self.level > 2);
            debug_assert!(self.level as usize == vivifier.sorted.len());
            log!(self, c, "vivification failed on");
            self.lrat_chain.clear();
            debug_assert!(subsume == 0);
            if subsume == 0 && self.opts.vivifyinst != 0 {
                res = self.vivify_instantiate(
                    &vivifier.sorted,
                    c,
                    &mut vivifier.lrat_stack,
                    &mut vivifier.ticks,
                );
                debug_assert!(self.conflict.is_null());
            } else {
                log!(self, "cannot apply instantiation");
                res = false;
            }
        }

        if self.conflict.is_some() && self.level == level_after_assumptions {
            log!(self, "forcing backtracking at least one level after conflict");
            let l = self.level - 1;
            self.backtrack_without_updating_phases(l);
        }

        self.clause.clear();
        self.clear_analyzed_literals(); // TODO why needed?
        self.lrat_chain.clear();
        self.conflict = CRef::NULL;
        self.ignore = CRef::NULL;

        if res {
            match vivifier.tier {
                Vivify_Mode::IRREDUNDANT => self.stats.vivifiedirred += 1,
                Vivify_Mode::TIER1 => self.stats.vivifiedtier1 += 1,
                Vivify_Mode::TIER2 => self.stats.vivifiedtier2 += 1,
                Vivify_Mode::TIER3 => self.stats.vivifiedtier3 += 1,
            }
        }
        res
    }

    // when we can strengthen clause c we have to build lrat.
    // uses f.seen so do not forget to clear flags afterwards.
    // this can happen in three cases. (1), (2) are only sound in redundant
    // mode (1) literal l in c is positively implied. in this case we call
    // the function with (l, l.reason). This justifies the reduction because
    // the new clause c' will include l and all decisions so l.reason is a
    // conflict assuming -c' (2) conflict during vivify propagation. function
    // is called with (0, conflict) similar to (1) but more direct. (3) some
    // literals in c are negatively implied and can therefore be removed. in
    // this case we call the function with (0, c). originally we justified
    // each literal in c on its own but this is not actually necessary.
    //

    // Non-recursive version, as some bugs have been found by Dominik
    // Schreiber during his very large experiments. DFS over the reasons with
    // preordering (aka we explore the entire reason before exploring deeper)
    pub fn vivify_build_lrat(&mut self, lit: i32, reason: CRef, stack: &mut Vec<(i32, CRef, bool)>) {
        debug_assert!(stack.is_empty());
        stack.push((lit, reason, false));
        while let Some(&(lit, reason, finished)) = stack.last() {
            log!(self, "VIVIFY LRAT justifying {}", lit);
            stack.pop();
            if lit != 0 && self.flags(lit).seen {
                log!(self, "skipping already justified");
                continue;
            }
            if finished {
                self.lrat_chain.push(reason.id());
                if lit != 0 && reason.is_some() {
                    self.flags_mut(lit).seen = true;
                    self.analyzed.push(lit); // assert (val (other) < 0);
                    debug_assert!(self.flags(lit).seen);
                }
                continue;
            } else {
                stack.push((lit, reason, true));
            }
            for k in 0..reason.size() as usize {
                let other = reason.lit(k);
                if other == lit {
                    continue;
                }
                let v = *self.var(other);
                if self.flags(other).seen {
                    continue;
                }
                if v.level == 0 {
                    let id = self.unit_id(-other);
                    self.lrat_chain.push(id);
                    self.flags_mut(other).seen = true;
                    self.analyzed.push(other);
                    continue;
                }
                if v.reason.is_some() {
                    // recursive justification
                    log!(self, "VIVIFY LRAT pushing {}", other);
                    stack.push((other, v.reason, false));
                }
            }
        }
        stack.clear();
    }

    // calculate lrat_chain
    //
    #[inline]
    pub fn vivify_chain_for_units(&mut self, lit: i32, reason: CRef) {
        if !self.lrat {
            return;
        }
        if self.level != 0 {
            return; // not decision level 0
        }
        debug_assert!(self.lrat_chain.is_empty());
        for k in 0..reason.size() as usize {
            let reason_lit = reason.lit(k);
            if lit == reason_lit {
                continue;
            }
            debug_assert!(self.val(reason_lit) != 0);
            let signed_reason_lit = self.val(reason_lit) as i32 * reason_lit;
            let id = self.unit_id(signed_reason_lit);
            self.lrat_chain.push(id);
        }
        self.lrat_chain.push(reason.id());
    }

    /*--------------------------------------------------------------------*/
    #[inline]
    pub fn vivify_prioritize_leftovers(&mut self, tag: u8, prioritized: usize, schedule: &mut Vec<CRef>) {
        if prioritized != 0 {
            phase!(
                self,
                "vivify",
                self.stats.vivifications,
                "[phase {}] leftovers of {} clause",
                tag as char,
                prioritized
            );
        } else {
            phase!(self, "vivify", self.stats.vivifications, "[phase {}] prioritizing all clause", tag as char);
            for &c in schedule.iter() {
                c.set_vivify(true);
            }
        }
        let max = self.opts.vivifyschedmax as usize;
        if schedule.len() > max {
            if prioritized != 0 {
                // put the left-overs first to be kept
                stable_partition(schedule, |c: &CRef| c.vivify());
            }
            schedule.truncate(max);
        }
        // let's try to save a bit of memory
        shrink_vector(schedule);
    }

    pub fn vivify_initialize(&mut self, vivifier: &mut Vivifier, ticks: &mut i64) {
        let tier1 = vivifier.tier1_limit;
        let tier2 = vivifier.tier2_limit;
        // Count the number of occurrences of literals in all clauses,
        // particularly binary clauses, which are usually responsible
        // for most of the propagations.
        //
        self.init_noccs();

        // Disconnect all watches since we sort literals within clauses.
        //
        debug_assert!(self.watching());

        let mut prioritized_irred: usize = 0;
        let mut prioritized_tier1: usize = 0;
        let mut prioritized_tier2: usize = 0;
        let mut prioritized_tier3: usize = 0;
        for ci in 0..self.clauses.len() {
            let c = self.clauses[ci];
            *ticks += 1;
            if c.size() == 2 {
                continue; // see also (NO-BINARY) above
            }
            if !self.consider_to_vivify_clause(c) {
                continue;
            }

            // This computes an approximation of the Jeroslow Wang heuristic
            // score
            //
            //       nocc (L) =     sum       2^(12-|C|)
            //                   L in C in F
            //
            // but we cap the size at 12, that is all clauses of size 12 and
            // larger contribute '1' to the score, which allows us to use
            // 'long' numbers. See the example above (search for '@1').
            //
            let shift = 12 - c.size();
            let score: i64 = if shift < 1 { 1 } else { 1i64 << shift }; // @4
            for k in 0..c.size() as usize {
                let lit = c.lit(k);
                *self.noccs_mut(lit) += score;
            }
            log!(self, c, "putting clause in candidates");
            if !c.redundant() {
                vivifier.schedule_irred().push(c);
                prioritized_irred += c.vivify() as usize;
            } else if c.glue() <= tier1 {
                vivifier.schedule_tier1().push(c);
                prioritized_tier1 += c.vivify() as usize;
            } else if c.glue() <= tier2 {
                vivifier.schedule_tier2().push(c);
                prioritized_tier2 += c.vivify() as usize;
            } else {
                vivifier.schedule_tier3().push(c);
                prioritized_tier3 += c.vivify() as usize;
            }
            *ticks += 1;
        }

        self.vivify_prioritize_leftovers(b'x', prioritized_irred, vivifier.schedule_irred());
        self.vivify_prioritize_leftovers(b'u', prioritized_tier1, vivifier.schedule_tier1());
        self.vivify_prioritize_leftovers(b'v', prioritized_tier2, vivifier.schedule_tier2());
        self.vivify_prioritize_leftovers(b'w', prioritized_tier3, vivifier.schedule_tier3());

        if self.opts.vivifyflush != 0 {
            self.clear_watches();
            for sched in vivifier.schedules.iter_mut() {
                // approximation for schedule
                *ticks += 1 + self.cache_lines_n(sched.len(), std::mem::size_of::<CRef>());
                for &c in sched.iter() {
                    // Literals in scheduled clauses are sorted with their
                    // highest score literals first (as explained above in
                    // the example at '@2').  This is also needed in the
                    // prefix subsumption checking below. We do an
                    // approximation below that is done only in the
                    // vivify_ref structure below.
                    //
                    crate::sort::std_sort(c.lits_mut(), |&a, &b| vivify_more_noccs(self, a, b));
                    //        ++ticks;
                }
                // Flush clauses subsumed by another clause with the same
                // prefix, which also includes flushing syntactically
                // identical clauses.
                //
                self.flush_vivification_schedule(sched, ticks);
            }
            // approximation for schedule
            //    ticks += 1 + cache_lines (clauses.size (), sizeof (Clause *));
            self.connect_watches(false); // watch all relevant clauses
        }
        self.vivify_propagate(ticks);

        phase!(
            self,
            "vivify",
            self.stats.vivifications,
            "[phase {}] leftovers out of {} clauses",
            'u',
            vivifier.schedules[0].len()
        );
    }

    /*--------------------------------------------------------------------*/
    // There are two modes of vivification, one using all clauses and one
    // focusing on irredundant clauses only.  The latter variant working on
    // irredundant clauses only can also remove irredundant asymmetric
    // tautologies (clauses subsumed through unit propagation), which in
    // redundant mode is incorrect (due to propagating over redundant
    // clauses).

    pub fn vivify_round(&mut self, vivifier: &mut Vivifier, ticks_limit: i64) {
        if self.unsat {
            return;
        }
        if self.terminated_asynchronously(1) {
            return;
        }

        let sidx = current_schedule_index(vivifier.tier);

        phase!(
            self,
            "vivify",
            self.stats.vivifications,
            "starting {} vivification round ticks limit {} with {} clauses",
            vivifier.tag as char,
            ticks_limit,
            vivifier.schedules[sidx].len()
        );

        debug_assert!(self.watching());

        let ticks: i64 = 1 + vivifier.schedules[sidx].len() as i64;

        // Sort candidates, with first to be tried candidate clause last,
        // i.e., many occurrences and high score literals) as in the example
        // explained above (search for '@3').
        //
        if vivifier.tier != Vivify_Mode::IRREDUNDANT || self.irredundant() / 10 < self.redundant() {
            // Literals in scheduled clauses are sorted with their highest
            // score literals first (as explained above in the example at
            // '@2').  This is also needed in the prefix subsumption checking
            // below. We do an approximation below that is done only in the
            // vivify_ref structure below.
            //

            // first build the schedule with vivifier_refs
            let Vivifier { refs_schedule, schedules, .. } = &mut *vivifier;
            let schedule = &mut schedules[sidx];
            refs_schedule.resize(schedule.len(), vivify_ref::default());
            for k in 0..schedule.len() {
                refs_schedule[k] = create_ref(self, schedule[k]);
            }
            let limit = self.opts.radixsortlim as usize;
            // now sort by size
            crate::radix::msort(limit, refs_schedule, vivify_inversesize_rank, vivify_inversesize_smaller);
            // now (stable) sort by number of occurrences
            for i in 0..COUNTREF_COUNTS {
                let offset = COUNTREF_COUNTS - 1 - i;
                crate::radix::msort(
                    limit,
                    refs_schedule,
                    |a: &vivify_ref| vivify_refcount_rank(offset, a),
                    |a: &vivify_ref, b: &vivify_ref| vivify_refcount_smaller(offset, a, b),
                );
            }
            // force left-overs at the end
            stable_partition(refs_schedule, |c: &vivify_ref| !c.vivify);
            for k in 0..refs_schedule.len() {
                schedule[k] = refs_schedule[k].clause;
            }
            refs_schedule.clear();
        } else {
            // skip sorting but still put clauses with the vivify tag at the
            // end to be done first Kissat does this implicitely by going
            // twice over all clauses
            stable_partition(&mut vivifier.schedules[sidx], |c: &CRef| !c.vivify());
        }

        // Remember old values of counters to summarize after each round with
        // verbose messages what happened in that round.
        //
        let mut checked = self.stats.vivifychecks;
        let mut subsumed = self.stats.vivifysubs;
        let mut strengthened = self.stats.vivifystrs;
        let mut units = self.stats.vivifyunits;

        let scheduled = vivifier.schedules[sidx].len() as i64;
        self.stats.vivifysched += scheduled;

        phase!(
            self,
            "vivify",
            self.stats.vivifications,
            "scheduled {} clauses to be vivified {}%",
            scheduled,
            crate::format::fmt_f(percent(scheduled as f64, self.stats.current.irredundant as f64), 0)
        );

        // Limit the number of propagations during vivification as in
        // 'probe'.
        //
        let limit = ticks_limit - self.stats.ticks.vivify;
        debug_assert!(limit >= 0);

        // the clauses might still contain set literals, so propagation since
        // the beginning
        self.propagated = 0;
        self.propagated2 = 0;

        if !self.unsat && !self.propagate() {
            log!(self, "propagation after connecting watches in inconsistency");
            self.learn_empty_clause();
        }

        vivifier.ticks = ticks;
        let mut retry = 0;
        while !self.unsat
            && !self.terminated_asynchronously(1)
            && !vivifier.schedules[sidx].is_empty()
            && vivifier.ticks < limit
        {
            let c = vivifier.schedules[sidx].pop().unwrap(); // Next candidate.
            if self.vivify_clause(vivifier, c) && !c.garbage() && c.size() > 2 && retry < self.opts.vivifyretry {
                retry += 1;
                vivifier.schedules[sidx].push(c);
            } else {
                retry = 0;
            }
        }

        if self.level != 0 {
            self.backtrack_without_updating_phases(0);
        }

        if !self.unsat {
            let schedule = &mut vivifier.schedules[sidx];
            let still_need_to_be_vivified = schedule.len() as i64;
            // if we have gone through all the leftovers (the next candidate
            // is not one), all the current clauses are leftovers for the
            // next round
            if !schedule.is_empty() && !schedule.last().unwrap().vivify() {
                for &c in schedule.iter() {
                    c.set_vivify(true);
                }
            }
            // Preference clauses scheduled but not vivified yet next time.
            //
            if still_need_to_be_vivified != 0 {
                phase!(
                    self,
                    "vivify",
                    self.stats.vivifications,
                    "still need to vivify {} clauses {}% of {} scheduled",
                    still_need_to_be_vivified,
                    crate::format::fmt_f(percent(still_need_to_be_vivified as f64, scheduled as f64), 2),
                    scheduled
                );
            } else {
                phase!(self, "vivify", self.stats.vivifications, "no previously not yet vivified clause left");
            }

            erase_vector(schedule); // Reclaim  memory early.
        }

        if !self.unsat {
            // Since redundant clause were disconnected during propagating
            // vivified units in redundant mode, and further irredundant
            // clauses are arbitrarily sorted, we have to propagate all
            // literals again after connecting the first two literals in the
            // clauses, in order to reestablish the watching invariant.
            //
            self.propagated = 0;
            self.propagated2 = 0;

            if !self.propagate() {
                log!(self, "propagating vivified units leads to conflict");
                self.learn_empty_clause();
            }
        }

        checked = self.stats.vivifychecks - checked;
        subsumed = self.stats.vivifysubs - subsumed;
        strengthened = self.stats.vivifystrs - strengthened;
        units = self.stats.vivifyunits - units;

        phase!(
            self,
            "vivify",
            self.stats.vivifications,
            "checked {} clauses {}% of {} scheduled using {} ticks",
            checked,
            crate::format::fmt_f(percent(checked as f64, scheduled as f64), 2),
            scheduled,
            vivifier.ticks as u64
        );
        if units != 0 {
            phase!(
                self,
                "vivify",
                self.stats.vivifications,
                "found {} units {}% of {} checked",
                units,
                crate::format::fmt_f(percent(units as f64, checked as f64), 2),
                checked
            );
        }
        if subsumed != 0 {
            phase!(
                self,
                "vivify",
                self.stats.vivifications,
                "subsumed {} clauses {}% of {} checked",
                subsumed,
                crate::format::fmt_f(percent(subsumed as f64, checked as f64), 2),
                checked
            );
        }
        if strengthened != 0 {
            phase!(
                self,
                "vivify",
                self.stats.vivifications,
                "strengthened {} clauses {}% of {} checked",
                strengthened,
                crate::format::fmt_f(percent(strengthened as f64, checked as f64), 2),
                checked
            );
        }

        self.stats.subsumed += subsumed;
        self.stats.strengthened += strengthened;
        self.stats.ticks.vivify += vivifier.ticks;

        let unsuccessful = (subsumed + strengthened + units) == 0;
        self.report(vivifier.tag, unsuccessful as i32);
    }

    /*--------------------------------------------------------------------*/

    pub fn compute_tier_limits(&mut self, vivifier: &mut Vivifier) {
        if self.opts.vivifycalctier == 0 {
            vivifier.tier1_limit = 2;
            vivifier.tier2_limit = 6;
            return;
        }
        vivifier.tier1_limit = self.tier1[0];
        vivifier.tier2_limit = self.tier2[0];
    }

    /*--------------------------------------------------------------------*/

    pub fn vivify(&mut self) -> bool {
        if self.unsat {
            return false;
        }
        if self.terminated_asynchronously(1) {
            return false;
        }
        if self.opts.vivify == 0 {
            return false;
        }
        if self.stats.current.irredundant == 0 {
            return false;
        }
        if self.level != 0 {
            self.backtrack(0);
        }
        debug_assert!(self.opts.vivify != 0);
        debug_assert!(self.level == 0);

        set_effort_limit!(self, totallimit, vivify, true);

        self.private_steps = true;

        start_simplifier!(self, vivify, VIVIFY);
        self.stats.vivifications += 1;

        // the effort is normalized by dividing by sumeffort below, hence no
        // need to multiply by 1e-3 (also making the precision better)
        let mut tier1effort: f64 = if self.opts.vivifytier1 == 0 { 0.0 } else { self.opts.vivifytier1eff as f64 };
        let mut tier2effort: f64 = if self.opts.vivifytier2 == 0 { 0.0 } else { self.opts.vivifytier2eff as f64 };
        let mut tier3effort: f64 = if self.opts.vivifytier3 == 0 { 0.0 } else { self.opts.vivifytier3eff as f64 };
        let mut irreffort: f64 =
            if self.delaying_vivify_irredundant.bumpreasons.delay() || self.opts.vivifyirred == 0 {
                0.0
            } else {
                self.opts.vivifyirredeff as f64
            };
        let mut sumeffort: f64 = tier1effort + tier2effort + tier3effort + irreffort;
        if self.stats.current.redundant == 0 {
            tier1effort = 0.0;
            tier2effort = 0.0;
            tier3effort = 0.0;
        }
        if sumeffort == 0.0 {
            irreffort = 1.0;
            sumeffort = 1.0;
        }
        let total: i64 = totallimit - self.stats.ticks.vivify;

        phase!(self, "vivify", self.stats.vivifications, "vivification limit of {} ticks", total);
        let mut vivifier = Vivifier::new(Vivify_Mode::TIER1);
        self.compute_tier_limits(&mut vivifier);

        if vivifier.tier1_limit == vivifier.tier2_limit {
            tier1effort += tier2effort;
            tier2effort = 0.0;
            log!(self, "vivification tier1 matches tier2 thus using tier2 budget for tier1");
        }
        let mut init_ticks: i64 = 0;

        // Refill the schedule every time. Unchecked clauses are 'saved' by
        // setting their 'vivify' bit, such that they can be tried next time.
        // There are two things to denote: the option 'vivifyonce' does what
        // it is supposed to do, and it works because the ticks are kept for
        // the next schedule. Also, we limit the size of the schedule to
        // limit the cost of sorting.
        //
        // TODO: After limiting, the cost we fixed some heuristics bug, so
        // maybe we could increase the limit.
        //
        // TODO: count against ticks.vivify directly instead of this unholy
        // shifting.
        self.vivify_initialize(&mut vivifier, &mut init_ticks);
        self.stats.ticks.vivify += init_ticks;
        let mut limit: i64 = self.stats.ticks.vivify;
        let shared_effort: f64 = init_ticks as f64 / 4.0;
        if self.opts.vivifytier1 != 0 {
            set_vivifier_mode(&mut vivifier, Vivify_Mode::TIER1);
            if limit < self.stats.ticks.vivify {
                limit = self.stats.ticks.vivify;
            }
            let effort: f64 = (total as f64 * tier1effort) / sumeffort;
            debug_assert!(i64::MAX - (effort as i64) >= limit);
            limit = (limit as f64 + effort) as i64;
            if limit as f64 - shared_effort > self.stats.ticks.vivify as f64 {
                limit = (limit as f64 - shared_effort) as i64;
                debug_assert!(limit >= 0);
                self.vivify_round(&mut vivifier, limit);
            } else {
                log!(self, "building the schedule already used our entire ticks budget for tier1");
            }
        }

        if !self.unsat && tier2effort != 0.0 {
            // save memory (well, not really as we
            // already reached the peak memory)
            erase_vector(vivifier.schedule_tier1());
            if limit < self.stats.ticks.vivify {
                limit = self.stats.ticks.vivify;
            }
            let effort: f64 = (total as f64 * tier2effort) / sumeffort;
            debug_assert!(i64::MAX - (effort as i64) >= limit);
            limit = (limit as f64 + effort) as i64;
            if limit as f64 - shared_effort > self.stats.ticks.vivify as f64 {
                limit = (limit as f64 - shared_effort) as i64;
                debug_assert!(limit >= 0);
                set_vivifier_mode(&mut vivifier, Vivify_Mode::TIER2);
                self.vivify_round(&mut vivifier, limit);
            } else {
                log!(self, "building the schedule already used our entire ticks budget for tier2");
            }
        }

        if !self.unsat && tier3effort != 0.0 {
            erase_vector(vivifier.schedule_tier2());
            if limit < self.stats.ticks.vivify {
                limit = self.stats.ticks.vivify;
            }
            let effort: f64 = (total as f64 * tier3effort) / sumeffort;
            debug_assert!(i64::MAX - (effort as i64) >= limit);
            limit = (limit as f64 + effort) as i64;
            if limit as f64 - shared_effort > self.stats.ticks.vivify as f64 {
                limit = (limit as f64 - shared_effort) as i64;
                debug_assert!(limit >= 0);
                set_vivifier_mode(&mut vivifier, Vivify_Mode::TIER3);
                self.vivify_round(&mut vivifier, limit);
            } else {
                log!(self, "building the schedule already used our entire ticks budget for tier3");
            }
        }

        if !self.unsat && irreffort != 0.0 {
            erase_vector(vivifier.schedule_tier3());
            if limit < self.stats.ticks.vivify {
                limit = self.stats.ticks.vivify;
            }
            let effort: f64 = (total as f64 * irreffort) / sumeffort;
            debug_assert!(i64::MAX - (effort as i64) >= limit);
            limit = (limit as f64 + effort) as i64;
            if limit as f64 - shared_effort > self.stats.ticks.vivify as f64 {
                limit = (limit as f64 - shared_effort) as i64;
                debug_assert!(limit >= 0);
                set_vivifier_mode(&mut vivifier, Vivify_Mode::IRREDUNDANT);
                let old: i32 = self.stats.vivifystrirr as i32;
                let old_tried: i32 = self.stats.vivifychecks as i32;
                self.vivify_round(&mut vivifier, limit);
                if self.stats.vivifychecks - old_tried as i64 == 0
                    || ((((self.stats.vivifystrirr - old as i64) as f32)
                        / ((self.stats.vivifychecks - old_tried as i64) as f32)) as f64)
                        < 0.01
                {
                    self.delaying_vivify_irredundant.bumpreasons.bump_delay();
                } else {
                    self.delaying_vivify_irredundant.bumpreasons.reduce_delay();
                }
            } else {
                self.delaying_vivify_irredundant.bumpreasons.bump_delay();
                log!(self, "building the schedule already used our entire ticks budget for irredundant");
            }
        }

        self.reset_noccs();
        stop_simplifier!(self, vivify, VIVIFY);

        self.private_steps = false;
        debug_assert!(self.ignore.is_null());

        true
    }
}

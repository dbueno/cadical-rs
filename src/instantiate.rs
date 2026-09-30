//! Port of `instantiate.hpp` and `instantiate.cpp`: variable
//! instantiation.

use crate::clause::CRef;
use crate::internal::Internal;

#[derive(Clone, Copy, Debug)]
pub struct Candidate {
    pub lit: i32,
    pub size: i32,
    pub negoccs: usize,
    pub clause: CRef,
}

impl Candidate {
    pub fn new(l: i32, c: CRef, s: i32, n: usize) -> Candidate {
        Candidate { lit: l, size: s, negoccs: n, clause: c }
    }
}

#[derive(Clone, Debug, Default)]
pub struct Instantiator {
    pub candidates: Vec<Candidate>,
}

impl Instantiator {
    pub fn new() -> Instantiator {
        Instantiator::default()
    }
    pub fn candidate(&mut self, l: i32, c: CRef, s: i32, n: usize) {
        self.candidates.push(Candidate::new(l, c, s, n));
    }
    /// `operator bool () const`.
    pub fn has_candidates(&self) -> bool {
        !self.candidates.is_empty()
    }
}

/*------------------------------------------------------------------------*/

// Port of 'instantiate.cpp': implementation of variable instantiation, a
// technique for removing literals with few occurrence (see also
// 'instantiate.hpp').

#[allow(unused_imports)]
use crate::prelude::*;

use crate::util::percent;

impl Internal {
    // Triggered at the end of a variable elimination round ('elim_round').

    pub fn collect_instantiation_candidates(&mut self, instantiator: &mut Instantiator) {
        debug_assert!(self.occurring());
        for idx in self.vars() {
            if self.frozen(idx) {
                continue;
            }
            if !self.active(idx) {
                continue;
            }
            if self.flags(idx).elim {
                continue; // BVE attempt pending
            }
            let mut sign = -1;
            while sign <= 1 {
                let lit = sign * idx;
                sign += 2;
                if self.noccs(lit) > self.opts.instantiateocclim as i64 {
                    continue;
                }
                let oi = self.vlit(lit) as usize;
                for k in 0..self.otab[oi].len() {
                    let c = self.otab[oi][k];
                    if c.garbage() {
                        continue;
                    }
                    if self.opts.instantiateonce != 0 && c.instantiated() {
                        continue;
                    }
                    if c.size() < self.opts.instantiateclslim {
                        continue;
                    }
                    let mut satisfied = false;
                    let mut unassigned = 0;
                    for &other in c.lits() {
                        let tmp = self.val(other);
                        if tmp > 0 {
                            satisfied = true;
                        }
                        if tmp == 0 {
                            unassigned += 1;
                        }
                    }
                    if satisfied {
                        continue;
                    }
                    if unassigned < 3 {
                        continue; // avoid learning units
                    }
                    let negoccs = self.occs(-lit).len();
                    log!(
                        self,
                        c,
                        "instantiation candidate literal {} with {} negative occurrences in",
                        lit,
                        negoccs
                    );
                    instantiator.candidate(lit, c, c.size(), negoccs);
                }
            }
        }
    }

    /*------------------------------------------------------------------------*/

    // Specialized propagation and assignment routines for instantiation.

    #[inline]
    pub fn inst_assign(&mut self, lit: i32) {
        log!(self, "instantiate assign {}", lit);
        debug_assert!(self.val(lit) == 0);
        debug_assert!((self.num_assigned as i32) < self.max_var);
        self.num_assigned += 1;
        self.set_val(lit, 1);
        self.trail.push(lit);
    }

    // Conflict analysis is only needed to do valid resolution proofs.
    // We remember propagated clauses in order of assignment (in inst_chain)
    // which allows us to do a variant of conflict analysis if the
    // instantiation attempt succeeds.
    //
    pub fn inst_propagate(&mut self) -> bool {
        // Adapted from 'propagate'.
        start!(self, propagate);
        let before = self.propagated as i64;
        let mut ok = true;
        while ok && self.propagated != self.trail.len() {
            let lit = -self.trail[self.propagated];
            self.propagated += 1;
            log!(self, "instantiate propagating {}", -lit);
            let wi = self.vlit(lit) as usize;
            // Only watches of other literals are added below.
            let eow = self.wtab[wi].len();
            let mut i = 0usize;
            let mut j = 0usize;
            while i != eow {
                let w = self.wtab[wi][i];
                self.wtab[wi][j] = w;
                i += 1;
                j += 1;
                let b = self.val(w.blit);
                if b > 0 {
                    continue;
                }
                if w.binary() {
                    if b < 0 {
                        ok = false;
                        log!(self, w.clause, "conflict");
                        if self.lrat {
                            self.inst_chain.push(w.clause);
                        }
                        break;
                    } else {
                        if self.lrat {
                            self.inst_chain.push(w.clause);
                        }
                        self.inst_assign(w.blit);
                    }
                } else {
                    let c = w.clause;
                    let other = c.lit(0) ^ c.lit(1) ^ lit;
                    c.set_lit(0, other);
                    c.set_lit(1, lit);
                    let u = self.val(other);
                    if u > 0 {
                        self.wtab[wi][j - 1].blit = other;
                    } else {
                        let size = c.size() as usize;
                        let middle = c.pos() as usize;
                        let mut k = middle;
                        let mut v: i8 = -1;
                        let mut r = 0i32;
                        while k != size && {
                            r = c.lit(k);
                            v = self.val(r);
                            v < 0
                        } {
                            k += 1;
                        }
                        if v < 0 {
                            k = 2;
                            debug_assert!(c.pos() as usize <= size);
                            while k != middle && {
                                r = c.lit(k);
                                v = self.val(r);
                                v < 0
                            } {
                                k += 1;
                            }
                        }
                        c.set_pos(k as i32);
                        debug_assert!(2 <= k);
                        debug_assert!(k <= size);
                        if v > 0 {
                            self.wtab[wi][j - 1].blit = r;
                        } else if v == 0 {
                            log!(self, c, "unwatch {} in", r);
                            c.set_lit(1, r);
                            c.set_lit(k, lit);
                            self.watch_literal(r, lit, c);
                            j -= 1;
                        } else if u == 0 {
                            debug_assert!(v < 0);
                            if self.lrat {
                                self.inst_chain.push(c);
                            }
                            self.inst_assign(other);
                        } else {
                            debug_assert!(u < 0);
                            debug_assert!(v < 0);
                            if self.lrat {
                                self.inst_chain.push(c);
                            }
                            log!(self, c, "conflict");
                            ok = false;
                            break;
                        }
                    }
                }
            }
            if j != i {
                let ws = &mut self.wtab[wi];
                while i != eow {
                    ws[j] = ws[i];
                    j += 1;
                    i += 1;
                }
                ws.truncate(j);
            }
        }
        let delta = self.propagated as i64 - before;
        self.stats.propagations.instantiate += delta;
        stop!(self, propagate);
        ok
    }

    /*------------------------------------------------------------------------*/

    // This is the instantiation attempt.

    pub fn instantiate_candidate(&mut self, lit: i32, c: CRef) -> bool {
        self.stats.instried += 1;
        if c.garbage() {
            return false;
        }
        debug_assert!(self.level == 0);
        let mut found = false;
        let mut satisfied = false;
        let mut inactive = false;
        let mut unassigned = 0;
        for &other in c.lits() {
            if other == lit {
                found = true;
            }
            let tmp = self.val(other);
            if tmp > 0 {
                satisfied = true;
                break;
            }
            if tmp == 0 && !self.active(other) {
                inactive = true;
                break;
            }
            if tmp == 0 {
                unassigned += 1;
            }
        }
        if !found {
            return false;
        }
        if inactive {
            return false;
        }
        if satisfied {
            return false;
        }
        if unassigned < 3 {
            return false;
        }
        let before = self.trail.len();
        debug_assert!(self.propagated == before);
        debug_assert!(self.active(lit));
        debug_assert!(self.inst_chain.is_empty());
        log!(self, c, "trying to instantiate {} in", lit);
        debug_assert!(!c.garbage());
        c.set_instantiated(true);
        debug_assert!(self.lrat_chain.is_empty());
        self.level += 1;
        self.inst_assign(lit); // Assume 'lit' to true.
        for i in 0..c.size() as usize {
            let other = c.lit(i);
            if other == lit {
                continue;
            }
            let tmp = self.val(other);
            if tmp != 0 {
                debug_assert!(tmp < 0);
                continue;
            }
            self.inst_assign(-other); // Assume other to false.
        }
        let ok = self.inst_propagate(); // Propagate.
        debug_assert!(self.lrat_chain.is_empty()); // chain will be built here
        if ok {
            self.inst_chain.clear();
        } else if self.lrat {
            // analyze conflict for lrat
            debug_assert!(!self.inst_chain.is_empty());
            let reason = self.inst_chain.pop().unwrap();
            self.lrat_chain.push(reason.id());
            for i in 0..reason.size() as usize {
                let other = reason.lit(i);
                debug_assert!(!self.flags(other).seen);
                self.flags_mut(other).seen = true;
                self.analyzed.push(other);
            }
        }
        while self.trail.len() > before {
            // Backtrack.
            let other = *self.trail.last().unwrap();
            log!(self, "instantiate unassign {}", other);
            self.trail.pop();
            debug_assert!(self.val(other) > 0);
            self.num_assigned -= 1;
            self.set_val(other, 0);
            // this is a variant of conflict analysis which is only needed for
            // lrat
            if !ok && !self.inst_chain.is_empty() && self.lrat {
                if self.flags(other).seen {
                    let reason = *self.inst_chain.last().unwrap();
                    self.lrat_chain.push(reason.id());
                    for i in 0..reason.size() as usize {
                        let other = reason.lit(i);
                        if self.flags(other).seen {
                            continue;
                        }
                        self.flags_mut(other).seen = true;
                        self.analyzed.push(other);
                    }
                    self.flags_mut(other).seen = false;
                }
                self.inst_chain.pop();
            }
        }
        debug_assert!(self.inst_chain.is_empty());
        // post processing step for lrat
        if !ok && self.lrat {
            if self.flags(lit).seen {
                self.lrat_chain.push(c.id());
            }
            for i in 0..c.size() as usize {
                let other = c.lit(i);
                self.flags_mut(other).seen = false;
            }
            for k in 0..self.analyzed.len() {
                let other = self.analyzed[k];
                if !self.flags(other).seen {
                    self.flags_mut(other).seen = true;
                    continue;
                }
                let id = self.unit_id(-other);
                self.lrat_chain.push(id);
            }
            self.clear_analyzed_literals();
            self.lrat_chain.reverse();
        }
        debug_assert!(self.analyzed.is_empty());
        self.propagated = before;
        debug_assert!(self.level == 1);
        self.level = 0;
        if ok {
            debug_assert!(self.lrat_chain.is_empty());
            log!(self, "instantiation failed");
            return false;
        }
        self.unwatch_clause(c);
        log!(self, &self.lrat_chain, "instantiate proof chain");
        self.strengthen_clause(c, lit);
        self.watch_clause(c);
        self.lrat_chain.clear();
        debug_assert!(c.size() > 1);
        log!(self, "instantiation succeeded");
        self.stats.instantiated += 1;
        true
    }

    /*------------------------------------------------------------------------*/

    // Try to instantiate all candidates collected before through the
    // 'collect_instantiation_candidates' routine.

    pub fn instantiate(&mut self, instantiator: &mut Instantiator) {
        debug_assert!(self.opts.instantiate != 0);
        start!(self, instantiate);
        self.stats.instrounds += 1;
        let candidates = instantiator.candidates.len() as i64;
        let mut tried: i64 = 0;
        let mut instantiated: i64 = 0;
        self.init_watches();
        self.connect_watches(false);
        if self.propagated < self.trail.len() {
            if !self.propagate() {
                log!(self, "propagation after connecting watches failed");
                self.learn_empty_clause();
                debug_assert!(self.unsat);
            }
        }
        phase!(
            self,
            "instantiate",
            self.stats.instrounds,
            "attempting to instantiate {} candidate literal clause pairs",
            candidates
        );
        while !self.unsat && !self.terminated_asynchronously(1) && !instantiator.candidates.is_empty() {
            let cand = instantiator.candidates.pop().unwrap();
            tried += 1;
            if !self.active(cand.lit) {
                continue;
            }
            log!(
                self,
                cand.clause,
                "trying to instantiate {} with {} negative occurrences in",
                cand.lit,
                cand.negoccs
            );
            if !self.instantiate_candidate(cand.lit, cand.clause) {
                continue;
            }
            instantiated += 1;
            verbose!(
                self,
                2,
                "instantiation {} ({}%) succeeded ({}%) with {} negative occurrences in size {} clause",
                tried,
                crate::format::fmt_f(percent(tried as f64, candidates as f64), 1),
                crate::format::fmt_f(percent(instantiated as f64, tried as f64), 1),
                cand.negoccs,
                cand.size
            );
        }
        phase!(
            self,
            "instantiate",
            self.stats.instrounds,
            "instantiated {} candidate successfully out of {} tried {}%",
            instantiated,
            tried,
            crate::format::fmt_f(percent(instantiated as f64, tried as f64), 1)
        );
        self.report(b'I', (instantiated == 0) as i32);
        self.reset_watches();
        stop!(self, instantiate);
    }
}

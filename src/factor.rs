//! Port of `factor.hpp` and `factor.cpp`: bounded variable addition.

use crate::clause::CRef;
use crate::heap::{Heap, HeapLess};
use crate::internal::Internal;

/// Comparator of the factor schedule (`factor_occs_size`).
#[derive(Clone, Copy, Debug)]
pub struct factor_occs_size {
    pub internal: *mut Internal,
}

impl factor_occs_size {
    pub fn new(i: *mut Internal) -> Self {
        factor_occs_size { internal: i }
    }
}

/// Quotients form a doubly linked list (raw pointers as in C++; allocated
/// with `Box::into_raw` in `new_quotient`).
#[derive(Debug)]
pub struct Quotient {
    pub factor: i32,
    pub id: usize,
    /// For LRAT.
    pub bid: i64,
    pub prev: *mut Quotient,
    pub next: *mut Quotient,
    pub qlauses: Vec<CRef>,
    pub matches: Vec<usize>,
    pub matched: usize,
}

impl Quotient {
    pub fn new(f: i32) -> Quotient {
        Quotient {
            factor: f,
            id: 0,
            bid: 0,
            prev: std::ptr::null_mut(),
            next: std::ptr::null_mut(),
            qlauses: Vec::new(),
            matches: Vec::new(),
            matched: 0,
        }
    }
}

pub type FactorSchedule = Heap<factor_occs_size>;

#[derive(Clone, Copy, Debug)]
pub struct FactoringQuotients {
    pub first: *mut Quotient,
    pub last: *mut Quotient,
}

pub struct Factoring {
    // These are initialized by the constructor
    pub internal: *mut Internal,
    pub limit: i64,
    pub schedule: FactorSchedule,
    pub initial: i32,
    pub bound: i32,
    pub count: Vec<u32>,
    pub fresh: Vec<i32>,
    pub counted: Vec<i32>,
    pub nounted: Vec<i32>,
    pub flauses: Vec<CRef>,
    pub quotients: FactoringQuotients,
}

/*------------------------------------------------------------------------*/
// Port of 'factor.cpp'.

#[allow(unused_imports)]
use crate::prelude::*;
use crate::format::fmt_f;
use crate::util::{enlarge_zero, percent};

const FACTORS: i32 = 1;
const QUOTIENT: i32 = 2;
const NOUNTED: i32 = 4;

/// `sizeof (Clause *)` on a 64-bit platform.
const CLAUSE_PTR_BYTES: usize = 8;

impl HeapLess for factor_occs_size {
    #[inline]
    fn less(&self, a: u32, b: u32) -> bool {
        // SAFETY: the back pointer to the owning 'Internal' is valid while
        // the schedule (part of a local 'Factoring') is alive.
        let internal = unsafe { &*self.internal };
        let s = internal.occs(internal.u2i(a)).len();
        let t = internal.occs(internal.u2i(b)).len();
        if s > t {
            return true;
        }
        if s < t {
            return false;
        }
        a > b
    }
}

impl Internal {
    // do full occurence list as in elim.cpp but filter out useless clauses
    pub fn factor_mode(&mut self) {
        self.reset_watches();

        debug_assert!(!self.watching());
        self.init_occs();

        let size_limit = self.opts.factorsize;

        let mut bincount: Vec<u32> = Vec::new();
        let mut largecount: Vec<u32> = Vec::new();
        let max_lit: u32 = 2 * (self.max_var as u32 + 1);
        enlarge_zero(&mut bincount, max_lit as usize);
        if size_limit > 2 {
            enlarge_zero(&mut largecount, max_lit as usize);
        }

        let mut candidates: Vec<CRef> = Vec::new();
        let delta = 1 + self.cache_lines_n(self.clauses.len(), CLAUSE_PTR_BYTES);
        self.stats.ticks.factor += delta;

        // push binary clauses on the occurrence stack.
        for i in 0..self.clauses.len() {
            let c = self.clauses[i];
            self.stats.ticks.factor += 1;
            if self.terminated_asynchronously(1) {
                return;
            }
            if c.garbage() {
                continue;
            }
            if c.redundant() && c.size() > 2 {
                continue;
            }
            if c.size() > size_limit {
                continue;
            }
            if c.size() == 2 {
                let lit = c.lit(0);
                let other = c.lit(1);
                bincount[self.vlit(lit) as usize] += 1;
                bincount[self.vlit(other) as usize] += 1;
                self.occs_mut(lit).push(c);
                self.occs_mut(other).push(c);
                continue;
            }
            candidates.push(c);
            for &lit in c.lits() {
                largecount[self.vlit(lit) as usize] += 1;
            }
        }
        if size_limit == 2 {
            return;
        }

        // iterate counts of larger clauses rounds often
        let rounds = self.opts.factorcandrounds as u32;
        let mut candidates_before: u32 = 0;
        let mut round: u32 = 1;
        while round <= rounds {
            if self.terminated_asynchronously(1) {
                return;
            }
            log!(self, "factor round {}", round);
            if candidates.len() == candidates_before as usize {
                break;
            }
            let delta = 1 + self.cache_lines_n(candidates.len(), CLAUSE_PTR_BYTES);
            self.stats.ticks.factor += delta;
            candidates_before = candidates.len() as u32;
            let mut newlargecount: Vec<u32> = Vec::new();
            enlarge_zero(&mut newlargecount, max_lit as usize);
            let end = candidates.len();
            let mut q = 0usize;
            let mut p = 0usize;
            'next_clause: while p != end {
                let c = candidates[p];
                candidates[q] = c;
                q += 1;
                p += 1;
                self.stats.ticks.factor += 1;
                for &lit in c.lits() {
                    let idx = self.vlit(lit) as usize;
                    if bincount[idx] + largecount[idx] < 2 {
                        q -= 1;
                        continue 'next_clause;
                    }
                }
                for &lit in c.lits() {
                    let idx = self.vlit(lit) as usize;
                    newlargecount[idx] += 1;
                }
            }
            candidates.truncate(q);
            std::mem::swap(&mut largecount, &mut newlargecount);
            round += 1;
        }

        // finally push remaining clause on the occurrence stack
        for &c in candidates.iter() {
            if self.terminated_asynchronously(1) {
                return;
            }
            for &lit in c.lits() {
                self.occs_mut(lit).push(c);
            }
        }
    }

    // go back to two watch scheme
    pub fn reset_factor_mode(&mut self) {
        self.reset_occs();
        self.init_watches();
        self.connect_watches(false);
    }

    pub fn tied_next_factor_score(&mut self, lit: i32) -> f64 {
        let res = self.occs(lit).len() as f64;
        log!(self, "watches score {} of {}", crate::format::fmt_g(res), lit);
        res
    }

    // the marks in cadical have 6 bits for marking but work on idx
    // to mark everything (FACTORS, QUOTIENT, NOUNTED) we shift the bits
    // depending on the sign of factor (+ bitmask)
    // i.e. if factor is positive, we apply a bitmask to only get
    // the first three bits (& 7u)
    // otherwise we leftshift by 3 (>> 3) to get the bits 4,5,6
    // use markfact, unmarkfact, getfact for this purpose.
    //
    pub fn new_quotient(&mut self, factoring: &mut Factoring, factor: i32) -> *mut Quotient {
        debug_assert!(!self.getfact(factor, FACTORS));
        self.markfact(factor, FACTORS);
        let res: *mut Quotient = Box::into_raw(Box::new(Quotient::new(factor)));
        // SAFETY: freshly allocated; the list nodes are only accessed here.
        let r = unsafe { &mut *res };
        r.next = std::ptr::null_mut();
        r.matched = 0;
        let last = factoring.quotients.last;
        r.bid = 0;
        if !last.is_null() {
            debug_assert!(!factoring.quotients.first.is_null());
            // SAFETY: 'last' is a live node of the quotient list.
            unsafe {
                debug_assert!((*last).next.is_null());
                (*last).next = res;
                r.id = (*last).id + 1;
            }
        } else {
            debug_assert!(factoring.quotients.first.is_null());
            factoring.quotients.first = res;
            r.id = 0;
        }
        factoring.quotients.last = res;
        r.prev = last;
        log!(self, "new quotient[{}] with factor {}", r.id, factor);
        res
    }

    pub fn release_quotients(&mut self, factoring: &mut Factoring) {
        let mut q = factoring.quotients.first;
        while !q.is_null() {
            // SAFETY: 'q' is a live node allocated in 'new_quotient'.
            let next = unsafe { (*q).next };
            let factor = unsafe { (*q).factor };
            debug_assert!(self.getfact(factor, FACTORS));
            self.unmarkfact(factor, FACTORS);
            // SAFETY: allocated with 'Box::into_raw' and released once.
            drop(unsafe { Box::from_raw(q) });
            q = next;
        }
        factoring.quotients.first = std::ptr::null_mut();
        factoring.quotients.last = std::ptr::null_mut();
    }

    pub fn first_factor(&mut self, factoring: &mut Factoring, factor: i32) -> usize {
        debug_assert!(factoring.quotients.first.is_null());
        let quotient = self.new_quotient(factoring, factor);
        // SAFETY: 'quotient' is a live node (not part of 'self').
        let qlauses = unsafe { &mut (*quotient).qlauses };
        let mut ticks: i64 = 0;
        for &c in self.occs(factor).iter() {
            qlauses.push(c);
            ticks += 1;
        }
        let res = qlauses.len();
        log!(self, "quotient[0] factor {} size {}", factor, res);
        // This invariant can of course be broken by previous factorings
        // assert (res > 1);
        self.stats.ticks.factor += ticks;
        res
    }

    pub fn clear_nounted(&mut self, nounted: &mut Vec<i32>) {
        for &lit in nounted.iter() {
            debug_assert!(self.getfact(lit, NOUNTED));
            self.unmarkfact(lit, NOUNTED);
        }
        nounted.clear();
    }

    pub fn clear_flauses(&mut self, flauses: &mut Vec<CRef>) {
        for &c in flauses.iter() {
            debug_assert!(c.swept());
            c.set_swept(false);
        }
        flauses.clear();
    }

    pub fn best_quotient(&mut self, factoring: &mut Factoring, best_reduction_ptr: Option<&mut usize>) -> *mut Quotient {
        let mut factors: usize = 1;
        let mut best_reduction: usize = 0;
        let mut best: *mut Quotient = std::ptr::null_mut();
        let mut q = factoring.quotients.first;
        while !q.is_null() {
            // SAFETY: live node of the quotient list.
            let qr = unsafe { &*q };
            let quotients = qr.qlauses.len();
            let before_factorization = quotients * factors;
            let after_factorization = quotients + factors;
            if before_factorization == after_factorization {
                log!(
                    self,
                    "quotient[{}] factors {} clauses into {} thus no change",
                    factors - 1,
                    before_factorization,
                    after_factorization
                );
            } else if before_factorization < after_factorization {
                log!(
                    self,
                    "quotient[{}] factors {} clauses into {} thus {} more",
                    factors - 1,
                    before_factorization,
                    after_factorization,
                    after_factorization - before_factorization
                );
            } else {
                let delta = before_factorization - after_factorization;
                log!(
                    self,
                    "quotient[{}] factors {} clauses into {} thus {} less",
                    factors - 1,
                    before_factorization,
                    after_factorization,
                    delta
                );
                if best.is_null() || best_reduction < delta {
                    best_reduction = delta;
                    best = q;
                }
            }
            factors += 1;
            q = qr.next;
        }
        if best.is_null() {
            log!(self, "no decreasing quotient found");
            return std::ptr::null_mut();
        }
        // SAFETY: 'best' is a live node.
        log!(self, "best decreasing quotient[{}] with reduction {}", unsafe { (*best).id }, best_reduction);
        if let Some(p) = best_reduction_ptr {
            *p = best_reduction;
        }
        best
    }

    #[allow(unused_assignments)]
    pub fn next_factor(&mut self, factoring: &mut Factoring, next_count_ptr: &mut u32) -> i32 {
        let last_quotient = factoring.quotients.last;
        debug_assert!(!last_quotient.is_null());
        // SAFETY: live node of the quotient list, not modified here.
        let last_clauses: &Vec<CRef> = unsafe { &(*last_quotient).qlauses };
        debug_assert!(factoring.counted.is_empty());
        debug_assert!(factoring.flauses.is_empty());
        let initial = factoring.initial;
        let mut ticks: i64 = 1 + self.cache_lines_n(last_clauses.len(), CLAUSE_PTR_BYTES);
        for &c in last_clauses.iter() {
            debug_assert!(!c.swept());
            let mut min_lit: i32 = 0;
            let mut factors: u32 = 0;
            let mut min_size: usize = 0;
            ticks += 1;
            for &other in c.lits() {
                if self.getfact(other, FACTORS) {
                    let f = factors;
                    factors += 1;
                    if f != 0 {
                        break;
                    }
                } else {
                    debug_assert!(!self.getfact(other, QUOTIENT));
                    self.markfact(other, QUOTIENT);
                    let other_size = self.occs(other).len();
                    if min_lit == 0 || other_size < min_size {
                        min_lit = other;
                        min_size = other_size;
                    }
                }
            }
            debug_assert!(factors != 0);
            if factors == 1 {
                debug_assert!(min_lit != 0);
                let c_size = c.size();
                debug_assert!(factoring.nounted.is_empty());
                ticks += 1 + self.cache_lines_n(self.occs(min_lit).len(), CLAUSE_PTR_BYTES);
                let n = self.occs(min_lit).len();
                'next_min_watch: for k in 0..n {
                    let d = self.occs(min_lit)[k];
                    if c == d {
                        continue;
                    }
                    ticks += 1;
                    if d.swept() {
                        continue;
                    }
                    if d.size() != c_size {
                        continue;
                    }
                    let mut next: i32 = 0;
                    for &other in d.lits() {
                        if self.getfact(other, QUOTIENT) {
                            continue;
                        }
                        if self.getfact(other, FACTORS) {
                            continue 'next_min_watch;
                        }
                        if self.getfact(other, NOUNTED) {
                            continue 'next_min_watch;
                        }
                        if next != 0 {
                            continue 'next_min_watch;
                        }
                        next = other;
                    }
                    debug_assert!(next != 0);
                    if next.abs() > initial.abs() {
                        continue;
                    }
                    if !self.active(next) {
                        continue;
                    }
                    debug_assert!(!self.getfact(next, FACTORS));
                    debug_assert!(!self.getfact(next, NOUNTED));
                    self.markfact(next, NOUNTED);
                    factoring.nounted.push(next);
                    d.set_swept(true);
                    factoring.flauses.push(d);
                    let vl = self.vlit(next) as usize;
                    if factoring.count[vl] == 0 {
                        factoring.counted.push(next);
                    }
                    factoring.count[vl] += 1;
                }
                self.clear_nounted(&mut factoring.nounted);
            }
            for &other in c.lits() {
                if self.getfact(other, QUOTIENT) {
                    self.unmarkfact(other, QUOTIENT);
                }
            }
            self.stats.ticks.factor += ticks;
            ticks = 0;
            if self.stats.ticks.factor > factoring.limit {
                break;
            }
        }
        self.clear_flauses(&mut factoring.flauses);
        let mut next_count: u32 = 0;
        let mut next: i32 = 0;
        if self.stats.ticks.factor <= factoring.limit {
            let mut ties: u32 = 0;
            for &lit in factoring.counted.iter() {
                let lit_count = factoring.count[self.vlit(lit) as usize];
                if lit_count < next_count {
                    continue;
                }
                if lit_count == next_count {
                    debug_assert!(lit_count != 0);
                    ties += 1;
                } else {
                    debug_assert!(lit_count > next_count);
                    next_count = lit_count;
                    next = lit;
                    ties = 1;
                }
            }
            if next_count < 2 {
                log!(self, "next factor count {} smaller than 2", next_count);
                next = 0;
            } else if ties > 1 {
                log!(
                    self,
                    "found {} tied next factor candidate literals with count {}",
                    ties,
                    next_count
                );
                let mut next_score: f64 = -1.0;
                for i in 0..factoring.counted.len() {
                    let lit = factoring.counted[i];
                    let lit_count = factoring.count[self.vlit(lit) as usize];
                    if lit_count != next_count {
                        continue;
                    }
                    let lit_score = self.tied_next_factor_score(lit);
                    debug_assert!(lit_score >= 0.0);
                    log!(
                        self,
                        "score {} of next factor candidate {}",
                        crate::format::fmt_g(lit_score),
                        lit
                    );
                    if lit_score <= next_score {
                        continue;
                    }
                    next_score = lit_score;
                    next = lit;
                }
                debug_assert!(next_score >= 0.0);
                debug_assert!(next != 0);
                log!(self, "best score {} of next factor {}", crate::format::fmt_g(next_score), next);
            } else {
                debug_assert!(ties == 1);
                log!(self, "single next factor {} with count {}", next, next_count);
            }
        }
        for &lit in factoring.counted.iter() {
            let vl = self.vlit(lit) as usize;
            factoring.count[vl] = 0;
        }
        factoring.counted.clear();
        debug_assert!(next == 0 || next_count > 1);
        *next_count_ptr = next_count;
        next
    }

    pub fn factorize_next(&mut self, factoring: &mut Factoring, next: i32, expected_next_count: u32) {
        let last_quotient = factoring.quotients.last;
        let next_quotient = self.new_quotient(factoring, next);

        debug_assert!(!last_quotient.is_null());
        // SAFETY: two distinct live nodes of the quotient list (not part of
        // 'self' or 'factoring').
        let last_clauses: &Vec<CRef> = unsafe { &(*last_quotient).qlauses };
        let nq = unsafe { &mut *next_quotient };
        debug_assert!(factoring.flauses.is_empty());

        let mut ticks: i64 = 1 + self.cache_lines_n(last_clauses.len(), CLAUSE_PTR_BYTES);

        let mut i: usize = 0;

        for &c in last_clauses.iter() {
            debug_assert!(!c.swept());
            let mut min_lit: i32 = 0;
            let mut factors: u32 = 0;
            let mut min_size: usize = 0;
            ticks += 1;
            for &other in c.lits() {
                if self.getfact(other, FACTORS) {
                    let f = factors;
                    factors += 1;
                    if f != 0 {
                        break;
                    }
                } else {
                    debug_assert!(!self.getfact(other, QUOTIENT));
                    self.markfact(other, QUOTIENT);
                    let other_size = self.occs(other).len();
                    if min_lit == 0 || other_size < min_size {
                        min_lit = other;
                        min_size = other_size;
                    }
                }
            }
            debug_assert!(factors != 0);
            if factors == 1 {
                debug_assert!(min_lit != 0);
                let c_size = c.size();
                ticks += 1 + self.cache_lines_n(self.occs(min_lit).len(), CLAUSE_PTR_BYTES);
                let n = self.occs(min_lit).len();
                'next_min_watch: for k in 0..n {
                    let d = self.occs(min_lit)[k];
                    if c == d {
                        continue;
                    }
                    ticks += 1;
                    if d.swept() {
                        continue;
                    }
                    if d.size() != c_size {
                        continue;
                    }
                    for &other in d.lits() {
                        if self.getfact(other, QUOTIENT) {
                            continue;
                        }
                        if other != next {
                            continue 'next_min_watch;
                        }
                    }
                    log!(self, c, "matched");
                    log!(self, d, "keeping");

                    nq.qlauses.push(d);
                    nq.matches.push(i);
                    factoring.flauses.push(d);
                    d.set_swept(true);
                    break;
                }
            }
            for &other in c.lits() {
                if self.getfact(other, QUOTIENT) {
                    self.unmarkfact(other, QUOTIENT);
                }
            }
            i += 1;
        }
        self.clear_flauses(&mut factoring.flauses);
        self.stats.ticks.factor += ticks;

        debug_assert!(expected_next_count as usize <= nq.qlauses.len());
        let _ = expected_next_count;
    }

    // We only need to enlarge factoring.count as everything else is
    // initialized in internal
    pub fn resize_factoring(&mut self, factoring: &mut Factoring, lit: i32) {
        debug_assert!(lit > 0);
        let new_var_size = lit as usize + 1;
        let new_lit_size = 2 * new_var_size;
        enlarge_zero(&mut factoring.count, new_lit_size);
    }

    pub fn flush_unmatched_clauses(&mut self, q: *mut Quotient) {
        // SAFETY: 'q' and its predecessor are distinct live nodes.
        let qr = unsafe { &mut *q };
        let prev = unsafe { &mut *qr.prev };
        let n = qr.qlauses.len();
        debug_assert!(n == qr.matches.len());
        let prev_is_first = prev.id == 0;
        let mut i: usize = 0;
        while i < qr.matches.len() {
            let j = qr.matches[i];
            qr.matches[i] = i;
            debug_assert!(i <= j);
            if !prev_is_first {
                let matches = prev.matches[j];
                prev.matches[i] = matches;
            }
            let c = prev.qlauses[j];
            prev.qlauses[i] = c;
            i += 1;
        }
        log!(self, "flushing {} clauses of quotient[{}]", prev.qlauses.len() - n, prev.id);
        if !prev_is_first {
            prev.matches.resize(n, 0);
        }
        prev.qlauses.resize(n, CRef::NULL);
    }

    // special case when we have two quotients with negated factors.
    // in this case, factoring does not make sense, and instead we
    // can resolve the clauses of the two quotients.
    // this subsumes all clauses in all quotients.
    pub fn add_self_subsuming_factor(&mut self, q: *mut Quotient, p: *mut Quotient) {
        // SAFETY: live nodes of the quotient list (not part of 'self').
        let qr = unsafe { &*q };
        let pr = unsafe { &*p };
        let factor = qr.factor;
        let not_factor = pr.factor;
        debug_assert!(-factor == not_factor);
        log!(self, "adding self subsuming factor because blocked clause is a tautology");
        for &c in qr.qlauses.iter() {
            for &lit in c.lits() {
                if lit == factor {
                    continue;
                }
                self.clause.push(lit);
            }
            if self.lrat {
                for &d in pr.qlauses.iter() {
                    let mut matched = true;
                    for &lit in d.lits() {
                        if lit == not_factor {
                            continue;
                        }
                        if !self.clause.iter().any(|&l| l == lit) {
                            matched = false;
                            break;
                        }
                    }
                    if matched {
                        self.lrat_chain.push(d.id());
                        break;
                    }
                }
                self.lrat_chain.push(c.id());
                debug_assert!(self.lrat_chain.len() == 2);
            }
            if self.clause.len() > 1 {
                self.new_factor_clause(0);
            } else {
                let unit = self.clause[0];
                let tmp = self.val(unit);
                if tmp == 0 {
                    self.assign_unit(unit);
                } else if tmp < 0 {
                    if self.lrat {
                        let id = self.unit_id(-unit);
                        self.lrat_chain.push(id);
                        self.lrat_chain.reverse();
                    }
                    self.learn_empty_clause();
                    self.clause.clear();
                    self.lrat_chain.clear();
                    break;
                }
            }
            self.clause.clear();
            self.lrat_chain.clear();
        }
    }

    pub fn self_subsuming_factor(&mut self, q: *mut Quotient) -> bool {
        let mut x: *mut Quotient = std::ptr::null_mut();
        let mut y: *mut Quotient = std::ptr::null_mut();
        let mut found = false;
        let mut p = q;
        while !p.is_null() {
            // SAFETY: live nodes of the quotient list.
            let factor = unsafe { (*p).factor };
            if self.flags(factor).seen {
                debug_assert!(self.analyzed.iter().any(|&l| l == -factor));
                found = true;
                x = p;
                let mut r = q;
                while !r.is_null() {
                    // SAFETY: see above.
                    if unsafe { (*r).factor } != -factor {
                        r = unsafe { (*r).prev };
                        continue;
                    }
                    y = r;
                    break;
                }
                break;
            }
            self.analyzed.push(factor);
            self.flags_mut(factor).seen = true;
            p = unsafe { (*p).prev };
        }
        debug_assert!(!found || (!x.is_null() && !y.is_null()));
        self.clear_analyzed_literals();
        if found {
            self.add_self_subsuming_factor(x, y);
            return true;
        }
        false
    }

    // this is a pure binary clauses containing fresh and one other literal
    // it is added for all applicable quotients.
    pub fn add_factored_divider(&mut self, q: *mut Quotient, fresh: i32) {
        // SAFETY: live node of the quotient list.
        let factor = unsafe { (*q).factor };
        log!(self, "factored {} divider {}", factor, fresh);
        self.clause.push(fresh);
        self.clause.push(factor);
        self.new_factor_clause(fresh);
        self.clause.clear();
        if self.lrat {
            self.mini_chain.push(-self.clause_id);
        }
    }

    // this clause is blocked on fresh, i.e., it contains all literals from
    // the binaries above, but negated. This is only added to the proof, to
    // make checking easier.
    pub fn blocked_clause(&mut self, q: *mut Quotient, not_fresh: i32) {
        if self.proof.is_none() {
            return;
        }
        self.clause_id += 1;
        let new_id = self.clause_id;
        // SAFETY: live nodes of the quotient list.
        unsafe { (*q).bid = new_id };
        debug_assert!(self.clause.is_empty());
        self.clause.push(not_fresh);
        let mut p = q;
        while !p.is_null() {
            // SAFETY: see above.
            let pr = unsafe { &*p };
            self.clause.push(-pr.factor);
            p = pr.prev;
        }
        debug_assert!(!self.lrat || !self.mini_chain.is_empty());
        let ext = self.externalize(not_fresh);
        self.proof.as_mut().unwrap().add_derived_rat_clause_lits(
            new_id,
            true,
            ext,
            &self.clause,
            &self.mini_chain,
        );
        self.mini_chain.clear();
        self.clause.clear();
    }

    // this is the other side of the factored clauses. To derive these,
    // one can resolved the blocked clause on all matching clauses of
    // one type
    pub fn add_factored_quotient(&mut self, q: *mut Quotient, not_fresh: i32) {
        // SAFETY: live nodes of the quotient list (not part of 'self').
        let qr = unsafe { &*q };
        log!(self, "adding factored quotient[{}] clauses", qr.id);
        let factor = qr.factor;
        debug_assert!(self.lrat_chain.is_empty());
        let qlauses = qr.qlauses.clone();
        let mut idx: u32 = 0;
        while (idx as usize) < qlauses.len() {
            let c = qlauses[idx as usize];
            debug_assert!(self.clause.is_empty());
            for &other in c.lits() {
                if other == factor {
                    continue;
                }
                self.clause.push(other);
            }
            if self.lrat {
                debug_assert!(self.proof.is_some());
                debug_assert!(qr.bid != 0);
                let mut idxtoo: u32 = idx;
                let mut p = q;
                while !p.is_null() {
                    // SAFETY: see above.
                    let pr = unsafe { &*p };
                    self.lrat_chain.push(pr.qlauses[idxtoo as usize].id());
                    if !pr.prev.is_null() {
                        idxtoo = pr.matches[idx as usize] as u32;
                    }
                    p = pr.prev;
                }
                self.lrat_chain.push(qr.bid);
            }
            self.clause.push(not_fresh);
            self.new_factor_clause(0);
            self.clause.clear();
            self.lrat_chain.clear();
            idx += 1;
        }
        if self.proof.is_some() {
            self.clause.push(not_fresh);
            let mut p = q;
            while !p.is_null() {
                // SAFETY: see above.
                let pr = unsafe { &*p };
                self.clause.push(-pr.factor);
                p = pr.prev;
            }
            self.proof.as_mut().unwrap().delete_clause_lits(qr.bid, true, &self.clause);
            self.clause.clear();
        }
    }

    // remove deleted clauses once factored.
    pub fn eagerly_remove_from_occurences(&mut self, c: CRef) {
        for &lit in c.lits() {
            let occ = self.occs_mut(lit);
            let end = occ.len();
            let mut p = 0usize;
            let mut q = 0usize;
            while p != end {
                occ[q] = occ[p];
                p += 1;
                if occ[q] != c {
                    q += 1;
                }
            }
            debug_assert!(q + 1 == p);
            occ.truncate(q);
        }
    }

    // delete the factored clauses
    pub fn delete_unfactored(&mut self, q: *mut Quotient) {
        // SAFETY: live node of the quotient list (not part of 'self').
        let qr = unsafe { &*q };
        log!(self, "deleting unfactored quotient[{}] clauses", qr.id);
        for &c in qr.qlauses.iter() {
            self.eagerly_remove_from_occurences(c);
            self.mark_garbage(c);
            self.stats.literals_unfactored += c.size() as i64;
            self.stats.clauses_unfactored += 1;
        }
    }

    // update the priority queue for scheduling
    pub fn update_factored(&mut self, factoring: &mut Factoring, q: *mut Quotient) {
        // SAFETY: live node of the quotient list (not part of 'self').
        let qr = unsafe { &*q };
        let factor = qr.factor;
        self.update_factor_candidate(factoring, factor);
        self.update_factor_candidate(factoring, -factor);
        for &c in qr.qlauses.iter() {
            log!(self, c, "deleting unfactored");
            for &lit in c.lits() {
                if lit != factor {
                    self.update_factor_candidate(factoring, lit);
                }
            }
        }
    }

    pub fn apply_factoring(&mut self, factoring: &mut Factoring, q: *mut Quotient) -> bool {
        // SAFETY (all dereferences below): live nodes of the quotient list.
        let mut p = q;
        while !unsafe { (*p).prev }.is_null() {
            self.flush_unmatched_clauses(p);
            p = unsafe { (*p).prev };
        }
        if self.self_subsuming_factor(q) {
            let mut p = q;
            while !p.is_null() {
                self.delete_unfactored(p);
                p = unsafe { (*p).prev };
            }
            let mut p = q;
            while !p.is_null() {
                self.update_factored(factoring, p);
                p = unsafe { (*p).prev };
            }
            return true;
        }
        let fresh = self.get_new_extension_variable();
        if fresh == 0 {
            return false;
        }
        self.stats.factored += 1;
        factoring.fresh.push(fresh);
        let mut p = q;
        while !p.is_null() {
            self.add_factored_divider(p, fresh);
            p = unsafe { (*p).prev };
        }
        let not_fresh = -fresh;
        self.blocked_clause(q, not_fresh);
        self.add_factored_quotient(q, not_fresh);
        let mut p = q;
        while !p.is_null() {
            self.delete_unfactored(p);
            p = unsafe { (*p).prev };
        }
        let mut p = q;
        while !p.is_null() {
            self.update_factored(factoring, p);
            p = unsafe { (*p).prev };
        }
        debug_assert!(fresh > 0);
        self.resize_factoring(factoring, fresh);
        true
    }

    pub fn update_factor_candidate(&mut self, factoring: &mut Factoring, lit: i32) {
        let schedule = &mut factoring.schedule;
        let size = self.occs(lit).len();
        let idx = self.vlit(lit);
        if schedule.contains(idx) {
            schedule.update(idx);
        } else if size > 1 {
            schedule.push_back(idx);
        }
    }

    pub fn schedule_factorization(&mut self, factoring: &mut Factoring) {
        for idx in self.vars() {
            if self.active(idx) {
                let f = self.flags(idx).factor;
                let lit = idx;
                let not_lit = -lit;
                if f & 1 != 0 {
                    self.update_factor_candidate(factoring, lit);
                }
                if f & 2 != 0 {
                    self.update_factor_candidate(factoring, not_lit);
                }
            }
        }
        let size_cands = factoring.schedule.size();
        verbose!(
            self,
            2,
            "scheduled {} factorization candidate literals {} %",
            size_cands,
            fmt_f(percent(size_cands as f64, self.max_var as f64), 0)
        );
    }

    pub fn adjust_scores_and_phases_of_fresh_variables(&mut self, factoring: &mut Factoring) {
        if self.opts.factorunbump == 0 {
            factoring.fresh.clear();
            return;
        }
        if factoring.fresh.is_empty() {
            return;
        }

        for &lit in factoring.fresh.iter() {
            log!(self, "dequeuing {}", loglit!(self, lit));
            self.queue.dequeue(&mut self.links, lit);
        }

        for &lit in factoring.fresh.iter() {
            log!(self, "dequeuing {}", loglit!(self, lit));
            self.queue.bury(&mut self.links, lit);
        }

        // fix the scores with negative numbers
        let mut lit = self.queue.first;
        self.queue.bumped = 0;
        while lit != 0 {
            self.queue.bumped += 1;
            self.btab[lit as usize] = self.queue.bumped;
            lit = self.links[lit as usize].next;
        }
        self.stats.bumped = self.queue.bumped;
        let last = self.queue.last;
        self.update_queue_unassigned(last);

        #[cfg(debug_assertions)]
        {
            for v in self.vars() {
                debug_assert!(self.val(v) != 0 || self.scores.contains(v as u32));
            }
            lit = self.queue.first;
            let mut next_lit = self.links[lit as usize].next;
            while next_lit != 0 {
                debug_assert!(self.btab[lit as usize] < self.btab[next_lit as usize]);
                let tmp = self.links[next_lit as usize].next;
                debug_assert!(tmp == 0 || self.links[tmp as usize].prev == next_lit);
                lit = next_lit;
                next_lit = tmp;
            }

            lit = self.queue.last;
            next_lit = self.links[lit as usize].prev;
            while next_lit != 0 {
                debug_assert!(self.btab[lit as usize] > self.btab[next_lit as usize]);
                let tmp = self.links[next_lit as usize].prev;
                debug_assert!(tmp == 0 || self.links[tmp as usize].next == next_lit);
                lit = next_lit;
                next_lit = tmp;
            }
            debug_assert!(self.queue.first != 0);
            debug_assert!(self.queue.last != 0);
        }
        factoring.fresh.clear();
    }

    pub fn run_factorization(&mut self, limit: i64) -> bool {
        let this: *mut Internal = self;
        let mut factoring = Factoring::new(this, limit);
        self.schedule_factorization(&mut factoring);
        let mut done = false;
        let mut factored: u32 = 0;
        verbose!(
            self,
            3,
            "factorization limit of {} ticks",
            (limit - self.stats.ticks.factor) as u64
        );

        while !self.unsat && !done && !factoring.schedule.empty() {
            let ufirst = factoring.schedule.pop_front();
            log!(self, "next factor candidate {}", ufirst as i32);
            let first = self.u2i(ufirst);
            let first_idx = self.vidx(first);
            if !self.active(first_idx) {
                continue;
            }
            if self.occs(first).is_empty() {
                factoring.schedule.clear();
                break;
            }
            if self.stats.ticks.factor > limit {
                verbose!(self, 2, "factorization ticks limit hit");
                break;
            }
            if self.terminated_asynchronously(1) {
                break;
            }
            let bit: u8 = (1u32 << ((first < 0) as u32)) as u8;
            if self.flags(first_idx).factor & bit == 0 {
                continue;
            }
            self.flags_mut(first_idx).factor &= !bit;
            let first_count = self.first_factor(&mut factoring, first);
            if first_count > 1 {
                loop {
                    let mut next_count: u32 = 0;
                    let next = self.next_factor(&mut factoring, &mut next_count);
                    if next == 0 {
                        break;
                    }
                    debug_assert!(next_count > 1);
                    if next_count < 2 {
                        break;
                    }
                    self.factorize_next(&mut factoring, next, next_count);
                }
                let mut reduction: usize = 0;
                let q = self.best_quotient(&mut factoring, Some(&mut reduction));
                if !q.is_null() && (reduction as i32) > factoring.bound {
                    if self.apply_factoring(&mut factoring, q) {
                        factored += 1;
                    } else {
                        done = true;
                    }
                }
            }
            self.release_quotients(&mut factoring);
        }

        // since we cannot remove elements from the heap we check wether the
        // first element in the heap has occurences
        let mut completed = factoring.schedule.empty();
        if !completed {
            let idx = factoring.schedule.front();
            completed = self.occs(self.u2i(idx)).is_empty();
        }
        self.adjust_scores_and_phases_of_fresh_variables(&mut factoring);
        self.report(b'f', (factored == 0) as i32);
        completed
    }

    pub fn get_new_extension_variable(&mut self) -> i32 {
        let current_max_external = self.external().max_var;
        let new_external = current_max_external + 1;
        let new_internal = self.external().internalize(new_external, true);
        // one sideeffect of internalize is enlarging the internal datastructures
        // which can initialize the watches (wtab)
        if self.watching() {
            self.reset_watches();
        }
        // it does not enlarge otab, however, so we do this manually
        self.init_occs();
        debug_assert!(self.vlit(new_internal) != 0);
        new_internal
    }

    pub fn factor(&mut self) -> bool {
        if self.unsat {
            return false;
        }
        if self.terminated_asynchronously(1) {
            return false;
        }
        if self.opts.factor == 0 {
            return false;
        }

        let v_active = self.active_count();
        if v_active == 0 {
            return false;
        }
        let log_active = (v_active as f64).log10() as usize;
        let eliminations = self.stats.elimrounds as usize;
        let delay = self.opts.factordelay as usize;
        let delay_limit = eliminations + delay;
        if log_active > delay_limit {
            verbose!(
                self,
                3,
                "factorization delayed as {} = log10 ({})> eliminations + delay = {} + {} = {}",
                log_active,
                v_active as u32,
                eliminations,
                delay,
                delay_limit
            );
            return false;
        }
        // The following assertion fails if there are *only* user propagator
        // clauses (which are redundant).
        // assert (stats.mark.factor || clauses.empty ());
        if self.last.factor.marked >= self.stats.mark.factor {
            verbose!(
                self,
                3,
                "factorization skipped as no literals have beenmarked to be added ({} < {})",
                self.last.factor.marked as u64,
                self.stats.mark.factor as u64
            );
            return false;
        }
        debug_assert!(self.level == 0);

        set_effort_limit!(self, limit, factor, self.stats.factor != 0);
        let mut limit = limit;
        if self.stats.factor == 0 {
            limit = (limit as f64 + self.opts.factoriniticks as f64 * 1e6) as i64;
        }

        self.mark_duplicated_binary_clauses_as_garbage();

        start_simplifier!(self, factor, FACTOR);
        self.stats.factor += 1;

        let before_variables = self.stats.variables_extension + self.stats.variables_original;
        let before_ticks = self.stats.ticks.factor;
        let before_clauses = self.stats.current.irredundant;

        self.factor_mode();
        let completed = self.run_factorization(limit);
        self.reset_factor_mode();

        self.propagated = 0;
        if !self.unsat && !self.propagate() {
            self.learn_empty_clause();
        }

        let after_variables = self.stats.variables_extension + self.stats.variables_original;
        let after_clauses = self.stats.current.irredundant;
        let after_ticks = self.stats.ticks.factor;
        let delta_variables = after_variables - before_variables;
        let delta_clauses = before_clauses - after_clauses;
        let delta_ticks = after_ticks - before_ticks;
        verbose!(
            self,
            2,
            "used {} million factorization ticks",
            fmt_f(delta_ticks as f64 * 1e-6, 6)
        );
        phase!(
            self,
            "factorization",
            self.stats.factor,
            "introduced {} extension variables {}%",
            delta_variables,
            fmt_f(percent(delta_variables as f64, before_variables as f64), 0)
        );
        phase!(
            self,
            "factorization",
            self.stats.factor,
            "removed {} irredundant clauses {}%",
            delta_clauses,
            fmt_f(percent(delta_clauses as f64, before_clauses as f64), 0)
        );

        if completed {
            self.last.factor.marked = self.stats.mark.factor;
        }
        stop_simplifier!(self, factor, FACTOR);
        true
    }
}

impl Factoring {
    /// `Factoring (Internal *, int64_t limit)`.
    pub fn new(internal: *mut Internal, limit: i64) -> Factoring {
        // SAFETY: 'internal' is the live owner creating this object.
        let i = unsafe { &*internal };
        let max_var = i.max_var as u32;
        let max_lit = 2 * (max_var + 1);
        let mut count: Vec<u32> = Vec::new();
        enlarge_zero(&mut count, max_lit as usize);
        Factoring {
            internal,
            limit,
            schedule: Heap::new(factor_occs_size::new(internal)),
            initial: max_var as i32,
            bound: i.lim.elimbound as i32,
            count,
            fresh: Vec::new(),
            counted: Vec::new(),
            nounted: Vec::new(),
            flauses: Vec::new(),
            quotients: FactoringQuotients { first: std::ptr::null_mut(), last: std::ptr::null_mut() },
        }
    }
}

impl Drop for Factoring {
    /// `~Factoring ()`.
    fn drop(&mut self) {
        debug_assert!(self.counted.is_empty());
        debug_assert!(self.nounted.is_empty());
        debug_assert!(self.flauses.is_empty());
        let internal = self.internal;
        // SAFETY: the owning 'Internal' outlives this local object.
        unsafe { (*internal).release_quotients(self) };
        self.schedule.erase(); // actually not necessary
    }
}

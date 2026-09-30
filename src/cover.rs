//! Port of `cover.hpp` (the `COVER` coverage macro) and `cover.cpp`
//! (covered clause elimination).

use crate::internal::Internal;

/// `COVER (COND)`: coverage goal, used similar to 'assert' (but with
/// flipped condition) and also included in optimized builds.
#[macro_export]
macro_rules! cover {
    ($cond:expr) => {
        if $cond {
            $crate::cfprintf!(
                $crate::message::c_stderr(),
                "{}cadical{}: {}:{}: {}: Coverage goal {}`{}'{} reached.\n",
                $crate::terminal::terr().bold_code(),
                $crate::terminal::terr().normal_code(),
                module_path!(),
                line!(),
                file!(),
                $crate::terminal::terr().green_code(),
                stringify!($cond),
                $crate::terminal::terr().normal_code()
            );
            $crate::message::fflush($crate::message::c_stderr());
            std::process::abort();
        }
    };
}

#[derive(Clone, Copy, Debug, Default)]
pub struct CoverorNext {
    pub added: usize,
    pub covered: usize,
}

/// `struct Coveror` (declared in 'cover.cpp').
#[derive(Clone, Debug, Default)]
pub struct Coveror {
    /// Acts as trail.
    pub added: Vec<i32>,
    /// Extension stack for witness.
    pub extend: Vec<i32>,
    /// Clause literals or added through CLA.
    pub covered: Vec<i32>,
    /// Of literals in resolution candidates.
    pub intersection: Vec<i32>,
    /// Actual number of ALAs.
    pub alas: usize,
    /// Actual number of CLAs.
    pub clas: usize,
    /// Propagate next ...
    pub next: CoverorNext,
}

impl Coveror {
    pub fn new() -> Coveror {
        Coveror::default()
    }
}

#[allow(dead_code)]
fn _uses(_: &Internal) {}

/*------------------------------------------------------------------------*/

// Covered clause elimination (CCE) is described in our short LPAR-10 paper
// and later in more detail in our JAIR'15 article.  Actually implement
// the asymmetric version which adds asymmetric literals too but still call
// it 'CCE' in the following (and not 'ACCE').  This implementation provides
// a simplified and cleaner version of the one implemented before in
// Lingeling. We still follow quite closely the original description in the
// literature, which is based on asymmetric literal addition (ALA) and
// covered literal addition (CLA).  Both can be seen as kind of propagation,
// where the literals in the original and then extended clause are assigned
// to false, and the literals on the trail (actually we use our own 'added'
// stack for that) make up the extended clause.   The ALA steps can be
// implemented by simple propagation (copied from 'propagate.cpp') using
// watches, while the CLA steps need full occurrence lists to determine the
// resolution candidate clauses.  The CCE is successful if a conflict is
// found during ALA steps or if during a CLA step all resolution candidates
// of a literal on the trail are satisfied (the extended clause is blocked).

#[allow(unused_imports)]
use crate::prelude::*;

use crate::format::fmt_f;
use crate::internal::Mode;

impl Internal {
    /*--------------------------------------------------------------------*/

    // Push on the extension stack a clause made up of the given literal,
    // the original clause (initially copied to 'covered') and all the added
    // covered literals so far.  The given literal will act as blocking
    // literal for that clause, if CCE is successful.  Only in this case,
    // this private extension stack is copied to the actual extension stack
    // of the solver.  Note, that even though all 'added' clauses correspond
    // to the extended clause, we only need to save the original and added
    // covered literals.

    #[inline]
    pub fn cover_push_extension(&mut self, lit: i32, coveror: &mut Coveror) {
        coveror.extend.push(0);
        coveror.extend.push(lit); // blocking literal comes first
        let mut found = false;
        for &other in coveror.covered.iter() {
            if lit == other {
                debug_assert!(!found);
                found = true;
            } else {
                coveror.extend.push(other);
            }
        }
        debug_assert!(found);
        let _ = found;
    }

    // Successful covered literal addition (CLA) step.

    #[inline]
    pub fn covered_literal_addition(&mut self, lit: i32, coveror: &mut Coveror) {
        self.require_mode(Mode::COVER);
        debug_assert!(self.level == 1);
        self.cover_push_extension(lit, coveror);
        for &other in coveror.intersection.iter() {
            log!(self, "covered literal addition {}", other);
            debug_assert!(self.val(other) == 0);
            debug_assert!(self.val(-other) == 0);
            self.set_val(other, -1);
            coveror.covered.push(other);
            coveror.added.push(other);
            coveror.clas += 1;
        }
        coveror.next.covered = 0;
    }

    // Successful asymmetric literal addition (ALA) step.

    #[inline]
    pub fn asymmetric_literal_addition(&mut self, lit: i32, coveror: &mut Coveror) {
        self.require_mode(Mode::COVER);
        debug_assert!(self.level == 1);
        log!(self, "initial asymmetric literal addition {}", lit);
        debug_assert!(self.val(lit) == 0);
        debug_assert!(self.val(-lit) == 0);
        self.set_val(lit, -1);
        coveror.added.push(lit);
        coveror.alas += 1;
        coveror.next.covered = 0;
    }

    /*--------------------------------------------------------------------*/

    // In essence copied and adapted from 'propagate' in 'propagate.cpp'.
    // Since this function is also a hot-spot here in 'cover' we specialize
    // it in the same spirit as 'probe_propagate' and 'vivify_propagate'.
    // Please refer to the detailed comments for 'propagate' in
    // 'propagate.cpp' for details.

    pub fn cover_propagate_asymmetric(&mut self, lit: i32, ignore: CRef, coveror: &mut Coveror) -> bool {
        self.require_mode(Mode::COVER);
        self.stats.propagations.cover += 1;
        debug_assert!(self.val(lit) < 0);
        let mut subsumed = false;
        log!(self, "asymmetric literal propagation of {}", lit);
        // SAFETY: the watch list of 'lit' is neither reallocated nor
        // otherwise accessed below: new watches are only pushed onto the
        // watch lists of unassigned literals ('r' in 'watch_literal') which
        // differ from the falsified 'lit', and the outer 'wtab' vector is
        // not resized during this function.
        let ws: *mut Watches = self.watches_mut(lit);
        let eow = unsafe { (*ws).len() };
        let mut j = 0usize;
        let mut i = 0usize;
        while !subsumed && i != eow {
            let w = unsafe { (&*ws)[i] };
            unsafe { (&mut *ws)[j] = w };
            j += 1;
            i += 1;
            if w.clause == ignore {
                continue; // costly but necessary here ...
            }
            let b = self.val(w.blit);
            if b > 0 {
                continue;
            }
            if w.clause.garbage() {
                j -= 1;
            } else if w.binary() {
                if b < 0 {
                    log!(self, w.clause, "found subsuming");
                    subsumed = true;
                } else {
                    self.asymmetric_literal_addition(-w.blit, coveror);
                }
            } else {
                let c = w.clause;
                let other = c.lit(0) ^ c.lit(1) ^ lit;
                c.set_lit(0, other);
                c.set_lit(1, lit);
                let u = self.val(other);
                if u > 0 {
                    unsafe { (&mut *ws)[j - 1].blit = other };
                } else {
                    let size = c.size();
                    let end = size as usize;
                    let middle = c.pos() as usize;
                    let mut k = middle;
                    let mut v: i8 = -1;
                    let mut r = 0;
                    while k != end {
                        r = c.lit(k);
                        v = self.val(r);
                        if v >= 0 {
                            break;
                        }
                        k += 1;
                    }
                    if v < 0 {
                        k = 2;
                        debug_assert!(c.pos() <= size);
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
                    debug_assert!(k <= end);
                    if v > 0 {
                        unsafe { (&mut *ws)[j - 1].blit = r };
                    } else if v == 0 {
                        log!(self, c, "unwatch {} in", lit);
                        c.set_lit(1, r);
                        c.set_lit(k, lit);
                        self.watch_literal(r, lit, c);
                        j -= 1;
                    } else if u == 0 {
                        debug_assert!(v < 0);
                        self.asymmetric_literal_addition(-other, coveror);
                    } else {
                        debug_assert!(u < 0);
                        debug_assert!(v < 0);
                        log!(self, c, "found subsuming");
                        subsumed = true;
                        break;
                    }
                }
            }
        }
        if j != i {
            let ws = unsafe { &mut *ws };
            while i != eow {
                ws[j] = ws[i];
                j += 1;
                i += 1;
            }
            ws.truncate(j);
        }
        subsumed
    }

    // Covered literal addition (which needs full occurrence lists).  The
    // function returns 'true' if the extended clause is blocked on 'lit.'

    pub fn cover_propagate_covered(&mut self, lit: i32, coveror: &mut Coveror) -> bool {
        self.require_mode(Mode::COVER);

        debug_assert!(self.val(lit) < 0);
        if self.frozen(lit) {
            log!(self, "no covered propagation on frozen literal {}", lit);
            return false;
        }

        self.stats.propagations.cover += 1;

        log!(self, "covered propagation of {}", lit);
        debug_assert!(coveror.intersection.is_empty());

        let end = self.occs(-lit).len();
        let mut first = true;

        // Compute the intersection of the literals in all the clauses with
        // '-lit'.  If all these clauses are double satisfied then we know
        // that the extended clauses (in 'added') is blocked.  All literals
        // in the intersection can be added as covered literal. As soon the
        // intersection becomes empty (during traversal of clauses with
        // '-lit') we abort.

        for i in 0..end {
            let c = self.occs(-lit)[i];
            if c.garbage() {
                continue;
            }

            // First check whether clause is 'blocked', i.e., is double
            // satisfied.

            let mut blocked = false;
            for &other in c.lits() {
                if other == -lit {
                    continue;
                }
                let tmp = self.val(other);
                if tmp < 0 {
                    continue;
                }
                if tmp > 0 {
                    blocked = true;
                    break;
                }
            }
            if blocked {
                // ... if 'c' is double satisfied.
                log!(self, c, "blocked");
                continue; // with next clause with '-lit'.
            }

            if first {
                // Copy and mark literals of first clause.

                for &other in c.lits() {
                    if other == -lit {
                        continue;
                    }
                    let tmp = self.val(other);
                    if tmp < 0 {
                        continue;
                    }
                    debug_assert!(tmp == 0);
                    coveror.intersection.push(other);
                    self.mark(other);
                }

                first = false;
            } else {
                // Unmark all literals in current clause.

                for &other in c.lits() {
                    if other == -lit {
                        continue;
                    }
                    let mut tmp = self.val(other);
                    if tmp < 0 {
                        continue;
                    }
                    debug_assert!(tmp == 0);
                    tmp = self.marked(other);
                    if tmp > 0 {
                        self.unmark(other);
                    }
                }

                // Then remove from intersection all marked literals.

                let iend = coveror.intersection.len();
                let mut j = 0usize;
                for k in 0..iend {
                    let other = coveror.intersection[k];
                    coveror.intersection[j] = other;
                    j += 1;
                    let tmp = self.marked(other);
                    debug_assert!(tmp >= 0);
                    if tmp != 0 {
                        j -= 1;
                        self.unmark(other); // remove marked and unmark it
                    } else {
                        self.mark(other); // keep unmarked and mark it
                    }
                }
                let new_size = j;
                coveror.intersection.truncate(new_size);

                if !coveror.intersection.is_empty() {
                    continue;
                }

                // No covered literal addition candidates in the
                // intersection left!  Move this clause triggering early
                // abort to the beginning.  This is a common move to front
                // strategy to minimize effort.

                let os = self.occs_mut(-lit);
                let mut ii = i;
                while ii != 0 {
                    let prev = ii - 1;
                    os[ii] = os[prev];
                    ii = prev;
                }
                os[0] = c;

                break; // early abort ...
            }
        }

        let mut res = false;
        if first {
            log!(self, "all resolution candidates with {} blocked", -lit);
            debug_assert!(coveror.intersection.is_empty());
            self.cover_push_extension(lit, coveror);
            res = true;
        } else if coveror.intersection.is_empty() {
            log!(self, "empty intersection of resolution candidate literals");
        } else {
            log!(
                self,
                &coveror.intersection,
                "non-empty intersection of resolution candidate literals"
            );
            self.covered_literal_addition(lit, coveror);
            self.unmark_lits(&coveror.intersection);
            coveror.intersection.clear();
            coveror.next.covered = 0; // Restart covering.
        }

        self.unmark_lits(&coveror.intersection);
        coveror.intersection.clear();

        res
    }

    /*--------------------------------------------------------------------*/

    /// Add the literals of `c` not needed for covering to `clause` and to
    /// the extension stack, which avoids RAT proofs (shared code written
    /// out twice in C++).
    fn cover_add_missing_literals(&mut self, c: CRef, coveror: &Coveror) {
        let mut i: i32 = 0;
        let mut j: i32 = 0;
        while i < c.size() {
            let lit = c.lit(i as usize);
            if j >= coveror.covered.len() as i32 || c.lit(i as usize) != coveror.covered[j as usize] {
                j -= 1;
                log!(self, "adding lit {} not needed for ATA", lit);
                self.clause.push(lit);
                self.external().push_clause_literal_on_extension_stack(lit);
            }
            i += 1;
            j += 1;
        }
    }

    pub fn cover_clause(&mut self, c: CRef, coveror: &mut Coveror) -> bool {
        self.require_mode(Mode::COVER);
        debug_assert!(!c.garbage());

        log!(self, c, "trying covered clauses elimination on");
        let mut satisfied = false;
        for &lit in c.lits() {
            if self.val(lit) > 0 {
                satisfied = true;
            }
        }

        if satisfied {
            log!(self, c, "clause already satisfied");
            self.mark_garbage(c);
            return false;
        }

        debug_assert!(coveror.added.is_empty());
        debug_assert!(coveror.extend.is_empty());
        debug_assert!(coveror.covered.is_empty());

        debug_assert!(self.level == 0);
        self.level = 1;
        log!(self, "assuming literals of candidate clause");
        for &lit in c.lits() {
            if self.val(lit) != 0 {
                continue;
            }
            self.asymmetric_literal_addition(lit, coveror);
            coveror.covered.push(lit);
        }

        let mut tautological = false;

        coveror.next.added = 0;
        coveror.next.covered = 0;

        while !tautological {
            if coveror.next.added < coveror.added.len() {
                let lit = coveror.added[coveror.next.added];
                coveror.next.added += 1;
                tautological = self.cover_propagate_asymmetric(lit, c, coveror);
            } else if coveror.next.covered < coveror.covered.len() {
                let lit = coveror.covered[coveror.next.covered];
                coveror.next.covered += 1;
                tautological = self.cover_propagate_covered(lit, coveror);
            } else {
                break;
            }
        }

        if tautological {
            if coveror.extend.is_empty() {
                self.stats.cover.asymmetric += 1;
                self.stats.cover.total += 1;
                log!(self, c, "asymmetric tautological");
            } else {
                self.stats.cover.blocked += 1;
                self.stats.cover.total += 1;
                // Only copy extension stack if successful.
                let mut prev = i32::MIN;
                let mut already_pushed = false;
                let mut last_id: i64 = 0;
                log!(self, c, "covered tautological");
                debug_assert!(self.clause.is_empty());
                log!(self, &coveror.extend, "extension = ");
                for k in 0..coveror.extend.len() {
                    let other = coveror.extend[k];
                    if prev == 0 {
                        // are we finishing a clause?
                        if already_pushed {
                            // add missing literals that are not needed for
                            // covering but avoid RAT proofs
                            self.cover_add_missing_literals(c, coveror);
                        }
                        if self.proof.is_some() && already_pushed {
                            if self.lrat {
                                self.lrat_chain.push(c.id());
                            }
                            log!(self, "LEARNING clause with id {}", last_id);
                            let proof = self.proof.as_mut().unwrap();
                            proof.add_derived_clause_lits(last_id, false, &self.clause, &self.lrat_chain);
                            proof.weaken_plus_lits(last_id, &self.clause);
                            self.lrat_chain.clear();
                        }
                        self.clause_id += 1;
                        last_id = self.clause_id;
                        let external = self.external();
                        external.push_zero_on_extension_stack();
                        external.push_witness_literal_on_extension_stack(other);
                        external.push_zero_on_extension_stack();
                        external.push_id_on_extension_stack(last_id);
                        external.push_zero_on_extension_stack();
                        self.clause.clear();
                        already_pushed = true;
                    }
                    if other != 0 {
                        self.external().push_clause_literal_on_extension_stack(other);
                        self.clause.push(other);
                        log!(self, &self.clause, "current clause is");
                    }
                    prev = other;
                }

                if self.proof.is_some() {
                    // add missing literals that are not needed for covering
                    // but avoid RAT proofs
                    self.cover_add_missing_literals(c, coveror);
                    if self.lrat {
                        self.lrat_chain.push(c.id());
                    }
                    let proof = self.proof.as_mut().unwrap();
                    proof.add_derived_clause_lits(last_id, false, &self.clause, &self.lrat_chain);
                    proof.weaken_plus_lits(last_id, &self.clause);
                    self.lrat_chain.clear();
                }
                self.clause.clear();

                self.mark_garbage(c);
            }
        }

        // Backtrack and 'unassign' all literals.

        debug_assert!(self.level == 1);
        for &lit in coveror.added.iter() {
            self.set_val(lit, 0);
        }
        self.level = 0;

        coveror.covered.clear();
        coveror.extend.clear();
        coveror.added.clear();

        tautological
    }

    /*--------------------------------------------------------------------*/

    pub fn cover_round(&mut self) -> i64 {
        if self.unsat {
            return 0;
        }

        self.init_watches();
        self.connect_watches(true); // irredundant watches only is enough

        let mut delta: i64 = self.stats.propagations.search;
        delta = (delta as f64 * (1e-3 * self.opts.covereffort as f64)) as i64;
        if delta < self.opts.covermineff as i64 {
            delta = self.opts.covermineff as i64;
        }
        if delta > self.opts.covermaxeff as i64 {
            delta = self.opts.covermaxeff as i64;
        }
        delta = std::cmp::max(delta, 2i64 * self.active_count() as i64);

        phase!(
            self,
            "cover",
            self.stats.cover.count,
            "covered clause elimination limit of {} propagations",
            delta
        );

        let limit = self.stats.propagations.cover + delta;

        self.init_occs();

        let mut schedule: Vec<CRef> = Vec::new();
        let mut coveror = Coveror::new();

        // First connect all clauses and find all not yet tried clauses.
        //
        let mut untried: i64 = 0;
        //
        for k in 0..self.clauses.len() {
            let c = self.clauses[k];
            debug_assert!(!c.frozen());
            if c.garbage() {
                continue;
            }
            if c.redundant() {
                continue;
            }
            let mut satisfied = false;
            let mut allfrozen = true;
            for &lit in c.lits() {
                if self.val(lit) > 0 {
                    satisfied = true;
                    break;
                } else if allfrozen && !self.frozen(lit) {
                    allfrozen = false;
                }
            }
            if satisfied {
                self.mark_garbage(c);
                continue;
            }
            if allfrozen {
                c.set_frozen(true);
                continue;
            }
            for &lit in c.lits() {
                self.occs_mut(lit).push(c);
            }
            if c.size() < self.opts.coverminclslim {
                continue;
            }
            if c.size() > self.opts.covermaxclslim {
                continue;
            }
            if c.covered() {
                continue;
            }
            schedule.push(c);
            untried += 1;
        }

        if schedule.is_empty() {
            phase!(self, "cover", self.stats.cover.count, "no previously untried clause left");

            for k in 0..self.clauses.len() {
                let c = self.clauses[k];
                if c.garbage() {
                    continue;
                }
                if c.redundant() {
                    continue;
                }
                if c.frozen() {
                    c.set_frozen(false);
                    continue;
                }
                if c.size() < self.opts.coverminclslim {
                    continue;
                }
                if c.size() > self.opts.covermaxclslim {
                    continue;
                }
                debug_assert!(c.covered());
                c.set_covered(false);
                schedule.push(c);
            }
        } else {
            // Mix of tried and not tried clauses ....

            for k in 0..self.clauses.len() {
                let c = self.clauses[k];
                if c.garbage() {
                    continue;
                }
                if c.redundant() {
                    continue;
                }
                if c.frozen() {
                    c.set_frozen(false);
                    continue;
                }
                if c.size() < self.opts.coverminclslim {
                    continue;
                }
                if c.size() > self.opts.covermaxclslim {
                    continue;
                }
                if !c.covered() {
                    continue;
                }
                schedule.push(c);
            }
        }

        // 'clause_covered_or_smaller': not yet tried and larger clauses are
        // tried first (stable sort).
        schedule.sort_by_key(|c| (!c.covered(), c.size()));

        let scheduled = schedule.len();
        phase!(
            self,
            "cover",
            self.stats.cover.count,
            "scheduled {} clauses {}% with {} untried {}%",
            scheduled,
            fmt_f(percent(scheduled as f64, self.stats.current.irredundant as f64), 0),
            untried,
            fmt_f(percent(untried as f64, scheduled as f64), 0)
        );

        // Heuristically it should be beneficial to intersect with smaller
        // clauses first, since then the chances are higher that the
        // intersection of resolution candidates becomes emptier earlier.

        for lit in self.lits() {
            if !self.active(lit) {
                continue;
            }
            self.occs_mut(lit).sort_by_key(|c| c.size());
        }

        // This is the main loop of trying to do CCE of candidate clauses.
        //
        let mut covered: i64 = 0;
        //
        while !self.terminated_asynchronously(1) && !schedule.is_empty() && self.stats.propagations.cover < limit {
            let c = schedule.pop().unwrap();
            c.set_covered(true);
            if self.cover_clause(c, &mut coveror) {
                covered += 1;
            }
        }

        let remain = schedule.len();
        let tried = scheduled - remain;
        phase!(
            self,
            "cover",
            self.stats.cover.count,
            "eliminated {} covered clauses out of {} tried {}%",
            covered,
            tried,
            fmt_f(percent(covered as f64, tried as f64), 0)
        );
        if remain != 0 {
            phase!(
                self,
                "cover",
                self.stats.cover.count,
                "remaining {} clauses {}% untried",
                remain,
                fmt_f(percent(remain as f64, scheduled as f64), 0)
            );
        } else {
            phase!(self, "cover", self.stats.cover.count, "all scheduled clauses tried");
        }
        self.reset_occs();
        self.reset_watches();

        covered
    }

    /*--------------------------------------------------------------------*/

    pub fn cover(&mut self) -> bool {
        if self.opts.cover == 0 {
            return false;
        }
        if self.unsat {
            return false;
        }
        if self.terminated_asynchronously(1) {
            return false;
        }
        if self.stats.current.irredundant == 0 {
            return false;
        }

        // TODO: Our current algorithm for producing the necessary clauses on
        // the reconstruction stack for extending the witness requires a
        // covered literal addition step which (empirically) conflicts with
        // flushing during restoring clauses (see 'regr00{48,51}.trace') even
        // though flushing during restore is disabled by default (as is
        // covered clause elimination).  The consequence of combining these
        // two options ('opts.cover' and 'opts.restoreflush') can thus
        // produce incorrect witness reconstruction and thus invalid
        // witnesses.  This is quite infrequent (one out of half billion
        // mobical test cases) but as the two regression traces show, does
        // happen. Thus we disable the combination.
        //
        if self.opts.restoreflush != 0 {
            return false;
        }

        start_simplifier!(self, cover, COVER);

        self.stats.cover.count += 1;

        // During variable elimination unit clauses can be generated which
        // need to be propagated properly over redundant clauses too.  Since
        // variable elimination avoids to have occurrence lists and watches
        // at the same time this propagation is delayed until the end of
        // variable elimination.  Since we want to interleave CCE with it, we
        // have to propagate here.  Otherwise this triggers inconsistencies.
        //
        if self.propagated < self.trail.len() {
            self.init_watches();
            self.connect_watches(false); // need to propagated over all clauses!
            log!(self, "elimination produced {} units", self.trail.len() - self.propagated);
            if !self.propagate() {
                log!(
                    self,
                    "propagating units before covered clause elimination results in empty clause"
                );
                self.learn_empty_clause();
                debug_assert!(self.unsat);
            }
            self.reset_watches();
        }
        debug_assert!(self.unsat || self.propagated == self.trail.len());

        let covered = self.cover_round();

        stop_simplifier!(self, cover, COVER);
        let quiet = self.opts.reportall == 0 && covered == 0;
        self.report(b'c', quiet as i32);

        covered != 0
    }
}

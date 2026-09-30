//! Port of `condition.cpp`.
//!
//! Globally blocked clause elimination (which we call here 'conditioning')
//! is described first in the PhD thesis of Benjamin Kiesl from 2019.  An
//! extended version, which in particular describes the algorithm
//! implemented below is in our invited ATVA'19 paper
//! [KieslHeuleBiere-ATVA'19].  This accordingly needs witnesses consisting
//! potentially of more than one literal.  It is the first technique
//! implemented in CaDiCaL with this feature (PR clause elimination thus
//! should work in principle too).
//!
//! Basically globally blocked clauses are like set blocked clauses, except
//! that the witness cube (of literals to be flipped during reconstruction)
//! can contain variables which are not in the blocked clause.  This can
//! simulate some interesting global optimizations like 'headlines' from the
//! FAN algorithm for ATPG.  The technique was actually motivated to
//! simulate this optimization.  It turns out that globally blocked clauses
//! can be seen as 'conditional autarkies', where in essence the condition
//! cube is the negation of the globally blocked redundant clause (it needs
//! to contain one autarky literal though) and the autarky part represents
//! the witness.

#[allow(unused_imports)]
use crate::prelude::*;

use crate::format::fmt_f;
use crate::util::{erase_vector, percent};

/// Sizes of the assignment and its partition (the anonymous C++ struct
/// used for 'initial' and 'remain' in 'condition_round').
#[derive(Clone, Copy, Debug, Default)]
struct AssignmentSizes {
    assigned: usize,
    conditional: usize,
    autarky: usize,
}

impl Internal {
    /*------------------------------------------------------------------------*/

    // Elimination of globally blocked clauses is first tried in regular
    // intervals in terms of the number of conflicts.  Then the main
    // heuristics is to trigger 'condition' if the decision level is above
    // the current moving average of the back jump level.

    // TODO We might need to consider less frequent conditioning.

    pub fn conditioning(&mut self) -> bool {
        if self.opts.condition == 0 {
            return false;
        }
        if !self.preprocessing && self.opts.inprocessing == 0 {
            return false;
        }
        if self.preprocessing {
            debug_assert!(self.lim.preprocessing != 0);
        }

        // Triggered in regular 'opts.conditionint' conflict intervals.
        //
        if self.lim.condition > self.stats.conflicts {
            return false;
        }

        if self.level == 0 {
            return false; // One decision necessary.
        }

        if self.level as f64 <= self.averages.current.jump.value() {
            return false; // Main heuristic.
        }

        if self.stats.current.irredundant == 0 {
            return false;
        }
        let remain = self.active_count() as f64;
        if remain == 0.0 {
            return false;
        }
        let ratio = self.stats.current.irredundant as f64 / remain;
        ratio <= self.opts.conditionmaxrat as f64
    }

    /*------------------------------------------------------------------------*/

    // We start with the current assignment and then temporarily unassign
    // literals.  They are reassigned afterwards.  The global state of the
    // CDCL solver should not change though.  Thus we copied from
    // 'search_unassign' in 'backtrack.cpp' what is needed to unassign
    // literals and then from 'search_assign' in 'propagate.cpp' what is
    // needed for reassigning literals, but restricted the copied code to
    // only updating the actual assignment (in 'vals') and not changing
    // anything else.

    // We use temporarily unassigning for two purposes.  First, if a
    // conditional literal does not occur negated in a candidate clause it is
    // unassigned.  Second, as a minor optimization, we first unassign all
    // root-level assigned (fixed) literals, to avoid checking the decision
    // level of literals during the procedure.

    pub fn condition_unassign(&mut self, lit: i32) {
        log!(self, "condition unassign {}", lit);
        debug_assert!(self.val(lit) > 0);
        self.set_val(lit, 0);
    }

    pub fn condition_assign(&mut self, lit: i32) {
        log!(self, "condition assign {}", lit);
        debug_assert!(self.val(lit) == 0);
        self.set_val(lit, 1);
    }

    /*------------------------------------------------------------------------*/

    // The current partition into conditional part and autarky part during
    // refinement is represented through a conditional bit in 'marks'.

    #[inline]
    pub fn is_conditional_literal(&self, lit: i32) -> bool {
        self.val(lit) > 0 && self.getbit(lit, 0)
    }

    #[inline]
    pub fn is_autarky_literal(&self, lit: i32) -> bool {
        self.val(lit) > 0 && !self.getbit(lit, 0)
    }

    #[inline]
    pub fn mark_as_conditional_literal(&mut self, lit: i32) {
        log!(self, "marking {} as conditional literal", lit);
        debug_assert!(self.val(lit) > 0);
        self.setbit(lit, 0);
        debug_assert!(self.is_conditional_literal(lit));
        debug_assert!(!self.is_autarky_literal(lit));
    }

    #[inline]
    pub fn unmark_as_conditional_literal(&mut self, lit: i32) {
        log!(self, "unmarking {} as conditional literal", lit);
        debug_assert!(self.is_conditional_literal(lit));
        self.unsetbit(lit, 0);
    }

    /*------------------------------------------------------------------------*/

    // We also need to know the literals which are in the current clause.
    // These are just marked (also in 'marks' but with the (signed) upper two
    // bits).  We need a signed mark here, since we have to distinguish
    // positive and negative occurrences of literals in the candidate clause.

    #[inline]
    pub fn is_in_candidate_clause(&self, lit: i32) -> bool {
        self.marked67(lit) > 0
    }

    #[inline]
    pub fn mark_in_candidate_clause(&mut self, lit: i32) {
        log!(self, "marking {} as literal of the candidate clause", lit);
        self.mark67(lit);
        debug_assert!(self.is_in_candidate_clause(lit));
        debug_assert!(!self.is_in_candidate_clause(-lit));
    }

    #[inline]
    pub fn unmark_in_candidate_clause(&mut self, lit: i32) {
        log!(self, "unmarking {} as literal of the candidate clause", lit);
        debug_assert!(self.is_in_candidate_clause(lit));
        self.unmark67(lit);
    }

    /*------------------------------------------------------------------------*/

    // This is the function for eliminating globally blocked clauses.  It is
    // triggered during CDCL search according to 'conditioning' above and
    // uses the current assignment as basis to find globally blocked clauses.

    pub fn condition_round(&mut self, delta: i64) -> i64 {
        let limit: i64;
        let mut props: i64 = 0;
        if i64::MAX - delta < self.stats.condprops {
            limit = i64::MAX;
        } else {
            limit = self.stats.condprops + delta;
        }

        let initial_trail_level = self.trail.len();
        let initial_level = self.level;

        log!(self, "initial trail level {}", initial_trail_level);

        self.protect_reasons();

        let mut additionally_assigned = 0i32;

        for idx in self.vars() {
            let tmp = self.val(idx);
            if tmp != 0 {
                if self.var(idx).level != 0 {
                    let lit = if tmp < 0 { -idx } else { idx };
                    if !self.active(idx) {
                        log!(self, "temporarily unassigning inactive literal {}", lit);
                        self.condition_unassign(lit);
                    }
                    if self.frozen(idx) {
                        log!(self, "temporarily unassigning frozen literal {}", lit);
                        self.condition_unassign(lit);
                    }
                }
            } else if self.frozen(idx) {
                log!(self, "keeping frozen literal {} unassigned", idx);
            } else if !self.active(idx) {
                log!(self, "keeping inactive literal {} unassigned", idx);
            } else {
                // if (preprocessing) {
                if initial_level == self.level {
                    self.level += 1;
                    log!(self, "new condition decision level");
                }
                let lit = self.decide_phase(idx, true);
                self.condition_assign(lit);
                let level = self.level;
                self.var_mut(idx).level = level;
                self.trail.push(lit);
                additionally_assigned += 1;
            }
        }
        log!(self, "assigned {} additional literals", additionally_assigned);

        // We compute statistics about the size of the assignments (see the
        // long comment in 'condition.cpp').
        //
        let mut initial = AssignmentSizes::default();
        let mut remain: AssignmentSizes;

        initial.assigned = 0;
        for idx in self.vars() {
            let tmp = self.val(idx);
            if tmp == 0 {
                continue;
            }
            if self.var(idx).level == 0 {
                continue;
            }
            log!(self, "initial assignment {}s", if tmp < 0 { -idx } else { idx });
            initial.assigned += 1;
        }

        phase!(
            self,
            "condition",
            self.stats.conditionings,
            "initial assignment of size {}",
            initial.assigned
        );

        // For each candidate clause we refine the assignment (monotonically),
        // by unassigning some conditional literals and turning some autarky
        // literals into conditionals.
        //
        // As the conditional part is usually smaller than the autarky part
        // our implementation only explicitly maintains the initial
        // conditional part, with conditional bit set to true through
        // 'mark_as_conditional_literal'.  The autarky part consists of all
        // literals assigned true which do not have their conditional bit set
        // to true.  Since in both cases the literal has to be assigned true,
        // we only need a single bit for both the literal as well as its
        // negation (it does not have to be 'signed').
        //
        let mut conditional: Vec<i32> = Vec::new();

        let mut candidates: Vec<CRef> = Vec::new(); // Gather candidate clauses.
        let mut watched: usize = 0; // Number of watched clauses.

        initial.autarky = initial.assigned; // Initially all are in autarky
        initial.conditional = 0; // and none in conditional part.

        // Upper bound on the number of watched clauses. In principle one
        // could use 'SIZE_MAX' but this is not available by default (yet).
        //
        let size_max = self.clauses.len() + 1;

        // Initialize additional occurrence lists.
        //
        self.init_occs();

        // Number of previously conditioned and unconditioned candidates.
        //
        let mut conditioned: usize = 0;
        let mut unconditioned: usize = 0;

        // Now go over all (non-garbage) irredundant clauses and check whether
        // they are candidates, have to be watched, or whether they force the
        // negation of some of their literals to be conditional initially.
        //
        for ci in 0..self.clauses.len() {
            let c = self.clauses[ci];
            if c.garbage() {
                continue; // Can already be ignored.
            }
            if c.redundant() {
                continue; // Ignore redundant clauses too.
            }

            // First determine the following numbers for the candidate clause
            // (restricted to non-root-level assignments).
            //
            let mut positive = 0; // Number true literals.
            let mut negative = 0; // Number false literals.
            let mut watch = 0; // True Literal to watch.
            //
            let mut minsize = size_max; // Number of occurrences of 'watch'.
            //
            // But also ignore root-level satisfied but not yet garbage
            // clauses.
            //
            let mut satisfied = false; // Root level satisfied.
            //
            let csize = c.size() as usize;
            let mut l = 0usize;
            while !satisfied && l != csize {
                let lit = c.lit(l);
                l += 1;
                let tmp = self.val(lit);
                if tmp != 0 && self.var(lit).level == 0 {
                    satisfied = tmp > 0;
                } else if tmp < 0 {
                    negative += 1;
                } else if tmp > 0 {
                    let size = self.occs(lit).len();
                    if size < minsize {
                        watch = lit;
                        minsize = size;
                    }
                    positive += 1;
                }
            }
            if satisfied {
                // Ignore root-level satisfied clauses.
                self.mark_garbage(c); // But mark them as garbage already now.
                continue; // ... with next clause 'c'.
            }

            // Candidates are clauses with at least a positive literal in it.
            //
            if positive > 0 {
                log!(self, c, "found {} positive literals in candidate", positive);
                candidates.push(c);
                if c.conditioned() {
                    conditioned += 1;
                } else {
                    unconditioned += 1;
                }
            }

            // Only one positive literal in each clauses with also at least one
            // negative literal has to be watched in occurrence lists.  These
            // watched clauses will be checked to contain only negative
            // literals as soon such a positive literal is unassigned.  If this
            // is the case these false literals have to be unassigned and
            // potentially new conditional literals have to be determined.
            //
            // Note that only conditional literals are unassigned. However it
            // does not matter that we might also watch autarky literals,
            // because either such an autarky literal remains a witness that
            // the clause is satisfied as long it remains an autarky literal.
            // Otherwise at one point it becomes conditional and is unassigned,
            // but then a replacement watch will be searched.
            //
            if negative > 0 && positive > 0 {
                log!(self, c, "found {} negative literals in candidate", negative);
                debug_assert!(watch != 0);
                debug_assert!(self.val(watch) > 0);
                debug_assert!(self.occs(watch).len() == minsize);
                self.occs_mut(watch).push(c);
                watched += 1;
                log!(self, c, "watching {} with {} occurrences in", watch, minsize);
            }

            // The initial global conditional part for the current assignment
            // is extracted from clauses with only negative literals.  It is
            // the same for all considered candidate clauses. These negative
            // literals make up the global conditional part, are marked here.
            //
            if negative > 0 && positive == 0 {
                let mut new_conditionals: usize = 0;

                for l in 0..csize {
                    let lit = c.lit(l);
                    let tmp = self.val(lit);
                    if tmp == 0 {
                        continue;
                    }
                    debug_assert!(tmp < 0);
                    if self.var(lit).level == 0 {
                        continue; // Not unassigned yet!
                    }
                    if self.is_conditional_literal(-lit) {
                        continue;
                    }
                    self.mark_as_conditional_literal(-lit);
                    conditional.push(-lit);
                    new_conditionals += 1;
                }
                if new_conditionals > 0 {
                    log!(
                        self,
                        c,
                        "marked {} negations of literals as conditional in",
                        new_conditionals
                    );
                }

                initial.conditional += new_conditionals;
                debug_assert!(initial.autarky >= new_conditionals);
                initial.autarky -= new_conditionals;
            }
        } // End of loop over all clauses to collect candidates etc.

        phase!(
            self,
            "condition",
            self.stats.conditionings,
            "found {} candidate clauses",
            candidates.len()
        );
        phase!(
            self,
            "condition",
            self.stats.conditionings,
            "watching {} literals and clauses",
            watched
        );
        phase!(
            self,
            "condition",
            self.stats.conditionings,
            "initially {} conditional literals {}%",
            initial.conditional,
            fmt_f(percent(initial.conditional as f64, initial.assigned as f64), 0)
        );
        phase!(
            self,
            "condition",
            self.stats.conditionings,
            "initially {} autarky literals {}%",
            initial.autarky,
            fmt_f(percent(initial.autarky as f64, initial.assigned as f64), 0)
        );
        #[cfg(feature = "logging")]
        {
            for i in 0..conditional.len() {
                log!(self, "initial conditional {}", conditional[i]);
                debug_assert!(self.is_conditional_literal(conditional[i]));
            }
            for i in 0..self.trail.len() {
                if self.is_autarky_literal(self.trail[i]) {
                    log!(self, "initial autarky {}", self.trail[i]);
                }
            }
        }
        debug_assert!(initial.conditional == conditional.len());
        debug_assert!(initial.assigned == initial.conditional + initial.autarky);

        self.stats.condassinit += initial.assigned as i64;
        self.stats.condcondinit += initial.conditional as i64;
        self.stats.condautinit += initial.autarky as i64;
        self.stats.condassvars += self.active_count() as i64;

        // To speed-up and particularly simplify the code we unassign all
        // root-level variables temporarily, actually all inactive assigned
        // variables.  This allows us to avoid tests on whether an assigned
        // literal is actually root-level assigned and thus should be ignored
        // (not considered to be assigned).  For this to work we have to
        // ignore root level satisfied clauses as done above.  These are
        // neither candidates nor have to be watched.  Remaining originally
        // root-level assigned literals in clauses are only set to false.
        //
        for i in 0..self.trail.len() {
            let lit = self.trail[i];
            if self.fixed(lit) != 0 {
                self.condition_unassign(lit);
            }
        }

        // Stack to save temporarily unassigned (conditional) literals.
        //
        let mut unassigned: Vec<i32> = Vec::new();

        // Make sure to focus on clauses not tried before by marking clauses
        // which have been checked before using the 'conditioned' bit of
        // clauses. If all candidates have their bit set, we have to reset it.
        // Since the assignment might be completely different then last time
        // and thus also the set of candidates this method does not really
        // exactly lead to a round robin scheme of scheduling clauses.
        //
        // TODO consider computing conditioned and unconditioned over all
        // clauses.
        //
        debug_assert!(conditioned + unconditioned == candidates.len());
        if conditioned != 0 && unconditioned != 0 {
            // 'stable_sort' with 'less_conditioned'.
            candidates.sort_by(|a, b| {
                let less_ab = !a.conditioned() && b.conditioned();
                let less_ba = !b.conditioned() && a.conditioned();
                if less_ab {
                    std::cmp::Ordering::Less
                } else if less_ba {
                    std::cmp::Ordering::Greater
                } else {
                    std::cmp::Ordering::Equal
                }
            });
            phase!(
                self,
                "condition",
                self.stats.conditionings,
                "focusing on {} candidates {}% not tried last time",
                unconditioned,
                fmt_f(percent(unconditioned as f64, candidates.len() as f64), 0)
            );
        } else if conditioned != 0 && unconditioned == 0 {
            for &c in candidates.iter() {
                debug_assert!(c.conditioned());
                c.set_conditioned(false); // Reset 'conditioned' bit.
            }
            phase!(
                self,
                "condition",
                self.stats.conditionings,
                "all {} candidates tried before",
                conditioned
            );
        } else {
            debug_assert!(conditioned == 0);
            phase!(
                self,
                "condition",
                self.stats.conditionings,
                "all {} candidates are fresh",
                unconditioned
            );
        }

        // TODO prune assignments further!
        // And thus might result in less watched clauses.
        // So watching should be done here and not earlier.
        // Also, see below, we might need to consider the negation of
        // unassigned literals in candidate clauses as being watched.

        // Now try to block all candidate clauses.
        //
        let mut blocked: i64 = 0; // Number of Successfully blocked clauses.
        //
        let mut untried: usize = candidates.len();
        for cand_idx in 0..candidates.len() {
            let c = candidates[cand_idx];

            if initial.autarky == 0 {
                break;
            }

            if c.reason() {
                continue;
            }

            let mut terminated_or_limit_hit = true;
            if self.terminated_asynchronously(1) {
                log!(self, "asynchronous termination detected");
            } else if self.stats.condprops >= limit {
                log!(self, "condition propagation limit {} hit", limit);
            } else {
                terminated_or_limit_hit = false;
            }

            if terminated_or_limit_hit {
                phase!(
                    self,
                    "condition",
                    self.stats.conditionings,
                    "{} candidates {}% not tried after {} propagations",
                    untried,
                    fmt_f(percent(untried as f64, candidates.len() as f64), 0),
                    props
                );
                break;
            }
            untried -= 1;
            debug_assert!(!c.garbage());
            debug_assert!(!c.redundant());

            log!(self, c, "candidate");
            c.set_conditioned(true); // Next time later.

            // We watch an autarky literal in the clause, and can stop trying
            // to globally block the clause as soon it turns into a
            // conditional literal and we can not find another one.  If the
            // fix-point assignment is reached and we still have an autarky
            // literal left the watched one is reported as witness for this
            // clause being globally blocked.
            //
            let mut watched_autarky_literal = 0;

            // First mark all true literals in the candidate clause and find an
            // autarky literal which witnesses that this clause has still a
            // chance to be globally blocked.
            //
            let csize = c.size() as usize;
            for l in 0..csize {
                let lit = c.lit(l);
                self.mark_in_candidate_clause(lit);
                if watched_autarky_literal != 0 {
                    continue;
                }
                if !self.is_autarky_literal(lit) {
                    continue;
                }
                watched_autarky_literal = lit;

                // TODO assign non-assigned literals to false?
                // Which might need to trigger watching additional clauses.
            }

            if watched_autarky_literal == 0 {
                log!(self, "no initial autarky literal found");
                for l in 0..csize {
                    self.unmark_in_candidate_clause(c.lit(l));
                }
                continue;
            }

            self.stats.condcands += 1; // Only now ...

            log!(self, "watching first autarky literal {}", watched_autarky_literal);

            // Save assignment sizes for statistics, logging and checking.
            //
            remain = initial;

            // Position of next conditional and unassigned literal to process
            // in the 'conditional' and the 'unassigned' stack.
            //
            let mut next_conditional: usize = 0;
            let mut next_unassigned: usize = 0;

            debug_assert!(unassigned.is_empty());
            debug_assert!(conditional.len() == initial.conditional);

            while watched_autarky_literal != 0
                && self.stats.condprops < limit
                && next_conditional < conditional.len()
            {
                debug_assert!(next_unassigned == unassigned.len());

                let conditional_lit = conditional[next_conditional];
                next_conditional += 1;
                log!(self, "processing next conditional {}", conditional_lit);
                debug_assert!(self.is_conditional_literal(conditional_lit));

                if self.is_in_candidate_clause(-conditional_lit) {
                    log!(self, "conditional {} negated in candidate clause", conditional_lit);
                    continue;
                }

                log!(
                    self,
                    "conditional {} does not occur negated in candidate clause",
                    conditional_lit
                );

                self.condition_unassign(conditional_lit);
                debug_assert!(!self.is_conditional_literal(conditional_lit));
                unassigned.push(conditional_lit);

                debug_assert!(remain.assigned > 0);
                debug_assert!(remain.conditional > 0);
                remain.conditional -= 1;
                remain.assigned -= 1;

                while watched_autarky_literal != 0
                    && self.stats.condprops < limit
                    && next_unassigned < unassigned.len()
                {
                    let unassigned_lit = unassigned[next_unassigned];
                    next_unassigned += 1;
                    log!(self, "processing next unassigned {}", unassigned_lit);
                    debug_assert!(self.val(unassigned_lit) == 0);
                    props += 1;
                    self.stats.condprops += 1;

                    let oi = self.vlit(unassigned_lit) as usize;
                    if self.otab[oi].is_empty() {
                        continue;
                    }

                    // Traverse all watched clauses of 'unassigned_lit' and
                    // find replacement watches or if none is found turn the
                    // negation of all false autarky literals in that clause
                    // into conditional literals.  If one of those autarky
                    // literals is the watched autarky literal in the candidate
                    // clause, that one has to be updated too.
                    //
                    // (Only occurrence lists of other literals are extended
                    // below, thus indices into 'otab[oi]' stay valid.)
                    //
                    let mut i = 0usize;
                    let mut j = 0usize;
                    while watched_autarky_literal != 0 && j != self.otab[oi].len() {
                        let d = self.otab[oi][j];
                        self.otab[oi][i] = d;
                        i += 1;
                        j += 1;

                        let mut replacement = 0; // New watched literal in 'd'.
                        let mut negative = 0; // Negative autarky literals in 'd'.

                        let dsize = d.size() as usize;
                        for l in 0..dsize {
                            let lit = d.lit(l);
                            let tmp = self.val(lit);
                            if tmp > 0 {
                                replacement = lit;
                            }
                            if tmp < 0 && self.is_autarky_literal(-lit) {
                                negative += 1;
                            }
                        }

                        if replacement != 0 {
                            log!(
                                self,
                                "found replacement {} for unassigned {}",
                                replacement,
                                unassigned_lit
                            );
                            log!(self, d, "unwatching {} in", unassigned_lit);
                            i -= 1; // Drop watch!
                            log!(self, d, "watching {} in", replacement);

                            debug_assert!(replacement != unassigned_lit);
                            self.occs_mut(replacement).push(d);

                            continue; // ... with next watched clause 'd'.
                        }

                        log!(self, "no replacement found for unassigned {}", unassigned_lit);

                        // Keep watching 'd' by 'unassigned_lit' if no
                        // replacement found.

                        if negative == 0 {
                            log!(self, d, "no negative autarky literals left in");
                            continue; // ... with next watched clause 'd'.
                        }

                        log!(self, d, "found {} negative autarky literals in", negative);

                        let mut l = 0usize;
                        while watched_autarky_literal != 0 && l != dsize {
                            let lit = d.lit(l);
                            l += 1;
                            if !self.is_autarky_literal(-lit) {
                                continue;
                            }
                            self.mark_as_conditional_literal(-lit);
                            conditional.push(-lit);

                            remain.conditional += 1;
                            debug_assert!(remain.autarky > 0);
                            remain.autarky -= 1;

                            if -lit != watched_autarky_literal {
                                continue;
                            }

                            log!(self, "need to replace autarky literal {} in candidate", -lit);
                            replacement = 0;

                            // TODO save starting point because we only move
                            // it forward?

                            let mut k = 0usize;
                            while replacement == 0 && k != csize {
                                let other = c.lit(k);
                                k += 1;
                                if self.is_autarky_literal(other) {
                                    replacement = other;
                                }
                            }
                            watched_autarky_literal = replacement;

                            if replacement != 0 {
                                log!(
                                    self,
                                    c,
                                    "watching autarky {} instead {} in candidate",
                                    replacement,
                                    watched_autarky_literal
                                );
                                watched_autarky_literal = replacement;
                            } else {
                                log!(self, "failed to find an autarky replacement");
                                watched_autarky_literal = 0; // Breaks out of 4 loops!!!!!
                            }
                        } // End of loop of turning autarky literals into conditionals.
                    } // End of loop of all watched clauses of an unassigned literal.
                    //
                    // We might abort the occurrence traversal early but
                    // already removed some watches, thus have to just copy the
                    // rest.
                    //
                    if i < j {
                        let os = &mut self.otab[oi];
                        while j != os.len() {
                            os[i] = os[j];
                            i += 1;
                            j += 1;
                        }
                        log!(
                            self,
                            "flushed {} occurrences of {}",
                            self.otab[oi].len() - i,
                            unassigned_lit
                        );
                        self.otab[oi].truncate(i);
                    }
                } // End of loop which goes over all unprocessed unassigned literals.
            } // End of loop which goes over all unprocessed conditional literals.

            // We are still processing the candidate 'c' and now have reached
            // a final fix-point assignment partitioned into a conditional and
            // an autarky part, or during unassigned literals figured that
            // there is no positive autarky literal left in 'c'.

            log!(self, "remaining assignment of size {}", remain.assigned);
            log!(self, "remaining conditional part of size {}", remain.conditional);
            log!(self, "remaining autarky part of size {}", remain.autarky);
            //
            debug_assert!(remain.assigned - remain.conditional == remain.autarky);
            //
            #[cfg(any(feature = "logging", debug_assertions))]
            {
                // This is a sanity check, that the size of our implicit
                // representation of the autarky part matches our 'remain'
                // counts.  We need the same code for determining autarky
                // literals as in the loop below which adds autarky literals
                // to the extension stack.
                //
                let mut check = AssignmentSizes::default();
                for i in 0..self.trail.len() {
                    let lit = self.trail[i];
                    if self.val(lit) != 0 {
                        check.assigned += 1;
                        if self.is_conditional_literal(lit) {
                            log!(self, "remaining conditional {}", lit);
                            debug_assert!(!self.is_autarky_literal(lit));
                            check.conditional += 1;
                        } else {
                            debug_assert!(self.is_autarky_literal(lit));
                            log!(self, "remaining autarky {}", lit);
                            check.autarky += 1;
                        }
                    } else {
                        debug_assert!(!self.is_autarky_literal(lit));
                        debug_assert!(!self.is_conditional_literal(lit));
                    }
                }
                debug_assert!(remain.assigned == check.assigned);
                debug_assert!(remain.conditional == check.conditional);
                debug_assert!(remain.autarky == check.autarky);
                let _ = check;
            }

            // Success if an autarky literal is left in the clause and we did
            // not abort the loop too early because the propagation limit was
            // hit.
            //
            if watched_autarky_literal != 0 && self.stats.condprops < limit {
                debug_assert!(self.is_autarky_literal(watched_autarky_literal));
                debug_assert!(self.is_in_candidate_clause(watched_autarky_literal));

                blocked += 1;
                self.stats.conditioned += 1;
                log!(
                    self,
                    c,
                    "positive autarky literal {} globally blocks",
                    watched_autarky_literal
                );

                log!(
                    self,
                    "remaining {} assigned literals {}%",
                    remain.assigned,
                    fmt_f(percent(remain.assigned as f64, initial.assigned as f64), 0)
                );
                log!(
                    self,
                    "remaining {} conditional literals {}%",
                    remain.conditional,
                    fmt_f(percent(remain.conditional as f64, remain.assigned as f64), 0)
                );
                log!(
                    self,
                    "remaining {} autarky literals {}%",
                    remain.autarky,
                    fmt_f(percent(remain.autarky as f64, remain.assigned as f64), 0)
                );

                // A satisfying assignment of a formula after removing a
                // globally blocked clause might not satisfy that clause.  As
                // for variable elimination and classical blocked clauses, we
                // thus maintain an extension stack for reconstructing an
                // assignment which both satisfies the remaining formula as
                // well as the clause.
                //
                // For globally blocked clauses we simply have to flip all
                // literals in the autarky part and thus save the autarky on
                // the extension stack in addition to the removed clause.  In
                // the classical situation (in bounded variable elimination
                // etc.) we simply save one literal on the extension stack.
                //
                // TODO find a way to shrink the autarky part or some other
                // way to avoid pushing too many literals on the extension
                // stack.
                //
                self.external().push_zero_on_extension_stack();
                for i in 0..self.trail.len() {
                    let lit = self.trail[i];
                    if self.is_autarky_literal(lit) {
                        self.external().push_witness_literal_on_extension_stack(lit);
                    }
                }
                if let Some(proof) = self.proof.as_mut() {
                    proof.weaken_minus(c);
                }
                self.external().push_clause_on_extension_stack(c);

                self.mark_garbage(c);

                self.stats.condassrem += remain.assigned as i64;
                self.stats.condcondrem += remain.conditional as i64;
                self.stats.condautrem += remain.autarky as i64;
                self.stats.condassirem += initial.assigned as i64;
            }

            // In this last part specific to one candidate clause, we have to
            // get back to the initial assignment and reset conditionals.
            // First we assign all the unassigned literals (if necessary).
            //
            if !unassigned.is_empty() {
                log!(self, "reassigning {} literals", unassigned.len());
                while let Some(lit) = unassigned.pop() {
                    self.condition_assign(lit);
                }
            }

            // Then we remove from the conditional stack autarky literals which
            // became conditional and also reset their 'conditional' bit.
            //
            if initial.conditional < conditional.len() {
                log!(
                    self,
                    "flushing {} autarky literals from conditional stack",
                    conditional.len() - initial.conditional
                );
                while initial.conditional < conditional.len() {
                    let lit = conditional.pop().unwrap();
                    self.unmark_as_conditional_literal(lit);
                }
            }

            // Finally unmark all literals in the candidate clause.
            //
            for l in 0..c.size() as usize {
                self.unmark_in_candidate_clause(c.lit(l));
            }
        } // End of loop over all candidate clauses.

        phase!(
            self,
            "condition",
            self.stats.conditionings,
            "globally blocked {} clauses {}%",
            blocked,
            fmt_f(percent(blocked as f64, candidates.len() as f64), 0)
        );

        // Unmark initial conditional variables.
        //
        for &lit in conditional.iter() {
            self.unmark_as_conditional_literal(lit);
        }

        erase_vector(&mut unassigned);
        erase_vector(&mut conditional);
        erase_vector(&mut candidates);

        // Unassign additionally assigned literals.
        //
        let mut additionally_unassigned = 0i32;
        while self.trail.len() > initial_trail_level {
            let lit = self.trail.pop().unwrap();
            self.condition_unassign(lit);
            additionally_unassigned += 1;
        }
        log!(self, "unassigned {} additionally assigned literals", additionally_unassigned);
        debug_assert!(additionally_unassigned == additionally_assigned);
        let _ = (additionally_assigned, additionally_unassigned);

        if self.level > initial_level {
            log!(self, "reset condition decision level");
            self.level = initial_level;
        }

        self.reset_occs();
        self.delete_garbage_clauses();

        // Reassign previously assigned variables again.
        //
        log!(self, "reassigning previously assigned variables");
        for i in 0..initial_trail_level {
            let lit = self.trail[i];
            let tmp = self.val(lit);
            debug_assert!(tmp >= 0);
            if tmp == 0 {
                self.condition_assign(lit);
            }
        }

        #[cfg(debug_assertions)]
        for &lit in self.trail.iter() {
            debug_assert!(self.marked(lit) == 0);
        }

        self.unprotect_reasons();

        let _ = watched;
        blocked
    }

    /// `update_limits` defaults to `true` in C++
    pub fn condition(&mut self, update_limits: bool) {
        if self.unsat {
            return;
        }
        if self.terminated_asynchronously(1) {
            return;
        }
        if self.stats.current.irredundant == 0 {
            return;
        }

        start_simplifier!(self, condition, CONDITION);
        self.stats.conditionings += 1;

        // Propagation limit to avoid too much work in 'condition'.  We mark
        // tried candidate clauses after giving up, such that next time we run
        // 'condition' we can try them.
        //
        let mut limit: i64 = self.stats.propagations.search;
        limit *= self.opts.conditioneffort as i64;
        limit /= 1000;
        if limit < self.opts.conditionmineff as i64 {
            limit = self.opts.conditionmineff as i64;
        }
        if limit > self.opts.conditionmaxeff as i64 {
            limit = self.opts.conditionmaxeff as i64;
        }
        debug_assert!(self.stats.current.irredundant != 0);
        limit = (limit as f64
            * (2.0 * self.active_count() as f64 / self.stats.current.irredundant as f64))
            as i64;
        limit = std::cmp::max(limit, 2i64 * self.active_count() as i64);

        phase!(
            self,
            "condition",
            self.stats.conditionings,
            "started after {} conflicts limited by {} propagations",
            self.stats.conflicts as u64,
            limit
        );

        let blocked = self.condition_round(limit);

        stop_simplifier!(self, condition, CONDITION);
        self.report(b'g', (blocked == 0) as i32);

        if !update_limits {
            return;
        }

        let delta: i64 = self.opts.conditionint as i64 * (self.stats.conditionings + 1);
        self.lim.condition = self.stats.conflicts + delta;

        phase!(
            self,
            "condition",
            self.stats.conditionings,
            "next limit at {} after {} conflicts",
            self.lim.condition as u64,
            delta
        );
    }
}

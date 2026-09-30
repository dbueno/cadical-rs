//! Port of `elim.hpp` and `elim.cpp`: bounded variable elimination.

use std::collections::VecDeque;

use crate::clause::CRef;
use crate::heap::{Heap, HeapLess};
use crate::internal::Internal;

/// Comparator of the elimination schedule (`elim_more`).
#[derive(Clone, Copy, Debug)]
pub struct elim_more {
    pub internal: *mut Internal,
}

impl elim_more {
    pub fn new(i: *mut Internal) -> Self {
        elim_more { internal: i }
    }
}

pub type ElimSchedule = Heap<elim_more>;

#[derive(Clone, Debug, Default)]
pub struct proof_clause {
    pub id: i64,
    pub literals: Vec<i32>,
    // for lrat
    /// Kitten id.
    pub cid: u32,
    pub learned: bool,
    pub chain: Vec<i64>,
}

/// `enum GateType`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(i32)]
pub enum GateType {
    NO = 0,
    EQUI = 1,
    AND = 2,
    ITE = 3,
    XOR = 4,
    DEF = 5,
}

pub struct Eliminator {
    pub internal: *mut Internal,
    pub schedule: ElimSchedule,
    /// `queue<Clause *> backward`.
    pub backward: VecDeque<CRef>,
    pub gates: Vec<CRef>,
    pub definition_unit: u32,
    pub proof_clauses: Vec<proof_clause>,
    pub marked: Vec<i32>,
    pub gatetype: GateType,
}

impl Eliminator {
    pub fn new(i: *mut Internal) -> Eliminator {
        Eliminator {
            internal: i,
            schedule: ElimSchedule::new(elim_more::new(i)),
            backward: VecDeque::new(),
            gates: Vec::new(),
            definition_unit: 0,
            proof_clauses: Vec::new(),
            marked: Vec::new(),
            gatetype: GateType::NO,
        }
    }
}

/*------------------------------------------------------------------------*/

// Implements a variant of bounded variable elimination as originally
// described in our SAT'05 paper introducing 'SATeLite'.  This is an
// inprocessing version, i.e., it is interleaved with search and triggers
// subsumption and strengthening, blocked and covered clause elimination
// during elimination rounds.  It focuses only those variables which
// occurred in removed irredundant clauses since the last time an
// elimination round was run.  By bounding the maximum resolvent size we can
// run each elimination round until completion.  See the code of 'elim' for
// how elimination rounds are interleaved with blocked clause elimination
// and subsumption (which in turn also calls vivification and transitive
// reduction of the binary implication graph).

#[allow(unused_imports)]
use crate::prelude::*;

use crate::format::fmt_f;
use crate::instantiate::Instantiator;
use crate::kitten::{kitten_init, kitten_release};
use crate::occs::erase_occs;

impl Internal {
    #[inline]
    pub fn compute_elim_score(&self, lit: u32) -> f64 {
        debug_assert!(1 <= lit);
        debug_assert!(lit <= self.max_var as u32);
        let pos = self.noccs(lit as i32) as f64;
        let neg = self.noccs(-(lit as i32)) as f64;
        if pos == 0.0 {
            return -neg;
        }
        if neg == 0.0 {
            return -pos;
        }
        let mut sum = 0.0;
        let mut prod = 0.0;
        if self.opts.elimsum != 0 {
            sum = self.opts.elimsum as f64 * (pos + neg);
        }
        if self.opts.elimprod != 0 {
            prod = self.opts.elimprod as f64 * (pos * neg);
        }
        prod + sum
    }

    /*--------------------------------------------------------------------*/

    // Note that the new fast subsumption algorithm implemented in 'subsume'
    // does not distinguish between irredundant and redundant clauses and is
    // also run during search to strengthen and remove 'sticky' redundant
    // clauses but also irredundant ones.  So beside learned units during
    // search or as consequence of other preprocessors, these subsumption
    // rounds during search can remove (irredundant) clauses (and literals),
    // which in turn might make new bounded variable elimination possible.
    // This is tested in the 'bool ineliminating ()' guard.

    pub fn ineliminating(&mut self) -> bool {
        if self.opts.elim == 0 {
            return false;
        }
        if !self.preprocessing && self.opts.inprocessing == 0 {
            return false;
        }
        if self.preprocessing {
            debug_assert!(self.lim.preprocessing != 0);
        }

        // Respect (increasing) conflict limit.
        //
        if self.lim.elim >= self.stats.conflicts {
            return false;
        }

        // Wait until there are new units or new removed variables
        // (in removed or shrunken irredundant clauses and thus marked).
        //
        if self.last.elim.fixed < self.stats.all.fixed {
            return true;
        }
        if self.last.elim.marked < self.stats.mark.elim {
            return true;
        }

        // VERBOSE (3, "elim not scheduled due to fixpoint");
        false
    }

    /*--------------------------------------------------------------------*/

    // Update the global elimination schedule after adding or removing a
    // clause.

    pub fn elim_update_added_clause(&mut self, eliminator: &mut Eliminator, c: CRef) {
        debug_assert!(!c.redundant());
        for &lit in c.lits() {
            if !self.active(lit) {
                continue;
            }
            self.occs_mut(lit).push(c);
            if self.frozen(lit) {
                continue;
            }
            *self.noccs_mut(lit) += 1;
            let idx = lit.abs() as u32;
            if eliminator.schedule.contains(idx) {
                eliminator.schedule.update(idx);
            }
        }
    }

    pub fn elim_update_removed_lit(&mut self, eliminator: &mut Eliminator, lit: i32) {
        if !self.active(lit) {
            return;
        }
        if self.frozen(lit) {
            return;
        }
        {
            let score = self.noccs_mut(lit);
            debug_assert!(*score > 0);
            *score -= 1;
        }
        let idx = lit.abs() as u32;
        let schedule = &mut eliminator.schedule;
        if schedule.contains(idx) {
            schedule.update(idx);
        } else {
            log!(self, "rescheduling {} for elimination after removing clause", idx);
            schedule.push_back(idx);
        }
    }

    /// `except` defaults to `0` in C++
    pub fn elim_update_removed_clause(&mut self, eliminator: &mut Eliminator, c: CRef, except: i32) {
        debug_assert!(!c.redundant());
        for &lit in c.lits() {
            if lit == except {
                continue;
            }
            debug_assert!(lit != -except);
            self.elim_update_removed_lit(eliminator, lit);
        }
    }

    /*--------------------------------------------------------------------*/

    // Since we do not have watches we have to do our own unit propagation
    // during elimination as soon we find a unit clause.  This finds new
    // units and also marks clauses satisfied by those units as garbage
    // immediately.

    pub fn elim_propagate(&mut self, eliminator: &mut Eliminator, root: i32) {
        debug_assert!(self.val(root) > 0);
        let mut work: Vec<i32> = Vec::new();
        let mut i = 0usize;
        work.push(root);
        while i < work.len() {
            let lit = work[i];
            i += 1;
            log!(self, "elimination propagation of {}", lit);
            debug_assert!(self.val(lit) > 0);
            let ns_size = self.occs(-lit).len();
            for k in 0..ns_size {
                let c = self.occs(-lit)[k];
                if c.garbage() {
                    continue;
                }
                let mut unit = 0;
                let mut satisfied = 0;
                for &other in c.lits() {
                    let tmp = self.val(other);
                    if tmp < 0 {
                        continue;
                    }
                    if tmp > 0 {
                        satisfied = other;
                        break;
                    }
                    if unit != 0 {
                        unit = i32::MIN;
                    } else {
                        unit = other;
                    }
                }
                if satisfied != 0 {
                    log!(self, c, "elimination propagation of {} finds {} satisfied", lit, satisfied);
                    self.elim_update_removed_clause(eliminator, c, satisfied);
                    self.mark_garbage(c);
                } else if unit == 0 {
                    log!(self, "empty clause during elimination propagation of {}", lit);
                    // need to set conflict = c for lrat
                    self.conflict = c;
                    self.learn_empty_clause();
                    self.conflict = CRef::NULL;
                    break;
                } else if unit != i32::MIN {
                    log!(self, "new unit {} during elimination propagation of {}", unit, lit);
                    self.build_chain_for_units(unit, c, false);
                    self.assign_unit(unit);
                    work.push(unit);
                }
            }
            if self.unsat {
                break;
            }
            let ps_size = self.occs(lit).len();
            for k in 0..ps_size {
                let c = self.occs(lit)[k];
                if c.garbage() {
                    continue;
                }
                log!(self, c, "elimination propagation of {} produces satisfied", lit);
                self.elim_update_removed_clause(eliminator, c, lit);
                self.mark_garbage(c);
            }
        }
    }

    /*--------------------------------------------------------------------*/

    // On-the-fly self-subsuming resolution during variable elimination is
    // due to HyoJung Han, Fabio Somenzi, SAT'09.  Basically while resolving
    // two clauses we test the resolvent to be smaller than one of the
    // antecedents.  If this is the case the pivot can be removed from the
    // antecedent on-the-fly and the resolution can be skipped during
    // elimination.

    pub fn elim_on_the_fly_self_subsumption(&mut self, eliminator: &mut Eliminator, c: CRef, pivot: i32) {
        log!(self, c, "pivot {} on-the-fly self-subsuming resolution", pivot);
        self.stats.elimotfstr += 1;
        self.stats.strengthened += 1;
        debug_assert!(self.clause.is_empty());
        for &lit in c.lits() {
            if lit == pivot {
                continue;
            }
            let tmp = self.val(lit);
            debug_assert!(tmp <= 0);
            if tmp < 0 {
                continue;
            }
            self.clause.push(lit);
        }
        let r = self.new_resolved_irredundant_clause();
        self.elim_update_added_clause(eliminator, r);
        self.clause.clear();
        self.lrat_chain.clear();
        self.elim_update_removed_clause(eliminator, c, pivot);
        self.mark_garbage(c);
    }

    /*--------------------------------------------------------------------*/

    // Resolve two clauses on the pivot literal 'pivot', which is assumed to
    // occur in opposite phases in 'c' and 'd'.  The actual resolvent is
    // stored in the temporary global 'clause' if it is not redundant.  It is
    // considered redundant if one of the clauses is already marked as
    // garbage it is root level satisfied, the resolvent is empty, a unit, or
    // produces a self-subsuming resolution, which results in the pivot to be
    // removed from at least one of the antecedents.

    // Note that current root level assignments are taken into account,
    // i.e., by removing root level falsified literals.  The function
    // returns true if the resolvent is not redundant and for instance has
    // to be taken into account during bounded variable elimination.

    // Detected units are immediately assigned and in case the last argument
    // is true also propagated eagerly in a elimination specific propagation
    // routine, which not only finds units but also updates the schedule.

    // When this function is called during computation of the number of
    // non-trivial (or non-satisfied) resolvents we can eagerly propagate
    // units.  But during actually adding the resolvents this results in
    // problems as we found one rare test case '../test/trace/reg0056.trace'
    // (out of billions), where the pivot itself was assigned during such a
    // propagation while adding resolvents and lead to pushing a clause to
    // the reconstruction stack that later flipped the value of the pivot
    // (while all other literals in that clause were unit implied too).  Not
    // pushing the pivot clauses to the reconstruction stack produced a wrong
    // model too.  Our fix is to only eagerly propagate during computation
    // of the number of resolvents and otherwise delay propagation until the
    // end of elimination (which is less precise regarding scheduling but
    // very rarely happens).

    pub fn resolve_clauses(
        &mut self,
        eliminator: &mut Eliminator,
        c: CRef,
        pivot: i32,
        d: CRef,
        propagate_eagerly: bool,
    ) -> bool {
        let mut c = c;
        let mut d = d;
        let mut pivot = pivot;

        debug_assert!(!c.redundant());
        debug_assert!(!d.redundant());

        self.stats.elimres += 1;

        if c.garbage() || d.garbage() {
            return false;
        }
        if c.size() > d.size() {
            pivot = -pivot;
            std::mem::swap(&mut c, &mut d);
        }

        debug_assert!(self.level == 0);
        debug_assert!(self.clause.is_empty());

        let mut satisfied = 0; // Contains this satisfying literal.
        let mut tautological = 0; // Clashing literal if tautological.

        let mut s: i32 = 0; // Actual literals from 'c'.
        let mut t: i32 = 0; // Actual literals from 'd'.

        // First determine whether the first antecedent is satisfied, add its
        // literals to 'clause' and mark them (except for 'pivot').
        //
        for &lit in c.lits() {
            if lit == pivot {
                s += 1;
                continue;
            }
            debug_assert!(lit != -pivot);
            let tmp = self.val(lit);
            if tmp > 0 {
                satisfied = lit;
                break;
            } else if tmp < 0 {
                if !self.lrat {
                    continue;
                }
                if self.flags(lit).seen {
                    continue;
                }
                self.analyzed.push(lit);
                self.flags_mut(lit).seen = true;
                let id = self.unit_id(-lit);
                self.lrat_chain.push(id);
                continue;
            } else {
                self.mark(lit);
                self.clause.push(lit);
                s += 1;
            }
        }
        if satisfied != 0 {
            log!(self, c, "satisfied by {} antecedent", satisfied);
            self.elim_update_removed_clause(eliminator, c, satisfied);
            self.mark_garbage(c);
            self.clause.clear();
            self.lrat_chain.clear();
            self.clear_analyzed_literals();
            self.unmark_clause_literals(c);
            return false;
        }

        // Then determine whether the second antecedent is satisfied, add its
        // literal to 'clause' and check whether a clashing literal is found,
        // such that the resolvent would be tautological.
        //
        for &lit in d.lits() {
            if lit == -pivot {
                t += 1;
                continue;
            }
            debug_assert!(lit != pivot);
            let mut tmp = self.val(lit);
            if tmp > 0 {
                satisfied = lit;
                break;
            } else if tmp < 0 {
                if !self.lrat {
                    continue;
                }
                if self.flags(lit).seen {
                    continue;
                }
                self.analyzed.push(lit);
                self.flags_mut(lit).seen = true;
                let id = self.unit_id(-lit);
                self.lrat_chain.push(id);
                continue;
            } else {
                tmp = self.marked(lit);
                if tmp < 0 {
                    tautological = lit;
                    break;
                } else if tmp == 0 {
                    self.clause.push(lit);
                    t += 1;
                } else {
                    debug_assert!(tmp > 0);
                    t += 1;
                }
            }
        }

        self.clear_analyzed_literals();
        self.unmark_clause_literals(c);
        let size = self.clause.len() as i64;

        if self.lrat {
            self.lrat_chain.push(d.id());
            self.lrat_chain.push(c.id());
        }

        if satisfied != 0 {
            log!(self, d, "satisfied by {} antecedent", satisfied);
            self.elim_update_removed_clause(eliminator, d, satisfied);
            self.mark_garbage(d);
            self.clause.clear();
            self.lrat_chain.clear();
            return false;
        }

        log!(self, c, "first antecedent");
        log!(self, d, "second antecedent");

        if tautological != 0 {
            self.clause.clear();
            log!(self, "resolvent tautological on {}", tautological);
            self.lrat_chain.clear();
            return false;
        }

        if size == 0 {
            self.clause.clear();
            log!(self, "empty resolvent");
            self.learn_empty_clause(); // already clears lrat_chain.
            return false;
        }

        if size == 1 {
            let unit = self.clause[0];
            log!(self, "unit resolvent {}", unit);
            self.clause.clear();
            self.assign_unit(unit); // already clears lrat_chain.
            if propagate_eagerly {
                self.elim_propagate(eliminator, unit);
            }
            return false;
        }

        log!(self, &self.clause, "resolvent");
        debug_assert!(!self.lrat || !self.lrat_chain.is_empty());

        // Double self-subsuming resolution.  The clauses 'c' and 'd' are
        // identical except for the pivot which occurs in different phase.
        // The resolvent subsumes both antecedents.

        if s as i64 > size && t as i64 > size {
            debug_assert!(s as i64 == size + 1);
            debug_assert!(t as i64 == size + 1);
            self.clause.clear();
            // LRAT is c + d (+ eventual units)
            self.elim_on_the_fly_self_subsumption(eliminator, c, pivot);
            log!(self, d, "double pivot {} on-the-fly self-subsuming resolution", -pivot);
            self.stats.elimotfsub += 1;
            self.stats.subsumed += 1;
            self.elim_update_removed_clause(eliminator, d, -pivot);
            self.mark_garbage(d);
            return false;
        }

        // Single self-subsuming resolution:  The pivot can be removed from
        // 'c', which is implemented by adding a clause which is the same as
        // 'c' but with 'pivot' removed and then marking 'c' as garbage.

        if s as i64 > size {
            debug_assert!(s as i64 == size + 1);
            self.clause.clear();
            // LRAT is c + d (+ eventual units)
            self.elim_on_the_fly_self_subsumption(eliminator, c, pivot);
            return false;
        }

        // Same single self-subsuming resolution situation, but only for 'd'.

        if t as i64 > size {
            debug_assert!(t as i64 == size + 1);
            self.clause.clear();
            // LRAT is c + d (+ eventual units) -> same.
            self.elim_on_the_fly_self_subsumption(eliminator, d, -pivot);
            return false;
        }
        if propagate_eagerly {
            self.lrat_chain.clear();
        }
        true
    }

    /*--------------------------------------------------------------------*/

    // Check whether the number of non-tautological resolvents on 'pivot' is
    // smaller or equal to the number of clauses with 'pivot' or '-pivot'.
    // This is the main criteria of bounded variable elimination.  As a side
    // effect it flushes garbage clauses with that variable, sorts its
    // occurrence lists (smallest clauses first) and also negates pivot if
    // it has more positive than negative occurrences.

    pub fn elim_resolvents_are_bounded(&mut self, eliminator: &mut Eliminator, pivot: i32) -> bool {
        let substitute = !eliminator.gates.is_empty();
        let resolve_gates = eliminator.definition_unit != 0;
        if substitute {
            log!(self, "trying to substitute {}", pivot);
        }

        self.stats.elimtried += 1;

        debug_assert!(!self.unsat);
        debug_assert!(self.active(pivot));

        let pos = self.occs(pivot).len() as i64;
        let neg = self.occs(-pivot).len() as i64;
        if pos == 0 || neg == 0 {
            return self.lim.elimbound >= 0;
        }
        let bound = pos + neg + self.lim.elimbound;

        log!(
            self,
            "checking number resolvents on {} bounded by {} = {} + {} + {}",
            pivot,
            bound,
            pos,
            neg,
            self.lim.elimbound
        );

        // Try all resolutions between a positive occurrence (outer loop) of
        // 'pivot' and a negative occurrence of 'pivot' (inner loop) as long
        // the bound on non-tautological resolvents is not hit and the size
        // of the generated resolvents does not exceed the resolvent clause
        // size limit.

        let mut resolvents: i64 = 0; // Non-tautological resolvents.

        let ps_size = self.occs(pivot).len();
        for i in 0..ps_size {
            let c = self.occs(pivot)[i];
            debug_assert!(!c.redundant());
            if c.garbage() {
                continue;
            }
            let ns_size = self.occs(-pivot).len();
            for j in 0..ns_size {
                let d = self.occs(-pivot)[j];
                debug_assert!(!d.redundant());
                if d.garbage() {
                    continue;
                }
                if !resolve_gates && substitute && c.gate() == d.gate() {
                    continue;
                }
                self.stats.elimrestried += 1;
                if self.resolve_clauses(eliminator, c, pivot, d, true) {
                    resolvents += 1;
                    let size = self.clause.len() as i32;
                    self.clause.clear();
                    log!(self, "now at least {} non-tautological resolvents on pivot {}", resolvents, pivot);
                    if size > self.opts.elimclslim {
                        log!(self, "resolvent size {} too big after {} resolvents on {}", size, resolvents, pivot);
                        return false;
                    }
                    if resolvents > bound {
                        log!(self, "too many non-tautological resolvents on {}", pivot);
                        return false;
                    }
                } else if self.unsat {
                    return false;
                } else if self.val(pivot) != 0 {
                    return false;
                }
            }
        }

        log!(self, "need {} <= {} non-tautological resolvents", resolvents, bound);

        true
    }

    /*--------------------------------------------------------------------*/
    // Add all resolvents on 'pivot' and connect them.

    #[inline]
    pub fn elim_add_resolvents(&mut self, eliminator: &mut Eliminator, pivot: i32) {
        let substitute = !eliminator.gates.is_empty();
        let resolve_gates = eliminator.definition_unit != 0;
        if substitute {
            log!(
                self,
                "substituting pivot {} by resolving with {} gate clauses",
                pivot,
                eliminator.gates.len()
            );
            self.stats.elimsubst += 1;
        }
        match eliminator.gatetype {
            GateType::EQUI => self.stats.eliminated_equi += 1,
            GateType::AND => self.stats.eliminated_and += 1,
            GateType::ITE => self.stats.eliminated_ite += 1,
            GateType::XOR => self.stats.eliminated_xor += 1,
            GateType::DEF => self.stats.eliminated_def += 1,
            GateType::NO => {}
        }

        log!(self, "adding all resolvents on {}", pivot);

        debug_assert!(self.val(pivot) == 0);
        debug_assert!(!self.flags(pivot).eliminated());

        #[cfg(feature = "logging")]
        let mut resolvents: i64 = 0;
        let ps_size = self.occs(pivot).len();
        for i in 0..ps_size {
            let c = self.occs(pivot)[i];
            if self.unsat {
                break;
            }
            if c.garbage() {
                continue;
            }
            let ns_size = self.occs(-pivot).len();
            for j in 0..ns_size {
                let d = self.occs(-pivot)[j];
                if self.unsat {
                    break;
                }
                if d.garbage() {
                    continue;
                }
                if !resolve_gates && substitute && c.gate() == d.gate() {
                    continue;
                }
                if !self.resolve_clauses(eliminator, c, pivot, d, false) {
                    continue;
                }
                debug_assert!(!self.lrat || !self.lrat_chain.is_empty());
                let r = self.new_resolved_irredundant_clause();
                self.elim_update_added_clause(eliminator, r);
                eliminator.enqueue(r);
                self.lrat_chain.clear();
                self.clause.clear();
                #[cfg(feature = "logging")]
                {
                    resolvents += 1;
                }
            }
        }

        log!(self, "added {} resolvents to eliminate {}", resolvents, pivot);
    }

    /*--------------------------------------------------------------------*/

    // Remove clauses with 'pivot' and '-pivot' by marking them as garbage
    // and push them on the extension stack.

    pub fn mark_eliminated_clauses_as_garbage(
        &mut self,
        eliminator: &mut Eliminator,
        pivot: i32,
        deleted_binary_clause: &mut bool,
    ) {
        debug_assert!(!self.unsat);

        log!(self, "marking irredundant clauses with {} as garbage", pivot);

        let substitute = eliminator.gates.len() as i64;
        if substitute != 0 {
            log!(self, "pushing {} gate clauses on extension stack", substitute);
        }
        #[cfg(debug_assertions)]
        let mut pushed: i64 = 0;
        let ps_size = self.occs(pivot).len();
        for i in 0..ps_size {
            let c = self.occs(pivot)[i];
            if c.garbage() {
                continue;
            }
            debug_assert!(!c.redundant());
            if substitute == 0 || c.gate() {
                if let Some(proof) = self.proof.as_mut() {
                    proof.weaken_minus(c);
                }
                if c.size() == 2 {
                    *deleted_binary_clause = true;
                }
                self.external().push_clause_on_extension_stack_with_witness(c, pivot);
                #[cfg(debug_assertions)]
                {
                    pushed += 1;
                }
            }
            self.mark_garbage(c);
            self.elim_update_removed_clause(eliminator, c, pivot);
        }
        erase_occs(self.occs_mut(pivot));

        log!(self, "marking irredundant clauses with {} as garbage", -pivot);

        let ns_size = self.occs(-pivot).len();
        for i in 0..ns_size {
            let d = self.occs(-pivot)[i];
            if d.garbage() {
                continue;
            }
            debug_assert!(!d.redundant());
            if substitute == 0 || d.gate() {
                if let Some(proof) = self.proof.as_mut() {
                    proof.weaken_minus(d);
                }
                if d.size() == 2 {
                    *deleted_binary_clause = true;
                }
                self.external().push_clause_on_extension_stack_with_witness(d, -pivot);
                #[cfg(debug_assertions)]
                {
                    pushed += 1;
                }
            }
            self.mark_garbage(d);
            self.elim_update_removed_clause(eliminator, d, -pivot);
        }
        erase_occs(self.occs_mut(-pivot));

        #[cfg(debug_assertions)]
        if substitute != 0 {
            debug_assert!(pushed <= substitute);
        }

        // Unfortunately, we can not use the trick by Niklas Soerensson
        // anymore, which avoids saving all clauses on the extension stack.
        // This would break our new incremental 'restore' logic.
    }

    /*--------------------------------------------------------------------*/

    // Try to eliminate 'pivot' by bounded variable elimination.
    pub fn try_to_eliminate_variable(
        &mut self,
        eliminator: &mut Eliminator,
        pivot: i32,
        deleted_binary_clause: &mut bool,
    ) {
        let mut pivot = pivot;
        if !self.active(pivot) {
            return;
        }
        debug_assert!(!self.frozen(pivot));

        // First flush garbage clauses.
        //
        let mut pos = self.flush_occs(pivot) as i64;
        let mut neg = self.flush_occs(-pivot) as i64;

        if pos > neg {
            pivot = -pivot;
            std::mem::swap(&mut pos, &mut neg);
        }
        log!(self, "pivot {} occurs positively {} times and negatively {} times", pivot, pos, neg);
        debug_assert!(!eliminator.schedule.contains(pivot.unsigned_abs()));
        debug_assert!(pos <= neg);

        if pos != 0 && neg > self.opts.elimocclim as i64 {
            log!(self, "too many occurrences thus not eliminated {}", pivot);
            debug_assert!(!eliminator.schedule.contains(pivot.unsigned_abs()));
            return;
        }

        log!(self, "trying to eliminate {}", pivot);
        debug_assert!(!self.flags(pivot).eliminated());

        // Sort occurrence lists, such that shorter clauses come first.
        self.occs_mut(pivot).sort_by_key(|c| c.size());
        self.occs_mut(-pivot).sort_by_key(|c| c.size());

        if pos != 0 {
            self.find_gate_clauses(eliminator, pivot);
        }

        if !self.unsat && self.val(pivot) == 0 {
            if self.elim_resolvents_are_bounded(eliminator, pivot) {
                log!(self, "number of resolvents on {} are bounded", pivot);
                self.elim_add_resolvents(eliminator, pivot);
                if !self.unsat {
                    self.mark_eliminated_clauses_as_garbage(eliminator, pivot, deleted_binary_clause);
                }
                if self.active(pivot) {
                    self.mark_eliminated(pivot);
                }
            } else {
                log!(self, "too many resolvents on {} so not eliminated", pivot);
            }
        }

        self.unmark_gate_clauses(eliminator);
        self.elim_backward_clauses(eliminator);
    }

    /*--------------------------------------------------------------------*/

    pub fn mark_redundant_clauses_with_eliminated_variables_as_garbage(&mut self) {
        for k in 0..self.clauses.len() {
            let c = self.clauses[k];
            if c.garbage() || !c.redundant() {
                continue;
            }
            let mut clean = true;
            for &lit in c.lits() {
                let f = self.flags(lit);
                if f.eliminated() {
                    clean = false;
                    break;
                }
                if f.pure() {
                    clean = false;
                    break;
                }
            }
            if !clean {
                self.mark_garbage(c);
            }
        }
    }

    /*--------------------------------------------------------------------*/

    // This function performs one round of bounded variable elimination and
    // returns the number of eliminated variables. The additional result
    // 'completed' is true if this elimination round ran to completion (all
    // variables have been tried).  Otherwise it was asynchronously
    // terminated or the resolution limit was hit.

    pub fn elim_round(&mut self, completed: &mut bool, deleted_binary_clause: &mut bool) -> i32 {
        debug_assert!(self.opts.elim != 0);
        debug_assert!(!self.unsat);

        start_simplifier!(self, elim, ELIM);
        self.stats.elimrounds += 1;

        let marked_before = self.last.elim.marked;
        self.last.elim.marked = self.stats.mark.elim;
        debug_assert!(self.level == 0);

        let resolution_limit: i64;

        if self.opts.elimlimited != 0 {
            let mut delta: i64 = self.stats.propagations.search;
            delta = (delta as f64 * (1e-3 * self.opts.elimeffort as f64)) as i64;
            if delta < self.opts.elimmineff as i64 {
                delta = self.opts.elimmineff as i64;
            }
            if delta > self.opts.elimmaxeff as i64 {
                delta = self.opts.elimmaxeff as i64;
            }
            delta = std::cmp::max(delta, 2i64 * self.active_count() as i64);

            phase!(self, "elim-round", self.stats.elimrounds, "limit of {} resolutions", delta);

            resolution_limit = self.stats.elimres + delta;
        } else {
            phase!(self, "elim-round", self.stats.elimrounds, "resolutions unlimited");
            resolution_limit = i64::MAX;
        }

        self.init_noccs();

        // First compute the number of occurrences of each literal and at the
        // same time mark satisfied clauses and update 'elim' flags of
        // variables in clauses with root level assigned literals (both false
        // and true).
        //
        for k in 0..self.clauses.len() {
            let c = self.clauses[k];
            if c.garbage() || c.redundant() {
                continue;
            }
            let mut satisfied = false;
            let mut falsified = false;
            for &lit in c.lits() {
                let tmp = self.val(lit);
                if tmp > 0 {
                    satisfied = true;
                } else if tmp < 0 {
                    falsified = true;
                } else {
                    debug_assert!(self.active(lit));
                }
            }
            if satisfied {
                self.mark_garbage(c); // forces more precise counts
            } else {
                for &lit in c.lits() {
                    if !self.active(lit) {
                        continue;
                    }
                    if falsified {
                        self.mark_elim(lit); // simulate unit propagation
                    }
                    *self.noccs_mut(lit) += 1;
                }
            }
        }

        self.init_occs();

        let mut eliminator = Eliminator::new(self as *mut Internal);
        debug_assert!(eliminator.schedule.empty());

        // Now find elimination candidates which occurred in clauses removed
        // since the last time we ran bounded variable elimination, which in
        // turned triggered their 'elim' bit to be set.
        //
        for idx in self.vars() {
            if !self.active(idx) {
                continue;
            }
            if self.frozen(idx) {
                continue;
            }
            if !self.flags(idx).elim {
                continue;
            }
            log!(self, "scheduling {} for elimination initially", idx);
            eliminator.schedule.push_back(idx as u32);
        }

        eliminator.schedule.shrink();

        let scheduled = eliminator.schedule.size() as i64;

        phase!(
            self,
            "elim-round",
            self.stats.elimrounds,
            "scheduled {} variables {}% for elimination",
            scheduled,
            fmt_f(percent(scheduled as f64, self.active_count() as f64), 0)
        );

        // Connect irredundant clauses.
        //
        for k in 0..self.clauses.len() {
            if self.terminated_asynchronously(1) {
                break;
            }
            let c = self.clauses[k];
            if !c.garbage() && !c.redundant() {
                for &lit in c.lits() {
                    if self.active(lit) {
                        self.occs_mut(lit).push(c);
                    }
                }
            }
        }

        let old_resolutions = self.stats.elimres;
        let old_eliminated = self.stats.all.eliminated as i32;
        let old_fixed = self.stats.all.fixed as i32;

        // Limit on garbage literals during variable elimination. If the
        // limit is hit a garbage collection is performed.
        //
        let garbage_limit: i64 = (2 * self.stats.irrlits / 3) + (1 << 20);

        // Main loops tries to eliminate variables according to the schedule.
        // The schedule is updated dynamically and variables are potentially
        // rescheduled to be tried again if they occur in a removed clause.
        //
        let mut tried: i64 = 0;
        while !self.unsat
            && !self.terminated_asynchronously(1)
            && self.stats.elimres <= resolution_limit
            && !eliminator.schedule.empty()
        {
            let idx = eliminator.schedule.front() as i32;
            eliminator.schedule.pop_front();
            self.flags_mut(idx).elim = false;
            self.try_to_eliminate_variable(&mut eliminator, idx, deleted_binary_clause);
            tried += 1;
            if self.stats.garbage.literals <= garbage_limit {
                continue;
            }
            self.mark_redundant_clauses_with_eliminated_variables_as_garbage();
            self.garbage_collection();
        }

        // If the schedule is empty all variables have been tried (even
        // rescheduled ones).  Otherwise asynchronous termination happened or
        // we ran into the resolution limit (or derived unsatisfiability).
        //
        *completed = eliminator.schedule.size() == 0;

        if !*completed {
            self.last.elim.marked = marked_before;
        }

        phase!(
            self,
            "elim-round",
            self.stats.elimrounds,
            "tried to eliminate {} variables {}% ({} remain)",
            tried,
            fmt_f(percent(tried as f64, scheduled as f64), 0),
            eliminator.schedule.size()
        );

        eliminator.schedule.erase();

        // Collect potential literal clause instantiation pairs, which needs
        // full occurrence lists and thus we have it here before resetting
        // them.
        //
        let mut instantiator = Instantiator::new();
        if !self.unsat && !self.terminated_asynchronously(1) && self.opts.instantiate != 0 {
            self.collect_instantiation_candidates(&mut instantiator);
        }

        self.reset_occs();
        self.reset_noccs();

        // Mark all redundant clauses with eliminated variables as garbage.
        //
        if !self.unsat {
            self.mark_redundant_clauses_with_eliminated_variables_as_garbage();
        }

        let eliminated = self.stats.all.eliminated as i32 - old_eliminated;
        let resolutions = self.stats.elimres - old_resolutions;
        phase!(
            self,
            "elim-round",
            self.stats.elimrounds,
            "eliminated {} variables {}% in {} resolutions",
            eliminated,
            fmt_f(percent(eliminated as f64, scheduled as f64), 0),
            resolutions
        );

        self.last.elim.subsumephases = self.stats.subsumephases;
        let units = self.stats.all.fixed as i32 - old_fixed;
        let quiet = self.opts.reportall == 0 && (eliminated + units) == 0;
        self.report(b'e', quiet as i32);
        stop_simplifier!(self, elim, ELIM);

        if !self.unsat && !self.terminated_asynchronously(1) && instantiator.has_candidates() {
            // Do we have candidate pairs?
            self.instantiate(&mut instantiator);
        }

        drop(eliminator);

        eliminated // non-zero if successful
    }

    /*--------------------------------------------------------------------*/

    // Increase elimination bound (additional clauses allowed during
    // variable elimination), which is triggered if elimination with last
    // bound completed (including no new subsumptions).  This was pioneered
    // by GlueMiniSAT in the SAT Race 2015 and then picked up Chanseok Oh in
    // his COMinisatPS solver, which in turn is used in the Maple series of
    // SAT solvers.  The bound is no increased if the maximum bound is
    // reached.

    pub fn increase_elimination_bound(&mut self) {
        if self.lim.elimbound >= self.opts.elimboundmax as i64 {
            return;
        }

        if self.lim.elimbound < 0 {
            self.lim.elimbound = 0;
        } else if self.lim.elimbound == 0 {
            self.lim.elimbound = 1;
        } else {
            self.lim.elimbound *= 2;
        }

        if self.lim.elimbound > self.opts.elimboundmax as i64 {
            self.lim.elimbound = self.opts.elimboundmax as i64;
        }

        phase!(self, "elim-phase", self.stats.elimphases, "new elimination bound {}", self.lim.elimbound);

        // Now reschedule all active variables for elimination again.
        //
        #[cfg(feature = "logging")]
        let mut count = 0;
        for idx in self.vars() {
            if !self.active(idx) {
                continue;
            }
            if self.flags(idx).elim {
                continue;
            }
            self.mark_elim(idx);
            #[cfg(feature = "logging")]
            {
                count += 1;
            }
        }
        log!(self, "marked {} variables as elimination candidates", count);

        self.report(b'^', 0);
    }

    pub fn init_citten(&mut self) {
        if self.opts.elimdef == 0 {
            return;
        }
        debug_assert!(self.citten.is_none());
        self.citten = Some(kitten_init());
    }

    pub fn reset_citten(&mut self) {
        if let Some(citten) = self.citten.take() {
            kitten_release(citten);
        }
    }

    /*--------------------------------------------------------------------*/

    /// `update_limits` defaults to `true` in C++
    pub fn elim(&mut self, update_limits: bool) {
        if self.unsat {
            return;
        }
        if self.terminated_asynchronously(1) {
            return;
        }
        if self.level != 0 {
            self.backtrack(0);
        }
        if !self.propagate() {
            self.learn_empty_clause();
            return;
        }

        self.stats.elimphases += 1;
        phase!(
            self,
            "elim-phase",
            self.stats.elimphases,
            "starting at most {} elimination rounds",
            self.opts.elimrounds
        );

        if self.external_prop {
            debug_assert!(self.level == 0);
            self.private_steps = true;
        }

        let old_active_variables = self.active_count();
        let old_eliminated = self.stats.all.eliminated as i32;

        // Make sure there was a complete subsumption phase since last
        // elimination
        //
        if self.last.elim.subsumephases == self.stats.subsumephases {
            self.subsume();
        }

        self.reset_watches(); // saves lots of memory

        self.init_citten();

        // Alternate one round of bounded variable elimination ('elim_round')
        // and subsumption ('subsume_round'), blocked ('block') and covered
        // clause elimination ('cover') until nothing changes, or the round
        // limit is hit.  The loop also aborts early if no variable could be
        // eliminated, the empty clause is resolved, it is asynchronously
        // terminated or a resolution limit is hit.

        // This variable determines whether the whole loop of this bounded
        // variable elimination phase ('elim') ran until completion.  This
        // potentially triggers an incremental increase of the elimination
        // bound.
        //
        let mut phase_complete = false;
        let mut deleted_binary_clause = false;

        let mut round = 1;

        let mut round_complete = false;
        while !self.unsat && !phase_complete && !self.terminated_asynchronously(1) {
            let eliminated = self.elim_round(&mut round_complete, &mut deleted_binary_clause);

            if !round_complete {
                phase!(
                    self,
                    "elim-phase",
                    self.stats.elimphases,
                    "last round {} incomplete {}",
                    round,
                    if eliminated != 0 { "but successful" } else { "and unsuccessful" }
                );
                debug_assert!(!phase_complete);
                break;
            }

            let r = round;
            round += 1;
            if r >= self.opts.elimrounds {
                phase!(
                    self,
                    "elim-phase",
                    self.stats.elimphases,
                    "round limit {} hit ({})",
                    round - 1,
                    if eliminated != 0 {
                        "though last round successful"
                    } else {
                        "last round unsuccessful anyhow"
                    }
                );
                debug_assert!(!phase_complete);
                break;
            }

            // Prioritize 'subsumption' over blocked and covered clause
            // elimination.

            if self.subsume_round() {
                continue;
            }
            if self.block() {
                continue;
            }
            if self.cover() {
                continue;
            }

            // Was not able to generate new variable elimination candidates
            // after variable elimination round, neither through subsumption,
            // nor blocked, nor covered clause elimination.
            //
            phase!(self, "elim-phase", self.stats.elimphases, "no new variable elimination candidates");

            debug_assert!(round_complete);
            phase_complete = true;
        }

        if phase_complete {
            self.stats.elimcompleted += 1;
            phase!(
                self,
                "elim-phase",
                self.stats.elimphases,
                "fully completed elimination {} at elimination bound {}",
                self.stats.elimcompleted,
                self.lim.elimbound
            );
        } else {
            phase!(
                self,
                "elim-phase",
                self.stats.elimphases,
                "incomplete elimination {} at elimination bound {}",
                self.stats.elimcompleted + 1,
                self.lim.elimbound
            );
        }

        self.reset_citten();
        if deleted_binary_clause {
            self.delete_garbage_clauses();
        }
        self.init_watches();
        self.connect_watches(false);

        if self.unsat {
            log!(self, "elimination derived empty clause");
        } else if self.propagated < self.trail.len() {
            log!(self, "elimination produced {} units", self.trail.len() - self.propagated);
            if !self.propagate() {
                log!(self, "propagating units after elimination results in empty clause");
                self.learn_empty_clause();
            }
        }

        // If we ran variable elimination until completion we increase the
        // variable elimination bound and reschedule elimination of all
        // variables.
        //
        if phase_complete {
            self.increase_elimination_bound();
        }

        let eliminated = self.stats.all.eliminated as i32 - old_eliminated;
        phase!(
            self,
            "elim-phase",
            self.stats.elimphases,
            "eliminated {} variables {}%",
            eliminated,
            fmt_f(percent(eliminated as f64, old_active_variables as f64), 2)
        );

        if self.external_prop {
            debug_assert!(self.level == 0);
            self.private_steps = false;
        }

        if !update_limits {
            return;
        }

        let delta = self.scale((self.opts.elimint as i64 * (self.stats.elimphases + 1)) as f64) as i64;
        self.lim.elim = self.stats.conflicts + delta;

        phase!(
            self,
            "elim-phase",
            self.stats.elimphases,
            "new limit at {} conflicts after {} conflicts",
            self.lim.elim,
            delta
        );

        self.last.elim.fixed = self.stats.all.fixed;
    }
}

impl HeapLess for elim_more {
    fn less(&self, a: u32, b: u32) -> bool {
        // SAFETY: the back pointer to the owning 'Internal' is valid while
        // the schedule is alive (only read access to 'ntab' and 'opts').
        let internal = unsafe { &*self.internal };
        let s = internal.compute_elim_score(a);
        let t = internal.compute_elim_score(b);
        if s > t {
            return true;
        }
        if s < t {
            return false;
        }
        a > b
    }
}

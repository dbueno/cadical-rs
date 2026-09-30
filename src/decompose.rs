//! Port of `decompose.hpp` and `decompose.cpp`: Tarjan's algorithm for
//! decomposing the binary implication graph into strongly connected
//! components (SCCs) and equivalent literal substitution (ELS).

use crate::clause::CRef;
use crate::internal::Internal;

/// Mark completely traversed.
pub const TRAVERSED: u32 = u32::MAX;

#[derive(Clone, Copy, Debug, Default)]
pub struct DFS {
    /// Depth first search index.
    pub idx: u32,
    /// Minimum reachable index.
    pub min: u32,
    /// For lrat.
    pub parent: CRef,
}

/*------------------------------------------------------------------------*/

// Port of 'decompose.cpp'.

#[allow(unused_imports)]
use crate::prelude::*;

use crate::format::fmt_f;
use crate::util::{erase_vector, percent};
use crate::watch::update_watch_size;

impl Internal {
    pub fn decompose_analyze_binary_chain(&mut self, dfs: &mut [DFS], from: i32) {
        if !self.lrat {
            return;
        }
        log!(self, "binary chain starting at {}", from);
        let reason = dfs[self.vlit(from) as usize].parent;
        if reason.is_null() {
            return;
        }
        debug_assert!(reason.size() == 2);
        self.mini_chain.push(reason.id());
        let mut other = reason.lit(0);
        other = if other == from { -reason.lit(1) } else { -other };
        if self.flags(other).seen {
            return;
        }
        self.flags_mut(other).seen = true;
        self.analyzed.push(other);
        self.decompose_analyze_binary_chain(dfs, other);
    }

    pub fn decompose_analyze_binary_clauses(&mut self, dfs: &mut [DFS], from: i32) -> Vec<CRef> {
        let mut from = from;
        let mut result: Vec<CRef> = Vec::new();
        log!(self, "binary chain starting at {}", from);
        let mut reason = dfs[self.vlit(from) as usize].parent;
        while !reason.is_null() {
            result.push(reason);
            debug_assert!(reason.size() == 2);
            let mut other = reason.lit(0);
            other = if other == from { -reason.lit(1) } else { -other };
            if self.flags(other).seen {
                break;
            }
            self.flags_mut(other).seen = true;
            self.analyzed.push(other);
            from = other;
            reason = dfs[self.vlit(from) as usize].parent;
        }
        result
    }

    pub fn decompose_conflicting_scc_lrat(&mut self, dfs: &mut [DFS], scc: &mut Vec<i32>) {
        if !self.lrat {
            return;
        }
        debug_assert!(self.lrat_chain.is_empty());
        debug_assert!(self.mini_chain.is_empty());
        for k in 0..scc.len() {
            let lit = scc[k];
            if self.flags(lit).seen {
                return;
            }
            self.flags_mut(lit).seen = true;
            self.analyzed.push(lit);
            self.decompose_analyze_binary_chain(dfs, lit);
            for p in (0..self.mini_chain.len()).rev() {
                let id = self.mini_chain[p];
                self.lrat_chain.push(id);
            }
            self.mini_chain.clear();
        }
        self.clear_analyzed_literals();
    }

    /// `invert` defaults to `false` in C++
    pub fn build_lrat_for_clause(&mut self, dfs_chains: &[Vec<CRef>], invert: bool) {
        debug_assert!(self.lrat);
        log!(self, "building chain for not subsumed clause");
        debug_assert!(self.lrat_chain.is_empty());
        debug_assert!(self.sign_marked.is_empty());
        // build chain for each replaced literal
        for ci in 0..self.clause.len() {
            let lit = self.clause[ci];
            let mut other = lit;
            if self.val(other) > 0 {
                if self.marked_decomposed(other) {
                    continue;
                }
                self.mark_decomposed(other);
                let id = self.unit_id(other);
                self.lrat_chain.push(id);
                continue;
            }
            debug_assert!(self.mini_chain.is_empty());
            // The range is evaluated once with the original 'other'.
            let chain = &dfs_chains[self.vlit(other) as usize];
            for &p in chain.iter() {
                if self.marked_decomposed(other) {
                    continue;
                }
                self.mark_decomposed(other);
                let mut implied = p.lit(0);
                implied = if implied == other { -p.lit(1) } else { -implied };
                log!(self, "ADDED {} -> {} ({})", implied, other, p.id());
                other = implied;
                self.mini_chain.push(p.id());
                if self.val(implied) <= 0 {
                    continue;
                }
                if self.marked_decomposed(implied) {
                    break;
                }
                self.mark_decomposed(implied);
                let id = self.unit_id(implied);
                self.mini_chain.push(id);
                break;
            }
            if invert {
                for p in (0..self.mini_chain.len()).rev() {
                    let id = self.mini_chain[p];
                    self.lrat_chain.push(id);
                }
            } else {
                for p in 0..self.mini_chain.len() {
                    let id = self.mini_chain[p];
                    self.lrat_chain.push(id);
                }
            }
            self.mini_chain.clear();
        }
        self.clear_sign_marked_literals();
        log!(self, &self.lrat_chain, "lrat_chain:");
    }

    pub fn clear_sign_marked_literals(&mut self) {
        log!(self, "clearing {} marked literals", self.sign_marked.len());
        for k in 0..self.sign_marked.len() {
            let lit = self.sign_marked[k];
            // assert (marked_signed (lit));  violated on purpose in factor
            self.unmark_decomposed(lit);
        }
        self.sign_marked.clear();
    }

    // This performs one round of Tarjan's algorithm, e.g., equivalent
    // literal detection and substitution, on the whole formula.  We might
    // want to repeat it since its application might produce new binary
    // clauses or units. Such units might even result in an empty clause.

    pub fn decompose_round(&mut self) -> bool {
        if self.opts.decompose == 0 {
            return false;
        }
        if self.unsat {
            return false;
        }
        if self.terminated_asynchronously(1) {
            return false;
        }

        debug_assert!(self.level == 0);

        start_simplifier!(self, decompose, DECOMP);

        self.stats.decompositions += 1;

        let size_dfs = 2 * (1 + self.max_var as usize);
        let mut dfs: Vec<DFS> = vec![DFS::default(); size_dfs];
        let mut reprs: Vec<i32> = vec![0; size_dfs];
        let mut dfs_chains: Vec<Vec<CRef>> = Vec::new();
        dfs_chains.resize(size_dfs, Vec::new());
        // (The C++ loop 'for (size_t i = 0; i > size_dfs; i++)' resetting
        // the chains never executes.)

        let mut substituted = 0i32;
        let mut non_trivial_sccs = 0i32;
        let before = self.active_count();
        let mut dfs_idx: u32 = 0;

        let mut work: Vec<i32> = Vec::new(); // depth first search working stack
        let mut scc: Vec<i32> = Vec::new(); // collects members of one SCC

        // The binary implication graph might have disconnected components and
        // thus we have in general to start several depth first searches.

        for root_idx in self.vars() {
            if self.unsat {
                break;
            }
            if !self.active(root_idx) {
                continue;
            }
            let mut root_sign = -1;
            while !self.unsat && root_sign <= 1 {
                if self.terminated_asynchronously(1) {
                    stop_simplifier!(self, decompose, DECOMP);
                    return false;
                }
                let root = root_sign * root_idx;
                root_sign += 2;
                if dfs[self.vlit(root) as usize].min == TRAVERSED {
                    continue; // skip traversed
                }
                log!(self, "new dfs search starting at root {}", root);
                debug_assert!(work.is_empty());
                debug_assert!(scc.is_empty());
                work.push(root);
                while !self.unsat && !work.is_empty() {
                    let parent = *work.last().unwrap();
                    let parent_vlit = self.vlit(parent) as usize;
                    if dfs[parent_vlit].min == TRAVERSED {
                        // skip traversed
                        debug_assert!(reprs[parent_vlit] != 0);
                        work.pop();
                    } else {
                        debug_assert!(reprs[parent_vlit] == 0);

                        // Go over all implied literals, thus need to iterate
                        // over all binary watched clauses with the negation
                        // of 'parent'.

                        let wi = self.vlit(-parent) as usize;

                        // Two cases: Either the node has never been visited
                        // before, i.e., it's depth first search index is
                        // zero, then perform the 'pre-fix' work before
                        // visiting it's children.  Otherwise all it's
                        // children and nodes reachable from those children
                        // have been visited and their minimum reachable depth
                        // first search index has been computed.  This second
                        // case is the 'post-fix' work.

                        if dfs[parent_vlit].idx != 0 {
                            // post-fix

                            work.pop(); // 'parent' done

                            // Get the minimum reachable depth first search
                            // index reachable from the children of 'parent'.

                            let mut new_min = dfs[parent_vlit].min;

                            for k in 0..self.wtab[wi].len() {
                                let w = self.wtab[wi][k];
                                if !w.binary() {
                                    continue;
                                }
                                let child = w.blit;
                                if !self.active(child) {
                                    continue;
                                }
                                let child_min = dfs[self.vlit(child) as usize].min;
                                if new_min > child_min {
                                    new_min = child_min;
                                }
                            }

                            log!(
                                self,
                                "post-fix work dfs search {} index {} reaches minimum {}",
                                parent,
                                dfs[parent_vlit].idx,
                                new_min
                            );

                            if dfs[parent_vlit].idx == new_min {
                                // entry to SCC

                                // All nodes on the 'scc' stack after and
                                // including 'parent' are in the same SCC.
                                // Their representative is computed as the
                                // smallest literal (index-wise) in the SCC.  If
                                // the SCC contains both a literal and its
                                // negation, then the formula becomes
                                // unsatisfiable.

                                if self.lrat {
                                    debug_assert!(self.analyzed.is_empty());
                                    let mut other;
                                    let mut first = 0;
                                    let mut conflicting = false;
                                    let mut j = scc.len();
                                    loop {
                                        debug_assert!(j > 0);
                                        j -= 1;
                                        other = scc[j];
                                        if first == 0 || self.vlit(other) < self.vlit(first) {
                                            first = other;
                                        }
                                        if other == -parent {
                                            conflicting = true; // conflicting scc
                                        }
                                        if !self.flags(other).seen {
                                            // (otherwise also conflicting scc)
                                            self.flags_mut(other).seen = true;
                                            self.analyzed.push(other);
                                        }
                                        if other == parent {
                                            break;
                                        }
                                    }

                                    debug_assert!(!conflicting || first > 0);
                                    let mut to_justify: Vec<i32> = Vec::new();
                                    if conflicting {
                                        log!(self, "conflicting scc simulating up at {}", parent);
                                        to_justify.push(-parent);
                                    } else {
                                        to_justify.push(first);
                                    }
                                    while let Some(next) = to_justify.pop() {
                                        let ni = self.vlit(-next) as usize;
                                        for k in 0..self.wtab[ni].len() {
                                            let w = self.wtab[ni][k];
                                            if !w.binary() {
                                                continue;
                                            }
                                            let child = w.blit;
                                            if !self.active(child) {
                                                continue;
                                            }
                                            if !self.flags(child).seen {
                                                continue;
                                            }
                                            let child_dfs = &mut dfs[self.vlit(child) as usize];
                                            if !child_dfs.parent.is_null() {
                                                continue;
                                            }
                                            child_dfs.parent = w.clause;
                                            to_justify.push(child);
                                        }
                                    }

                                    self.clear_analyzed_literals();
                                }

                                let mut other;
                                let mut repr = parent;
                                let mut size = 0i32;
                                debug_assert!(!scc.is_empty());
                                let mut j = scc.len();
                                loop {
                                    debug_assert!(j > 0);
                                    j -= 1;
                                    other = scc[j];
                                    if other == -parent {
                                        log!(self, "both {} and {} in one SCC", parent, -parent);
                                        if self.lrat {
                                            self.flags_mut(-parent).seen = true;
                                            self.analyzed.push(-parent);
                                            self.decompose_analyze_binary_chain(&mut dfs, parent);
                                            for p in 0..self.mini_chain.len() {
                                                let id = self.mini_chain[p];
                                                self.lrat_chain.push(id);
                                            }
                                            self.mini_chain.clear();
                                        }
                                        self.assign_unit(parent);
                                        let ok = self.propagate();
                                        debug_assert!(!ok);
                                        let _ = ok;
                                        self.learn_empty_clause();
                                        self.lrat_chain.clear();
                                    } else {
                                        if other.abs() < repr.abs() {
                                            repr = other;
                                        }
                                        size += 1;
                                    }
                                    if !(!self.unsat && other != parent) {
                                        break;
                                    }
                                }

                                if self.unsat {
                                    break;
                                }
                                log!(self, "SCC of representative {} of size {}", repr, size);
                                loop {
                                    'body: {
                                        debug_assert!(!scc.is_empty());
                                        other = scc.pop().unwrap();
                                        let ov = self.vlit(other) as usize;
                                        dfs[ov].min = TRAVERSED;
                                        if self.frozen(other) {
                                            reprs[ov] = other;
                                            break 'body;
                                        }
                                        reprs[ov] = repr;
                                        if other == repr {
                                            break 'body;
                                        }
                                        substituted += 1;
                                        log!(self, "literal {} in SCC of {}", other, repr);
                                        if !self.lrat {
                                            break 'body;
                                        }
                                        debug_assert!(self.mini_chain.is_empty());
                                        self.flags_mut(repr).seen = true;
                                        self.analyzed.push(repr);
                                        // no need to reverse dfs_chain because
                                        // this is handled by
                                        // build_lrat_for_clause.
                                        dfs_chains[ov] = self.decompose_analyze_binary_clauses(&mut dfs, other);
                                        self.clear_analyzed_literals();
                                    }
                                    if other == parent {
                                        break;
                                    }
                                }

                                if size > 1 {
                                    non_trivial_sccs += 1;
                                }
                            } else {
                                // Current node 'parent' is in a non-trivial
                                // SCC but is not the entry point of the SCC in
                                // this depth first search, so keep it on the
                                // SCC stack until the entry point is reached.

                                dfs[parent_vlit].min = new_min;
                            }
                        } else {
                            // pre-fix

                            dfs_idx += 1;
                            debug_assert!(dfs_idx < TRAVERSED);
                            dfs[parent_vlit].idx = dfs_idx;
                            dfs[parent_vlit].min = dfs_idx;
                            scc.push(parent);

                            log!(self, "pre-fix work dfs search {} index {}", parent, dfs_idx);

                            // Now traverse all the children in the binary
                            // implication graph but keep 'parent' on the
                            // stack for 'post-fix' work.

                            for k in 0..self.wtab[wi].len() {
                                let w = self.wtab[wi][k];
                                if !w.binary() {
                                    continue;
                                }
                                let child = w.blit;
                                if !self.active(child) {
                                    continue;
                                }
                                if dfs[self.vlit(child) as usize].idx != 0 {
                                    continue;
                                }
                                work.push(child);
                            }
                        }
                    }
                }
            }
        }

        erase_vector(&mut work);
        erase_vector(&mut scc);
        // delete [] dfs; need to postpone until after changing clauses...

        // Only keep the representatives 'repr' mapping.

        phase!(
            self,
            "decompose",
            self.stats.decompositions,
            "{} non-trivial sccs, {} substituted {}%",
            non_trivial_sccs,
            substituted,
            fmt_f(percent(substituted as f64, before as f64), 2)
        );

        let mut new_unit = false;
        let mut new_binary_clause = false;

        // Finally, mark substituted literals as such and push the
        // equivalences of the substituted literals to their representative on
        // the extension stack to fix an assignment during 'extend'.  It is
        // also necessary to do so for proper IDRUP/LIDRUP/Resolution proofs

        let mut decompose_ids: Vec<i64> = Vec::new();
        let size = 2 * (1 + self.max_var as usize);
        decompose_ids.resize(size, 0);

        for idx in self.vars() {
            if substituted == 0 {
                break;
            }
            if self.unsat {
                break;
            }
            if !self.active(idx) {
                continue;
            }
            let other = reprs[self.vlit(idx) as usize];
            if other == idx {
                continue;
            }
            debug_assert!(!self.flags(other).eliminated());
            debug_assert!(!self.flags(other).substituted());

            log!(self, "marking equivalence of {} and {}", idx, other);
            debug_assert!(self.clause.is_empty());
            debug_assert!(self.lrat_chain.is_empty());
            self.clause.push(other);
            self.clause.push(-idx);
            if self.lrat {
                self.build_lrat_for_clause(&dfs_chains, false);
                debug_assert!(!self.lrat_chain.is_empty());
            }

            self.clause_id += 1;
            let id1 = self.clause_id;
            if let Some(proof) = self.proof.as_mut() {
                proof.add_derived_clause_lits(id1, false, &self.clause, &self.lrat_chain);
                proof.weaken_minus_lits(id1, &self.clause);
            }
            self.external().push_binary_clause_on_extension_stack(id1, -idx, other);

            decompose_ids[self.vlit(-idx) as usize] = id1;

            self.lrat_chain.clear();
            self.clause.clear();

            debug_assert!(self.clause.is_empty());
            debug_assert!(self.lrat_chain.is_empty());
            self.clause.push(idx);
            self.clause.push(-other);
            if self.lrat {
                self.build_lrat_for_clause(&dfs_chains, false);
                debug_assert!(!self.lrat_chain.is_empty());
            }
            self.clause_id += 1;
            let id2 = self.clause_id;
            if let Some(proof) = self.proof.as_mut() {
                proof.add_derived_clause_lits(id2, false, &self.clause, &self.lrat_chain);
                proof.weaken_minus_lits(id2, &self.clause);
            }
            self.external().push_binary_clause_on_extension_stack(id2, idx, -other);
            decompose_ids[self.vlit(idx) as usize] = id2;
            if !self.tracers.is_empty() {
                let eidx = self.externalize(idx);
                let eother = self.externalize(other);
                for tracer in self.tracers.iter_mut() {
                    tracer.notify_equivalence(eidx, eother);
                }
            }

            self.clause.clear();
            self.lrat_chain.clear();
        }

        let mut postponed_garbage: Vec<CRef> = Vec::new();

        // Now go over all clauses and find clause which contain literals that
        // should be substituted by their representative.

        let clauses_size = self.clauses.len();
        let mut garbage: usize = 0;
        let mut replaced: usize = 0;
        let mut i = 0usize;
        while substituted != 0 && !self.unsat && i < clauses_size {
            let c = self.clauses[i];
            if c.garbage() {
                i += 1;
                continue;
            }
            let size = c.size();
            let mut j = 0;
            while j < size {
                let lit = c.lit(j as usize);
                if reprs[self.vlit(lit) as usize] != lit {
                    break;
                }
                j += 1;
            }

            if j == size {
                i += 1;
                continue;
            }

            replaced += 1;
            log!(self, c, "first substituted literal {} in", substituted);

            // Now copy the result to 'clause'.  Substitute literals if they
            // have a different representative.  Skip duplicates and false
            // literals.  If a literal occurs in both phases or is assigned to
            // true the clause is satisfied and can be marked as garbage.

            debug_assert!(self.clause.is_empty());
            debug_assert!(self.lrat_chain.is_empty());
            debug_assert!(self.analyzed.is_empty());
            let mut satisfied = false;

            let mut k = 0;
            while !satisfied && k < size {
                let lit = c.lit(k as usize);
                k += 1;
                let mut tmp = self.val(lit);
                if tmp > 0 {
                    satisfied = true;
                } else if tmp < 0 {
                    if !self.lrat {
                        continue;
                    }
                    if self.flags(lit).seen {
                        continue;
                    }
                    self.flags_mut(lit).seen = true;
                    self.analyzed.push(lit);
                    let id = self.unit_id(-lit);
                    self.lrat_chain.push(id);
                    continue;
                } else {
                    let other = reprs[self.vlit(lit) as usize];
                    tmp = self.val(other);
                    if tmp < 0 {
                        if !self.lrat {
                            continue;
                        }
                        if !self.flags(other).seen {
                            self.flags_mut(other).seen = true;
                            self.analyzed.push(other);
                            let id = self.unit_id(-other);
                            self.lrat_chain.push(id);
                        }
                        if other == lit {
                            continue;
                        }
                        let id = decompose_ids[self.vlit(-lit) as usize];
                        debug_assert!(id != 0);
                        self.lrat_chain.push(id);
                        continue;
                    } else if tmp > 0 {
                        satisfied = true;
                    } else {
                        tmp = self.marked(other);
                        if tmp < 0 {
                            satisfied = true;
                        } else if tmp == 0 {
                            self.mark(other);
                            self.clause.push(other);
                        }
                        if other == lit {
                            continue;
                        }
                        if !self.lrat {
                            continue;
                        }
                        let id = decompose_ids[self.vlit(-lit) as usize];
                        debug_assert!(id != 0);
                        self.lrat_chain.push(id);
                    }
                }
            }
            if self.lrat {
                self.lrat_chain.push(c.id());
            }
            self.clear_analyzed_literals();
            log!(self, &self.lrat_chain, "lrat_chain:");
            if satisfied {
                log!(self, c, "satisfied after substitution (postponed)");
                postponed_garbage.push(c);
                garbage += 1;
            } else if self.clause.is_empty() {
                log!(self, "learned empty clause during decompose");
                self.learn_empty_clause();
            } else if self.clause.len() == 1 {
                log!(self, c, "unit {} after substitution", self.clause[0]);
                let unit = self.clause[0];
                self.assign_unit(unit);
                self.mark_garbage(c);
                new_unit = true;
                garbage += 1;
            } else if c.lit(0) != self.clause[0] || c.lit(1) != self.clause[1] {
                log!(self, "need new clause since at least one watched literal changed");
                if self.clause.len() == 2 {
                    new_binary_clause = true;
                }
                let d_clause_idx = self.clauses.len();
                let d = self.new_clause_as(c);
                debug_assert!(self.clauses[d_clause_idx] == d);
                self.clauses[d_clause_idx] = c;
                self.clauses[i] = d;
                self.mark_garbage(c);
                garbage += 1;
            } else {
                log!(self, "simply shrinking clause since watches did not change");
                debug_assert!(c.size() > 2);
                if !c.redundant() {
                    self.mark_removed(c, 0);
                }
                if self.proof.is_some() {
                    self.clause_id += 1;
                    let id = self.clause_id;
                    let proof = self.proof.as_mut().unwrap();
                    proof.add_derived_clause_lits(id, c.redundant(), &self.clause, &self.lrat_chain);
                    proof.delete_clause(c);
                    c.set_id(self.clause_id);
                }
                let mut l = 2usize;
                while l < self.clause.len() {
                    c.set_lit(l, self.clause[l]);
                    l += 1;
                }
                let flushed = c.size() - l as i32;
                if flushed != 0 {
                    if l == 2 {
                        new_binary_clause = true;
                    }
                    log!(self, "flushed {} literals", flushed);
                    let _ = self.shrink_clause(c, l as i32);
                } else if self.likely_to_be_kept_clause(c) {
                    self.mark_added(c);
                }
                // we have shrunken c->size to l so even though there is an
                // assertion for c->size > 2 at the beginning of this else
                // block, the new size can be 2 now.
                if c.size() == 2 {
                    // cheaper to update only new binary clauses
                    debug_assert!(new_binary_clause);
                    let l0 = c.lit(0);
                    let l1 = c.lit(1);
                    update_watch_size(self.watches_mut(l0), l1, c);
                    update_watch_size(self.watches_mut(l1), l0, c);
                }
                log!(self, c, "substituted");
            }
            while let Some(lit) = self.clause.pop() {
                debug_assert!(self.marked(lit) > 0);
                self.unmark(lit);
            }
            self.lrat_chain.clear();
            i += 1;
        }

        if self.proof.is_some() {
            for idx in self.vars() {
                if substituted == 0 {
                    break;
                }
                if !self.active(idx) {
                    continue;
                }
                let id1 = decompose_ids[self.vlit(-idx) as usize];
                if id1 == 0 {
                    continue;
                }
                let other = reprs[self.vlit(idx) as usize];
                debug_assert!(other != idx);
                debug_assert!(!self.flags(other).eliminated());
                debug_assert!(!self.flags(other).substituted());

                self.clause.push(other);
                self.clause.push(-idx);
                self.proof.as_mut().unwrap().delete_clause_lits(id1, false, &self.clause);
                self.clause.clear();

                self.clause.push(idx);
                self.clause.push(-other);
                let id2 = decompose_ids[self.vlit(idx) as usize];
                self.proof.as_mut().unwrap().delete_clause_lits(id2, false, &self.clause);
                self.clause.clear();
            }
        }

        if !self.unsat && !postponed_garbage.is_empty() {
            log!(self, "now marking {} postponed garbage clauses", postponed_garbage.len());
            for &c in postponed_garbage.iter() {
                self.mark_garbage(c);
            }
        }
        erase_vector(&mut postponed_garbage);

        phase!(
            self,
            "decompose",
            self.stats.decompositions,
            "{} clauses replaced {}% producing {} garbage clauses {}%",
            replaced,
            fmt_f(percent(replaced as f64, clauses_size as f64), 2),
            garbage,
            fmt_f(percent(garbage as f64, replaced as f64), 2)
        );

        erase_vector(&mut scc);

        // Propagate found units.

        if !self.unsat && self.propagated < self.trail.len() && !self.propagate() {
            log!(self, "empty clause after propagating units from substitution");
            self.learn_empty_clause();
        }

        for idx in self.vars() {
            if substituted == 0 {
                break;
            }
            if self.unsat {
                break;
            }
            if !self.active(idx) {
                continue;
            }
            let other = reprs[self.vlit(idx) as usize];
            if other == idx {
                continue;
            }
            debug_assert!(!self.flags(other).eliminated());
            debug_assert!(!self.flags(other).substituted());
            if !self.flags(other).fixed() {
                self.mark_substituted(idx);
            }
        }

        drop(reprs);
        drop(dfs);
        erase_vector(&mut dfs_chains);

        if substituted != 0 {
            self.flush_all_occs_and_watches(); // particularly the 'blit's
        }

        let success = self.unsat || (substituted > 0 && (new_unit || new_binary_clause));
        let quiet = self.opts.reportall == 0 && !success;
        self.report(b'd', quiet as i32);

        stop_simplifier!(self, decompose, DECOMP);

        success
    }

    pub fn decompose(&mut self) {
        let mut round = 1;
        while round <= self.opts.decomposerounds {
            if !self.decompose_round() {
                break;
            }
            round += 1;
        }
    }
}

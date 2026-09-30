//! Port of `collect.cpp`.

#[allow(unused_imports)]
use crate::prelude::*;

use crate::occs::shrink_occs;
use crate::radix::{pointer_rank, rsort};

impl Internal {
    /*----------------------------------------------------------------------*/

    /// Returns the positive number '1' ( > 0) if the given clause is root
    /// level satisfied or the negative number '-1' ( < 0) if it is not root
    /// level satisfied but contains a root level falsified literal.
    /// Otherwise, if it contains neither a satisfied nor falsified literal,
    /// then '0' is returned.
    pub fn clause_contains_fixed_literal(&mut self, c: CRef) -> i32 {
        let mut satisfied = 0;
        let mut falsified = 0;
        for &lit in c.lits() {
            let tmp = self.fixed(lit);
            if tmp > 0 {
                log!(self, c, "root level satisfied literal {} in", lit);
                satisfied += 1;
            }
            if tmp < 0 {
                log!(self, c, "root level falsified literal {} in", lit);
                falsified += 1;
            }
        }
        if satisfied != 0 {
            1
        } else if falsified != 0 {
            -1
        } else {
            0
        }
    }

    /// Assume that the clause is not root level satisfied but contains a
    /// literal set to false (root level falsified literal), so it can be
    /// shrunken.  The clause data is not actually reallocated at this point
    /// to avoid dealing with issues of special policies for watching binary
    /// clauses or whether a clause is extended or not. Only its size field
    /// is adjusted accordingly after flushing out root level falsified
    /// literals.
    pub fn remove_falsified_literals(&mut self, c: CRef) {
        let end = c.size() as usize;
        let mut num_non_false = 0;
        let mut i = 0;
        while num_non_false < 2 && i != end {
            if self.fixed(c.lit(i)) >= 0 {
                num_non_false += 1;
            }
            i += 1;
        }
        if num_non_false < 2 {
            return;
        }
        if self.proof.is_some() {
            // Flush changes the clause id, external forgettables need to be
            // marked here (or the new id could be used instead of old one)
            if self.opts.check != 0 && self.is_external_forgettable(c.id()) {
                self.mark_garbage_external_forgettable(c.id());
            }
            self.proof.as_mut().unwrap().flush_clause(c);
        }
        let mut j = 0;
        for i in 0..end {
            let lit = c.lit(i);
            c.set_lit(j, lit);
            j += 1;
            let tmp = self.fixed(lit);
            debug_assert!(tmp <= 0);
            if tmp >= 0 {
                continue;
            }
            log!(self, "flushing {}", lit);
            j -= 1;
        }
        let collected = self.shrink_clause(c, j as i32);
        self.stats.collected += collected as i64;
    }

    /// If there are new units (fixed variables) since the last garbage
    /// collection we go over all clauses, mark satisfied ones as garbage
    /// and flush falsified literals.  Otherwise if no new units have been
    /// generated since the last garbage collection just skip this step.
    pub fn mark_satisfied_clauses_as_garbage(&mut self) {
        if self.last.collect.fixed >= self.stats.all.fixed {
            return;
        }
        self.last.collect.fixed = self.stats.all.fixed;

        log!(self, "marking satisfied clauses and removing falsified literals");

        for k in 0..self.clauses.len() {
            let c = self.clauses[k];
            if c.garbage() {
                continue;
            }
            let tmp = self.clause_contains_fixed_literal(c);
            if tmp > 0 {
                self.mark_garbage(c);
            } else if tmp < 0 {
                self.remove_falsified_literals(c);
            }
        }
    }

    /*----------------------------------------------------------------------*/

    // Reason clauses can not be collected.
    //
    // We protect reasons before and release protection after garbage
    // collection (actually within garbage collection).
    //
    // For 'reduce' we still need to make sure that all clauses which should
    // not be removed are marked as such and thus we need to call it before
    // marking clauses to be flushed.

    pub fn protect_reasons(&mut self) {
        log!(self, "protecting reason clauses of all assigned variables on trail");
        debug_assert!(!self.protected_reasons);
        #[cfg(feature = "logging")]
        let mut count: usize = 0;
        for k in 0..self.trail.len() {
            let lit = self.trail[k];
            if !self.active(lit) {
                continue;
            }
            debug_assert!(self.val(lit) != 0);
            let v = self.var(lit);
            debug_assert!(v.level > 0);
            let reason = v.reason;
            if reason.is_null() {
                continue;
            }
            if reason == self.external_reason {
                continue;
            }
            log!(self, reason, "protecting assigned {} reason {:p}", lit, reason);
            debug_assert!(!reason.reason());
            reason.set_reason(true);
            #[cfg(feature = "logging")]
            {
                count += 1;
            }
        }
        log!(self, "protected {} reason clauses referenced on trail", count);
        self.protected_reasons = true;
    }

    /*----------------------------------------------------------------------*/

    /// After garbage collection we reset the 'reason' flag of the reasons
    /// of assigned literals on the trail.
    pub fn unprotect_reasons(&mut self) {
        log!(self, "unprotecting reasons clauses of all assigned variables on trail");
        debug_assert!(self.protected_reasons);
        #[cfg(feature = "logging")]
        let mut count: usize = 0;
        for k in 0..self.trail.len() {
            let lit = self.trail[k];
            if !self.active(lit) {
                continue;
            }
            debug_assert!(self.val(lit) != 0);
            let v = self.var(lit);
            debug_assert!(v.level > 0);
            let reason = v.reason;
            if reason.is_null() {
                continue;
            }
            if reason == self.external_reason {
                continue;
            }
            log!(self, reason, "unprotecting assigned {} reason {:p}", lit, reason);
            debug_assert!(reason.reason());
            reason.set_reason(false);
            #[cfg(feature = "logging")]
            {
                count += 1;
            }
        }
        log!(self, "unprotected {} reason clauses referenced on trail", count);
        self.protected_reasons = false;
    }

    /*----------------------------------------------------------------------*/

    /// Update occurrence lists before deleting garbage clauses in the
    /// context of preprocessing, e.g., during bounded variable elimination
    /// 'elim'.  The result is the number of remaining clauses, which in
    /// this context means the number of non-garbage clauses.
    pub fn flush_occs(&mut self, lit: i32) -> usize {
        let os = self.occs_mut(lit);
        let end = os.len();
        let mut j = 0;
        let mut res = 0;
        for i in 0..end {
            let c = os[i];
            if c.collect() {
                continue;
            }
            os[j] = if c.moved() { c.copy() } else { c };
            j += 1;
            // assert (!c->redundant); // -> not true in sweeping
            res += 1;
        }
        os.truncate(j);
        shrink_occs(os);
        res
    }

    /// Update watch lists before deleting garbage clauses in the context of
    /// 'reduce' where we watch and no occurrence lists.  We have to protect
    /// reason clauses not be collected and thus we have this additional
    /// check hidden in 'Clause.collect', which for the root level context
    /// of preprocessing is actually redundant.
    #[inline]
    pub fn flush_watches(&mut self, lit: i32, saved: &mut Watches) {
        debug_assert!(saved.is_empty());
        let widx = self.vlit(lit) as usize;
        let end = self.wtab[widx].len();
        let mut j = 0;
        for i in 0..end {
            let mut w = self.wtab[widx][i];
            let mut c = w.clause;
            if c.collect() {
                continue;
            }
            if c.moved() {
                c = c.copy();
                w.clause = c;
            }
            w.size = c.size();
            let new_blit_pos = (c.lit(0) == lit) as usize;
            log!(self, c, "clause in flush_watch starting from {}", lit);
            debug_assert!(c.lit((new_blit_pos == 0) as usize) == lit); /*FW1*/
            w.blit = c.lit(new_blit_pos);
            if w.binary() {
                self.wtab[widx][j] = w;
                j += 1;
            } else {
                saved.push(w);
            }
        }
        let ws = &mut self.wtab[widx];
        ws.truncate(j);
        for &w in saved.iter() {
            ws.push(w);
        }
        saved.clear();
        shrink_vector(ws);
    }

    pub fn flush_all_occs_and_watches(&mut self) {
        if self.occurring() {
            for idx in self.vars() {
                self.flush_occs(idx);
                self.flush_occs(-idx);
            }
        }

        if self.watching() {
            let mut tmp: Watches = Vec::new();
            for idx in self.vars() {
                self.flush_watches(idx, &mut tmp);
                self.flush_watches(-idx, &mut tmp);
            }
        }
    }

    /*----------------------------------------------------------------------*/

    pub fn update_reason_references(&mut self) {
        log!(self, "update assigned reason references");
        #[cfg(feature = "logging")]
        let mut count: usize = 0;
        for k in 0..self.trail.len() {
            let lit = self.trail[k];
            if !self.active(lit) {
                continue;
            }
            let c = self.var(lit).reason;
            if c.is_null() {
                continue;
            }
            if c == self.external_reason {
                continue;
            }
            log!(self, c, "updating assigned {} reason", lit);
            debug_assert!(c.reason());
            debug_assert!(c.moved());
            let d = c.copy();
            self.var_mut(lit).reason = d;
            #[cfg(feature = "logging")]
            {
                count += 1;
            }
        }
        log!(self, "updated {} assigned reason references", count);
    }

    /*----------------------------------------------------------------------*/

    /// This is a simple garbage collector which does not move clauses.  It
    /// needs less space than the arena based clause allocator, but is not
    /// as cache efficient, since the copying garbage collector can put
    /// clauses together which are likely accessed after each other.
    pub fn delete_garbage_clauses(&mut self) {
        self.flush_all_occs_and_watches();

        log!(self, "deleting garbage clauses");
        let mut collected_bytes: i64 = 0;
        let mut collected_clauses: i64 = 0;
        let end = self.clauses.len();
        let mut j = 0;
        for i in 0..end {
            let c = self.clauses[i];
            self.clauses[j] = c;
            j += 1;
            if !c.collect() {
                continue;
            }
            collected_bytes += c.bytes() as i64;
            collected_clauses += 1;
            self.delete_clause(c);
            j -= 1;
        }
        self.clauses.truncate(j);
        shrink_vector(&mut self.clauses);

        phase!(
            self,
            "collect",
            self.stats.collections,
            "collected {} bytes of {} garbage clauses",
            collected_bytes,
            collected_clauses
        );
        let _ = (collected_bytes, collected_clauses);
    }

    /*----------------------------------------------------------------------*/

    /// This is the start of the copying garbage collector using the arena.
    /// At the core is the following function, which copies a clause to the
    /// 'to' space of the arena.  Be careful if this clause is a reason of
    /// an assignment.  In that case update the reason reference.
    pub fn copy_clause(&mut self, c: CRef) {
        log!(self, c, "moving");
        debug_assert!(!c.moved());
        let p = c.as_ptr() as *const u8;
        let q = self.arena.copy(p, c.bytes());
        c.set_copy(CRef(q as *mut Clause));
        c.set_moved(true);
        log!(self, "copied clause[{}] from {:p} to {:p}", c.id(), c, c.copy());
    }

    /// This is the moving garbage collector.
    pub fn copy_non_garbage_clauses(&mut self) {
        let mut collected_clauses: usize = 0;
        let mut collected_bytes: usize = 0;
        let mut moved_clauses: usize = 0;
        let mut moved_bytes: usize = 0;

        // First determine 'moved_bytes' and 'collected_bytes'.
        //
        for &c in self.clauses.iter() {
            if !c.collect() {
                moved_bytes += c.bytes();
                moved_clauses += 1;
            } else {
                collected_bytes += c.bytes();
                collected_clauses += 1;
            }
        }

        phase!(
            self,
            "collect",
            self.stats.collections,
            "moving {} bytes {}% of {} non garbage clauses",
            moved_bytes,
            crate::format::fmt_f(percent(moved_bytes as f64, (collected_bytes + moved_bytes) as f64), 0),
            moved_clauses
        );
        let _ = (moved_clauses, collected_clauses, collected_bytes);
        // Prepare 'to' space of size 'moved_bytes'.
        //
        self.arena.prepare(moved_bytes);

        // Keep clauses in arena in the same order.
        //
        if self.opts.arenacompact != 0 {
            for k in 0..self.clauses.len() {
                let c = self.clauses[k];
                if !c.collect() && self.arena.contains(c.as_ptr() as *const u8) {
                    self.copy_clause(c);
                }
            }
        }

        if self.opts.arenatype == 1 || !self.watching() {
            // Localize according to current clause order.

            // If the option 'opts.arenatype == 1' is set, then this means
            // the solver uses the original order of clauses.  If there are
            // no watches, we can not use the watched based copying policies
            // below.  This happens if garbage collection is triggered during
            // bounded variable elimination.

            // Copy clauses according to the order of calling 'copy_clause',
            // which in essence just gives a compacting garbage collector,
            // since their relative order is kept, and actually already gives
            // the largest benefit due to better cache locality.

            for k in 0..self.clauses.len() {
                let c = self.clauses[k];
                if !c.moved() && !c.collect() {
                    self.copy_clause(c);
                }
            }
        } else if self.opts.arenatype == 2 {
            // Localize according to (original) variable order.

            // This is almost the version used by MiniSAT and descendants.
            // Our version uses saved phases too.

            let mut sign = -1;
            while sign <= 1 {
                for idx in self.vars() {
                    let lit = sign * self.likely_phase(idx);
                    let widx = self.vlit(lit) as usize;
                    for k in 0..self.wtab[widx].len() {
                        let c = self.wtab[widx][k].clause;
                        if !c.moved() && !c.collect() {
                            self.copy_clause(c);
                        }
                    }
                }
                sign += 2;
            }
        } else {
            // Localize according to decision queue order.

            // This is the default for search. It allocates clauses in the
            // order of the decision queue and also uses saved phases.  It
            // seems faster than the MiniSAT version and thus we keep
            // 'opts.arenatype == 3'.

            debug_assert!(self.opts.arenatype == 3);

            let mut sign = -1;
            while sign <= 1 {
                let mut idx = self.queue.last;
                while idx != 0 {
                    let lit = sign * self.likely_phase(idx);
                    let widx = self.vlit(lit) as usize;
                    for k in 0..self.wtab[widx].len() {
                        let c = self.wtab[widx][k].clause;
                        if !c.moved() && !c.collect() {
                            self.copy_clause(c);
                        }
                    }
                    idx = self.link(idx).prev;
                }
                sign += 2;
            }
        }

        // Do not forget to move clauses which are not watched, which
        // happened in a rare situation, and now is only left as defensive
        // code.
        //
        for k in 0..self.clauses.len() {
            let c = self.clauses[k];
            if !c.collect() && !c.moved() {
                self.copy_clause(c);
            }
        }

        self.flush_all_occs_and_watches();
        self.update_reason_references();

        // Replace and flush clause references in 'clauses'.
        //
        let end = self.clauses.len();
        let mut j = 0;
        for i in 0..end {
            let c = self.clauses[i];
            if c.collect() {
                self.delete_clause(c);
            } else {
                debug_assert!(c.moved());
                self.clauses[j] = c.copy();
                j += 1;
                self.deallocate_clause(c);
            }
        }
        self.clauses.truncate(j);
        if self.clauses.len() < self.clauses.capacity() / 2 {
            shrink_vector(&mut self.clauses);
        }

        if self.opts.arenasort != 0 {
            rsort(&mut self.clauses, pointer_rank);
        }

        // Release 'from' space completely and then swap 'to' with 'from'.
        //
        self.arena.swap();

        phase!(
            self,
            "collect",
            self.stats.collections,
            "collected {} bytes {}% of {} garbage clauses",
            collected_bytes,
            crate::format::fmt_f(percent(collected_bytes as f64, (collected_bytes + moved_bytes) as f64), 0),
            collected_clauses
        );
    }

    /*----------------------------------------------------------------------*/

    /// Maintaining clause statistics is complex and error prone but
    /// necessary for proper scheduling of garbage collection, particularly
    /// during bounded variable elimination.  With this function we can
    /// check whether these statistics are updated correctly.
    pub fn check_clause_stats(&mut self) {
        #[cfg(debug_assertions)]
        {
            let mut irredundant: i64 = 0;
            let mut redundant: i64 = 0;
            let mut total: i64 = 0;
            let mut irrlits: i64 = 0;
            for &c in self.clauses.iter() {
                if c.garbage() {
                    continue;
                }
                if c.redundant() {
                    redundant += 1;
                } else {
                    irredundant += 1;
                }
                if !c.redundant() {
                    irrlits += c.size() as i64;
                }
                total += 1;
            }
            debug_assert!(self.stats.current.irredundant == irredundant);
            debug_assert!(self.stats.current.redundant == redundant);
            debug_assert!(self.stats.current.total == total);
            debug_assert!(self.stats.irrlits == irrlits);
        }
    }

    /*----------------------------------------------------------------------*/

    /// only delete binary clauses from watch list that are already mark as
    /// deleted.
    pub fn remove_garbage_binaries(&mut self) {
        if self.unsat {
            return;
        }
        start!(self, collect);

        if !self.protected_reasons {
            self.protect_reasons();
        }
        let mut backtrack_level = self.level + 1;
        for v in self.vars() {
            for lit in [-v, v] {
                let widx = self.vlit(lit) as usize;
                let end = self.wtab[widx].len();
                let mut j = 0;
                for i in 0..end {
                    let w = self.wtab[widx][i];
                    self.wtab[widx][j] = w;
                    j += 1;
                    let c = w.clause;
                    cover!(!w.binary() && c.size() == 2);
                    if !w.binary() {
                        continue;
                    }
                    if c.reason() && c.garbage() {
                        cover!(true);
                        debug_assert!(c.size() == 2);
                        backtrack_level = backtrack_level.min(self.var(c.lit(0)).level);
                        log!(self, "need to backtrack to before level {}", backtrack_level);
                        j -= 1;
                        continue;
                    }
                    if !c.collect() {
                        continue;
                    }
                    log!(self, c, "removing from watch list");
                    j -= 1;
                }
                let ws = &mut self.wtab[widx];
                ws.truncate(j);
                shrink_vector(ws);
            }
        }
        self.delete_garbage_clauses();
        self.unprotect_reasons();
        if backtrack_level - 1 < self.level {
            self.backtrack(backtrack_level - 1);
        }
        stop!(self, collect);
    }

    /*----------------------------------------------------------------------*/

    pub fn arenaing(&mut self) -> bool {
        self.opts.arena != 0 && (self.stats.collections > 1)
    }

    pub fn garbage_collection(&mut self) {
        if self.unsat {
            return;
        }
        start!(self, collect);
        self.report(b'G', 1);
        self.stats.collections += 1;
        self.mark_satisfied_clauses_as_garbage();
        if !self.protected_reasons {
            self.protect_reasons();
        }
        if self.arenaing() {
            self.copy_non_garbage_clauses();
        } else {
            self.delete_garbage_clauses();
        }
        self.check_clause_stats();
        self.check_var_stats();
        self.unprotect_reasons();
        self.report(b'C', 1);
        stop!(self, collect);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn setup(n: i32) -> (Box<Internal>, Box<External>) {
        let mut internal = Internal::new();
        let ip: *mut Internal = &mut *internal;
        let mut external = External::new(ip);
        #[cfg(feature = "logging")]
        {
            internal.opts.log = 1;
        }
        external.init(n, false);
        for idx in 1..=n {
            internal.mark_active(idx);
        }
        (internal, external)
    }

    fn add(internal: &mut Internal, lits: &[i32], red: bool) -> CRef {
        internal.clause = lits.to_vec();
        let c = internal.new_clause(red, 0);
        internal.clause.clear();
        internal.watch_clause(c);
        c
    }

    #[test]
    fn moving_garbage_collector() {
        let (mut internal, external) = setup(6);
        assert!(internal.watching());
        let c1 = add(&mut internal, &[1, 2, 3], false);
        let c2 = add(&mut internal, &[-1, 4, 5], true);
        let c3 = add(&mut internal, &[2, -6], false);
        let c4 = add(&mut internal, &[-3, 5, 6, -2], false);
        assert_eq!(internal.stats.current.total, 4);
        assert_eq!(internal.stats.current.redundant, 1);
        assert_eq!(internal.stats.irrlits, 9);
        internal.mark_garbage(c2);
        internal.mark_garbage(c3);
        assert_eq!(internal.stats.current.total, 2);
        assert_eq!(internal.stats.irrlits, 7);
        assert_eq!(internal.stats.garbage.clauses, 2);
        internal.check_clause_stats();

        internal.opts.arenatype = 1;
        internal.protect_reasons();
        internal.copy_non_garbage_clauses();
        internal.unprotect_reasons();
        internal.check_clause_stats();
        assert_eq!(internal.stats.garbage.clauses, 0);
        assert_eq!(internal.stats.garbage.bytes, 0);
        assert_eq!(internal.clauses.len(), 2);
        let (d1, d4) = (internal.clauses[0], internal.clauses[1]);
        assert!(d1.addr() < d4.addr());
        assert_eq!(d1.lits(), &[1, 2, 3]);
        assert_eq!(d4.lits(), &[-3, 5, 6, -2]);
        assert_eq!(d1.addr() + d1.bytes(), d4.addr());
        assert!(internal.arena.contains(d1.as_ptr() as *const u8));
        assert_eq!(internal.watches(1).len(), 1);
        assert_eq!(internal.watches(1)[0].clause, d1);
        assert_eq!(internal.watches(1)[0].blit, 2);
        assert_eq!(internal.watches(-3).len(), 1);
        assert_eq!(internal.watches(-3)[0].clause, d4);
        assert!(internal.watches(-1).is_empty());
        assert!(internal.watches(-6).is_empty());
        let _ = (c1, c4);

        // Second collection moves out of the old arena and deletes.
        internal.mark_garbage(d1);
        internal.opts.arenacompact = 1;
        internal.protect_reasons();
        internal.copy_non_garbage_clauses();
        internal.unprotect_reasons();
        internal.check_clause_stats();
        assert_eq!(internal.clauses.len(), 1);
        assert_eq!(internal.clauses[0].lits(), &[-3, 5, 6, -2]);
        assert_eq!(internal.watches(5)[0].clause, internal.clauses[0]);

        // Non moving collector.
        add(&mut internal, &[4, 5], false);
        let e = add(&mut internal, &[1, -4, 6], true);
        internal.mark_garbage(e);
        internal.protect_reasons();
        internal.delete_garbage_clauses();
        internal.unprotect_reasons();
        internal.check_clause_stats();
        assert_eq!(internal.clauses.len(), 2);
        assert!(internal.watches(1).is_empty());
        assert_eq!(internal.watches(4).len(), 1);
        assert!(internal.watches(4)[0].binary());
        drop(internal);
        drop(external);
    }

    #[test]
    fn flip_literal() {
        let (mut internal, external) = setup(3);
        let c = add(&mut internal, &[1, 2, 3], false);
        // Assign 1 = true, 2 = false, 3 = true on level 0.
        for (k, &lit) in [1, -2, 3].iter().enumerate() {
            internal.set_val(lit, 1);
            let v = internal.var_mut(lit);
            v.level = 0;
            v.trail = k as i32;
            internal.trail.push(lit);
        }
        internal.propagated = 3;
        internal.propergated = 3;
        assert!(internal.flippable(1));
        assert!(internal.flip(1));
        assert_eq!(internal.val(1), -1);
        assert_eq!(internal.trail, vec![-1, -2, 3]);
        assert_eq!(c.lits(), &[2, 3, 1]);
        assert_eq!(c.pos(), 2);
        assert!(internal.watches(1).is_empty());
        assert_eq!(internal.watches(3).len(), 1);
        assert_eq!(internal.watches(3)[0].blit, 1);
        // Now 3 is the only true literal left, not flippable.
        assert!(!internal.flippable(3));
        assert!(!internal.flip(3));
        assert_eq!(internal.val(3), 1);
        drop(internal);
        drop(external);
    }
}

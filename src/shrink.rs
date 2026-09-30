//! Port of `shrink.cpp`.
//!
//! The C++ `std::vector<int>::reverse_iterator` arguments into `clause`
//! are `usize` positions counted from `rbegin` (so reverse position `r`
//! denotes `clause[clause.len () - 1 - r]` and `rend ()` is
//! `clause.len ()`).

#[allow(unused_imports)]
use crate::prelude::*;

impl Internal {
    /// `*r` for a reverse position into `clause`.
    #[inline(always)]
    fn clause_rget(&self, r: usize) -> i32 {
        let n = self.clause.len();
        debug_assert!(r < n);
        self.clause[n - 1 - r]
    }

    /// `*r = lit` for a reverse position into `clause`.
    #[inline(always)]
    fn clause_rset(&mut self, r: usize, lit: i32) {
        let n = self.clause.len();
        debug_assert!(r < n);
        self.clause[n - 1 - r] = lit;
    }

    pub fn reset_shrinkable(&mut self) {
        #[cfg(feature = "logging")]
        let mut reset: usize = 0;
        for k in 0..self.shrinkable.len() {
            let lit = self.shrinkable[k];
            log!(self, "resetting lit {}", lit);
            let f = self.flags_mut(lit);
            debug_assert!(f.shrinkable);
            f.shrinkable = false;
            #[cfg(feature = "logging")]
            {
                reset += 1;
            }
        }
        log!(self, "resetting {} shrinkable variables", reset);
    }

    pub fn mark_shrinkable_as_removable(&mut self, blevel: i32, minimized_start: usize) {
        #[cfg(feature = "logging")]
        let mut marked: usize = 0;
        #[cfg(feature = "logging")]
        let mut reset: usize = 0;
        #[cfg(debug_assertions)]
        {
            let mut kept: u32 = 0;
            let mut minireset: u32 = 0;
            let mut ms = minimized_start;
            while ms < self.minimized.len() {
                let lit = self.minimized[ms];
                let f = self.flags(lit);
                let v = self.var(lit);
                if v.level == blevel {
                    debug_assert!(!f.poison);
                    minireset += 1;
                } else {
                    kept += 1;
                }
                ms += 1;
            }
            let _ = (kept, minireset);
        }
        let _ = (blevel, minimized_start);

        for k in 0..self.shrinkable.len() {
            let lit = self.shrinkable[k];
            let idx = self.vidx(lit) as usize;
            let f = &mut self.ftab[idx];
            debug_assert!(f.shrinkable);
            debug_assert!(!f.poison);
            f.shrinkable = false;
            #[cfg(feature = "logging")]
            {
                reset += 1;
            }
            if f.removable {
                continue;
            }
            f.removable = true;
            self.minimized.push(lit);
            #[cfg(feature = "logging")]
            {
                marked += 1;
            }
        }
        log!(self, "resetting {} shrinkable variables", reset);
        log!(self, "marked {} removable variables", marked);
    }

    #[inline]
    pub fn shrink_literal(&mut self, lit: i32, blevel: i32, max_trail: u32) -> i32 {
        debug_assert!(self.val(lit) < 0);

        let idx = self.vidx(lit) as usize;
        debug_assert!(self.vtab[idx].level <= blevel);

        if self.vtab[idx].level == 0 {
            log!(self, "skipping root level assigned {}", lit);
            return 0;
        }

        if self.vtab[idx].reason == self.external_reason {
            debug_assert!(self.opts.exteagerreasons == 0);
            let r = self.learn_external_reason_clause(-lit, 0, true);
            self.vtab[idx].reason = r;
            if r.is_null() {
                debug_assert!(self.vtab[idx].level == 0);
                return 0;
            }
        }
        debug_assert!(self.vtab[idx].reason != self.external_reason);
        if self.ftab[idx].shrinkable {
            log!(self, "skipping already shrinkable literal {}", lit);
            return 0;
        }

        let v_level = self.vtab[idx].level;
        if v_level < blevel {
            if self.ftab[idx].removable {
                log!(self, "skipping removable thus shrinkable {}", lit);
                return 0;
            }
            let always_minimize_on_lower_blevel = self.opts.shrink > 2;
            if always_minimize_on_lower_blevel && self.minimize_literal(-lit, 1) {
                log!(self, "minimized thus shrinkable {}", lit);
                return 0;
            }
            log!(
                self,
                "literal {} on lower blevel {} < {} not removable/shrinkable",
                lit,
                v_level as u32,
                blevel as u32
            );
            return -1;
        }

        log!(self, "marking {} as shrinkable", lit);
        {
            let f = &mut self.ftab[idx];
            f.shrinkable = true;
            f.poison = false;
        }
        self.shrinkable.push(lit);
        if self.opts.shrinkreap != 0 {
            debug_assert!((max_trail as usize) < self.trail.len());
            let dist = max_trail.wrapping_sub(self.vtab[idx].trail as u32);
            self.reap.push(dist);
        }
        1
    }

    pub fn shrunken_block_uip(
        &mut self,
        uip: i32,
        blevel: i32,
        rbegin_block: &mut usize,
        rend_block: &mut usize,
        minimized_start: usize,
        uip0: i32,
    ) -> u32 {
        debug_assert!(self.clause[0] == uip0);

        log!(self, "UIP on level {}, uip: {} (replacing by {})", blevel as u32, uip, uip0);
        debug_assert!(*rend_block > *rbegin_block);
        debug_assert!(*rend_block < self.clause.len());
        let mut block_shrunken: u32 = 0;
        self.clause_rset(*rbegin_block, -uip);
        let v = *self.var(-uip);
        {
            let l = &mut self.control[v.level as usize];
            l.seen.trail = v.trail;
            l.seen.count = 1;
        }

        if !self.flags(-uip).seen {
            self.analyzed.push(-uip);
            self.flags_mut(-uip).seen = true;
        }

        self.flags_mut(-uip).keep = true;
        let mut p = *rbegin_block + 1;
        while p != *rend_block {
            let lit = self.clause_rget(p);
            if lit == -uip0 {
                p += 1;
                continue;
            }
            self.clause_rset(p, uip0);
            // if (lit == -uip) continue;
            block_shrunken += 1;
            debug_assert!(self.clause[0] == uip0);
            p += 1;
        }
        self.mark_shrinkable_as_removable(blevel, minimized_start);
        debug_assert!(self.clause[0] == uip0);
        block_shrunken
    }

    #[inline]
    pub fn shrunken_block_no_uip(
        &mut self,
        rbegin_block: usize,
        rend_block: usize,
        block_minimized: &mut u32,
        uip0: i32,
    ) {
        stop!(self, shrink);
        start!(self, minimize);
        debug_assert!(rend_block > rbegin_block);
        log!(self, "no UIP found, now minimizing");
        let mut p = rbegin_block;
        while p != rend_block {
            debug_assert!(p != self.clause.len() - 1);
            let lit = self.clause_rget(p);
            if self.opts.minimize != 0 && self.minimize_literal(-lit, 0) {
                debug_assert!(!self.flags(lit).keep);
                *block_minimized += 1;
                self.clause_rset(p, uip0);
            } else {
                self.flags_mut(lit).keep = true;
                debug_assert!(self.flags(lit).keep);
            }
            p += 1;
        }
        stop!(self, minimize);
        start!(self, shrink);
    }

    pub fn push_literals_of_block(&mut self, rbegin_block: usize, rend_block: usize, blevel: i32, max_trail: u32) {
        debug_assert!(rbegin_block < rend_block);
        let mut p = rbegin_block;
        while p != rend_block {
            debug_assert!(p != self.clause.len() - 1);
            debug_assert!(!self.flags(self.clause_rget(p)).keep);
            let lit = self.clause_rget(p);
            log!(self, "pushing lit {} of blevel {}", lit, self.var(lit).level);
            let tmp = self.shrink_literal(lit, blevel, max_trail);
            debug_assert!(tmp > 0);
            let _ = tmp;
            p += 1;
        }
    }

    #[inline]
    pub fn shrink_next(&mut self, blevel: i32, open: &mut u32, max_trail: &mut u32) -> u32 {
        let _ = blevel;
        if self.opts.shrinkreap != 0 {
            debug_assert!(!self.reap.empty());
            let dist = self.reap.pop();
            *open -= 1;
            debug_assert!(dist <= *max_trail);
            let pos = max_trail.wrapping_sub(dist);
            debug_assert!((pos as usize) < self.trail.len());
            let uip = self.trail[pos as usize];
            debug_assert!(self.val(uip) > 0);
            log!(self, "trying to shrink literal {} at trail[{}] and level {}", uip, pos, blevel);
            uip as u32
        } else {
            let mut uip;
            #[cfg(debug_assertions)]
            let init_max_trail = *max_trail;
            loop {
                #[cfg(debug_assertions)]
                debug_assert!(*max_trail <= init_max_trail);
                uip = self.trail[*max_trail as usize];
                *max_trail = max_trail.wrapping_sub(1);
                if self.flags(uip).shrinkable {
                    break;
                }
            }
            *open -= 1;
            log!(self, "open is now {}, uip = {}, level {}", *open as i32, uip, blevel);
            uip as u32
        }
    }

    #[inline]
    pub fn shrink_along_reason(
        &mut self,
        uip: i32,
        blevel: i32,
        resolve_large_clauses: bool,
        failed_ptr: &mut bool,
        max_trail: u32,
    ) -> u32 {
        log!(self, "shrinking along the reason of lit {}", uip);
        let mut open: u32 = 0;
        let v = *self.var(uip);

        debug_assert!(self.flags(uip).shrinkable);
        debug_assert!(v.level == blevel);
        debug_assert!(!v.reason.is_null());

        if self.opts.minimizeticks != 0 {
            self.stats.ticks.search[self.stable as usize] += 1;
        }

        let c = v.reason;
        if resolve_large_clauses || c.size() == 2 {
            log!(self, c, "resolving with reason");
            let size = c.size() as usize;
            for i in 0..size {
                let lit = c.lit(i);
                if lit == uip {
                    continue;
                }
                debug_assert!(self.val(lit) < 0);
                let tmp = self.shrink_literal(lit, blevel, max_trail);
                if tmp < 0 {
                    *failed_ptr = true;
                    break;
                }
                if tmp > 0 {
                    open += 1;
                }
            }
        } else {
            *failed_ptr = true;
        }
        open
    }

    #[allow(clippy::too_many_arguments)]
    pub fn shrink_block(
        &mut self,
        rbegin_lits: &mut usize,
        rend_block: &mut usize,
        blevel: i32,
        open: &mut u32,
        block_minimized: &mut u32,
        uip0: i32,
        max_trail: u32,
    ) -> u32 {
        debug_assert!(self.shrinkable.is_empty());
        debug_assert!(blevel <= self.level);
        debug_assert!((*open as usize) < self.clause.len());
        debug_assert!(*rend_block < self.clause.len());
        debug_assert!(*rbegin_lits < *rend_block);
        debug_assert!(self.opts.shrink != 0);

        #[cfg(feature = "logging")]
        {
            log!(self, "trying to shrink {} literals on level {}", *open, blevel as u32);
            log!(self, "maximum trail position {} on level {}", self.trail.len(), blevel as u32);
            if self.opts.shrinkreap != 0 {
                log!(self, "shrinking up to {}", max_trail);
            }
        }

        let resolve_large_clauses = self.opts.shrink > 1;
        let mut failed = false;
        let mut block_shrunken: u32 = 0;
        let minimized_start = self.minimized.len();
        let mut uip = uip0;
        let mut max_trail = max_trail;
        let max_trail2 = max_trail;

        if !failed {
            self.push_literals_of_block(*rbegin_lits, *rend_block, blevel, max_trail);
            debug_assert!(self.opts.shrinkreap == 0 || self.reap.size() == *open as usize);

            debug_assert!(*open > 0);
            while !failed {
                debug_assert!(self.opts.shrinkreap == 0 || self.reap.size() == *open as usize);
                uip = self.shrink_next(blevel, open, &mut max_trail) as i32;
                if *open == 0 {
                    break;
                }
                *open += self.shrink_along_reason(uip, blevel, resolve_large_clauses, &mut failed, max_trail2);
                debug_assert!(*open >= 1);
            }

            if !failed {
                log!(self, "shrinking found UIP {} on level {} (open: {})", uip, blevel, *open as i32);
            } else {
                log!(self, "shrinking failed on level {}", blevel);
            }
        }

        if failed {
            self.reset_shrinkable();
            self.shrunken_block_no_uip(*rbegin_lits, *rend_block, block_minimized, uip0);
        } else {
            block_shrunken =
                self.shrunken_block_uip(uip, blevel, rbegin_lits, rend_block, minimized_start, uip0);
        }

        if self.opts.shrinkreap != 0 {
            self.reap.clear();
        }
        self.shrinkable.clear();
        block_shrunken
    }

    // Finds the beginning of the block (rend_block, non-included) ending at
    // rend_block (included). Then tries to shrinks and minimizes literals
    // the block
    pub fn minimize_and_shrink_block(
        &mut self,
        rbegin_block: &mut usize,
        total_shrunken: &mut u32,
        total_minimized: &mut u32,
        uip0: i32,
    ) -> usize {
        log!(self, "shrinking block");
        debug_assert!(*rbegin_block < self.clause.len() - 1);
        let blevel: i32;
        let mut open: u32 = 0;
        let mut max_trail: u32;

        // find begining of block;
        let mut rend_block: usize;
        {
            debug_assert!(*rbegin_block <= self.clause.len());
            let lit = self.clause_rget(*rbegin_block);
            let idx = self.vidx(lit) as usize;
            blevel = self.vtab[idx].level;
            max_trail = self.vtab[idx].trail as u32;
            log!(self, "Block at level {} (first lit: {})", blevel, lit);

            rend_block = *rbegin_block;
            loop {
                debug_assert!(rend_block < self.clause.len() - 1);
                rend_block += 1;
                let lit = self.clause_rget(rend_block);
                let idx = self.vidx(lit) as usize;
                let finished = blevel != self.vtab[idx].level;
                if !finished && (self.vtab[idx].trail as u32) > max_trail {
                    max_trail = self.vtab[idx].trail as u32;
                }
                open += 1;
                log!(
                    self,
                    "testing if lit {} is on the same level (of lit: {}, global: {})",
                    lit,
                    self.vtab[idx].level,
                    blevel
                );
                if finished {
                    break;
                }
            }
        }
        debug_assert!(open > 0);
        debug_assert!((open as usize) < self.clause.len());
        debug_assert!(*rbegin_block < self.clause.len());
        debug_assert!(rend_block < self.clause.len());

        let mut block_shrunken: u32 = 0;
        let mut block_minimized: u32 = 0;
        if open < 2 {
            let lit = self.clause_rget(*rbegin_block);
            self.flags_mut(lit).keep = true;
            self.minimized.push(lit);
        } else {
            block_shrunken = self.shrink_block(
                rbegin_block,
                &mut rend_block,
                blevel,
                &mut open,
                &mut block_minimized,
                uip0,
                max_trail,
            );
        }

        log!(
            self,
            "shrunken {} literals on level {} (including {} minimized)",
            block_shrunken,
            blevel as u32,
            block_minimized
        );

        *total_shrunken += block_shrunken;
        *total_minimized += block_minimized;

        rend_block
    }

    pub fn shrink_and_minimize_clause(&mut self) {
        debug_assert!(self.opts.minimize != 0 || self.opts.shrink > 0);
        log!(self, &self.clause, "shrink first UIP clause");

        start!(self, shrink);
        self.external().check_learned_clause(); // check 1st UIP learned clause first
        {
            // Smaller level and trail.  Comparing literals on their level
            // is necessary for chronological backtracking, since trail
            // order might in this case not respect level order
            // ('shrink_trail_negative_rank' and 'shrink_trail_larger').
            let limit = self.opts.radixsortlim as usize;
            let vtab = &self.vtab;
            let rank = |a: &i32| -> u64 {
                let v = &vtab[a.unsigned_abs() as usize];
                let mut res: u64 = v.level as u64;
                res <<= 32;
                res |= v.trail as u64;
                !res
            };
            crate::radix::msort(limit, &mut self.clause, rank, |a: &i32, b: &i32| rank(a) < rank(b));
        }
        let mut total_shrunken: u32 = 0;
        let mut total_minimized: u32 = 0;

        log!(self, &self.clause, "shrink first UIP clause (asserting lit: {})", self.clause[0]);

        let rend_lits = self.clause.len() - 1;
        let mut rend_block: usize = 0;
        let uip0 = self.clause[0];

        // for direct LRAT we remember how the clause used to look
        let mut old_clause_lrat: Vec<i32> = Vec::new();
        debug_assert!(self.minimize_chain.is_empty());
        if self.lrat {
            for &i in &self.clause {
                old_clause_lrat.push(i);
            }
        }

        while rend_block != rend_lits {
            rend_block = self.minimize_and_shrink_block(
                &mut rend_block,
                &mut total_shrunken,
                &mut total_minimized,
                uip0,
            );
        }

        log!(self, &self.clause, "post shrink pass (with uips, not removed) first UIP clause");
        log!(self, &old_clause_lrat, "(used for lratdirect) before shrink: clause");
        #[cfg(any(feature = "logging", debug_assertions))]
        let old_size = self.clause.len() as u32;
        let mut stack: Vec<i32> = Vec::new();
        {
            let mut i: usize = 1;
            let mut j: usize = 1;
            while j < self.clause.len() {
                debug_assert!(i <= j);
                self.clause[i] = self.clause[j];
                if self.lrat {
                    debug_assert!(j < old_clause_lrat.len());
                    debug_assert!(self.mini_chain.is_empty());
                    if self.clause[j] != old_clause_lrat[j] {
                        self.calculate_minimize_chain(-old_clause_lrat[j], &mut stack);
                        for k in 0..self.mini_chain.len() {
                            let p = self.mini_chain[k];
                            self.minimize_chain.push(p);
                        }
                        self.mini_chain.clear();
                    }
                }
                if self.clause[j] == uip0 {
                    j += 1;
                    continue;
                }
                debug_assert!(self.flags(self.clause[i]).keep);
                i += 1;
                log!(self, "keeping literal {}", self.clause[j]);
                j += 1;
            }
            self.clause.truncate(i);
        }
        #[cfg(debug_assertions)]
        debug_assert!(old_size == self.clause.len() as u32 + total_shrunken + total_minimized);
        log!(self, &self.clause, "after shrinking first UIP clause");
        log!(
            self,
            "clause shrunken by {} literals (including {} minimized)",
            old_size as usize - self.clause.len(),
            total_minimized
        );

        self.stats.shrunken += total_shrunken as i64;
        self.stats.minishrunken += total_minimized as i64;
        stop!(self, shrink);

        start!(self, minimize);
        self.clear_minimized_literals();
        for k in (0..self.minimize_chain.len()).rev() {
            let p = self.minimize_chain[k];
            self.lrat_chain.push(p);
        }
        self.minimize_chain.clear();
        stop!(self, minimize);
    }
}

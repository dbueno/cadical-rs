//! Port of `backbone.cpp`.

#[allow(unused_imports)]
use crate::prelude::*;

impl Internal {
    #[inline]
    pub fn backbone_lrat_for_units(&mut self, lit: i32, reason: CRef) {
        if !self.lrat {
            return;
        }
        if self.level != 0 {
            return; // not decision level 0
        }
        log!(self, "backbone building chain for units");
        debug_assert!(self.lrat_chain.is_empty());
        debug_assert!(reason.is_some());
        for i in 0..reason.size() as usize {
            let reason_lit = reason.lit(i);
            if lit == reason_lit {
                continue;
            }
            debug_assert!(self.val(reason_lit) != 0);
            if self.val(reason_lit) == 0 {
                continue;
            }
            let signed_reason_lit = self.val(reason_lit) as i32 * reason_lit;
            let id = self.unit_id(signed_reason_lit);
            self.lrat_chain.push(id);
        }
        self.lrat_chain.push(reason.id());
    }

    #[inline]
    pub fn backbone_propagate(&mut self, ticks: &mut i64) -> bool {
        self.require_mode(Mode::BACKBONE);
        debug_assert!(!self.unsat);
        start!(self, propagate);
        self.propagated2 = self.propagated;
        let before = self.propagated2 as i64;
        loop {
            if self.propagated2 != self.trail.len() {
                let lit = -self.trail[self.propagated2];
                self.propagated2 += 1;
                log!(self, "backbone propagating {} over binary clauses", -lit);
                let widx = self.vlit(lit) as usize;
                let size = self.wtab[widx].len();
                *ticks += 1 + self.cache_lines_n(size, std::mem::size_of::<*const Watch>());
                for k in 0..size {
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
                        self.backbone_assign(w.blit, w.clause);
                        self.lrat_chain.clear();
                    }
                }
            } else if self.conflict.is_null() && self.propagated != self.trail.len() {
                let lit = -self.trail[self.propagated];
                self.propagated += 1;
                log!(self, "backbone propagating {} over large clauses", -lit);
                let widx = self.vlit(lit) as usize;
                let eow = self.wtab[widx].len();
                let mut i = 0usize;
                *ticks += 1 + self.cache_lines_n(eow, std::mem::size_of::<Watch>());
                let mut j = 0usize;
                while i != eow {
                    let w = self.wtab[widx][i];
                    self.wtab[widx][j] = w;
                    i += 1;
                    j += 1;
                    if w.binary() {
                        continue;
                    }
                    if self.val(w.blit) > 0 {
                        continue;
                    }
                    *ticks += 1;
                    if w.clause.garbage() {
                        j -= 1;
                        continue;
                    }
                    let c = w.clause;
                    let other = c.lit(0) ^ c.lit(1) ^ lit;
                    let u = self.val(other);
                    if u > 0 {
                        self.wtab[widx][j - 1].blit = other;
                    } else {
                        let size = c.size() as usize;
                        let end = size;
                        let middle = c.pos() as usize;
                        let mut k = middle;
                        let mut v: i8 = -1;
                        let mut r: i32 = 0;
                        while k != end && {
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
                            self.wtab[widx][j - 1].blit = r;
                        } else if v == 0 {
                            log!(self, c, "unwatch {} in", r);
                            c.set_lit(0, other);
                            c.set_lit(1, r);
                            c.set_lit(k, lit);
                            *ticks += 1;
                            self.watch_literal(r, lit, c);
                            j -= 1;
                        } else if u == 0 {
                            *ticks += 1;
                            debug_assert!(v < 0);
                            self.build_chain_for_units(other, c, false);
                            self.backbone_assign_any(other, c);
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
                    let ws = &mut self.wtab[widx];
                    while i != eow {
                        ws[j] = ws[i];
                        j += 1;
                        i += 1;
                    }
                    ws.truncate(j);
                }
            } else {
                break;
            }
        }
        let delta = self.propagated2 as i64 - before;
        self.stats.propagations.backbone += delta;
        if self.conflict.is_some() {
            log!(self, self.conflict, "conflict");
        }
        stop!(self, propagate);
        self.conflict.is_null()
    }

    #[inline]
    pub fn backbone_propagate2(&mut self, ticks: &mut i64) {
        self.require_mode(Mode::BACKBONE);
        debug_assert!(self.propagated2 <= self.trail.len());
        let before = self.propagated2 as i64;
        while self.propagated2 != self.trail.len() {
            let lit = -self.trail[self.propagated2];
            self.propagated2 += 1;
            log!(self, "probe propagating {} over binary clauses", -lit);
            let widx = self.vlit(lit) as usize;
            let size = self.wtab[widx].len();
            *ticks += 1 + self.cache_lines_n(size, std::mem::size_of::<*const Watch>());
            for k in 0..size {
                let w = self.wtab[widx][k];
                if !w.binary() {
                    break;
                }
                let b = self.val(w.blit);
                if b > 0 {
                    continue;
                }
                *ticks += 1;
                if b < 0 {
                    self.conflict = w.clause; // no need to continue
                    break;
                } else {
                    debug_assert!(self.lrat_chain.is_empty());
                    self.backbone_lrat_for_units(w.blit, w.clause);
                    self.backbone_assign(w.blit, w.clause);
                    self.lrat_chain.clear();
                }
            }
        }

        let delta = self.propagated2 as i64 - before;
        self.stats.propagations.backbone += delta;
    }

    pub fn schedule_backbone_cands(&mut self, candidates: &mut Vec<i32>) {
        let mut not_rescheduled: u32 = 0;
        for v in self.vars() {
            let f = *self.flags(v);
            if !f.active() {
                continue;
            }
            if f.backbone0 {
                log!(self, "scheduling backbone literal candidate {}", loglit!(self, v));
                candidates.push(v);
            } else {
                not_rescheduled += 1;
            }
            if f.backbone1 {
                log!(self, "scheduling backbone literal candidate {}", loglit!(self, -v));
                candidates.push(-v);
            } else {
                not_rescheduled += 1;
            }
        }

        if not_rescheduled != 0 {
            for v in self.vars() {
                let f = *self.flags(v);
                if !f.active() {
                    continue;
                }
                if !f.backbone0 {
                    log!(self, "scheduling backbone literal candidate {}", loglit!(self, v));
                    candidates.push(v);
                }
                if !f.backbone1 {
                    log!(self, "scheduling backbone literal candidate {}", loglit!(self, -v));
                    candidates.push(-v);
                }
            }
        }
        debug_assert!(candidates.len() <= 2 * self.max_var as usize);

        verbose!(
            self,
            3,
            "backbone schedule {} backbone candidates in total {} (rescheduled: {}%)",
            candidates.len(),
            crate::format::fmt_f(percent(candidates.len() as f64, (2 * self.max_var) as f64), 6),
            crate::format::fmt_f(percent(not_rescheduled as f64, (2 * self.max_var) as f64), 6)
        );
    }

    pub fn backbone_analyze(&mut self, _arg0: CRef, ticks: &mut i64) -> i32 {
        debug_assert!(self.conflict.is_some());
        debug_assert!(self.conflict.size() == 2);
        let conflict = self.conflict;
        self.analyzed.push(conflict.lit(0).abs());
        self.flags_mut(conflict.lit(0)).seen = true;
        self.analyzed.push(conflict.lit(1).abs());
        self.flags_mut(conflict.lit(1)).seen = true;
        log!(self, conflict, "analyzing conflict");
        if self.lrat {
            self.lrat_chain.push(conflict.id());
        }
        self.conflict = CRef::NULL;

        let mut t = self.trail.len();
        loop {
            debug_assert!(t > 0);
            t -= 1;
            let lit = self.trail[t];
            log!(self, "analyzing {}", loglit!(self, lit));
            if !self.flags(lit).seen {
                continue;
            }
            let reason = self.var(lit).reason;
            log!(self, reason, "resolving with reason of {}", loglit!(self, lit));
            debug_assert!(reason.is_some());
            debug_assert!(reason != Internal::decision_reason());
            *ticks += 1;
            let other = reason.lit(0) ^ reason.lit(1) ^ lit;
            if self.lrat {
                self.lrat_chain.push(reason.id());
            }
            if !self.flags(other).seen {
                self.flags_mut(other).seen = true;
                self.analyzed.push(other);
            } else {
                log!(self, "backbone UIP {}", loglit!(self, other));
                for i in 0..self.analyzed.len() {
                    let l = self.analyzed[i];
                    self.flags_mut(l).seen = false;
                }
                self.analyzed.clear();
                if self.lrat {
                    self.lrat_chain.reverse();
                }
                return other;
            }
        }
    }

    #[inline]
    pub fn backbone_unit_reassign(&mut self, lit: i32) {
        #[cfg(feature = "logging")]
        {
            log!(self, "reassigning {} to level 0", loglit!(self, lit));
            debug_assert!(self.val(lit) > 0);
            debug_assert!(self.val(-lit) < 0);
        }
        let _ = lit;
    }

    #[inline]
    pub fn backbone_unit_assign(&mut self, lit: i32) {
        log!(self, "assigning {} to level 0", loglit!(self, lit));
        self.require_mode(Mode::BACKBONE);
        let idx = self.vidx(lit);
        debug_assert!(self.val(idx) == 0);
        let trail_size = self.trail.len() as i32;
        {
            let v = self.var_mut(idx);
            v.level = 0; // required to reuse decisions
            v.trail = trail_size; // used in 'vivify_better_watch'
        }
        debug_assert!((self.num_assigned as i32) < self.max_var);
        self.num_assigned += 1;
        self.var_mut(idx).reason = CRef::NULL; // for conflict analysis
        self.learn_unit_clause(lit);
        self.lrat_chain.clear();
        let tmp = sign(lit) as i8;
        self.set_val(idx, tmp);
        debug_assert!(self.val(lit) > 0);
        debug_assert!(self.val(-lit) < 0);
        self.trail.push(lit);
        log!(self, "backbone assign {} to level 0", lit);
    }

    #[inline]
    pub fn backbone_assign_any(&mut self, lit: i32, reason: CRef) {
        self.require_mode(Mode::BACKBONE);
        let idx = self.vidx(lit);
        debug_assert!(self.val(idx) == 0);
        debug_assert!(!self.flags(idx).eliminated() || reason.is_null());
        debug_assert!(reason == Internal::decision_reason() || reason.is_null() || reason.size() >= 2);
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
        log!(self, reason, "backbone assign {}", lit);
    }

    #[inline]
    pub fn backbone_assign(&mut self, lit: i32, reason: CRef) {
        self.require_mode(Mode::BACKBONE);
        let idx = self.vidx(lit);
        debug_assert!(self.val(idx) == 0);
        debug_assert!(!self.flags(idx).eliminated() || reason.is_null());
        debug_assert!(reason == Internal::decision_reason() || reason.is_null() || reason.size() == 2);
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
        log!(self, reason, "backbone assign {}", lit);
    }

    pub fn backbone_decision(&mut self, lit: i32) {
        self.require_mode(Mode::BACKBONE);
        debug_assert!(self.propagated2 == self.trail.len());
        self.new_trail_level(lit);
        self.notify_decision();
        log!(self, "search decide {}", lit);
        self.backbone_assign(lit, Internal::decision_reason());
    }

    /// Note that `inconsistent` is passed by value in C++ too (updates are
    /// not visible to the caller).
    pub fn compute_backbone_round(
        &mut self,
        candidates: &mut Vec<i32>,
        units: &mut Vec<i32>,
        ticks_limit: i64,
        ticks: &mut i64,
        mut inconsistent: u32,
    ) -> u32 {
        debug_assert!(self.conflict.is_null());
        let mut p = 0usize;
        let mut q = p;
        let end = candidates.len();
        let mut failed: usize = 0;
        self.stats.backbone.rounds += 1;

        log!(self, &*candidates, "candidates: ");
        *ticks += 1 + self.cache_lines_n(candidates.len(), std::mem::size_of::<*const i32>());
        while p != end {
            debug_assert!(p < end);
            debug_assert!(q <= p);
            debug_assert!(self.conflict.is_null());
            candidates[q] = candidates[p];
            let probe = candidates[q];
            self.stats.backbone.probes += 1;

            p += 1;
            q += 1;
            let v = self.val(probe);
            if v > 0 {
                q -= 1;
                log!(self, "removing satisfied backbone probe {}", loglit!(self, probe));
                if probe < 0 {
                    self.flags_mut(probe).backbone1 = false;
                } else {
                    self.flags_mut(probe).backbone0 = false;
                }
                continue;
            }

            if v < 0 {
                if self.var(probe).level != 0 {
                    log!(self, "skipping falsified backbone probe {}", loglit!(self, probe));
                } else {
                    log!(self, "removing root-level falsified backbone probe {}", loglit!(self, probe));
                    q -= 1;
                }
                continue;
            }
            if *ticks >= ticks_limit {
                break;
            }
            self.backbone_decision(probe);
            self.backbone_propagate2(ticks);
            if self.conflict.is_null() {
                log!(
                    self,
                    &*candidates,
                    "propagating backbone probe {} successful; candidates:",
                    loglit!(self, probe)
                );
                continue;
            }

            failed += 1;
            self.stats.backbone.units += 1;
            let conflict = self.conflict;
            let uip = self.backbone_analyze(conflict, ticks);
            let new_level = self.level - 1;
            self.backtrack_without_updating_phases(new_level);
            self.backbone_unit_assign(uip);
            self.stats.units += 1;
            debug_assert!(self.conflict.is_null());
            if self.external().learner.is_some() {
                self.external().export_learned_unit_clause(uip);
            }

            self.backbone_propagate2(ticks);
            if self.conflict.is_some() {
                log!(self, "propagating backbone forced {} failed", loglit!(self, uip));
                inconsistent = uip as u32;
                // we have to give up on the current conflict
                self.conflict = CRef::NULL;
                break;
            }
            units.push(uip);
        }
        while p != end {
            candidates[q] = candidates[p];
            q += 1;
            p += 1;
        }
        debug_assert!(q <= end);
        candidates.truncate(q);
        log!(self, &*candidates, "candidates: ");

        if inconsistent == 0 {
            log!(self, "flushing satisfied probe candidates");
            let mut p = 0usize;
            let mut q = p;
            let end = candidates.len();

            while p != end {
                candidates[q] = candidates[p];
                let probe = candidates[q];
                q += 1;
                p += 1;
                let v = self.val(probe);
                if v > 0 {
                    q -= 1;
                    log!(self, "removing satisfied backbone probe {}", loglit!(self, probe));
                    if probe < 0 {
                        self.flags_mut(probe).backbone1 = false;
                    } else {
                        self.flags_mut(probe).backbone0 = false;
                    }
                    continue;
                }

                if v < 0 {
                    log!(self, "keeping falsified probe {}", loglit!(self, probe));
                    continue;
                }
                debug_assert!(v == 0);
                log!(self, "keeping unassigned probe {}", loglit!(self, probe));
            }
            candidates.truncate(q);
        }
        log!(self, &*candidates, "candidates after !inconsistent: ");
        if self.level != 0 {
            self.backtrack_without_updating_phases(0);
        }
        if inconsistent == 0 && !units.is_empty() {
            for i in 0..units.len() {
                let l = units[i];
                self.backbone_unit_reassign(l);
            }
            units.clear();
            if !self.backbone_propagate(ticks) {
                log!(self, self.conflict, "final repropagation yielded conflict");
                self.learn_empty_clause();
            }
        } else if !self.backbone_propagate(ticks) {
            self.learn_empty_clause();
        }
        log!(self, &*candidates, "candidates end of loop: ");

        log!(self, &*candidates, "candidates end of backbone_round: ");
        failed as u32
    }

    pub fn keep_backbone_candidates(&mut self, candidates: &[i32]) {
        let mut remain: usize = 0;
        let mut prioritized: usize = 0;
        for &v in candidates {
            let f = self.flags(v);
            if !f.active() {
                continue;
            }
            remain += 1;
            if v < 0 {
                prioritized += f.backbone1 as usize;
            } else {
                prioritized += f.backbone0 as usize;
            }
        }
        debug_assert!(prioritized <= remain);
        if remain == 0 {
            #[cfg(debug_assertions)]
            for &v in candidates {
                let f = self.flags(v);
                if !f.active() {
                    continue;
                }
                debug_assert!(!f.backbone0);
                debug_assert!(!f.backbone1);
            }
            return;
        }
        if prioritized == remain {
            log!(self, "keeping all remaining backbones");
        } else if prioritized == 0 {
            for &v in candidates {
                let f = self.flags_mut(v);
                if !f.active() {
                    continue;
                }
                remain += 1;
                if v < 0 {
                    debug_assert!(!f.backbone1);
                    f.backbone1 = true;
                } else {
                    debug_assert!(!f.backbone0);
                    f.backbone0 = true;
                }
            }
        }
        let _ = remain;
    }

    /// Helper for `SET_EFFORT_LIMIT (totalticks, backbone, false)` inside
    /// `compute_backbone` (which returns `unsigned` in C++, so the macro's
    /// `return false` cannot be expanded there directly; with threshold
    /// `false` it is never taken anyhow).
    fn backbone_set_effort_limit(&mut self, totalticks: &mut i64) -> bool {
        set_effort_limit!(self, limit, backbone, false);
        *totalticks = limit;
        true
    }

    pub fn compute_backbone(&mut self) -> u32 {
        let mut failed: usize = 0;
        if self.terminated_asynchronously(1) {
            return failed as u32;
        }

        let mut ticks: i64 = 0;
        self.backbone_propagate2(&mut ticks);
        debug_assert!(self.conflict.is_null());

        let mut candidates: Vec<i32> = Vec::new();
        let mut units: Vec<i32> = Vec::new();
        let inconsistent: u32 = 0;
        debug_assert!(self.conflict.is_null());

        self.stats.backbone.phases += 1;
        self.schedule_backbone_cands(&mut candidates);

        let max_rounds = self.opts.backbonemaxrounds as usize;
        let mut round_limit = self.opts.backbonerounds as usize;
        round_limit = round_limit.wrapping_mul(self.stats.backbone.phases as usize);
        if round_limit > max_rounds {
            round_limit = max_rounds;
        }

        let mut totalticks: i64 = 0;
        let _ = self.backbone_set_effort_limit(&mut totalticks);
        let ticks_limit = totalticks - self.stats.ticks.backbone;
        phase!(self, "backbone", self.stats.backbone.phases, "backbone limit of {} ticks", ticks_limit);
        let mut rounds: usize = 0;
        loop {
            rounds += 1;
            if rounds == 0 {
                break;
            }
            if rounds >= round_limit {
                log!(self, "backround round limit {} rounds", rounds);
                break;
            }
            if ticks >= ticks_limit {
                log!(self, "backround round limit {} ticks", ticks as u64);
                break;
            }
            verbose!(
                self,
                3,
                "backbone round {} of {} with {} ticks  ({} % done) with {} failed so far",
                rounds,
                max_rounds,
                ticks,
                crate::format::fmt_f(percent(ticks as f64, ticks_limit as f64), 6),
                failed
            );
            let new_failed =
                self.compute_backbone_round(&mut candidates, &mut units, ticks_limit, &mut ticks, inconsistent)
                    as usize;
            failed += new_failed;
            if inconsistent != 0 {
                break;
            }
            if candidates.is_empty() {
                break;
            }
            if self.unsat {
                break;
            }
        }

        if inconsistent != 0 && !self.unsat {
            log!(
                self,
                "using forced unit {} by repropagating at level 0",
                loglit!(self, inconsistent as i32)
            );
            self.backtrack_without_updating_phases(0);
            self.propagate();
            self.learn_empty_clause();
        }
        if self.unsat {
            phase!(self, "backbone", self.stats.backbone.phases, "inconsistent binary clauses");
        } else {
            phase!(
                self,
                "backbone",
                self.stats.backbone.phases,
                "found {} backbone literals {} round in {} ticks",
                failed,
                rounds,
                ticks
            );
        }

        self.keep_backbone_candidates(&candidates);
        if self.level != 0 {
            self.backtrack_without_updating_phases(0);
            if !self.backbone_propagate(&mut ticks) {
                self.learn_empty_clause();
            }
        }
        self.stats.ticks.backbone += ticks;
        failed as u32
    }

    pub fn binary_clauses_backbone(&mut self) {
        if self.unsat {
            return;
        }
        if self.opts.backbone == 0 {
            return;
        }
        if self.terminated_asynchronously(1) {
            return;
        }
        if self.level != 0 {
            self.backtrack_without_updating_phases(0);
        }
        self.propagated2 = 0; // TODO: why?
        if !self.propagate() {
            log!(self, "propagation after connecting watches in inconsistency");
            self.learn_empty_clause();
            return;
        }

        for lit in self.lits() {
            let widx = self.vlit(lit) as usize;
            let w = &mut self.wtab[widx];
            // std::stable_partition (binary watches first).
            let mut bin: Watches = Vec::with_capacity(w.len());
            let mut rest: Watches = Vec::new();
            for &x in w.iter() {
                if x.binary() {
                    bin.push(x);
                } else {
                    rest.push(x);
                }
            }
            let n = bin.len();
            w[..n].copy_from_slice(&bin);
            w[n..].copy_from_slice(&rest);
        }
        debug_assert!(self.propagated2 <= self.trail.len());
        self.private_steps = true;

        debug_assert!(self.watching());
        start_simplifier!(self, backbone, BACKBONE);
        let failed = self.compute_backbone() as i32;
        debug_assert!(self.level == 0);
        self.private_steps = false;

        self.report(b'k', (failed == 0) as i32);
        stop_simplifier!(self, backbone, BACKBONE);
    }
}

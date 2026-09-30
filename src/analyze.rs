//! Port of `analyze.cpp`.

#[allow(unused_imports)]
use crate::prelude::*;

/*------------------------------------------------------------------------*/

// Code for conflict analysis, i.e., to generate the first UIP clause.  The
// main function is 'analyze' below.  It further uses 'minimize' to
// minimize the first UIP clause, which is in 'minimize.cpp'.  An important
// side effect of conflict analysis is to update the decision queue by
// bumping variables.  Similarly analyzed clauses are bumped to mark them
// as active.

/*------------------------------------------------------------------------*/

// It would be better to use 'isinf' but there are some historical issues
// with this function.  We simply put a hard limit here (as in older solvers
// since the MiniSAT team invented EVSIDS).

#[inline(always)]
fn evsids_limit_hit(score: f64) -> bool {
    score > 1e150 // MAX_DOUBLE is around 1.8e308
}

/*------------------------------------------------------------------------*/

// Smaller level and trail.  Comparing literals on their level is necessary
// for chronological backtracking, since trail order might in this case not
// respect level order ('analyze_trail_negative_rank').

#[inline(always)]
fn analyze_trail_negative_rank(vtab: &[Var], a: i32) -> u64 {
    let v = &vtab[a.unsigned_abs() as usize];
    let mut res: u64 = v.level as u64;
    res <<= 32;
    res |= v.trail as u64;
    !res
}

impl Internal {
    pub fn learn_empty_clause(&mut self) {
        debug_assert!(!self.unsat);
        self.build_chain_for_empty();
        log!(self, "learned empty clause");
        self.external().check_learned_empty_clause();
        self.clause_id += 1;
        let id = self.clause_id;
        if let Some(proof) = self.proof.as_mut() {
            proof.add_derived_empty_clause(id, &self.lrat_chain);
        }
        self.unsat = true;
        self.conflict_id = id;
        self.marked_failed = true;
        self.conclusion.push(id);
        self.lrat_chain.clear();
    }

    pub fn learn_unit_clause(&mut self, lit: i32) {
        debug_assert!(!self.unsat);
        log!(self, "learned unit clause {}, stored at position {}", lit, self.vlit(lit));
        self.external().check_learned_unit_clause(lit);
        self.clause_id += 1;
        let id = self.clause_id;
        if self.lrat || self.frat {
            let uidx = self.vlit(lit);
            *self.unit_clauses(uidx as i32) = id;
        }
        if let Some(proof) = self.proof.as_mut() {
            proof.add_derived_unit_clause(id, lit, &self.lrat_chain);
        }
        self.mark_fixed(lit);
    }

    /*--------------------------------------------------------------------*/

    // Move bumped variables to the front of the (VMTF) decision queue.  The
    // 'bumped' time stamp is updated accordingly.  It is used to determine
    // whether the 'queue.assigned' pointer has to be moved in 'unassign'.

    pub fn bump_queue(&mut self, lit: i32) {
        debug_assert!(self.opts.bump != 0);
        let idx = self.vidx(lit);
        if self.links[idx as usize].next == 0 {
            return;
        }
        self.queue.dequeue(&mut self.links, idx);
        self.queue.enqueue(&mut self.links, idx);
        debug_assert!(self.stats.bumped != i64::MAX);
        self.stats.bumped += 1;
        self.btab[idx as usize] = self.stats.bumped;
        log!(self, "moved to front variable {} and bumped to {}", idx, self.btab[idx as usize]);
        if self.val(idx) == 0 {
            self.update_queue_unassigned(idx);
        }
    }

    /*--------------------------------------------------------------------*/

    // Classical exponential VSIDS as pioneered by MiniSAT.

    pub fn rescale_variable_scores(&mut self) {
        self.stats.rescored += 1;
        let mut divider = self.score_inc;
        for idx in self.vars() {
            let tmp = self.stab[idx as usize];
            if tmp > divider {
                divider = tmp;
            }
        }
        phase!(
            self,
            "rescore",
            self.stats.rescored,
            "rescoring {} variable scores by 1/{}",
            self.max_var,
            crate::format::fmt_g(divider)
        );
        debug_assert!(divider > 0.0);
        let factor = 1.0 / divider;
        for idx in self.vars() {
            self.stab[idx as usize] *= factor;
        }
        self.score_inc *= factor;
        phase!(
            self,
            "rescore",
            self.stats.rescored,
            "new score increment {} after {} conflicts",
            crate::format::fmt_g(self.score_inc),
            self.stats.conflicts
        );
    }

    pub fn bump_variable_score(&mut self, lit: i32) {
        debug_assert!(self.opts.bump != 0);
        let idx = self.vidx(lit);
        let mut old_score = self.score(idx);
        debug_assert!(!evsids_limit_hit(old_score));
        let mut new_score = old_score + self.score_inc;
        if evsids_limit_hit(new_score) {
            log!(
                self,
                "bumping {} score of {} hits EVSIDS score limit",
                crate::format::fmt_g(old_score),
                idx
            );
            self.rescale_variable_scores();
            old_score = self.score(idx);
            debug_assert!(!evsids_limit_hit(old_score));
            new_score = old_score + self.score_inc;
        }
        debug_assert!(!evsids_limit_hit(new_score));
        log!(self, "new {} score of {}", crate::format::fmt_g(new_score), idx);
        *self.score_mut(idx) = new_score;
        if self.scores.contains(idx as u32) {
            self.scores.update(idx as u32);
        }
    }

    // Important variables recently used in conflict analysis are 'bumped',

    pub fn bump_variable(&mut self, lit: i32) {
        if self.use_scores() {
            self.bump_variable_score(lit);
        } else {
            self.bump_queue(lit);
        }
    }

    // After every conflict the variable score increment is increased by a
    // factor (if we are currently using scores).

    pub fn bump_variable_score_inc(&mut self) {
        debug_assert!(self.use_scores());
        debug_assert!(!evsids_limit_hit(self.score_inc));
        let f = 1e3 / self.opts.scorefactor as f64;
        let mut new_score_inc = self.score_inc * f;
        if evsids_limit_hit(new_score_inc) {
            log!(
                self,
                "bumping {} increment by {} hits EVSIDS score limit",
                crate::format::fmt_g(self.score_inc),
                crate::format::fmt_g(f)
            );
            self.rescale_variable_scores();
            new_score_inc = self.score_inc * f;
        }
        debug_assert!(!evsids_limit_hit(new_score_inc));
        log!(
            self,
            "bumped score increment from {} to {} with factor {}",
            crate::format::fmt_g(self.score_inc),
            crate::format::fmt_g(new_score_inc),
            crate::format::fmt_g(f)
        );
        self.score_inc = new_score_inc;
    }

    /*--------------------------------------------------------------------*/

    pub fn bump_variables(&mut self) {
        debug_assert!(self.opts.bump != 0);

        start!(self, bump);

        if !self.use_scores() {
            // Variables are bumped in the order they are in the current
            // decision queue.  This maintains relative order between bumped
            // variables in the queue and seems to work best.  We also
            // experimented with focusing on variables of the last decision
            // level, but results were mixed.

            // 'analyze_bumped_rank' and 'analyze_bumped_smaller'.
            let limit = self.opts.radixsortlim as usize;
            let btab = &self.btab;
            let rank = |a: &i32| -> u64 { btab[a.unsigned_abs() as usize] as u64 };
            crate::radix::msort(limit, &mut self.analyzed, rank, |a: &i32, b: &i32| rank(a) < rank(b));
        }

        for k in 0..self.analyzed.len() {
            let lit = self.analyzed[k];
            self.bump_variable(lit);
        }

        if self.use_scores() {
            self.bump_variable_score_inc();
        }

        stop!(self, bump);
    }

    /*--------------------------------------------------------------------*/

    // We use the glue time stamp table 'gtab' for fast glue computation.

    pub fn recompute_glue(&mut self, c: CRef) -> i32 {
        let mut res = 0;
        self.stats.recomputed += 1;
        let stamp = self.stats.recomputed;
        let size = c.size() as usize;
        for i in 0..size {
            let lit = c.lit(i);
            debug_assert!(self.val(lit) != 0);
            let level = self.var(lit).level as usize;
            debug_assert!(self.gtab[level] <= stamp);
            if self.gtab[level] == stamp {
                continue;
            }
            self.gtab[level] = stamp;
            res += 1;
        }
        res
    }

    // Clauses resolved since the last reduction are marked as 'used', their
    // glue is recomputed and they are promoted if the glue shrinks.  Note
    // that promotion from 'tier3' to 'tier2' will set 'used' to '2'.

    #[inline]
    pub fn bump_clause(&mut self, c: CRef) {
        log!(self, c, "bumping");
        c.set_used(Internal::MAX_USED);
        if c.hyper() {
            return;
        }
        if !c.redundant() {
            return;
        }
        let new_glue = self.recompute_glue(c);
        if new_glue < c.glue() {
            self.promote_clause(c, new_glue);
        }

        let s = self.stable as usize;
        let glue = std::cmp::min(c.glue() as usize, self.stats.used[s].len() - 1);
        self.stats.used[s][glue] += 1;
        self.stats.bump_used[s] += 1;
    }

    pub fn bump_clause2(&mut self, c: CRef) {
        self.bump_clause(c);
    }

    /*--------------------------------------------------------------------*/

    // During conflict analysis literals not seen yet either become part of
    // the first unique implication point (UIP) clause (if on lower decision
    // level), are dropped (if fixed), or are resolved away (if on the
    // current decision level and different from the first UIP).  At the
    // same time we update the number of seen literals on a decision level.
    // This helps conflict clause minimization.  The number of seen levels
    // is the glucose level (also called 'glue', or 'LBD').

    #[inline]
    pub fn analyze_literal(&mut self, lit: i32, open: &mut i32, resolvent_size: &mut i32, antecedent_size: &mut i32) {
        debug_assert!(lit != 0);
        let idx = self.vidx(lit) as usize;

        if self.vtab[idx].level == 0 {
            if self.ftab[idx].seen || !self.lrat {
                return;
            }
            self.ftab[idx].seen = true;
            self.unit_analyzed.push(lit);
            debug_assert!(self.val(lit) < 0);
            let id = self.unit_id(-lit);
            self.unit_chain.push(id);
            return;
        }
        *antecedent_size += 1;
        if self.ftab[idx].seen {
            return;
        }

        // before marking as seen, get reason and check for missed unit

        debug_assert!(self.val(lit) < 0);
        debug_assert!(self.vtab[idx].level <= self.level);
        if self.vtab[idx].reason == self.external_reason {
            debug_assert!(self.opts.exteagerreasons == 0);
            let r = self.learn_external_reason_clause(-lit, 0, true);
            self.vtab[idx].reason = r;
            if r.is_null() {
                // actually a unit
                *antecedent_size -= 1;
                log!(self, "{} unit after explanation", -lit);
                if self.ftab[idx].seen || !self.lrat {
                    return;
                }
                self.ftab[idx].seen = true;
                self.unit_analyzed.push(lit);
                debug_assert!(self.val(lit) < 0);
                let uidx = self.vlit(-lit);
                let id = *self.unit_clauses(uidx as i32);
                debug_assert!(id != 0);
                self.unit_chain.push(id);
                return;
            }
        }

        self.ftab[idx].seen = true;
        self.analyzed.push(lit);

        let v = self.vtab[idx];
        debug_assert!(v.reason != self.external_reason);
        if v.level < self.level {
            self.clause.push(lit);
        }
        let l = &mut self.control[v.level as usize];
        let count = l.seen.count;
        l.seen.count += 1;
        if v.trail < l.seen.trail {
            l.seen.trail = v.trail;
        }
        if count == 0 {
            log!(self, "found new level {} contributing to conflict", v.level);
            self.levels.push(v.level);
        }
        *resolvent_size += 1;
        log!(self, "analyzed literal {} assigned at level {}", lit, v.level);
        if v.level == self.level {
            *open += 1;
        }
    }

    #[inline]
    pub fn analyze_reason(
        &mut self,
        lit: i32,
        reason: CRef,
        open: &mut i32,
        resolvent_size: &mut i32,
        antecedent_size: &mut i32,
    ) {
        debug_assert!(!reason.is_null());
        debug_assert!(reason != self.external_reason);
        self.bump_clause(reason);
        if self.lrat {
            self.lrat_chain.push(reason.id());
        }
        let size = reason.size() as usize;
        for i in 0..size {
            let other = reason.lit(i);
            if other != lit {
                self.analyze_literal(other, open, resolvent_size, antecedent_size);
            }
        }
    }

    /*--------------------------------------------------------------------*/

    // This is an idea which was implicit in MapleCOMSPS 2016 for 'limit =
    // 1'.  See also the paragraph on 'bumping reason side literals' in
    // their SAT'16 paper [LiangGaneshPoupartCzarnecki-SAT'16].  (See the
    // C++ source for the full history.)

    #[inline]
    pub fn bump_also_reason_literal(&mut self, lit: i32) -> bool {
        debug_assert!(lit != 0);
        debug_assert!(self.val(lit) < 0);
        let idx = self.vidx(lit) as usize;
        if self.ftab[idx].seen {
            return false;
        }
        let level = self.vtab[idx].level;
        if level == 0 {
            return false;
        }
        self.ftab[idx].seen = true;
        self.analyzed.push(lit);
        log!(self, "bumping also reason literal {} assigned at level {}", lit, level);
        true
    }

    // We experimented with deeper reason bumping without much success
    // though.

    #[inline]
    pub fn bump_also_reason_literals(&mut self, lit: i32, depth_limit: i32, analyzed_limit: usize) {
        debug_assert!(lit != 0);
        debug_assert!(depth_limit > 0);
        let v = *self.var(lit);
        debug_assert!(self.val(lit) != 0);
        if v.level == 0 {
            return;
        }
        let reason = v.reason;
        if reason.is_null() || reason == self.external_reason {
            return;
        }
        self.stats.ticks.search[self.stable as usize] += 1;
        let size = reason.size() as usize;
        for i in 0..size {
            let other = reason.lit(i);
            if other == lit {
                continue;
            }
            if !self.bump_also_reason_literal(other) {
                continue;
            }
            if depth_limit < 2 {
                continue;
            }
            self.bump_also_reason_literals(-other, depth_limit - 1, analyzed_limit);
            if self.analyzed.len() > analyzed_limit {
                break;
            }
        }
    }

    #[inline]
    pub fn bump_also_all_reason_literals(&mut self) {
        debug_assert!(self.opts.bump != 0);
        if self.opts.bumpreason == 0 {
            return;
        }
        if self.averages.current.decisions.value() > self.opts.bumpreasonrate as f64 {
            log!(
                self,
                "decisions per conflict rate {} > limit {}",
                crate::format::fmt_g(self.averages.current.decisions.value()),
                self.opts.bumpreasonrate
            );
            return;
        }
        let s = self.stable as usize;
        if self.delay[s].bumpreasons.limit != 0 {
            log!(self, "delaying reason bumping {} more times", self.delay[s].bumpreasons.limit);
            self.delay[s].bumpreasons.limit -= 1;
            return;
        }
        debug_assert!(self.opts.bumpreasondepth > 0);
        let depth_limit = self.opts.bumpreasondepth + self.stable as i32;
        let saved_analyzed = self.analyzed.len();
        let analyzed_limit = saved_analyzed.wrapping_mul(self.opts.bumpreasonlimit as usize);
        for k in 0..self.clause.len() {
            let lit = self.clause[k];
            if self.analyzed.len() <= analyzed_limit {
                self.bump_also_reason_literals(-lit, depth_limit, analyzed_limit);
            } else {
                break;
            }
        }
        if self.analyzed.len() > analyzed_limit {
            log!(self, "not bumping reason side literals as limit exhausted");
            for i in saved_analyzed..self.analyzed.len() {
                let lit = self.analyzed[i];
                let f = self.flags_mut(lit);
                debug_assert!(f.seen);
                f.seen = false;
            }
            self.delay[s].bumpreasons.interval += 1;
            self.analyzed.truncate(saved_analyzed);
        } else {
            log!(self, "bumping reasons up to depth {}", self.opts.bumpreasondepth);
            self.delay[s].bumpreasons.interval /= 2;
        }
        log!(self, "delay internal {}", self.delay[s].bumpreasons.interval);
        self.delay[s].bumpreasons.limit = self.delay[s].bumpreasons.interval;
    }

    /*--------------------------------------------------------------------*/

    pub fn clear_unit_analyzed_literals(&mut self) {
        log!(self, "clearing {} unit analyzed literals", self.unit_analyzed.len());
        for k in 0..self.unit_analyzed.len() {
            let lit = self.unit_analyzed[k];
            debug_assert!(self.var(lit).level == 0);
            let f = self.flags_mut(lit);
            debug_assert!(f.seen);
            f.seen = false;
            debug_assert!(!f.keep);
            debug_assert!(!f.poison);
            debug_assert!(!f.removable);
        }
        self.unit_analyzed.clear();
    }

    pub fn clear_analyzed_literals(&mut self) {
        log!(self, "clearing {} analyzed literals", self.analyzed.len());
        for k in 0..self.analyzed.len() {
            let lit = self.analyzed[k];
            let f = self.flags_mut(lit);
            debug_assert!(f.seen);
            f.seen = false;
            debug_assert!(!f.keep);
            debug_assert!(!f.poison);
            debug_assert!(!f.removable);
        }
        self.analyzed.clear();
    }

    pub fn clear_analyzed_levels(&mut self) {
        log!(self, "clearing {} analyzed levels", self.levels.len());
        for k in 0..self.levels.len() {
            let l = self.levels[k];
            if l < self.control.len() as i32 {
                self.control[l as usize].reset();
            }
        }
        self.levels.clear();
    }

    /*--------------------------------------------------------------------*/

    // Generate new driving clause and compute jump level.

    pub fn new_driving_clause(&mut self, glue: i32, jump: &mut i32, driving_level: &mut i32) -> CRef {
        let size = self.clause.len();
        let res: CRef;

        if size == 0 {
            *jump = 0;
            res = CRef::NULL;
        } else if size == 1 {
            self.iterating = true;
            *jump = 0;
            res = CRef::NULL;
        } else {
            debug_assert!(self.clause.len() > 1);

            // We have to get the last assigned literals into the watch
            // position.  Sorting all literals with respect to reverse
            // assignment order is overkill but seems to get slightly faster
            // run-time.  For 'minimize' we sort the literals too
            // heuristically along the trail order (so in the opposite order)
            // with the hope to hit the recursion limit less frequently.
            // Thus sorting effort is doubled here.
            //
            {
                let limit = self.opts.radixsortlim as usize;
                let vtab = &self.vtab;
                crate::radix::msort(
                    limit,
                    &mut self.clause,
                    |a: &i32| analyze_trail_negative_rank(vtab, *a),
                    |a: &i32, b: &i32| {
                        analyze_trail_negative_rank(vtab, *a) < analyze_trail_negative_rank(vtab, *b)
                    },
                );
            }

            *jump = self.var(self.clause[1]).level;
            *driving_level = self.var(self.clause[0]).level;
            res = self.new_learned_redundant_clause(glue);
            res.set_used(Internal::MAX_USED);
        }

        log!(self, "jump level {}", *jump);

        res
    }

    /*--------------------------------------------------------------------*/

    // determine the OTFS level for OTFS. Unlike the find_conflict_level, we
    // do not have to fix the clause

    #[inline]
    pub fn otfs_find_backtrack_level(&mut self, forced: &mut i32) -> i32 {
        debug_assert!(self.opts.otfs != 0 || self.external_prop);
        let mut res = 0;

        let conflict = self.conflict;
        let size = conflict.size() as usize;
        for i in 0..size {
            let lit = conflict.lit(i);
            let tmp = self.var(lit).level;
            if tmp == self.level {
                *forced = lit;
            } else if tmp > res {
                res = tmp;
                log!(self, "bt level is now {} due to {}", res, lit);
            }
        }
        res
    }

    /*--------------------------------------------------------------------*/

    // If chronological backtracking is enabled we need to find the actual
    // conflict level and then potentially can also reuse the conflict
    // clause as driving clause instead of deriving a redundant new driving
    // clause (forcing 'forced') if the number 'count' of literals in
    // conflict assigned at the conflict level is exactly one.

    #[inline]
    pub fn find_conflict_level(&mut self, forced: &mut i32) -> i32 {
        debug_assert!(!self.conflict.is_null());

        let mut res = 0;
        let mut count = 0;

        *forced = 0;

        let conflict = self.conflict;
        let size = conflict.size() as usize;
        for i in 0..size {
            let lit = conflict.lit(i);
            let tmp = self.var(lit).level;
            if tmp > res {
                res = tmp;
                *forced = lit;
                count = 1;
            } else if tmp == res {
                count += 1;
                if res == self.level && count > 1 {
                    break;
                }
            }
        }

        log!(self, "{} literals on actual conflict level {}", count, res);

        let size = conflict.size();

        // Move the two highest level literals to the front.
        //
        for i in 0..2i32 {
            let lit = conflict.lit(i as usize);
            debug_assert!(self.val(lit) < 0);
            let mut highest_position = i;
            let mut highest_literal = lit;
            let mut highest_level = self.var(highest_literal).level;

            let mut j = i + 1;
            while j < size {
                let other = conflict.lit(j as usize);
                let tmp = self.var(other).level;
                if highest_level >= tmp {
                    j += 1;
                    continue;
                }
                highest_literal = other;
                highest_position = j;
                highest_level = tmp;
                if highest_level == res {
                    break;
                }
                j += 1;
            }

            // No unwatched higher assignment level literal.
            //
            if highest_position == i {
                continue;
            }

            if highest_position > 1 {
                log!(self, conflict, "unwatch {} in", lit);
                remove_watch(self.watches_mut(lit), conflict);
            }

            conflict.set_lit(highest_position as usize, lit);
            conflict.set_lit(i as usize, highest_literal);

            if highest_position > 1 {
                let other = conflict.lit((i == 0) as usize);
                self.watch_literal(highest_literal, other, conflict);
            }
        }

        // Only if the number of highest level literals in the conflict is
        // one then we can reuse the conflict clause as driving clause for
        // 'forced'.
        //
        if count != 1 {
            *forced = 0;
        }

        res
    }

    /*--------------------------------------------------------------------*/

    #[inline]
    pub fn determine_actual_backtrack_level(&mut self, jump: i32) -> i32 {
        let mut res: i32;

        debug_assert!(self.level > jump);

        if self.opts.chrono == 0 {
            res = jump;
            log!(self, "chronological backtracking disabled using jump level {}", res);
        } else if self.opts.chronoalways != 0 {
            self.stats.chrono += 1;
            res = self.level - 1;
            log!(self, "forced chronological backtracking to level {}", res);
        } else if jump >= self.level - 1 {
            res = jump;
            log!(self, "jump level identical to chronological backtrack level {}", res);
        } else if (jump as usize) < self.assumptions.len() {
            res = jump;
            log!(
                self,
                "using jump level {} since it is lower than assumption level {}",
                res,
                self.assumptions.len()
            );
        } else if self.level - jump > self.opts.chronolevelim {
            self.stats.chrono += 1;
            res = self.level - 1;
            log!(
                self,
                "back-jumping over {} > {} levels prohibitedthus backtracking chronologically to level {}",
                self.level - jump,
                self.opts.chronolevelim,
                res
            );
        } else if self.opts.chronoreusetrail != 0 {
            let mut best_idx: i32 = 0;
            let mut best_pos: i32 = 0;

            if self.use_scores() {
                let less = self.scores.less;
                let start = self.control[(jump + 1) as usize].trail as usize;
                for i in start..self.trail.len() {
                    let idx = self.trail[i].abs();
                    if best_idx != 0 && !less.less(best_idx as u32, idx as u32) {
                        continue;
                    }
                    best_idx = idx;
                    best_pos = i as i32;
                }
                log!(self, "best variable score {}", crate::format::fmt_g(self.score(best_idx)));
            } else {
                let start = self.control[(jump + 1) as usize].trail as usize;
                for i in start..self.trail.len() {
                    let idx = self.trail[i].abs();
                    if best_idx != 0 && self.bumped(best_idx) >= self.bumped(idx) {
                        continue;
                    }
                    best_idx = idx;
                    best_pos = i as i32;
                }
                log!(self, "best variable bumped {}", self.bumped(best_idx));
            }
            debug_assert!(best_idx != 0);
            log!(self, "best variable {} at trail position {}", best_idx, best_pos);

            // Now find the frame and decision level in the control stack of
            // that best variable index.  Note that, as in 'reuse_trail', the
            // frame 'control[i]' for decision level 'i' contains the trail
            // before that decision level, i.e., the decision
            // 'control[i].decision' sits at 'control[i].trail' in the trail
            // and we thus have to check the level of the control frame one
            // higher than at the result level.
            //
            res = jump;
            while res < self.level - 1 && self.control[(res + 1) as usize].trail <= best_pos {
                res += 1;
            }

            if res == jump {
                log!(self, "default non-chronological back-jumping to level {}", res);
            } else {
                self.stats.chrono += 1;
                log!(self, "chronological backtracking to level {} to reuse trail", res);
            }
        } else {
            res = jump;
            log!(self, "non-chronological back-jumping to level {}", res);
        }

        res
    }

    /*--------------------------------------------------------------------*/

    pub fn eagerly_subsume_recently_learned_clauses(&mut self, c: CRef) {
        debug_assert!(self.opts.eagersubsume != 0);
        log!(self, c, "trying eager subsumption with");
        self.mark_clause_literals(c);
        let lim = self.stats.eagertried + self.opts.eagersubsumelim as i64;
        let mut it = self.clauses.len();
        #[cfg(feature = "logging")]
        let before = self.stats.eagersub;
        while it != 0 && {
            let t = self.stats.eagertried;
            self.stats.eagertried += 1;
            t <= lim
        } {
            it -= 1;
            let d = self.clauses[it];
            if c == d {
                continue;
            }
            if d.garbage() {
                continue;
            }
            if !d.redundant() {
                continue;
            }
            let mut needed = c.size();
            let dsize = d.size() as usize;
            for k in 0..dsize {
                let lit = d.lit(k);
                if self.marked(lit) <= 0 {
                    continue;
                }
                needed -= 1;
                if needed == 0 {
                    break;
                }
            }
            if needed != 0 {
                continue;
            }
            log!(self, d, "eager subsumed");
            self.stats.eagersub += 1;
            self.stats.subsumed += 1;
            self.mark_garbage(d);
        }
        self.unmark_clause_literals(c);
        #[cfg(feature = "logging")]
        {
            let subsumed = (self.stats.eagersub - before) as u64;
            if subsumed != 0 {
                log!(self, "eagerly subsumed {} clauses", subsumed);
            }
        }
    }

    /*--------------------------------------------------------------------*/

    pub fn on_the_fly_strengthen(&mut self, new_conflict: CRef, uip: i32) -> CRef {
        debug_assert!(!new_conflict.is_null());
        debug_assert!(new_conflict.size() > 2);
        log!(self, new_conflict, "applying OTFS on lit {}", uip);
        let mut sorted: Vec<i32> = Vec::with_capacity(new_conflict.size() as usize);
        debug_assert!(sorted.is_empty());
        self.stats.otfs.strengthened += 1;

        let lits = new_conflict;

        debug_assert!(lits.lit(0) == uip || lits.lit(1) == uip);
        let other_init = lits.lit(0) ^ lits.lit(1) ^ uip;

        debug_assert!(self.mini_chain.is_empty());

        let old_size = new_conflict.size();
        let mut new_size: i32 = 0;
        let mut best: i32 = 0;
        let mut second_best: i32 = 0;
        for i in 0..old_size {
            let other = lits.lit(i as usize);
            sorted.push(other);
            if self.var(other).level != 0 {
                lits.set_lit(new_size as usize, other);
                new_size += 1;
            }
            if other == uip {
                continue;
            }
            if best == 0 || self.var(other).level > self.var(best).level {
                second_best = best;
                best = other;
            } else if second_best == 0 || self.var(other).level > self.var(second_best).level {
                second_best = other;
            }
        }

        log!(self, new_conflict, "removing all units in");

        debug_assert!(lits.lit(0) == uip || lits.lit(1) == uip);
        let mut other = lits.lit(0) ^ lits.lit(1) ^ uip;
        lits.set_lit(0, other);
        new_size -= 1;
        lits.set_lit(1, lits.lit(new_size as usize));
        log!(self, new_conflict, "putting uip at pos 1");

        if lits.lit(0) != best {
            let repl = lits.lit(0);
            lits.set_lit(0, best);
            other = best;
            for i in 1..new_size {
                if lits.lit(i as usize) != best {
                    continue;
                }
                lits.set_lit(i as usize, repl);
                break;
            }
        }
        if lits.lit(1) != second_best {
            let repl = lits.lit(1);
            lits.set_lit(1, second_best);
            for i in 2..new_size {
                if lits.lit(i as usize) != second_best {
                    continue;
                }
                lits.set_lit(i as usize, repl);
                break;
            }
        }
        log!(self, new_conflict, "fix watch invariant");

        if other_init != other {
            remove_watch(self.watches_mut(other_init), new_conflict);
        }
        remove_watch(self.watches_mut(uip), new_conflict);

        debug_assert!(!self.lrat || *self.lrat_chain.last().unwrap() == new_conflict.id());
        if self.lrat {
            debug_assert!(!self.lrat_chain.is_empty());
            for k in 0..self.unit_chain.len() {
                let id = self.unit_chain[k];
                self.mini_chain.push(id);
            }
            for k in (0..self.lrat_chain.len()).rev() {
                let id = self.lrat_chain[k];
                self.mini_chain.push(id);
            }
            self.lrat_chain.clear();
            self.clear_unit_analyzed_literals();
            self.unit_chain.clear();
        }
        debug_assert!(self.unit_analyzed.is_empty());
        // sort the clause
        {
            let mut highest_pos: i32 = 0;
            let mut highest_level: i32 = 0;
            for i in 1..new_size {
                let other = lits.lit(i as usize) as u32;
                debug_assert!(self.val(other as i32) < 0);
                let level = self.var(other as i32).level;
                debug_assert!(level != 0);
                log!(self, "checking {}", other as i32);
                if level <= highest_level {
                    continue;
                }
                highest_pos = i;
                highest_level = level;
            }
            log!(self, "highest lit is {}", lits.lit(highest_pos as usize));
            if highest_pos != 1 {
                let a = lits.lit(1);
                let b = lits.lit(highest_pos as usize);
                lits.set_lit(1, b);
                lits.set_lit(highest_pos as usize, a);
            }
            log!(self, "removing {} literals", new_conflict.size() - new_size);

            if new_size == 1 {
                log!(self, new_conflict, "new size = 1, so interrupting");
                debug_assert!(self.opts.exteagerreasons == 0);
                return CRef::NULL;
            } else {
                self.otfs_strengthen_clause(new_conflict, uip, new_size, &sorted);
                debug_assert!(new_size == new_conflict.size());
            }
        }

        if other_init != other {
            let l1 = lits.lit(1);
            self.watch_literal(other, l1, new_conflict);
        } else {
            let l1 = lits.lit(1);
            update_watch_size(self.watches_mut(other), l1, new_conflict);
        }
        let l1 = lits.lit(1);
        self.watch_literal(l1, other, new_conflict);

        log!(self, new_conflict, "strengthened clause by OTFS");
        sorted.clear();

        new_conflict
    }

    /*--------------------------------------------------------------------*/

    #[inline]
    pub fn otfs_subsume_clause(&mut self, subsuming: CRef, subsumed: CRef) {
        self.stats.subsumed += 1;
        debug_assert!(subsuming.size() <= subsumed.size());
        log!(self, subsumed, "subsumed");
        if subsumed.redundant() {
            self.stats.subred += 1;
        } else {
            self.stats.subirr += 1;
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
        self.stats.current.irredundant += 1;
        self.stats.added.irredundant += 1;
        self.stats.irrlits += subsuming.size() as i64;
        debug_assert!(self.stats.current.redundant > 0);
        self.stats.current.redundant -= 1;
        debug_assert!(self.stats.added.redundant > 0);
        self.stats.added.redundant -= 1;
        // ... and keep 'stats.added.total'.
    }

    /*--------------------------------------------------------------------*/

    // Candidate clause 'c' is strengthened by removing 'lit' and units.
    //
    pub fn otfs_strengthen_clause(&mut self, c: CRef, lit: i32, new_size: i32, old: &[i32]) {
        self.stats.strengthened += 1;
        debug_assert!(c.size() > 2);
        let _ = self.shrink_clause(c, new_size);
        if let Some(proof) = self.proof.as_mut() {
            proof.otfs_strengthen_clause(c, old, &self.mini_chain);
        }
        if !c.redundant() {
            self.mark_removed_lit(lit);
        }
        self.mini_chain.clear();
        c.set_used(Internal::MAX_USED);
        log!(self, c, "strengthened");
        self.external().check_shrunken_clause(c);
    }

    /*--------------------------------------------------------------------*/

    // If the average number of decisions per conflict (analysis actually
    // so not taking OTFS conflicts into account) is high we do not bump
    // reasons. This is the function which updates the exponential moving
    // decision rate average.

    pub fn update_decision_rate_average(&mut self) {
        let current = self.stats.decisions;
        let decisions = current - self.saved_decisions;
        update_average!(self, averages.current.decisions, decisions);
        self.saved_decisions = current;
    }

    pub fn fix_trail_levels(&mut self) {
        debug_assert!(self.out_of_order_level != -1);
        if self.out_of_order_level > self.level || self.opts.elevate != 3 {
            self.out_of_order_level = -1;
            self.out_of_order_trail = -1;
            return;
        }
        log!(self, "fixing all trail levels before backtracking");
        let trix = self.control[self.out_of_order_level as usize].trail as usize;
        debug_assert!(trix <= self.trail.len());
        let mut i = trix;
        while i < self.trail.len() {
            let lit = self.trail[i];
            i += 1;
            let reason = self.var(lit).reason;
            if reason.is_null() || reason == self.external_reason {
                continue;
            }

            let mut res = 0;

            let size = reason.size() as usize;
            for k in 0..size {
                let other = reason.lit(k);
                if other == lit {
                    continue;
                }
                debug_assert!(self.val(other) != 0);
                let tmp = self.var(other).level;
                if tmp > res {
                    res = tmp;
                }
            }
            if self.var(lit).level != res {
                log!(
                    self,
                    reason,
                    "update level of {} from {} to {} with",
                    lit,
                    self.var(lit).level,
                    res
                );
            }

            self.var_mut(lit).level = res;
            if self.lrat && res == 0 {
                // 'auto tmp = std::move (lrat_chain)' (explicit move in C++).
                let tmp = std::mem::take(&mut self.lrat_chain);
                self.lrat_chain.clear();
                self.build_chain_for_units(lit, reason, false);
                self.mark_garbage(reason);
                self.var_mut(lit).reason = CRef::NULL;
                self.learn_unit_clause(lit);
                self.lrat_chain = tmp;
            } else if res == 0 {
                self.mark_fixed(lit);
                self.mark_garbage(reason);
                self.var_mut(lit).reason = CRef::NULL;
            }
        }
        self.out_of_order_level = -1;
        self.out_of_order_trail = -1;
    }

    /*--------------------------------------------------------------------*/

    // This is the main conflict analysis routine.  It assumes that a
    // conflict was found.  Then we derive the 1st UIP clause, optionally
    // minimize it, add it as learned clause, and then uses the clause for
    // conflict directed back-jumping and flipping the 1st UIP literal.  In
    // combination with chronological backtracking (see discussion above)
    // the algorithm becomes slightly more involved.

    pub fn analyze(&mut self) {
        start!(self, analyze);

        debug_assert!(!self.conflict.is_null());
        debug_assert!(self.lrat_chain.is_empty());
        debug_assert!(self.unit_chain.is_empty());
        debug_assert!(self.unit_analyzed.is_empty());
        debug_assert!(self.clause.is_empty());

        // First update moving averages of trail height at conflict.
        //
        update_average!(self, averages.current.trail.fast, self.num_assigned);
        update_average!(self, averages.current.trail.slow, self.num_assigned);
        self.update_decision_rate_average();

        /*------------------------------------------------------------------*/

        if self.external_prop && !self.external_prop_is_lazy && self.opts.exteagerreasons != 0 {
            self.explain_external_propagations();
        }

        let mut forced: i32 = 0;

        let mut conflict_level = self.find_conflict_level(&mut forced);

        if self.control[conflict_level as usize].trail <= self.out_of_order_trail {
            self.fix_trail_levels();
            conflict_level = self.find_conflict_level(&mut forced);
        }

        // In principle we can perform conflict analysis as in
        // non-chronological backtracking except if there is only one
        // literal with the maximum assignment level in the clause.  Then
        // standard conflict analysis is unnecessary and we can use the
        // conflict as a driving clause.  In the pseudo code of the SAT'18
        // paper on chronological backtracking this corresponds to the
        // situation handled in line 4-6 in Alg. 1, except that the pseudo
        // code in the paper only backtracks while we eagerly assign the
        // single literal on the highest decision level.

        if forced != 0 {
            debug_assert!(forced != 0);
            debug_assert!(conflict_level > 0);
            log!(self, "single highest level literal {}", forced);

            // The pseudo code in the SAT'18 paper actually backtracks to the
            // 'second highest decision' level, while their code backtracks
            // to 'conflict_level-1', which is more in the spirit of
            // chronological backtracking anyhow and thus we also do the
            // latter.
            //
            self.backtrack(conflict_level - 1);

            // if we are on decision level 0 search assign will learn unit so
            // we need a valid chain here (of course if we are not on
            // decision level 0 this will not result in a valid chain).  we
            // can just use build_chain_for_units in propagate
            //
            let conflict = self.conflict;
            self.build_chain_for_units(forced, conflict, false);

            log!(self, "forcing {}", forced);
            self.search_assign_driving(forced, conflict);

            self.conflict = CRef::NULL;
            if self.opts.chrono == 0 {
                self.did_external_prop = true;
            }
            stop!(self, analyze);
            return;
        }

        // Backtracking to the conflict level is in the pseudo code in the
        // SAT'18 chronological backtracking paper, but not in their actual
        // implementation.  In principle we do not need to backtrack here.
        // However, as a side effect of backtracking to the conflict level we
        // set 'level' to the conflict level which then allows us to reuse
        // the old 'analyze' code as is.  The alternative (which we also
        // tried but then abandoned) is to use 'conflict_level' instead of
        // 'level' in the analysis, which however requires to pass it to the
        // 'analyze_reason' and 'analyze_literal' functions.
        //
        self.backtrack(conflict_level);

        // Actual conflict on root level, thus formula unsatisfiable.
        //
        if self.level == 0 {
            self.learn_empty_clause();
            if self.external().learner.is_some() {
                self.external().export_learned_empty_clause();
            }
            stop!(self, analyze);
            return;
        }

        /*------------------------------------------------------------------*/

        // First derive the 1st UIP clause by going over literals assigned on
        // the current decision level.  Literals in the conflict are marked
        // as 'seen' as well as all literals in reason clauses of already
        // 'seen' literals on the current decision level.  Thus the outer
        // loop starts with the conflict clause as 'reason' and then uses the
        // 'reason' of the next seen literal on the trail assigned on the
        // current decision level.  During this process maintain the number
        // 'open' of seen literals on the current decision level with not yet
        // processed 'reason'.  As soon 'open' drops to one, we have found
        // the first unique implication point.  This is sound because the
        // topological order in which literals are processed follows the
        // assignment order and a more complex algorithm to find articulation
        // points is not necessary.
        //
        let mut reason = self.conflict;
        log!(self, reason, "analyzing conflict");

        debug_assert!(self.clause.is_empty());
        debug_assert!(self.lrat_chain.is_empty());

        let mut i: i32 = self.trail.len() as i32; // Start at end-of-trail.
        let mut open: i32 = 0; // Seen but not processed on this level.
        let mut uip: i32 = 0; // The first UIP literal.
        let mut resolvent_size: i32 = 0; // without the uip
        let mut antecedent_size: i32; // with the uip and without unit literals
        let mut conflict_size: i32 = 0; // without the uip and without unit literals
        let mut resolved: i32 = 0; // number of resolution (0 = clause in CNF)
        let otfs = self.opts.otfs != 0;

        loop {
            antecedent_size = 1; // for uip
            self.analyze_reason(uip, reason, &mut open, &mut resolvent_size, &mut antecedent_size);
            if resolved == 0 {
                conflict_size = antecedent_size - 1;
            }
            log!(self, "conflict size {} after {}", conflict_size, resolved);
            debug_assert!(resolvent_size == open + self.clause.len() as i32);

            if otfs && resolved > 0 && antecedent_size > 2 && resolvent_size < antecedent_size {
                debug_assert!(reason != self.conflict);
                log!(self, &self.analyzed, "found candidate for OTFS conflict");
                log!(self, &self.clause, "found candidate for OTFS conflict");
                log!(self, reason, "found candidate (size {}) for OTFS resolvent", antecedent_size);
                let other = reason.lit(0) ^ reason.lit(1) ^ uip;
                debug_assert!(other != uip);
                reason = self.on_the_fly_strengthen(reason, uip);
                if self.opts.bump != 0 {
                    self.bump_variables();
                }

                debug_assert!(conflict_size != 0);
                if reason.is_null() {
                    uip = -other;
                    debug_assert!(open == 1);
                    log!(self, "clause is actually unit {}, stopping", -uip);
                    self.mini_chain.reverse();
                    for k in 0..self.mini_chain.len() {
                        let id = self.mini_chain[k];
                        self.lrat_chain.push(id);
                    }
                    self.mini_chain.clear();
                    self.clear_analyzed_levels();
                    debug_assert!(self.opts.exteagerreasons == 0);
                    self.clause.clear();
                    break;
                }
                debug_assert!(conflict_size >= 2);

                if resolved == 1 && resolvent_size < conflict_size {
                    // here both clauses are part of the CNF, so one subsumes
                    // the other
                    let conflict = self.conflict;
                    self.otfs_subsume_clause(reason, conflict);
                    log!(self, reason, "changing conflict to");
                    conflict_size -= 1;
                    debug_assert!(conflict_size == reason.size());
                    self.stats.otfs.subsumed += 1;
                    self.stats.subsumed += 1;
                }

                log!(self, reason, "changing conflict to");
                self.conflict = reason;
                if open == 1 {
                    let mut forced: i32 = 0;
                    let conflict_level = self.otfs_find_backtrack_level(&mut forced);
                    let new_level = self.determine_actual_backtrack_level(conflict_level);
                    update_average!(self, averages.current.level, new_level);
                    self.backtrack(new_level);

                    log!(self, "forcing {}", forced);
                    let conflict = self.conflict;
                    self.search_assign_driving(forced, conflict);

                    // Clean up.
                    //
                    self.conflict = CRef::NULL;
                    self.clear_analyzed_literals();
                    self.clear_analyzed_levels();
                    self.clause.clear();
                    stop!(self, analyze);
                    return;
                }

                self.stats.conflicts += 1;

                self.clear_analyzed_literals();
                self.clear_analyzed_levels();
                self.clause.clear();
                resolvent_size = 0;
                antecedent_size = 1;
                resolved = 0;
                open = 0;
                self.analyze_reason(0, reason, &mut open, &mut resolvent_size, &mut antecedent_size);
                conflict_size = antecedent_size - 1;
                debug_assert!(open > 1);
            }

            resolved += 1;

            uip = 0;
            while uip == 0 {
                if i == 0 {
                    if self.lazy_external_propagator_out_of_order_clause(&mut uip) {
                        return;
                    }
                    if self.unsat {
                        return;
                    } else if uip != 0 {
                        open = 1;
                        break;
                    } else {
                        log!(self, reason, "restarting the analysis on the new conflict");
                        self.stats.conflicts += 1;
                        reason = self.conflict;
                        resolvent_size = 0;
                        antecedent_size = 1;
                        resolved = 0;
                        open = 0;
                        self.analyze_reason(0, reason, &mut open, &mut resolvent_size, &mut antecedent_size);
                        conflict_size = antecedent_size - 1;
                        debug_assert!(open > 1);
                        i = self.trail.len() as i32;
                    }
                }
                debug_assert!(i > 0);
                i -= 1;
                let lit = self.trail[i as usize];
                if !self.flags(lit).seen {
                    continue;
                }
                if self.var(lit).level == self.level {
                    uip = lit;
                }
            }
            open -= 1;
            if open == 0 {
                break;
            }
            reason = self.var(uip).reason;
            if reason == self.external_reason {
                debug_assert!(self.opts.exteagerreasons == 0);
                reason = self.learn_external_reason_clause(-uip, 0, true);
                self.var_mut(uip).reason = reason;
            }
            debug_assert!(reason != self.external_reason);
            log!(self, reason, "analyzing {} reason", uip);
            debug_assert!(resolvent_size != 0);
            resolvent_size -= 1;
        }
        let _ = (conflict_size, resolved);
        log!(self, "first UIP {}", uip);
        self.clause.push(-uip);

        // Update glue and learned (1st UIP literals) statistics.
        //
        let mut size = self.clause.len() as i32;
        let glue = self.levels.len() as i32 - 1;
        log!(self, &self.clause, "1st UIP size {} and glue {} clause", size, glue);
        update_average!(self, averages.current.glue.fast, glue);
        update_average!(self, averages.current.glue.slow, glue);
        self.stats.learned.literals += size as i64;
        self.stats.learned.clauses += 1;
        debug_assert!(glue < size);

        // up to this point lrat_chain contains the proof for current clause
        // in reversed order. in minimize and shrink the clause is changed
        // and therefore lrat_chain has to be extended. Unfortunately we
        // cannot create the chain directly during minimization (or
        // shrinking) but afterwards we can calculate it pretty easily and
        // even better the same algorithm works for both shrinking and
        // minimization.

        // Minimize the 1st UIP clause as pioneered by Niklas Soerensson in
        // MiniSAT and described in our joint SAT'09 paper.
        //
        if size > 1 {
            if self.opts.shrink != 0 {
                self.shrink_and_minimize_clause();
            } else if self.opts.minimize != 0 {
                self.minimize_clause();
            }

            size = self.clause.len() as i32;

            // Update decision heuristics.
            //
            if self.opts.bump != 0 {
                self.bump_also_all_reason_literals();
                self.bump_variables();
            }

            if self.external().learner.is_some() {
                let clause: &[i32] = &self.clause;
                self.external().export_learned_large_clause(clause);
            }
        } else if self.external().learner.is_some() {
            self.external().export_learned_unit_clause(-uip);
        }

        // Update actual size statistics.
        //
        self.stats.units += (size == 1) as i64;
        self.stats.binaries += (size == 2) as i64;
        update_average!(self, averages.current.size, size);

        // reverse lrat_chain. We could probably work with reversed iterators
        // (views) to be more efficient but we would have to distinguish in
        // proof
        //
        if self.lrat {
            log!(self, &self.unit_chain, "unit chain: ");
            for k in 0..self.unit_chain.len() {
                let id = self.unit_chain[k];
                self.lrat_chain.push(id);
            }
            self.unit_chain.clear();
            self.lrat_chain.reverse();
        }

        // Determine back-jump level, learn driving clause, backtrack and
        // assign flipped 1st UIP literal.
        //
        let mut jump: i32 = 0;
        let mut driving: i32 = 0;
        let driving_clause = self.new_driving_clause(glue, &mut jump, &mut driving);
        update_average!(self, averages.current.jump, jump);

        let new_level = self.determine_actual_backtrack_level(jump);
        update_average!(self, averages.current.level, new_level);
        self.backtrack(new_level);

        // It should hold that (!level <=> size == 1)
        //                 and (!uip   <=> size == 0)
        // this means either we have already learned a clause => size >= 2
        // in this case we will not learn empty clause or unit here or we
        // haven't actually learned a clause in new_driving_clause then
        // lrat_chain is still valid and we will learn a unit or empty clause
        //
        if uip != 0 {
            self.search_assign_driving(-uip, driving_clause);
        } else {
            self.learn_empty_clause();
        }

        if self.stable {
            self.reluctant.tick(); // Reluctant has its own 'conflict' counter.
        }

        // Clean up.
        //
        self.clear_analyzed_literals();
        self.clear_unit_analyzed_literals();
        self.clear_analyzed_levels();
        self.clause.clear();
        self.conflict = CRef::NULL;

        self.lrat_chain.clear();
        stop!(self, analyze);

        if !driving_clause.is_null() && self.opts.eagersubsume != 0 {
            self.eagerly_subsume_recently_learned_clauses(driving_clause);
        }

        if self.lim.recompute_tier <= self.stats.conflicts {
            self.recompute_tier();
        }
    }

    // In the special case where the external propagator is lazy, the same
    // invariants as OTFS break (but even more complicated). There are three
    // possible cases:
    //   - the clause becomes empty (unsat must be answered)
    //   - the clause is a unit (backtrack and set the clause)
    //   - the clause is a new conflict on lower level and we restart the
    //   - the clause is a fake conflict with only one decision level
    //   analysis
    //
    // TODO: we do not really need to keep the clause longer than the
    // conflict analysis.
    pub fn lazy_external_propagator_out_of_order_clause(&mut self, uip: &mut i32) -> bool {
        debug_assert!(self.opts.exteagerreasons == 0);
        debug_assert!(self.external_prop);
        log!(self, &self.clause, "out-of-order conflict");
        *uip = 0;
        let mut exiting = false;
        if self.clause.is_empty() {
            log!(self, &self.lrat_chain, "lrat_chain:");
            log!(self, &self.clause, "clause:");
            log!(self, &self.unit_chain, "units:");
            if self.lrat {
                log!(self, &self.unit_chain, "unit chain: ");
                for k in 0..self.unit_chain.len() {
                    let id = self.unit_chain[k];
                    self.lrat_chain.push(id);
                }
                self.unit_chain.clear();
                self.lrat_chain.reverse();
            }
            log!(self, &self.lrat_chain, "lrat_chain:");
            self.learn_empty_clause();
            if self.external().learner.is_some() {
                self.external().export_learned_empty_clause();
            }
            self.conflict = CRef::NULL;
            exiting = true;
        } else if self.clause.len() == 1 {
            log!(self, "found out-of-order unit");
            *uip = -self.clause[0];
            debug_assert!(*uip != 0);
            let l = self.var(*uip).level;
            self.backtrack(l);
            debug_assert!(self.val(*uip) > 0);
            self.clause.clear();
        } else {
            let mut jump: i32 = 0;
            let mut driving: i32 = 0;
            let glue = self.clause.len() as i32 - 1;
            log!(self, &self.lrat_chain, "lrat_chain:");
            log!(self, &self.clause, "clause:");
            if self.lrat {
                log!(self, &self.unit_chain, "unit chain: ");
                for k in 0..self.unit_chain.len() {
                    let id = self.unit_chain[k];
                    self.lrat_chain.push(id);
                }
                self.unit_chain.clear();
                self.lrat_chain.reverse();
            }
            self.conflict = self.new_driving_clause(glue, &mut jump, &mut driving);
            update_average!(self, averages.current.level, jump);
            self.backtrack(driving);

            if jump != driving {
                log!(self, self.conflict, "fake conflict");
                let mut forced: i32 = 0;
                let conflict_level = self.otfs_find_backtrack_level(&mut forced);
                let new_level = self.determine_actual_backtrack_level(conflict_level);
                self.backtrack(new_level);

                log!(self, "forcing {}", forced);
                let conflict = self.conflict;
                self.search_assign_driving(forced, conflict);
                exiting = true;
            } else {
                log!(self, self.conflict, "new conflict");
            }
        }
        // Clean up.
        //
        self.clear_analyzed_literals();
        self.clear_unit_analyzed_literals();
        self.clear_analyzed_levels();
        self.clause.clear();

        if exiting {
            self.conflict = CRef::NULL;
            self.clear_unit_analyzed_literals();
            self.lrat_chain.clear();
            stop!(self, analyze);
        }
        exiting
    }

    // We wait reporting a learned unit until propagation of that unit is
    // completed.  Otherwise the 'i' report gives the number of remaining
    // variables before propagating the unit (and hides the actual
    // remaining variables after propagating it).

    pub fn iterate(&mut self) {
        self.iterating = false;
        self.report(b'i', 0);
    }
}

//! Port of `sweep.hpp` and `sweep.cpp`: SAT sweeping with kitten.

use crate::clause::CRef;
use crate::internal::Internal;
use crate::random::Random;

#[derive(Clone, Debug, Default)]
pub struct sweep_proof_clause {
    /// Index for sweeper.clauses.
    pub sweep_id: u32,
    /// CaDiCaL id.
    pub cad_id: i64,
    /// Kitten id.
    pub kit_id: u32,
    pub learned: bool,
    pub literals: Vec<i32>,
    /// LRAT.
    pub chain: Vec<u32>,
}

#[derive(Clone, Debug, Default)]
pub struct sweep_blocked_clause {
    pub blit: i32,
    pub id: i64,
    pub literals: Vec<i32>,
}

#[derive(Clone, Copy, Debug, Default)]
pub struct sweep_binary {
    pub lit: i32,
    pub other: i32,
    pub id: i64,
}

#[derive(Clone, Copy, Debug, Default)]
pub struct SweeperLimit {
    pub ticks: u64,
    pub clauses: u32,
    pub depth: u32,
    pub vars: u32,
}

pub struct Sweeper {
    pub internal: *mut Internal,
    pub random: Random,
    pub depths: Vec<u32>,
    /// `int *reprs` (indexed by literal, see 'sweep.cpp').
    pub reprs: Vec<i32>,
    pub next: Vec<i32>,
    pub prev: Vec<i32>,
    pub first: i32,
    pub last: i32,
    pub blit: i32,
    pub encoded: u32,
    pub save: u32,
    pub vars: Vec<i32>,
    pub clauses: Vec<CRef>,
    pub blocked_clauses: Vec<sweep_blocked_clause>,
    pub flush_blocked_clauses: bool,
    pub blockable: Vec<i32>,
    pub clause: Vec<i32>,
    pub propagate: Vec<i32>,
    pub backbone: Vec<i32>,
    pub partition: Vec<i32>,
    pub prev_units: Vec<bool>,
    pub binaries: Vec<sweep_binary>,
    pub core: [Vec<sweep_proof_clause>; 2],
    pub current_ticks: u64,
    pub limit: SweeperLimit,
}

/*------------------------------------------------------------------------*/
// Port of the functions defined in 'sweep.cpp'.

#[allow(unused_imports)]
use crate::prelude::*;
use crate::format::fmt_f;
use crate::kitten::*;
#[allow(unused_imports)]
use crate::util::{enlarge_zero, erase_vector, percent, relative};

/// `INVALID64` in 'sweep.cpp'.
const INVALID64: i64 = i64::MAX;
/// `INVALID` in 'sweep.cpp'.
const INVALID: u32 = u32::MAX;

/// The kitten sub-solver ('citten') of the solver.
#[inline(always)]
fn citten(internal: &mut Internal) -> &mut Kitten {
    internal.citten.as_deref_mut().expect("citten initialized")
}

impl Sweeper {
    /// `Sweeper (Internal *)`.
    pub fn new(internal: *mut Internal) -> Sweeper {
        // SAFETY: 'internal' is the valid solver creating the sweeper.
        let i = unsafe { &mut *internal };
        let mut random = Random::new(i.opts.seed as u64);
        random += i.stats.sweep as u64; // different seed every time
        let mut sweeper = Sweeper {
            internal,
            random,
            depths: Vec::new(),
            reprs: Vec::new(),
            next: Vec::new(),
            prev: Vec::new(),
            first: 0,
            last: 0,
            blit: 0,
            encoded: 0,
            save: 0,
            vars: Vec::new(),
            clauses: Vec::new(),
            blocked_clauses: Vec::new(),
            flush_blocked_clauses: false,
            blockable: Vec::new(),
            clause: Vec::new(),
            propagate: Vec::new(),
            backbone: Vec::new(),
            partition: Vec::new(),
            prev_units: Vec::new(),
            binaries: Vec::new(),
            core: [Vec::new(), Vec::new()],
            current_ticks: 0,
            limit: SweeperLimit::default(),
        };
        i.init_sweeper(&mut sweeper);
        sweeper
    }

    /// `reprs[lit]` (C++ 'reprs' points to the middle of the allocation of
    /// size '2 * max_var + 1').
    #[inline(always)]
    fn repr_of(&self, lit: i32) -> i32 {
        let max_var = (self.reprs.len() / 2) as i32;
        self.reprs[(lit + max_var) as usize]
    }

    /// `reprs[lit] = val`.
    #[inline(always)]
    fn set_repr(&mut self, lit: i32, val: i32) {
        let max_var = (self.reprs.len() / 2) as i32;
        self.reprs[(lit + max_var) as usize] = val;
    }
}

impl Drop for Sweeper {
    fn drop(&mut self) {
        // this is already called actively
        // internal->release_sweeper (this);
    }
}

/*------------------------------------------------------------------------*/

// Call backs for kitten ('extern "C"' functions in C++).

fn save_core_clause(sweeper: &mut Sweeper, id: u32, learned: bool, lits: &[u32]) {
    // SAFETY: the sweeper does not outlive the solver it points to.
    let internal = unsafe { &mut *sweeper.internal };
    if internal.unsat || internal.terminated_asynchronously(1) {
        return;
    }
    let mut pc = sweep_proof_clause::default();
    if learned {
        pc.sweep_id = INVALID; // necessary
        pc.cad_id = INVALID64; // delay giving ids
    } else {
        pc.sweep_id = id; // necessary
        debug_assert!((id as usize) < sweeper.clauses.len());
        pc.cad_id = sweeper.clauses[id as usize].id();
    }
    pc.kit_id = 0;
    pc.learned = learned;
    for &p in lits {
        pc.literals.push(internal.citten2lit(p)); // conversion
    }
    log!(
        internal,
        &pc.literals,
        "traced {}",
        if pc.learned { "learned" } else { "original" }
    );
    sweeper.core[sweeper.save as usize].push(pc);
}

fn save_core_clause_with_lrat(
    sweeper: &mut Sweeper,
    cid: u32,
    id: u32,
    learned: bool,
    lits: &[u32],
    chain: &[u32],
) {
    // SAFETY: the sweeper does not outlive the solver it points to.
    let internal = unsafe { &mut *sweeper.internal };
    if internal.unsat || internal.terminated_asynchronously(1) {
        return;
    }
    let mut pc = sweep_proof_clause::default();
    pc.kit_id = cid;
    pc.learned = learned;
    pc.sweep_id = INVALID;
    pc.cad_id = INVALID64;
    if !learned {
        debug_assert!(!lits.is_empty());
        debug_assert!(chain.is_empty());
        debug_assert!((id as usize) < sweeper.clauses.len());
        pc.sweep_id = id;
        debug_assert!((id as usize) < sweeper.clauses.len());
        let c = sweeper.clauses[id as usize];
        pc.cad_id = c.id();
        for &lit in c.lits() {
            pc.literals.push(lit);
        }
    } else {
        debug_assert!(!chain.is_empty());
        pc.sweep_id = INVALID;
        pc.cad_id = INVALID64; // delay giving ids
        for &p in lits {
            pc.literals.push(internal.citten2lit(p)); // conversion
        }
        for &p in chain.iter().rev() {
            pc.chain.push(p);
        }
    }
    #[cfg(feature = "logging")]
    {
        if learned {
            log!(
                internal,
                &pc.literals,
                "traced {}",
                if pc.learned { "learned" } else { "original" }
            );
        } else {
            debug_assert!((id as usize) < sweeper.clauses.len());
            log!(internal, sweeper.clauses[id as usize], "traced");
        }
    }
    sweeper.core[sweeper.save as usize].push(pc);
}

fn citten_terminate(data: *mut libc::c_void) -> i32 {
    // SAFETY: 'data' is the 'Internal' registered in
    // 'citten_clear_track_log_terminate'.
    unsafe { (*(data as *mut Internal)).terminated_asynchronously(1) as i32 }
}

#[derive(Clone, Copy, Debug)]
struct sweep_candidate {
    rank: u32,
    idx: i32,
}

#[inline]
fn rank_sweep_candidate(a: &sweep_candidate, b: &sweep_candidate) -> bool {
    debug_assert!(a.rank != 0 && b.rank != 0);
    debug_assert!(a.idx > 0 && b.idx > 0);
    if a.rank < b.rank {
        return true;
    }
    if b.rank < a.rank {
        return false;
    }
    a.idx < b.idx
}

/*------------------------------------------------------------------------*/

impl Internal {
    pub fn sweep_solve(&mut self) -> i32 {
        start!(self, sweepsolve);
        kitten_randomize_phases(citten(self));
        self.stats.sweep_solved += 1;
        let res = kitten_solve(citten(self));
        if res == 10 {
            self.stats.sweep_sat += 1;
        }
        if res == 20 {
            self.stats.sweep_unsat += 1;
        }
        stop!(self, sweepsolve);
        res
    }

    pub fn sweep_flip(&mut self, lit: i32) -> bool {
        start!(self, sweepflip);
        let res = kitten_flip_signed_literal(citten(self), lit);
        stop!(self, sweepflip);
        res
    }

    pub fn sweep_flip_and_implicant(&mut self, lit: i32) -> i32 {
        start!(self, sweepimplicant);
        let res = kitten_flip_and_implicant_for_signed_literal(citten(self), lit);
        stop!(self, sweepimplicant);
        res
    }

    pub fn sweep_set_kitten_ticks_limit(&mut self, sweeper: &mut Sweeper) {
        let mut remaining: u64 = 0;
        let current = sweeper.current_ticks;
        if current < sweeper.limit.ticks {
            remaining = sweeper.limit.ticks - current;
        }
        log!(self, "'kitten_ticks' remaining {}", remaining);
        kitten_set_ticks_limit(citten(self), remaining);
    }

    pub fn sweep_update_noccs(&mut self, c: CRef) {
        if c.redundant() {
            return;
        }
        for &lit in c.lits() {
            *self.noccs_mut(lit) -= 1;
        }
    }

    pub fn can_sweep_clause(&mut self, c: CRef) -> bool {
        if c.garbage() {
            return false;
        }
        if !c.redundant() {
            return true;
        }
        c.size() == 2 // && !c->hyper;  // could ignore hyper
    }

    /// Essentially do full occurence list as in 'elim.cpp'.
    pub fn sweep_dense_mode_and_watch_irredundant(&mut self) {
        self.reset_watches();

        self.init_noccs();

        // mark satisfied irredundant clauses as garbage
        for ci in 0..self.clauses.len() {
            let c = self.clauses[ci];
            if !self.can_sweep_clause(c) {
                continue;
            }
            let mut satisfied = false;
            for &lit in c.lits() {
                let tmp = self.val(lit);
                if tmp <= 0 {
                    continue;
                }
                if tmp > 0 {
                    satisfied = true;
                    break;
                }
            }
            if satisfied {
                self.mark_garbage(c); // forces more precise counts
            } else {
                for &lit in c.lits() {
                    *self.noccs_mut(lit) += 1;
                }
            }
        }

        self.init_occs();

        // Connect irredundant clauses.
        //
        for ci in 0..self.clauses.len() {
            let c = self.clauses[ci];
            if self.terminated_asynchronously(1) {
                break;
            }
            if !c.garbage() {
                for &lit in c.lits() {
                    if self.active(lit) {
                        self.occs_mut(lit).push(c);
                    }
                }
            } else if c.size() == 2 {
                if !c.flushed() {
                    if self.proof.is_some() {
                        c.set_flushed(true);
                        self.proof.as_mut().unwrap().delete_clause(c);
                    }
                }
            }
        }
    }

    /// Go back to two watch scheme.
    pub fn sweep_sparse_mode(&mut self) {
        self.reset_occs();
        self.reset_noccs();
        self.init_watches();
        self.connect_watches(false);
    }

    /// Propagate without watches but full occurence list.
    pub fn sweep_dense_propagate(&mut self, sweeper: &mut Sweeper) {
        let mut i = 0usize;
        while i < sweeper.propagate.len() {
            let lit = sweeper.propagate[i];
            i += 1;
            log!(self, "sweeping propagation of {}", lit);
            debug_assert!(self.val(lit) > 0);
            sweeper.current_ticks = sweeper.current_ticks.wrapping_add(
                (1 + self.cache_lines_n(self.occs(-lit).len(), std::mem::size_of::<*const Clause>()))
                    as u64,
            );
            // The occurrence list of '-lit' is not changed below.
            let nns = self.occs(-lit).len();
            for k in 0..nns {
                let c = self.occs(-lit)[k];
                sweeper.current_ticks = sweeper.current_ticks.wrapping_add(1);
                if !self.can_sweep_clause(c) {
                    continue;
                }
                let mut unit = 0i32;
                let mut satisfied = 0i32;
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
                    log!(
                        self,
                        c,
                        "sweeping propagation of {} finds {} satisfied",
                        lit,
                        satisfied
                    );
                    self.mark_garbage(c);
                    self.sweep_update_noccs(c);
                } else if unit == 0 {
                    log!(self, "empty clause during sweeping propagation of {}", lit);
                    // need to set conflict = c for lrat
                    self.conflict = c;
                    self.learn_empty_clause();
                    self.conflict = CRef::NULL;
                    break;
                } else if unit != i32::MIN {
                    log!(self, "new unit {} during sweeping propagation of {}", unit, lit);
                    self.build_chain_for_units(unit, c, false);
                    self.assign_unit(unit);
                    sweeper.propagate.push(unit);
                    sweeper.current_ticks = sweeper.current_ticks.wrapping_add(1);
                }
            }
            if self.unsat {
                break;
            }

            // not necessary but should help
            sweeper.current_ticks = sweeper.current_ticks.wrapping_add(
                (1 + self.cache_lines_n(self.occs(lit).len(), std::mem::size_of::<*const Clause>()))
                    as u64,
            );
            let nps = self.occs(lit).len();
            for k in 0..nps {
                let c = self.occs(lit)[k];
                sweeper.current_ticks = sweeper.current_ticks.wrapping_add(1);
                if c.garbage() {
                    continue;
                }
                // if (c->redundant)  // TODO I assume it does not hurt to
                // mark everything here continue;
                log!(self, c, "sweeping propagation of {} produces satisfied", lit);
                self.mark_garbage(c);
                self.sweep_update_noccs(c);
            }
        }
        sweeper.propagate.clear();
    }

    pub fn kitten_ticks_limit_hit(&mut self, sweeper: &mut Sweeper, when: &str) -> bool {
        let current = kitten_current_ticks(citten(self)).wrapping_add(sweeper.current_ticks);
        if current >= sweeper.limit.ticks {
            log!(
                self,
                "'kitten_ticks' limit of {} ticks hit after {} ticks during {}",
                sweeper.limit.ticks,
                current,
                when
            );
            return true;
        }
        let _ = when;
        false
    }

    pub fn init_sweeper(&mut self, sweeper: &mut Sweeper) {
        sweeper.encoded = 0;
        enlarge_zero(&mut sweeper.depths, (self.max_var + 1) as usize);
        sweeper.reprs = vec![0; (2 * self.max_var + 1) as usize];
        enlarge_zero(&mut sweeper.prev, (self.max_var + 1) as usize);
        enlarge_zero(&mut sweeper.next, (self.max_var + 1) as usize);
        for lit in self.lits() {
            sweeper.set_repr(lit, lit);
        }
        sweeper.first = 0;
        sweeper.last = 0;
        sweeper.current_ticks = 2 * self.clauses.len() as u64; // initialize with the cost of building full occ list.
        sweeper.current_ticks = sweeper.current_ticks.wrapping_add(
            (2 + 2 * self.cache_lines_n(self.clauses.len(), std::mem::size_of::<*const Clause>()))
                as u64,
        );
        debug_assert!(self.citten.is_none());
        self.citten = Some(kitten_init());
        self.citten_clear_track_log_terminate();

        self.sweep_dense_mode_and_watch_irredundant(); // full occurence list

        if self.lrat {
            sweeper.prev_units.push(false);
            for idx in self.vars() {
                sweeper.prev_units.push(self.val(idx) != 0);
            }
        }

        let mut completed: u32 = self.stats.sweep_completed as u32;
        let max_completed: u32 = 32;
        if completed > max_completed {
            completed = max_completed;
        }

        let mut vars_limit: u64 = self.opts.sweepvars as u64;
        vars_limit <<= completed;
        let max_vars_limit: u32 = self.opts.sweepmaxvars as u32;
        if vars_limit > max_vars_limit as u64 {
            vars_limit = max_vars_limit as u64;
        }
        sweeper.limit.vars = vars_limit as u32;
        verbose!(self, 3, "sweeper variable limit {}", sweeper.limit.vars);

        let mut depth_limit: u64 = self.stats.sweep_completed as u64;
        depth_limit = depth_limit.wrapping_add(self.opts.sweepdepth as u64);
        let max_depth: u32 = self.opts.sweepmaxdepth as u32;
        if depth_limit > max_depth as u64 {
            depth_limit = max_depth as u64;
        }
        sweeper.limit.depth = depth_limit as u32;
        verbose!(self, 3, "sweeper depth limit {}", sweeper.limit.depth);

        let mut clause_limit: u64 = self.opts.sweepclauses as u64;
        clause_limit <<= completed;
        let max_clause_limit: u32 = self.opts.sweepmaxclauses as u32;
        if clause_limit > max_clause_limit as u64 {
            clause_limit = max_clause_limit as u64;
        }
        sweeper.limit.clauses = clause_limit as u32;
        verbose!(self, 3, "sweeper clause limit {}", sweeper.limit.clauses);
    }

    pub fn release_sweeper(&mut self, sweeper: &mut Sweeper) {
        erase_vector(&mut sweeper.reprs);

        erase_vector(&mut sweeper.depths);
        erase_vector(&mut sweeper.prev);
        erase_vector(&mut sweeper.next);
        erase_vector(&mut sweeper.vars);
        erase_vector(&mut sweeper.clause);
        erase_vector(&mut sweeper.backbone);
        erase_vector(&mut sweeper.partition);
        erase_vector(&mut sweeper.prev_units);
        for i in 0..2 {
            erase_vector(&mut sweeper.core[i]);
        }

        kitten_release(self.citten.take().expect("citten initialized"));
        self.stats.ticks.sweep = (self.stats.ticks.sweep as u64).wrapping_add(sweeper.current_ticks) as i64;
        self.sweep_sparse_mode();
    }

    pub fn clear_sweeper(&mut self, sweeper: &mut Sweeper) {
        log!(self, "clearing sweeping environment");
        sweeper.current_ticks = sweeper.current_ticks.wrapping_add(kitten_current_ticks(citten(self)));

        self.citten_clear_track_log_terminate();
        for &idx in sweeper.vars.iter() {
            debug_assert!(sweeper.depths[idx as usize] != 0);
            sweeper.depths[idx as usize] = 0;
        }
        sweeper.vars.clear();
        for &c in sweeper.clauses.iter() {
            debug_assert!(c.swept());
            c.set_swept(false);
        }
        sweeper.clauses.clear();
        sweeper.backbone.clear();
        sweeper.partition.clear();
        sweeper.encoded = 0;
        self.sweep_set_kitten_ticks_limit(sweeper);
    }

    pub fn sweep_repr(&mut self, sweeper: &mut Sweeper, lit: i32) -> i32 {
        let mut res;
        {
            let mut prev = lit;
            loop {
                res = sweeper.repr_of(prev);
                if res == prev {
                    break;
                }
                prev = res;
            }
        }
        if res == lit {
            return res;
        }
        log!(self, "sweeping repr[{}] = {}", lit, res);
        {
            let not_res = -res;
            let mut prev = lit;
            loop {
                let next = sweeper.repr_of(prev);
                if next == res {
                    break;
                }
                let not_prev = -prev;
                sweeper.set_repr(not_prev, not_res);
                sweeper.set_repr(prev, res);
                prev = next;
            }
            debug_assert!(sweeper.repr_of(-prev) == not_res);
        }
        res
    }

    pub fn add_literal_to_environment(&mut self, sweeper: &mut Sweeper, depth: u32, lit: i32) {
        let repr = self.sweep_repr(sweeper, lit);
        if repr != lit {
            return;
        }
        let idx = lit.abs();
        if sweeper.depths[idx as usize] != 0 {
            return;
        }
        debug_assert!(depth < u32::MAX);
        sweeper.depths[idx as usize] = depth + 1;
        debug_assert!(idx != 0);
        sweeper.vars.push(idx);
        log!(self, "sweeping[{}] adding literal {}", depth, lit);
    }

    pub fn sweep_add_clause(&mut self, sweeper: &mut Sweeper, depth: u32) {
        // TODO: assertion fails, check if this an issue or can be avoided
        // assert (sweeper.clause.size () > 1);
        for k in 0..sweeper.clause.len() {
            let lit = sweeper.clause[k];
            self.add_literal_to_environment(sweeper, depth, lit);
        }
        citten_clause_with_id(citten(self), sweeper.clauses.len() as u32, &sweeper.clause);
        sweeper.clause.clear();
        if self.opts.sweepcountbinary != 0 || sweeper.clause.len() > 2 {
            sweeper.encoded += 1;
        }
    }

    pub fn sweep_clause(&mut self, sweeper: &mut Sweeper, depth: u32, c: CRef) {
        if c.swept() {
            return;
        }
        debug_assert!(self.can_sweep_clause(c));
        log!(self, c, "sweeping[{}]", depth);
        debug_assert!(sweeper.clause.is_empty());
        for &lit in c.lits() {
            let tmp = self.val(lit);
            if tmp > 0 {
                self.mark_garbage(c);
                self.sweep_update_noccs(c);
                sweeper.clause.clear();
                return;
            }
            if tmp < 0 {
                if self.lrat {
                    sweeper.prev_units[lit.abs() as usize] = true;
                }
                continue;
            }
            sweeper.clause.push(lit);
        }
        c.set_swept(true);
        self.sweep_add_clause(sweeper, depth);
        sweeper.clauses.push(c);
    }

    pub fn citten_clear_track_log_terminate(&mut self) {
        debug_assert!(self.citten.is_some());
        kitten_clear(citten(self));
        kitten_track_antecedents(citten(self));
        if self.external().terminator.is_some() {
            let data = self as *mut Internal as *mut libc::c_void;
            kitten_set_terminator(citten(self), data, citten_terminate);
        }
        #[cfg(feature = "logging")]
        if self.opts.log != 0 {
            kitten_set_logging(citten(self));
        }
    }

    pub fn add_core(&mut self, sweeper: &mut Sweeper, core_idx: u32) {
        if self.unsat {
            return;
        }
        log!(self, "check and add extracted core[{}] lemmas to proof", core_idx);
        debug_assert!(core_idx == 0 || core_idx == 1);
        let ci = core_idx as usize;

        debug_assert!(!self.lrat || self.proof.is_some());

        let mut unsat_size: u32 = 0;
        let ncore = sweeper.core[ci].len();
        for pi in 0..ncore {
            unsat_size += 1;

            if !sweeper.core[ci][pi].learned {
                log!(
                    self,
                    &sweeper.core[ci][pi].literals,
                    "not adding already present core[{}] kitten[{}] clause",
                    core_idx,
                    sweeper.core[ci][pi].kit_id
                );
                continue;
            }

            log!(
                self,
                &sweeper.core[ci][pi].literals,
                "adding extracted core[{}] kitten[{}] lemma",
                core_idx,
                sweeper.core[ci][pi].kit_id
            );

            let new_size = sweeper.core[ci][pi].literals.len() as u32;

            if self.lrat {
                debug_assert!(sweeper.core[ci][pi].cad_id == INVALID64);
                let core = &sweeper.core[ci];
                let pc = &core[pi];
                for &cid in pc.chain.iter() {
                    let mut id: i64 = 0;
                    for cpc in core.iter() {
                        if cpc.kit_id == cid {
                            if cpc.learned {
                                id = cpc.cad_id;
                            } else {
                                id = cpc.cad_id;
                                debug_assert!(cpc.cad_id == sweeper.clauses[cpc.sweep_id as usize].id());
                                debug_assert!(!sweeper.clauses[cpc.sweep_id as usize].garbage());
                                // avoid duplicate ids of units with seen flags
                                for &lit in cpc.literals.iter() {
                                    if self.val(lit) >= 0 {
                                        continue;
                                    }
                                    if self.flags(lit).seen {
                                        continue;
                                    }
                                    let idx = lit.abs();
                                    if sweeper.prev_units[idx as usize] {
                                        let uid = self.unit_id(-lit);
                                        self.lrat_chain.push(uid);
                                        self.analyzed.push(lit);
                                        self.flags_mut(lit).seen = true;
                                    }
                                }
                            }
                            break;
                        }
                    }
                    debug_assert!(id != 0);
                    if id != INVALID64 {
                        self.lrat_chain.push(id);
                    }
                }
                self.clear_analyzed_literals();
            }

            if new_size == 0 {
                log!(self, "sweeping produced empty clause");
                self.learn_empty_clause();
                sweeper.core[ci].truncate(unsat_size as usize);
                return;
            }

            if new_size == 1 {
                let unit = sweeper.core[ci][pi].literals[0];
                if self.val(unit) > 0 {
                    log!(self, "already assigned sweeping unit {}", unit);
                    self.lrat_chain.clear();
                } else if self.val(unit) < 0 {
                    log!(self, "falsified sweeping unit {} leads to empty clause", unit);
                    if self.lrat {
                        let id = self.unit_id(-unit);
                        self.lrat_chain.push(id);
                    }
                    self.learn_empty_clause();
                    sweeper.core[ci].truncate(unsat_size as usize);
                    return;
                } else {
                    log!(self, "sweeping produced unit {}", unit);
                    self.assign_unit(unit);
                    self.stats.sweep_units += 1;
                    sweeper.propagate.push(unit);
                }
                if self.proof.is_some() && self.lrat {
                    sweeper.core[ci][pi].cad_id = self.unit_id(unit);
                }
                continue;
            }

            debug_assert!(new_size > 1);
            debug_assert!(sweeper.core[ci][pi].learned);

            if self.proof.is_some() {
                self.clause_id += 1;
                let id = self.clause_id;
                sweeper.core[ci][pi].cad_id = id;
                self.proof.as_mut().unwrap().add_derived_clause_lits(
                    id,
                    true,
                    &sweeper.core[ci][pi].literals,
                    &self.lrat_chain,
                );
                self.lrat_chain.clear();
            }
        }
    }

    pub fn save_core(&mut self, sweeper: &mut Sweeper, core: u32) {
        log!(self, "saving extracted core[{}] lemmas", core);
        debug_assert!(core == 0 || core == 1);
        debug_assert!(sweeper.core[core as usize].is_empty());
        sweeper.save = core;
        kitten_compute_clausal_core(citten(self), None);
        // The call backs access the solver through 'sweeper.internal' (as
        // in C++), which does not touch the kitten itself.
        let k: *mut Kitten = citten(self);
        if self.lrat {
            // SAFETY: the kitten is boxed and stays alive during the call.
            kitten_trace_core(unsafe { &mut *k }, &mut |cid, id, learned, lits, chain| {
                save_core_clause_with_lrat(sweeper, cid, id, learned, lits, chain)
            });
        } else {
            // SAFETY: see above.
            kitten_traverse_core_clauses_with_id(unsafe { &mut *k }, &mut |id, learned, lits| {
                save_core_clause(sweeper, id, learned, lits)
            });
        }
    }

    pub fn clear_core(&mut self, sweeper: &mut Sweeper, core_idx: u32) {
        debug_assert!(core_idx == 0 || core_idx == 1);
        log!(self, "clearing core[{}] lemmas", core_idx);
        let ci = core_idx as usize;
        if self.proof.is_some() {
            log!(self, "deleting sub-solver core clauses");
            for pc in sweeper.core[ci].iter() {
                if pc.learned && pc.literals.len() > 1 {
                    self.proof.as_mut().unwrap().delete_clause_lits(pc.cad_id, true, &pc.literals);
                }
            }
        }
        sweeper.core[ci].clear();
    }

    pub fn save_add_clear_core(&mut self, sweeper: &mut Sweeper) {
        self.save_core(sweeper, 0);
        // now skip adding the core completely if terminated_asynchronously.
        // Else need full adding and clearing (including proof deletion
        // steps)
        if !self.terminated_asynchronously(1) {
            self.add_core(sweeper, 0);
            self.clear_core(sweeper, 0);
        } else {
            sweeper.core[0].clear(); // just clear the (possibly partially) filled vec
        }
    }

    pub fn init_backbone_and_partition(&mut self, sweeper: &mut Sweeper) {
        log!(self, "initializing backbone and equivalent literals candidates");
        sweeper.backbone.clear();
        sweeper.partition.clear();
        for k in 0..sweeper.vars.len() {
            let idx = sweeper.vars[k];
            if !self.active(idx) {
                continue;
            }
            debug_assert!(idx > 0);
            let lit = idx;
            let not_lit = -lit;
            let tmp = kitten_signed_value(citten(self), lit);
            let candidate = if tmp < 0 { not_lit } else { lit };
            log!(self, "sweeping candidate {}", candidate);
            sweeper.backbone.push(candidate);
            sweeper.partition.push(candidate);
        }
        sweeper.partition.push(0);

        log!(self, &sweeper.backbone, "initialized backbone candidates");
        log!(self, &sweeper.partition, "initialized equivalence candidates");
    }

    pub fn sweep_empty_clause(&mut self, sweeper: &mut Sweeper) {
        debug_assert!(!self.unsat);
        self.save_add_clear_core(sweeper);
        debug_assert!(self.unsat || self.terminated_asynchronously(1));
    }

    pub fn sweep_refine_partition(&mut self, sweeper: &mut Sweeper) {
        log!(self, "refining partition");
        let mut new_partition: Vec<i32> = Vec::new();
        let old_end = sweeper.partition.len();
        #[cfg(feature = "logging")]
        let mut old_classes: u32 = 0;
        #[cfg(feature = "logging")]
        let mut new_classes: u32 = 0;
        let mut p = 0usize;
        while p != old_end {
            let mut assigned_true: u32 = 0;
            #[allow(unused_assignments)]
            let mut other: i32;
            let mut q = p;
            loop {
                other = sweeper.partition[q];
                if other == 0 {
                    break;
                }
                q += 1;
                if self.sweep_repr(sweeper, other) != other {
                    continue;
                }
                if self.val(other) != 0 {
                    continue;
                }
                let value = kitten_signed_value(citten(self), other);
                if value == 0 {
                    log!(self, "dropping sub-solver unassigned {}", other);
                } else if value > 0 {
                    new_partition.push(other);
                    assigned_true += 1;
                }
            }
            #[cfg(feature = "logging")]
            {
                log!(self, "refining class {} of size {}", old_classes, q - p);
                old_classes += 1;
            }
            if assigned_true == 0 {
                log!(self, "no positive literal in class");
            } else if assigned_true == 1 {
                other = *new_partition.last().unwrap();
                new_partition.pop();
                log!(self, "dropping singleton class {}", other);
            } else {
                log!(self, "{} positive literal in class", assigned_true);
                new_partition.push(0);
                #[cfg(feature = "logging")]
                {
                    new_classes += 1;
                }
            }

            let mut assigned_false: u32 = 0;
            q = p;
            loop {
                other = sweeper.partition[q];
                if other == 0 {
                    break;
                }
                q += 1;
                if self.sweep_repr(sweeper, other) != other {
                    continue;
                }
                if self.val(other) != 0 {
                    continue;
                }
                let value = kitten_signed_value(citten(self), other);
                if value < 0 {
                    new_partition.push(other);
                    assigned_false += 1;
                }
            }

            if assigned_false == 0 {
                log!(self, "no negative literal in class");
            } else if assigned_false == 1 {
                other = *new_partition.last().unwrap();
                new_partition.pop();
                log!(self, "dropping singleton class {}", other);
            } else {
                log!(self, "{} negative literal in class", assigned_false);
                new_partition.push(0);
                #[cfg(feature = "logging")]
                {
                    new_classes += 1;
                }
            }
            let _ = other;
            p = q + 1;
        }
        std::mem::swap(&mut sweeper.partition, &mut new_partition);
        log!(self, "refined {} classes into {}", old_classes, new_classes);
    }

    pub fn sweep_refine_backbone(&mut self, sweeper: &mut Sweeper) {
        log!(self, "refining backbone candidates");
        let end = sweeper.backbone.len();
        let mut q = 0usize;
        let mut p = q;
        while p != end {
            let lit = sweeper.backbone[p];
            p += 1;
            if self.val(lit) != 0 {
                continue;
            }
            let value = kitten_signed_value(citten(self), lit);
            if value == 0 {
                log!(self, "dropping sub-solver unassigned {}", lit);
            } else if value > 0 {
                sweeper.backbone[q] = lit;
                q += 1;
            }
        }
        sweeper.backbone.truncate(q);
    }

    pub fn sweep_refine(&mut self, sweeper: &mut Sweeper) {
        debug_assert!(kitten_status(citten(self)) == 10);
        if sweeper.backbone.is_empty() {
            log!(self, "no need to refine empty backbone candidates");
        } else {
            self.sweep_refine_backbone(sweeper);
        }
        if sweeper.partition.is_empty() {
            log!(self, "no need to refine empty partition candidates");
        } else {
            self.sweep_refine_partition(sweeper);
        }
    }

    pub fn flip_backbone_literals(&mut self, sweeper: &mut Sweeper) {
        let max_rounds = self.opts.sweepfliprounds as u32;
        if max_rounds == 0 {
            return;
        }
        debug_assert!(!sweeper.backbone.is_empty());
        if kitten_status(citten(self)) != 10 {
            return;
        }
        #[cfg(feature = "logging")]
        let mut total_flipped: u32 = 0;
        let mut flipped: u32;
        let mut round: u32 = 0;
        loop {
            round += 1;
            flipped = 0;
            let refine = false;
            let mut q = 0usize;
            let mut p = q;
            let end = sweeper.backbone.len();
            let limit_hit = false;
            while p != end {
                let lit = sweeper.backbone[p];
                p += 1;
                self.stats.sweep_flip_backbone += 1;
                if limit_hit || self.terminated_asynchronously(1) {
                    break;
                } else if self.sweep_flip(lit) {
                    log!(self, "flipping backbone candidate {} succeeded", lit);
                    #[cfg(feature = "logging")]
                    {
                        total_flipped += 1;
                    }
                    self.stats.sweep_flipped_backbone += 1;
                    flipped += 1;
                } else {
                    log!(self, "flipping backbone candidate {} failed", lit);
                    sweeper.backbone[q] = lit;
                    q += 1;
                }
            }
            while p != end {
                sweeper.backbone[q] = sweeper.backbone[p];
                q += 1;
                p += 1;
            }
            sweeper.backbone.truncate(q);
            log!(self, "flipped {} backbone candidates in round {}", flipped, round);

            if limit_hit {
                break;
            }
            if self.terminated_asynchronously(1) {
                break;
            }
            if self.kitten_ticks_limit_hit(sweeper, "backbone flipping") {
                break;
            }
            if refine {
                self.sweep_refine(sweeper);
            }
            if !(flipped != 0 && round < max_rounds) {
                break;
            }
        }
        log!(
            self,
            "flipped {} backbone candidates in total in {} rounds",
            total_flipped,
            round
        );
    }

    pub fn sweep_extract_fixed(&mut self, sweeper: &mut Sweeper, lit: i32) -> bool {
        let not_lit = -lit;
        self.stats.sweep_solved_backbone += 1;
        kitten_assume_signed(citten(self), not_lit);
        let res = self.sweep_solve();
        if res == 0 {
            self.stats.sweep_unknown_backbone += 1;
            return false;
        }
        debug_assert!(res == 20);
        log!(self, "sweep unit {}", lit);
        self.save_add_clear_core(sweeper);
        self.stats.sweep_unsat_backbone += 1;
        true
    }

    pub fn sweep_backbone_candidate(&mut self, sweeper: &mut Sweeper, lit: i32) -> bool {
        log!(self, "trying backbone candidate {}", lit);
        let value = kitten_fixed_signed(citten(self), lit);
        if value != 0 {
            self.stats.sweep_fixed_backbone += 1;
            debug_assert!(value > 0);
            if self.val(lit) <= 0 {
                return self.sweep_extract_fixed(sweeper, lit);
            } else {
                log!(self, "literal {} already fixed", lit);
            }
            return false;
        }

        let mut res = kitten_status(citten(self));
        if res != 10 {
            log!(self, "not flipping due to status {} != 10", res);
        }
        self.stats.sweep_flip_backbone += 1;
        if res == 10 && self.sweep_flip(lit) {
            self.stats.sweep_flipped_backbone += 1;
            log!(self, "flipping {} succeeded", lit);
            // LOGBACKBONE ("refined backbone candidates");
            return false;
        }

        log!(self, "flipping {} failed", lit);
        let not_lit = -lit;
        self.stats.sweep_solved_backbone += 1;
        kitten_assume_signed(citten(self), not_lit);
        res = self.sweep_solve();
        if res == 10 {
            log!(self, "sweeping backbone candidate {} failed", lit);
            self.sweep_refine(sweeper);
            self.stats.sweep_sat_backbone += 1;
            return false;
        }

        if res == 20 {
            log!(self, "sweep unit {}", lit);
            self.save_add_clear_core(sweeper);
            debug_assert!(self.val(lit) != 0 || self.terminated_asynchronously(1));
            self.stats.sweep_unsat_backbone += 1;
            return true;
        }

        self.stats.sweep_unknown_backbone += 1;

        log!(self, "sweeping backbone candidate {} failed", lit);
        false
    }

    /// At this point the binary (lit or other) is already present in the
    /// proof via 'add_core'.  We just copy it as an irredundant clause, call
    /// weaken minus and push it on the extension stack.
    pub fn add_sweep_binary(&mut self, pc: sweep_proof_clause, lit: i32, other: i32) -> i64 {
        debug_assert!(!self.unsat);
        if self.unsat {
            return 0; // sanity check, should be fuzzed
        }

        debug_assert!(self.val(lit) == 0 && self.val(other) == 0);
        if self.val(lit) != 0 || self.val(other) != 0 {
            return 0;
        }

        if self.lrat {
            for &plit in pc.literals.iter() {
                if self.val(plit) != 0 {
                    let id = self.unit_id(-plit);
                    self.lrat_chain.push(id);
                }
            }
            self.lrat_chain.push(pc.cad_id);
        }
        self.clause.push(lit);
        self.clause.push(other);
        self.clause_id += 1;
        let id = self.clause_id;
        if self.proof.is_some() {
            self.proof.as_mut().unwrap().add_derived_clause_lits(id, false, &self.clause, &self.lrat_chain);
            self.proof.as_mut().unwrap().weaken_minus_lits(id, &self.clause);
        }
        self.external().push_binary_clause_on_extension_stack(id, lit, other);
        for t in 0..self.tracers.len() {
            if self.externalize(lit) < 0 {
                break;
            }
            let elit = self.externalize(lit);
            let eother = self.externalize(other);
            self.tracers[t].notify_equivalence(elit, -eother);
        }
        self.clause.clear();
        self.lrat_chain.clear();
        id
    }

    pub fn delete_sweep_binary(&mut self, sb: &sweep_binary) {
        if self.unsat {
            return;
        }
        if self.proof.is_none() {
            return;
        }
        let bin: Vec<i32> = vec![sb.lit, sb.other];
        self.proof.as_mut().unwrap().delete_clause_lits(sb.id, false, &bin);
    }

    pub fn scheduled_variable(&mut self, sweeper: &mut Sweeper, idx: i32) -> bool {
        sweeper.prev[idx as usize] != 0 || sweeper.first == idx
    }

    pub fn schedule_inner(&mut self, sweeper: &mut Sweeper, idx: i32) {
        debug_assert!(idx != 0);
        if !self.active(idx) {
            return;
        }
        let next = sweeper.next[idx as usize];
        if next != 0 {
            log!(self, "rescheduling inner {} as last", idx);
            let prev = sweeper.prev[idx as usize];
            debug_assert!(sweeper.prev[next as usize] == idx);
            sweeper.prev[next as usize] = prev;
            if prev == 0 {
                debug_assert!(sweeper.first == idx);
                sweeper.first = next;
            } else {
                debug_assert!(sweeper.next[prev as usize] == idx);
                sweeper.next[prev as usize] = next;
            }
            let last = sweeper.last;
            if last == 0 {
                debug_assert!(sweeper.first == 0);
                sweeper.first = idx;
            } else {
                debug_assert!(sweeper.next[last as usize] == 0);
                sweeper.next[last as usize] = idx;
            }
            sweeper.prev[idx as usize] = last;
            sweeper.next[idx as usize] = 0;
            sweeper.last = idx;
        } else if sweeper.last != idx {
            log!(self, "scheduling inner {} as last", idx);
            let last = sweeper.last;
            if last == 0 {
                debug_assert!(sweeper.first == 0);
                sweeper.first = idx;
            } else {
                debug_assert!(sweeper.next[last as usize] == 0);
                sweeper.next[last as usize] = idx;
            }
            debug_assert!(sweeper.next[idx as usize] == 0);
            sweeper.prev[idx as usize] = last;
            sweeper.last = idx;
        } else {
            log!(self, "keeping inner {} scheduled as last", idx);
        }
    }

    pub fn schedule_outer(&mut self, sweeper: &mut Sweeper, idx: i32) {
        debug_assert!(!self.scheduled_variable(sweeper, idx));
        debug_assert!(self.active(idx));
        let first = sweeper.first;
        if first == 0 {
            debug_assert!(sweeper.last == 0);
            sweeper.last = idx;
        } else {
            debug_assert!(sweeper.prev[first as usize] == 0);
            sweeper.prev[first as usize] = idx;
        }
        debug_assert!(sweeper.prev[idx as usize] == 0);
        sweeper.next[idx as usize] = first;
        sweeper.first = idx;
        log!(self, "scheduling outer {} as first", idx);
    }

    pub fn next_scheduled(&mut self, sweeper: &mut Sweeper) -> i32 {
        let res = sweeper.last;
        if res == 0 {
            log!(self, "no more scheduled variables left");
            return 0;
        }
        debug_assert!(res > 0);
        log!(self, "dequeuing next scheduled {}", res);
        let prev = sweeper.prev[res as usize];
        debug_assert!(sweeper.next[res as usize] == 0);
        sweeper.prev[res as usize] = 0;
        if prev == 0 {
            debug_assert!(sweeper.first == res);
            sweeper.first = 0;
        } else {
            debug_assert!(sweeper.next[prev as usize] == res);
            sweeper.next[prev as usize] = 0;
        }
        sweeper.last = prev;
        res
    }

    pub fn sweep_substitute_lrat(&mut self, c: CRef, id: i64) {
        if !self.lrat {
            return;
        }
        for &lit in c.lits() {
            debug_assert!(self.val(lit) <= 0);
            if self.val(lit) < 0 {
                let id = self.unit_id(-lit);
                self.lrat_chain.push(id);
            }
        }
        self.lrat_chain.push(id);
        self.lrat_chain.push(c.id());
    }

    /// Substitute equivalences in clauses (see
    /// 'sweep_substitute_new_equivalences' for explanation).
    pub fn substitute_connected_clauses(&mut self, sweeper: &mut Sweeper, lit: i32, repr: i32, id: i64) {
        if self.unsat {
            return;
        }
        if self.val(lit) != 0 {
            return;
        }
        if self.val(repr) != 0 {
            return;
        }
        log!(self, "substituting {} with {} in all irredundant clauses", lit, repr);

        debug_assert!(lit != repr);
        debug_assert!(lit != -repr);

        debug_assert!(self.active(lit));
        debug_assert!(self.active(repr));

        {
            sweeper.current_ticks = sweeper.current_ticks.wrapping_add(
                (1 + self.cache_lines_n(self.occs(lit).len(), std::mem::size_of::<*const Clause>()))
                    as u64,
            );
            // Only 'occs (repr)' gets new elements below ('repr != lit'), so
            // re-indexing 'occs (lit)' is equivalent to the C++ reference.
            let end = self.occs(lit).len();
            let mut q = 0usize;
            let mut p = q;
            while p != end {
                let c = self.occs(lit)[p];
                self.occs_mut(lit)[q] = c;
                q += 1;
                p += 1;
                sweeper.current_ticks = sweeper.current_ticks.wrapping_add(1);
                if c.garbage() {
                    continue;
                }
                debug_assert!(self.clause.is_empty());
                let mut satisfied = false;
                let mut repr_already_watched = false;
                let not_repr = -repr;
                #[cfg(debug_assertions)]
                let mut found = false;
                for &other in c.lits() {
                    if other == lit {
                        #[cfg(debug_assertions)]
                        {
                            debug_assert!(!found);
                            found = true;
                        }
                        self.clause.push(repr);
                        continue;
                    }
                    debug_assert!(other != -lit);
                    if other == repr {
                        debug_assert!(!repr_already_watched);
                        repr_already_watched = true;
                        continue;
                    }
                    if other == not_repr {
                        satisfied = true;
                        break;
                    }
                    let tmp = self.val(other);
                    if tmp < 0 {
                        continue;
                    }
                    if tmp > 0 {
                        satisfied = true;
                        break;
                    }
                    self.clause.push(other);
                }
                if satisfied {
                    self.clause.clear();
                    self.mark_garbage(c);
                    self.sweep_update_noccs(c);
                    continue;
                }
                #[cfg(debug_assertions)]
                debug_assert!(found);
                let new_size = self.clause.len() as u32;
                self.sweep_substitute_lrat(c, id);
                if new_size == 0 {
                    log!(self, c, "substituted empty clause");
                    debug_assert!(!self.unsat);
                    self.learn_empty_clause();
                    break;
                }
                sweeper.current_ticks = sweeper.current_ticks.wrapping_add(1);
                if new_size == 1 {
                    log!(self, c, "reduces to unit");
                    let unit = self.clause[0];
                    self.clause.clear();
                    self.assign_unit(unit);
                    sweeper.propagate.push(unit);
                    self.mark_garbage(c);
                    self.sweep_update_noccs(c);
                    self.stats.sweep_units += 1;
                    break;
                }
                debug_assert!(c.size() >= 2);
                if !c.redundant() {
                    self.mark_removed(c, 0);
                }
                self.clause_id += 1;
                let new_id = self.clause_id as u64;
                if self.proof.is_some() {
                    self.proof.as_mut().unwrap().add_derived_clause_lits(
                        new_id as i64,
                        c.redundant(),
                        &self.clause,
                        &self.lrat_chain,
                    );
                    self.proof.as_mut().unwrap().delete_clause(c);
                }
                c.set_id(new_id as i64);
                self.lrat_chain.clear();
                let mut l = 0usize;
                while l < self.clause.len() {
                    c.set_lit(l, self.clause[l]);
                    l += 1;
                }
                let flushed = c.size() - l as i32;
                if flushed != 0 {
                    log!(self, "flushed {} literals", flushed);
                    let _ = self.shrink_clause(c, l as i32);
                } else if self.likely_to_be_kept_clause(c) {
                    self.mark_added(c);
                }
                log!(self, c, "substituted");
                if !repr_already_watched {
                    self.occs_mut(repr).push(c);
                    *self.noccs_mut(repr) += 1;
                }
                self.clause.clear();
                q -= 1;
            }
            while p != end {
                let c = self.occs(lit)[p];
                self.occs_mut(lit)[q] = c;
                q += 1;
                p += 1;
            }
            self.occs_mut(lit).truncate(q);
        }
    }

    /// In contrast to kissat we substitute the equivalences explicitely
    /// after every successful round of sweeping. This is necessary in order
    /// to extract valid LRAT proofs for subsequent rounds of sweeping.
    pub fn sweep_substitute_new_equivalences(&mut self, sweeper: &mut Sweeper) {
        if self.unsat {
            return;
        }

        let mut count: u32 = 0;
        debug_assert!(self.lrat_chain.is_empty());

        for k in 0..sweeper.binaries.len() {
            let sb = sweeper.binaries[k];
            count += 1;
            let lit = sb.lit;
            let other = sb.other;
            if lit.abs() < other.abs() {
                self.substitute_connected_clauses(sweeper, -other, lit, sb.id);
            } else {
                self.substitute_connected_clauses(sweeper, -lit, other, sb.id);
            }
            debug_assert!(self.lrat_chain.is_empty());
            if self.val(lit) < 0 {
                if self.lrat {
                    let lid = self.unit_id(-lit);
                    self.lrat_chain.push(lid);
                }
                if self.val(other) == 0 {
                    if self.lrat {
                        self.lrat_chain.push(sb.id);
                    }
                    self.assign_unit(other);
                } else if self.val(other) < 0 {
                    if self.lrat {
                        let oid = self.unit_id(-other);
                        self.lrat_chain.push(oid);
                        self.lrat_chain.push(sb.id);
                    }
                    self.learn_empty_clause();
                    return;
                }
            } else if self.val(other) < 0 {
                if self.val(lit) == 0 {
                    if self.lrat {
                        let oid = self.unit_id(-other);
                        self.lrat_chain.push(oid);
                        self.lrat_chain.push(sb.id);
                    }
                    self.assign_unit(lit);
                } else {
                    debug_assert!(self.val(lit) > 0);
                }
            }
            self.lrat_chain.clear();
            self.delete_sweep_binary(&sb);
            if count == 2 {
                if self.val(lit) == 0 && self.val(other) == 0 {
                    let idx = if lit.abs() < other.abs() { other.abs() } else { lit.abs() };
                    if !self.flags(idx).fixed() {
                        self.mark_substituted(idx);
                    }
                }
                count = 0;
            }
            debug_assert!(self.lrat_chain.is_empty());
        }
        sweeper.binaries.clear();
    }

    pub fn sweep_remove(&mut self, sweeper: &mut Sweeper, lit: i32) {
        debug_assert!(sweeper.repr_of(lit) != lit);
        let partition = &mut sweeper.partition;
        let begin_partition = 0usize;
        let mut p = begin_partition;
        let end_partition = partition.len();
        while partition[p] != lit {
            debug_assert!(p + 1 != end_partition);
            p += 1;
        }
        let mut begin_class = p;
        while begin_class != begin_partition && partition[begin_class - 1] != 0 {
            begin_class -= 1;
        }
        let mut end_class = p;
        while partition[end_class] != 0 {
            end_class += 1;
        }
        let size = (end_class - begin_class) as u32;
        log!(
            self,
            "removing non-representative {} from equivalence class of size {}",
            lit,
            size
        );
        debug_assert!(size > 1);
        let mut q = begin_class;
        if size == 2 {
            log!(self, "completely squashing equivalence class of {}", lit);
            let mut r = end_class + 1;
            while r != end_partition {
                partition[q] = partition[r];
                q += 1;
                r += 1;
            }
        } else {
            let mut r = begin_class;
            while r != end_partition {
                if r != p {
                    partition[q] = partition[r];
                    q += 1;
                }
                r += 1;
            }
        }
        partition.truncate(q);
    }

    pub fn flip_partition_literals(&mut self, sweeper: &mut Sweeper) {
        let max_rounds = self.opts.sweepfliprounds as u32;
        if max_rounds == 0 {
            return;
        }
        debug_assert!(!sweeper.partition.is_empty());
        if kitten_status(citten(self)) != 10 {
            return;
        }
        #[cfg(feature = "logging")]
        let mut total_flipped: u32 = 0;
        let mut flipped: u32;
        let mut round: u32 = 0;
        loop {
            round += 1;
            flipped = 0;
            let refine = false;
            let mut limit_hit = false;
            let begin = 0usize;
            let mut dst = begin;
            let mut src = dst;
            let end = sweeper.partition.len();
            while src != end {
                let mut end_src = src;
                while {
                    debug_assert!(end_src != end);
                    sweeper.partition[end_src] != 0
                } {
                    end_src += 1;
                }
                let mut size = (end_src - src) as u32;
                debug_assert!(size > 1);
                let mut q = dst;
                let mut p = src;
                while p != end_src {
                    let lit = sweeper.partition[p];
                    if limit_hit {
                        sweeper.partition[q] = lit;
                        q += 1;
                        p += 1;
                        continue;
                    } else if self.kitten_ticks_limit_hit(sweeper, "partition flipping") {
                        sweeper.partition[q] = lit;
                        q += 1;
                        limit_hit = true;
                        p += 1;
                        continue;
                    } else if self.sweep_flip(lit) {
                        log!(self, "flipping equivalence candidate {} succeeded", lit);
                        #[cfg(feature = "logging")]
                        {
                            total_flipped += 1;
                        }
                        flipped += 1;
                        size -= 1;
                        if size < 2 {
                            break;
                        }
                    } else {
                        log!(self, "flipping equivalence candidate {} failed", lit);
                        sweeper.partition[q] = lit;
                        q += 1;
                    }
                    self.stats.sweep_flip_equivalences += 1;
                    p += 1;
                }
                if size > 1 {
                    sweeper.partition[q] = 0;
                    q += 1;
                    dst = q;
                }
                src = end_src + 1;
            }
            self.stats.sweep_flipped_equivalences += flipped as i64;
            sweeper.partition.truncate(dst);
            log!(self, "flipped {} equivalence candidates in round {}", flipped, round);
            if self.terminated_asynchronously(1) {
                break;
            }
            if self.kitten_ticks_limit_hit(sweeper, "partition flipping") {
                break;
            }
            if refine {
                self.sweep_refine(sweeper);
            }
            if !(flipped != 0 && round < max_rounds) {
                break;
            }
        }
        log!(
            self,
            "flipped {} equivalence candidates in total in {} rounds",
            total_flipped,
            round
        );
    }

    pub fn sweep_equivalence_candidates(&mut self, sweeper: &mut Sweeper, lit: i32, other: i32) -> bool {
        log!(self, "trying equivalence candidates {} = {}", lit, other);
        let end = sweeper.partition.len();
        debug_assert!(3 <= end);
        debug_assert!(sweeper.partition[end - 3] == lit);
        debug_assert!(sweeper.partition[end - 2] == other);
        let third = if end == 3 { 0 } else { sweeper.partition[end - 4] };
        let mut res = kitten_status(citten(self));
        if res == 10 {
            self.stats.sweep_flip_equivalences += 1;
            if self.sweep_flip(lit) {
                self.stats.sweep_flipped_equivalences += 1;
                log!(self, "flipping {} succeeded", lit);
                if third == 0 {
                    log!(self, "squashing equivalence class of {}", lit);
                    let n = sweeper.partition.len() - 3;
                    sweeper.partition.truncate(n);
                } else {
                    log!(self, "removing {} from equivalence class of {}", lit, other);
                    sweeper.partition[end - 3] = other;
                    sweeper.partition[end - 2] = 0;
                    let n = sweeper.partition.len() - 1;
                    sweeper.partition.truncate(n);
                }
                return false;
            }
            self.stats.sweep_flip_equivalences += 1;
            if self.sweep_flip(other) {
                self.stats.sweep_flipped_equivalences += 1;
                log!(self, "flipping {} succeeded", other);
                if third == 0 {
                    log!(self, "squashing equivalence class of {}", lit);
                    let n = sweeper.partition.len() - 3;
                    sweeper.partition.truncate(n);
                } else {
                    log!(self, "removing {} from equivalence class of {}", other, lit);
                    sweeper.partition[end - 2] = 0;
                    let n = sweeper.partition.len() - 1;
                    sweeper.partition.truncate(n);
                }
                return false;
            }
        }
        // frozen variables are not allowed to be eliminated.
        // It might still be beneficial to learn the binaries, if they
        // really are equivalent, but we avoid the issue by not trying
        // for equivalence at all if the non-representative is frozen.
        // i.e., the higher absolute value
        if lit.abs() > other.abs() && self.frozen(lit) {
            if third == 0 {
                log!(self, "squashing equivalence class of {}", lit);
                let n = sweeper.partition.len() - 3;
                sweeper.partition.truncate(n);
            } else {
                log!(self, "removing {} from equivalence class of {}", lit, other);
                sweeper.partition[end - 3] = other;
                sweeper.partition[end - 2] = 0;
                let n = sweeper.partition.len() - 1;
                sweeper.partition.truncate(n);
            }
            return false;
        } else if other.abs() > lit.abs() && self.frozen(other) {
            if third == 0 {
                log!(self, "squashing equivalence class of {}", lit);
                let n = sweeper.partition.len() - 3;
                sweeper.partition.truncate(n);
            } else {
                log!(self, "removing {} from equivalence class of {}", lit, other);
                sweeper.partition[end - 2] = 0;
                let n = sweeper.partition.len() - 1;
                sweeper.partition.truncate(n);
            }
            return false;
        }

        let not_other = -other;
        let not_lit = -lit;
        log!(self, "flipping {} and {} both failed", lit, other);
        kitten_assume_signed(citten(self), not_lit);
        kitten_assume_signed(citten(self), other);
        self.stats.sweep_solved_equivalences += 1;
        res = self.sweep_solve();
        if res == 10 {
            self.stats.sweep_sat_equivalences += 1;
            log!(self, "first sweeping implication {} -> {} failed", other, lit);
            self.sweep_refine(sweeper);
        } else if res == 0 {
            self.stats.sweep_unknown_equivalences += 1;
            log!(self, "first sweeping implication {} -> {} hit ticks limit", other, lit);
        }

        if res != 20 {
            return false;
        }

        self.stats.sweep_unsat_equivalences += 1;
        log!(self, "first sweeping implication {} -> {} succeeded", other, lit);

        self.save_core(sweeper, 0);

        kitten_assume_signed(citten(self), lit);
        kitten_assume_signed(citten(self), not_other);
        res = self.sweep_solve();
        self.stats.sweep_solved_equivalences += 1;
        if res == 10 {
            self.stats.sweep_sat_equivalences += 1;
            log!(self, "second sweeping implication {} <- {} failed", other, lit);
            self.sweep_refine(sweeper);
        } else if res == 0 {
            self.stats.sweep_unknown_equivalences += 1;
            log!(self, "second sweeping implication {} <- {} hit ticks limit", other, lit);
        }

        if res != 20 {
            sweeper.core[0].clear();
            return false;
        }

        debug_assert!(res == 20);

        self.stats.sweep_unsat_equivalences += 1;
        log!(self, "second sweeping implication {} <- {} succeeded too", other, lit);

        self.save_core(sweeper, 1);
        if self.terminated_asynchronously(1) {
            sweeper.core[0].clear();
            sweeper.core[1].clear();
            return false;
        }
        log!(self, "sweep equivalence {} = {}", lit, other);

        // If kitten behaves as expected, the two binaries of the equivalence
        // should be stored at sweeper.core[i].back () for i in {0, 1}.
        // We pick the smaller absolute valued literal as representative and
        // store the equivalence .
        self.add_core(sweeper, 0);
        self.add_core(sweeper, 1);
        if self.val(lit) == 0 && self.val(other) == 0 {
            debug_assert!(!sweeper.core[0].is_empty());
            debug_assert!(!sweeper.core[1].is_empty());
            self.stats.sweep_equivalences += 1;
            let mut bin1 = sweep_binary::default();
            let mut bin2 = sweep_binary::default();
            if lit.abs() > other.abs() {
                bin1.lit = lit;
                bin1.other = not_other;
                bin2.lit = not_lit;
                bin2.other = other;
                bin1.id = self.add_sweep_binary(sweeper.core[0].last().unwrap().clone(), lit, not_other);
                bin2.id = self.add_sweep_binary(sweeper.core[1].last().unwrap().clone(), not_lit, other);
            } else {
                bin1.lit = not_other;
                bin1.other = lit;
                bin2.lit = other;
                bin2.other = not_lit;
                bin1.id = self.add_sweep_binary(sweeper.core[0].last().unwrap().clone(), not_other, lit);
                bin2.id = self.add_sweep_binary(sweeper.core[1].last().unwrap().clone(), other, not_lit);
            }
            if bin1.id != 0 && bin2.id != 0 {
                sweeper.binaries.push(bin1);
                sweeper.binaries.push(bin2);
            }
        }

        let repr;
        if lit.abs() < other.abs() {
            sweeper.set_repr(other, lit);
            repr = lit;
            sweeper.set_repr(not_other, not_lit);
            self.sweep_remove(sweeper, other);
        } else {
            sweeper.set_repr(lit, other);
            repr = other;
            sweeper.set_repr(not_lit, not_other);
            self.sweep_remove(sweeper, lit);
        }
        self.clear_core(sweeper, 0);
        self.clear_core(sweeper, 1);

        let repr_idx = repr.abs();
        self.schedule_inner(sweeper, repr_idx);

        true
    }

    pub fn sweep_variable(&mut self, sweeper: &mut Sweeper, idx: i32) -> &'static str {
        debug_assert!(!self.unsat);
        if !self.active(idx) {
            return "inactive variable";
        }
        let start = idx;
        if sweeper.repr_of(start) != start {
            return "non-representative variable";
        }
        debug_assert!(sweeper.vars.is_empty());
        debug_assert!(sweeper.clauses.is_empty());
        debug_assert!(sweeper.backbone.is_empty());
        debug_assert!(sweeper.partition.is_empty());
        debug_assert!(sweeper.encoded == 0);

        self.stats.sweep_variables += 1;

        log!(self, "sweeping {}", idx);
        debug_assert!(self.val(start) == 0);
        log!(self, "starting sweeping[0]");
        self.add_literal_to_environment(sweeper, 0, start);
        log!(self, "finished sweeping[0]");
        log!(self, "starting sweeping[1]");

        let mut limit_reached = false;
        let mut expand: usize = 0;
        let mut next: usize = 1;
        let mut success = false;
        let mut depth: u32 = 1;

        while !limit_reached {
            if sweeper.encoded >= sweeper.limit.clauses {
                log!(self, "environment clause limit reached");
                limit_reached = true;
                break;
            }
            if expand == next {
                log!(self, "finished sweeping[{}]", depth);
                if depth >= sweeper.limit.depth {
                    log!(self, "environment depth limit reached");
                    break;
                }
                next = sweeper.vars.len();
                if expand == next {
                    log!(self, "completely copied all clauses");
                    break;
                }
                depth += 1;
                log!(self, "starting sweeping[{}]", depth);
            }
            let choices = (next - expand) as u32;
            if self.opts.sweeprand != 0 && choices > 1 {
                let swaps = sweeper.random.pick_int(0, (choices - 1) as i32) as u32;
                if swaps != 0 {
                    debug_assert!(expand + (swaps as usize) < sweeper.vars.len());
                    sweeper.vars.swap(expand, expand + swaps as usize);
                }
            }
            let idx = sweeper.vars[expand];
            log!(self, "traversing and adding clauses of {}", idx);
            for sign in 0..2u32 {
                let lit = if sign != 0 { -idx } else { idx };
                sweeper.current_ticks = sweeper.current_ticks.wrapping_add(
                    (1 + self.cache_lines_n(self.occs(lit).len(), std::mem::size_of::<*const Clause>()))
                        as u64,
                );
                // 'sweep_clause' does not modify occurrence lists.
                let nns = self.occs(lit).len();
                for k in 0..nns {
                    let c = self.occs(lit)[k];
                    sweeper.current_ticks = sweeper.current_ticks.wrapping_add(1);
                    if !self.can_sweep_clause(c) {
                        continue;
                    }
                    self.sweep_clause(sweeper, depth, c);
                    if sweeper.vars.len() >= sweeper.limit.vars as usize {
                        log!(self, "environment variable limit reached");
                        limit_reached = true;
                        break;
                    }
                }
                if limit_reached {
                    break;
                }
            }
            expand += 1;
        }
        self.stats.sweep_depth += depth as i64;
        self.stats.sweep_clauses += sweeper.encoded as i64;
        self.stats.sweep_environment += sweeper.vars.len() as i64;
        verbose!(
            self,
            3,
            "sweeping variable {} environment of {} variables {} clauses depth {}",
            self.externalize(idx),
            sweeper.vars.len(),
            sweeper.encoded,
            depth
        );

        'done: {
            if sweeper.vars.len() == 1 {
                log!(self, "not sweeping literal {} with environment size 1", idx);
                break 'done;
            }
            let res = self.sweep_solve();
            log!(self, "sub-solver returns '{}'", res);
            if res == 10 {
                self.init_backbone_and_partition(sweeper);
                let mut units = self.stats.sweep_units as u64;
                let mut solved = self.stats.sweep_solved as u64;
                start!(self, sweepbackbone);
                while !sweeper.backbone.is_empty() {
                    if self.unsat
                        || self.terminated_asynchronously(1)
                        || self.kitten_ticks_limit_hit(sweeper, "backbone refinement")
                    {
                        limit_reached = true;
                        // STOP_SWEEP_BACKBONE:
                        stop!(self, sweepbackbone);
                        break 'done;
                    }
                    self.flip_backbone_literals(sweeper);
                    if self.terminated_asynchronously(1)
                        || self.kitten_ticks_limit_hit(sweeper, "backbone refinement")
                    {
                        limit_reached = true;
                        // goto STOP_SWEEP_BACKBONE
                        stop!(self, sweepbackbone);
                        break 'done;
                    }
                    if sweeper.backbone.is_empty() {
                        break;
                    }
                    let lit = sweeper.backbone.pop().unwrap();
                    if !self.active(lit) {
                        continue;
                    }
                    if self.sweep_backbone_candidate(sweeper, lit) {
                        success = true;
                    }
                }
                stop!(self, sweepbackbone);
                units = (self.stats.sweep_units as u64).wrapping_sub(units);
                solved = (self.stats.sweep_solved as u64).wrapping_sub(solved);
                verbose!(
                    self,
                    4,
                    "complete swept variable {} backbone with {} units in {} solver calls",
                    self.externalize(idx),
                    units,
                    solved
                );
                debug_assert!(sweeper.backbone.is_empty());
                let mut equivalences = self.stats.sweep_equivalences as u64;
                solved = self.stats.sweep_solved as u64;
                start!(self, sweepequivalences);
                while !sweeper.partition.is_empty() {
                    if self.unsat
                        || self.terminated_asynchronously(1)
                        || self.kitten_ticks_limit_hit(sweeper, "partition refinement")
                    {
                        limit_reached = true;
                        // STOP_SWEEP_EQUIVALENCES:
                        stop!(self, sweepequivalences);
                        break 'done;
                    }
                    self.flip_partition_literals(sweeper);
                    if self.terminated_asynchronously(1)
                        || self.kitten_ticks_limit_hit(sweeper, "backbone refinement")
                    {
                        limit_reached = true;
                        // goto STOP_SWEEP_EQUIVALENCES
                        stop!(self, sweepequivalences);
                        break 'done;
                    }
                    if sweeper.partition.is_empty() {
                        break;
                    }
                    if sweeper.partition.len() > 2 {
                        let end = sweeper.partition.len();
                        debug_assert!(sweeper.partition[end - 1] == 0);
                        let lit = sweeper.partition[end - 3];
                        let other = sweeper.partition[end - 2];
                        if self.sweep_equivalence_candidates(sweeper, lit, other) {
                            success = true;
                        }
                    } else {
                        sweeper.partition.clear();
                    }
                }
                stop!(self, sweepequivalences);
                equivalences = (self.stats.sweep_equivalences as u64).wrapping_sub(equivalences);
                solved = (self.stats.sweep_solved as u64).wrapping_sub(solved);
                if equivalences != 0 {
                    verbose!(
                        self,
                        3,
                        "complete swept variable {} partition with {} equivalences in {} solver calls",
                        self.externalize(idx),
                        equivalences,
                        solved
                    );
                }
            } else if res == 20 {
                self.sweep_empty_clause(sweeper);
            }
        }

        // DONE:
        self.clear_sweeper(sweeper);

        if !self.unsat {
            self.sweep_substitute_new_equivalences(sweeper);
        }
        if !self.unsat {
            self.sweep_dense_propagate(sweeper);
        }

        if success && limit_reached {
            return "successfully despite reaching limit";
        }
        if !success && !limit_reached {
            "unsuccessfully without reaching limit"
        } else if success && !limit_reached {
            "successfully without reaching limit"
        } else {
            debug_assert!(!success && limit_reached);
            "unsuccessfully and reached limit"
        }
    }

    pub fn scheduable_variable(&mut self, sweeper: &mut Sweeper, idx: i32, occ_ptr: &mut usize) -> bool {
        let lit = idx;
        let pos = self.noccs(lit) as usize;
        if pos == 0 {
            return false;
        }
        let max_occurrences = sweeper.limit.clauses;
        if pos > max_occurrences as usize {
            return false;
        }
        let not_lit = -lit;
        let neg = self.noccs(not_lit) as usize;
        if neg == 0 {
            return false;
        }
        if neg > max_occurrences as usize {
            return false;
        }
        *occ_ptr = pos + neg;
        true
    }

    pub fn schedule_all_other_not_scheduled_yet(&mut self, sweeper: &mut Sweeper) -> u32 {
        if self.terminated_asynchronously(1) {
            return 0;
        }
        let mut fresh: Vec<sweep_candidate> = Vec::new();
        for idx in self.vars() {
            if !self.flags(idx).active() {
                continue;
            }
            if self.sweep_incomplete && !self.flags(idx).sweep {
                continue;
            }
            if self.scheduled_variable(sweeper, idx) {
                continue;
            }
            let mut occ: usize = 0;
            if !self.scheduable_variable(sweeper, idx, &mut occ) {
                self.flags_mut(idx).sweep = false;
                continue;
            }
            let cand = sweep_candidate { rank: occ as u32, idx };
            fresh.push(cand);
        }
        let size = fresh.len();
        debug_assert!(size <= u32::MAX as usize);
        crate::sort::std_sort(&mut fresh, rank_sweep_candidate);
        for cand in fresh.iter() {
            self.schedule_outer(sweeper, cand.idx);
        }
        size as u32
    }

    pub fn reschedule_previously_remaining(&mut self, sweeper: &mut Sweeper) -> u32 {
        let mut rescheduled: u32 = 0;
        if self.terminated_asynchronously(1) {
            return rescheduled;
        }
        for k in 0..self.sweep_schedule.len() {
            let idx = self.sweep_schedule[k];
            if !self.flags(idx).active() {
                continue;
            }
            if self.scheduled_variable(sweeper, idx) {
                continue;
            }
            let mut occ: usize = 0;
            if !self.scheduable_variable(sweeper, idx, &mut occ) {
                self.flags_mut(idx).sweep = false;
                continue;
            }
            self.schedule_inner(sweeper, idx);
            rescheduled += 1;
        }
        self.sweep_schedule.clear();
        rescheduled
    }

    pub fn incomplete_variables(&mut self) -> u32 {
        let mut res: u32 = 0;
        for idx in self.vars() {
            let f = self.flags(idx);
            if !f.active() {
                continue;
            }
            if f.sweep {
                res += 1;
            }
        }
        res
    }

    pub fn mark_incomplete(&mut self, sweeper: &mut Sweeper) {
        let mut marked: u32 = 0;
        // for (all_scheduled (idx))
        let mut idx = sweeper.first;
        while idx != 0 {
            let next_idx = sweeper.next[idx as usize];
            if !self.flags(idx).sweep {
                self.flags_mut(idx).sweep = true;
                marked += 1;
            }
            idx = next_idx;
        }
        self.sweep_incomplete = true;
        verbose!(self, 2, "marked {} scheduled sweeping variables as incomplete", marked);
    }

    pub fn schedule_sweeping(&mut self, sweeper: &mut Sweeper) -> u32 {
        let rescheduled = self.reschedule_previously_remaining(sweeper);
        let fresh = self.schedule_all_other_not_scheduled_yet(sweeper);
        let scheduled = fresh.wrapping_add(rescheduled);
        let incomplete = self.incomplete_variables();
        phase!(
            self,
            "sweep",
            self.stats.sweep,
            "scheduled {} variables {}% ({} rescheduled {}%, {} incomplete {}%)",
            scheduled,
            fmt_f(percent(scheduled as f64, self.active_count() as f64), 0),
            rescheduled,
            fmt_f(percent(rescheduled as f64, scheduled as f64), 0),
            incomplete,
            fmt_f(percent(incomplete as f64, scheduled as f64), 0)
        );
        if incomplete != 0 {
            debug_assert!(self.sweep_incomplete);
        } else {
            if self.sweep_incomplete {
                self.stats.sweep_completed += 1;
            }
            self.mark_incomplete(sweeper);
        }
        scheduled
    }

    pub fn unschedule_sweeping(&mut self, sweeper: &mut Sweeper, swept: u32, scheduled: u32) {
        debug_assert!(self.sweep_schedule.is_empty() || self.terminated_asynchronously(1));
        debug_assert!(self.sweep_incomplete);
        // for (all_scheduled (idx))
        let mut idx = sweeper.first;
        while idx != 0 {
            let next_idx = sweeper.next[idx as usize];
            if self.active(idx) {
                self.sweep_schedule.push(idx);
                log!(self, "untried scheduled {}", idx);
            }
            idx = next_idx;
        }
        let retained = self.sweep_schedule.len() as u32;
        verbose!(
            self,
            3,
            "retained {} variables {}% to be swept next time",
            retained,
            fmt_f(percent(retained as f64, self.active_count() as f64), 0)
        );
        let incomplete = self.incomplete_variables();
        if incomplete != 0 {
            verbose!(
                self,
                3,
                "need to sweep {} more variables {}% for completion",
                incomplete,
                fmt_f(percent(incomplete as f64, self.active_count() as f64), 0)
            );
        } else {
            verbose!(self, 3, "no more variables needed to complete sweep");
            self.sweep_incomplete = false;
            self.stats.sweep_completed += 1;
        }
        phase!(
            self,
            "sweep",
            self.stats.sweep,
            "swept {} variables ({} remain {}%)",
            swept,
            incomplete,
            fmt_f(percent(incomplete as f64, scheduled as f64), 0)
        );
    }

    pub fn sweep(&mut self) -> bool {
        if self.opts.sweep == 0 {
            return false;
        }
        if self.unsat {
            return false;
        }
        if self.terminated_asynchronously(1) {
            return false;
        }
        if self.delaying_sweep.bumpreasons.delay() {
            // TODO need to fix Delay
            self.last.sweep.ticks = self.stats.ticks.search[0] + self.stats.ticks.search[1];
            return false;
        }
        self.delaying_sweep.bumpreasons.bypass_delay();
        set_effort_limit!(self, tickslimit, sweep, self.opts.sweepcomplete == 0);
        self.delaying_sweep.bumpreasons.unbypass_delay();

        debug_assert!(self.level == 0);
        start_simplifier!(self, sweep, SWEEP);
        self.stats.sweep += 1;
        let mut equivalences = self.stats.sweep_equivalences as u64;
        let mut units = self.stats.sweep_units as u64;
        let mut sweeper = Sweeper::new(self as *mut Internal);
        if self.opts.sweepcomplete != 0 {
            sweeper.limit.ticks = i64::MAX as u64;
        } else {
            sweeper.limit.ticks = (tickslimit - self.stats.ticks.sweep) as u64;
        }
        self.sweep_set_kitten_ticks_limit(&mut sweeper);
        let scheduled = self.schedule_sweeping(&mut sweeper);
        let mut swept: u64 = 0;
        let mut limit: u64 = 10;
        loop {
            if self.unsat {
                break;
            }
            if self.terminated_asynchronously(1) {
                break;
            }
            if self.kitten_ticks_limit_hit(&mut sweeper, "sweeping loop") {
                break;
            }
            let idx = self.next_scheduled(&mut sweeper);
            if idx == 0 {
                break;
            }
            self.flags_mut(idx).sweep = false;
            let res = self.sweep_variable(&mut sweeper, idx);
            verbose!(
                self,
                3,
                "swept[{}] external variable {} {}",
                swept,
                self.externalize(idx),
                res
            );
            swept += 1;
            if swept == limit {
                verbose!(
                    self,
                    2,
                    "found {} equivalences and {} units after sweeping {} variables ",
                    (self.stats.sweep_equivalences as u64).wrapping_sub(equivalences),
                    (self.stats.sweep_units as u64).wrapping_sub(units),
                    swept
                );
                limit *= 10;
            }
        }
        verbose!(self, 2, "swept {} variables", swept);
        equivalences = (self.stats.sweep_equivalences as u64).wrapping_sub(equivalences);
        units = (self.stats.sweep_units as u64).wrapping_sub(units);
        phase!(
            self,
            "sweep",
            self.stats.sweep,
            "found {} equivalences and {} units",
            equivalences,
            units
        );
        self.unschedule_sweeping(&mut sweeper, swept as u32, scheduled);
        self.release_sweeper(&mut sweeper);

        if !self.unsat {
            self.propagated = 0;
            if !self.propagate() {
                self.learn_empty_clause();
            }
        }

        let eliminated = equivalences.wrapping_add(units);
        self.report(b'=', (eliminated == 0) as i32);

        if relative(eliminated as f64, swept as f64) < 0.001 {
            self.delaying_sweep.bumpreasons.bump_delay();
        } else {
            self.delaying_sweep.bumpreasons.reduce_delay();
        }
        stop_simplifier!(self, sweep, SWEEP);
        eliminated != 0
    }
}

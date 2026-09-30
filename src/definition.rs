//! Port of `definition.cpp`.

#[allow(unused_imports)]
use crate::prelude::*;

use crate::kitten::{
    citten_clause_with_id_and_exception, kitten_compute_clausal_core, kitten_current_ticks,
    kitten_set_ticks_limit, kitten_shrink_to_clausal_core, kitten_shuffle_clauses, kitten_solve,
    kitten_trace_core, kitten_traverse_core_clauses, kitten_traverse_core_ids,
};

// functions below are passed to kitten
//
// In C++ the call backs get a 'definition_extractor' state.  In Rust they
// are closures in 'find_definition' calling the functions below, which get
// the state explicitly.
struct DefinitionExtractor {
    eliminator: *mut Eliminator,
    internal: *mut Internal,
    clauses: [Vec<CRef>; 2],
    #[allow(dead_code)]
    lit: i32,
    unit: i32,
}

// used to extract definitions from kitten
//
fn traverse_definition_core(extractor: &mut DefinitionExtractor, id: u32) {
    let clause: CRef;
    let clauses0 = &extractor.clauses[0];
    let clauses1 = &extractor.clauses[1];
    // SAFETY: the eliminator outlives the call to 'find_definition'.
    let eliminator = unsafe { &mut *extractor.eliminator };
    let size_clauses0 = clauses0.len();
    let size_clauses1 = clauses1.len();
    debug_assert!(size_clauses0 <= u32::MAX as usize);
    let sign: u32;
    debug_assert!((id as usize) < size_clauses0 + size_clauses1);
    if (id as usize) < size_clauses0 {
        clause = clauses0[id as usize];
        sign = 1;
    } else {
        let tmp = id.wrapping_sub(size_clauses0 as u32);
        #[cfg(debug_assertions)]
        {
            debug_assert!(size_clauses1 <= u32::MAX as usize);
            debug_assert!((tmp as usize) < size_clauses1);
        }
        clause = clauses1[tmp as usize];
        sign = 2;
    }
    let _ = size_clauses1;
    clause.set_gate(true);
    eliminator.gates.push(clause);
    log!(extractor.internal, clause, "extracted gate");
    eliminator.definition_unit |= sign;
}

// extracts relevant learned clauses from kissat for drat proofs
//
fn traverse_one_sided_core_lemma(extractor: &mut DefinitionExtractor, learned: bool, lits: &[u32]) {
    if !learned {
        return;
    }
    // SAFETY: the eliminator and the internal solver outlive the call to
    // 'find_definition' (and are not otherwise borrowed during the call
    // back).
    let eliminator = unsafe { &mut *extractor.eliminator };
    let internal = unsafe { &mut *extractor.internal };
    let unit = extractor.unit;
    let size = lits.len();
    if size != 0 {
        let mut pc = proof_clause::default();
        internal.clause_id += 1;
        pc.id = internal.clause_id;
        pc.literals.push(unit);
        for &p in lits {
            pc.literals.push(internal.citten2lit(p)); // conversion
        }
        eliminator.proof_clauses.push(pc);
        let pc = eliminator.proof_clauses.last().unwrap();
        let proof = internal.proof.as_mut();
        debug_assert!(proof.is_some());
        proof.unwrap().add_derived_clause_lits(pc.id, true, &pc.literals, &pc.chain);
    } else {
        internal.assign_unit(unit);
        let proof = internal.proof.as_mut().unwrap();
        for pc in eliminator.proof_clauses.iter() {
            proof.delete_clause_lits(pc.id, true, &pc.literals);
        }
        eliminator.proof_clauses.clear();
    }
}

// extract lrat proofs for relevant clauses
//
fn traverse_one_sided_core_lemma_with_lrat(
    extractor: &mut DefinitionExtractor,
    cid: u32,
    id: u32,
    learned: bool,
    lits: &[u32],
    chain: &[u32],
) {
    // SAFETY: see 'traverse_one_sided_core_lemma'.
    let eliminator = unsafe { &mut *extractor.eliminator };
    let internal = unsafe { &mut *extractor.internal };
    let unit = extractor.unit;
    let clauses0 = &extractor.clauses[0];
    let clauses1 = &extractor.clauses[1];
    let size = lits.len();
    let chain_size = chain.len();
    if !learned {
        // remember clauses for mapping to kitten internal
        debug_assert!(size != 0);
        debug_assert!(chain_size == 0);
        let mut pc = proof_clause::default();
        pc.cid = cid;
        pc.learned = false;
        let size_clauses0 = clauses0.len();
        debug_assert!(size_clauses0 <= u32::MAX as usize);
        if (id as usize) < size_clauses0 {
            pc.id = clauses0[id as usize].id();
        } else {
            let tmp = id.wrapping_sub(size_clauses0 as u32);
            #[cfg(debug_assertions)]
            {
                let size_clauses1 = clauses1.len();
                debug_assert!(size_clauses1 <= u32::MAX as usize);
                debug_assert!((tmp as usize) < size_clauses1);
            }
            pc.id = clauses1[tmp as usize].id();
        }
        eliminator.proof_clauses.push(pc);
    } else {
        // actually add to proof
        debug_assert!(chain_size != 0);
        if size != 0 {
            let mut pc = proof_clause::default();
            internal.clause_id += 1;
            pc.id = internal.clause_id;
            pc.cid = cid;
            pc.learned = true;
            pc.literals.push(unit);
            for &p in lits {
                pc.literals.push(internal.citten2lit(p)); // conversion
            }
            for p in (0..chain_size).rev() {
                let mut id: i64 = 0;
                for cpc in eliminator.proof_clauses.iter() {
                    if cpc.cid == chain[p] {
                        id = cpc.id;
                        break;
                    }
                }
                debug_assert!(id != 0);
                pc.chain.push(id);
            }
            eliminator.proof_clauses.push(pc);
            let pc = eliminator.proof_clauses.last().unwrap();
            let proof = internal.proof.as_mut();
            debug_assert!(proof.is_some());
            proof.unwrap().add_derived_clause_lits(pc.id, true, &pc.literals, &pc.chain);
        } else {
            // learn unit finish proof
            debug_assert!(internal.lrat_chain.is_empty());
            for p in (0..chain_size).rev() {
                let mut id: i64 = 0;
                for cpc in eliminator.proof_clauses.iter() {
                    if cpc.cid == chain[p] {
                        id = cpc.id;
                        break;
                    }
                }
                debug_assert!(id != 0);
                internal.lrat_chain.push(id);
            }
            internal.assign_unit(unit);
            debug_assert!(internal.lrat_chain.is_empty());
            let proof = internal.proof.as_mut().unwrap();
            for pc in eliminator.proof_clauses.iter() {
                if pc.learned {
                    proof.delete_clause_lits(pc.id, true, &pc.literals);
                }
            }
            eliminator.proof_clauses.clear();
        }
    }
}

impl Internal {
    // Code ported from kissat. Kitten (and kissat) use unsigned
    // representation for literals whereas CaDiCaL uses signed
    // representation. Conversion is necessary for communication using
    // lit2citten and citten2lit.  This code is called in elim and kitten is
    // initialized beforehand.  To avoid confusion all cadical interal
    // definitions with kitten are called citten.
    //
    pub fn find_definition(&mut self, eliminator: &mut Eliminator, lit: i32) {
        if self.opts.elimdef == 0 {
            return;
        }
        if self.unsat {
            return;
        }
        if self.val(lit) != 0 {
            return;
        }
        if !eliminator.gates.is_empty() {
            return;
        }
        debug_assert!(self.val(lit) == 0);
        debug_assert!(self.level == 0);
        debug_assert!(self.citten.is_some());
        let not_lit = -lit;
        let mut extractor = DefinitionExtractor {
            eliminator: eliminator as *mut Eliminator,
            internal: self as *mut Internal,
            clauses: [self.occs(lit).clone(), self.occs(not_lit).clone()],
            lit,
            unit: 0,
        };
        self.citten_clear_track_log_terminate();
        // SAFETY: 'citten' is boxed (stable address) and neither released
        // nor replaced during this function; the call backs below do not
        // access it.
        let citten: *mut Kitten = &mut **self.citten.as_mut().unwrap();
        let citten = unsafe { &mut *citten };
        let mut exported: u32 = 0;
        for sign in 0..2usize {
            let except = if sign != 0 { self.lit2citten(not_lit) } else { self.lit2citten(lit) };
            for k in 0..extractor.clauses[sign].len() {
                let c = extractor.clauses[sign][k];
                // to avoid copying the literals of c in their unsigned
                // representation we instead implement the translation in
                // kitten
                if !c.garbage() {
                    log!(self, c, "adding to kitten");
                    citten_clause_with_id_and_exception(citten, exported, c.lits(), except);
                }
                exported += 1;
            }
        }
        self.stats.definitions_checked += 1;
        let limit = self.opts.elimdefticks as usize;
        kitten_set_ticks_limit(citten, limit as u64);
        let status = kitten_solve(citten);
        'abort: {
            if exported == 0 {
                break 'abort;
            }
            if status == 20 {
                log!(self, "sub-solver result UNSAT shows definition exists");
                let mut learned: u64 = 0;
                let mut reduced = kitten_compute_clausal_core(citten, Some(&mut learned));
                log!(
                    self,
                    "1st sub-solver core of size {} original clauses out of {}",
                    reduced,
                    exported
                );
                for i in 2..=self.opts.elimdefcores {
                    kitten_shrink_to_clausal_core(citten);
                    kitten_shuffle_clauses(citten);
                    kitten_set_ticks_limit(citten, (10 * limit) as u64);
                    let tmp = kitten_solve(citten);
                    debug_assert!(tmp == 0 || tmp == 20);
                    if tmp == 0 {
                        log!(self, "aborting core extraction");
                        break 'abort;
                    }
                    #[cfg(debug_assertions)]
                    let previous = reduced;
                    reduced = kitten_compute_clausal_core(citten, Some(&mut learned));
                    log!(
                        self,
                        "{} sub-solver core of size {} original clauses out of {}",
                        i,
                        reduced,
                        exported
                    );
                    #[cfg(debug_assertions)]
                    debug_assert!(reduced <= previous);
                    let _ = (i, reduced);
                }
                self.stats.definitions_extracted += 1;
                eliminator.gatetype = GateType::DEF;
                eliminator.definition_unit = 0;
                kitten_traverse_core_ids(citten, &mut |id| traverse_definition_core(&mut extractor, id));
                debug_assert!(eliminator.definition_unit != 0);
                let mut unit = 0;
                if eliminator.definition_unit == 2 {
                    unit = not_lit;
                } else if eliminator.definition_unit == 1 {
                    unit = lit;
                }

                if unit != 0 {
                    self.stats.definition_units += 1;
                    verbose!(self, 2, "one sided core definition extraction yields failed literal");
                    if self.proof.is_some() {
                        if self.lrat {
                            extractor.unit = unit;
                            kitten_trace_core(citten, &mut |cid, id, learned, lits, chain| {
                                traverse_one_sided_core_lemma_with_lrat(&mut extractor, cid, id, learned, lits, chain)
                            });
                        } else {
                            extractor.unit = unit;
                            kitten_traverse_core_clauses(citten, &mut |learned, lits| {
                                traverse_one_sided_core_lemma(&mut extractor, learned, lits)
                            });
                        }
                    } else {
                        self.assign_unit(unit);
                    }
                    self.elim_propagate(eliminator, unit);
                }
                self.stats.definition_ticks += kitten_current_ticks(citten) as i64;
                return;
            }
        }
        // ABORT:
        log!(self, "sub-solver failed to show that definition exists");
        self.stats.definition_ticks += kitten_current_ticks(citten) as i64;
    }
}

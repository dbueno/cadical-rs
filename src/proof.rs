//! Port of `proof.hpp` and `proof.cpp`: the abstraction layer between the
//! solver and the proof tracers / checkers.

use crate::internal::Internal;
use crate::tracer::{FileTracer, Tracer};

pub struct Proof {
    pub internal: *mut Internal,
    /// Of external literals.
    pub clause: Vec<i32>,
    /// LRAT style proof chain of clause.
    pub proof_chain: Vec<i64>,
    /// Id of added clause.
    pub clause_id: i64,
    pub redundant: bool,
    pub witness: i32,
    /// Tracers (ie checker).  Raw pointers to tracers owned by `Internal`.
    pub tracers: Vec<*mut dyn Tracer>,
    /// File tracers (ie LRAT tracer).  Raw pointers to tracers owned by
    /// `Internal`.
    pub file_tracers: Vec<*mut dyn FileTracer>,
}

impl Proof {
    /// `void connect (Tracer *t)`.
    #[inline]
    pub fn connect(&mut self, t: *mut dyn Tracer) {
        self.tracers.push(t);
    }
}

/*------------------------------------------------------------------------*/

#[allow(unused_imports)]
use crate::prelude::*;

use crate::checker::Checker;
use crate::drattracer::DratTracer;
use crate::frattracer::FratTracer;
use crate::idruptracer::IdrupTracer;
use crate::lidruptracer::LidrupTracer;
use crate::lratchecker::LratChecker;
use crate::lrattracer::LratTracer;
use crate::veripbtracer::VeripbTracer;

/// Address of a (possibly fat) tracer pointer as used for `TracerRef`.
#[inline]
fn tracer_addr<T: ?Sized>(p: *const T) -> usize {
    p as *const () as usize
}

// Enable proof logging and checking by allocating a 'Proof' object.

impl Internal {
    pub fn new_proof_on_demand(&mut self) {
        if self.proof.is_none() {
            log!(self, "connecting proof to internal solver");
            let internal: *mut Internal = self;
            self.proof = Some(Box::new(Proof::new(internal)));
        }
    }

    pub fn resize_unit_clauses_idx(&mut self) {
        let new_vsize = if self.vsize != 0 { 2 * self.vsize } else { 1 + self.max_var as usize };
        self.unit_clauses_idx.resize(2 * new_vsize, 0);
    }

    pub fn force_lrat(&mut self) {
        if self.lrat {
            return;
        }
        debug_assert!(self.proof.is_some());
        self.lrat = true;
    }

    /// `finalize_clauses` defaults to `false` in C++.
    pub fn connect_proof_tracer(&mut self, mut tracer: Box<dyn Tracer>, antecedents: bool, finalize_clauses: bool) -> TracerRef {
        self.new_proof_on_demand();
        if antecedents {
            self.force_lrat();
        }
        if finalize_clauses {
            self.frat = true;
        }
        self.resize_unit_clauses_idx();
        let p: *mut dyn Tracer = &mut *tracer;
        let r = TracerRef(tracer_addr(p));
        self.proof.as_mut().unwrap().connect(p);
        self.tracers.push(tracer);
        r
    }

    /// C++ overload for `InternalTracer *` (renamed).  `finalize_clauses` defaults to `false` in C++.
    pub fn connect_proof_tracer_internal(&mut self, mut tracer: Box<dyn InternalTracer>, antecedents: bool, finalize_clauses: bool) -> TracerRef {
        self.new_proof_on_demand();
        if antecedents {
            self.force_lrat();
        }
        if finalize_clauses {
            self.frat = true;
        }
        self.resize_unit_clauses_idx();
        let internal: *mut Internal = self;
        tracer.connect_internal(internal);
        let mut tracer: Box<dyn Tracer> = tracer;
        let p: *mut dyn Tracer = &mut *tracer;
        let r = TracerRef(tracer_addr(p));
        self.proof.as_mut().unwrap().connect(p);
        self.tracers.push(tracer);
        r
    }

    /// C++ overload for `StatTracer *` (renamed).  `finalize_clauses` defaults to `false` in C++.
    pub fn connect_proof_tracer_stat(&mut self, mut tracer: Box<dyn StatTracer>, antecedents: bool, finalize_clauses: bool) -> TracerRef {
        self.new_proof_on_demand();
        if antecedents {
            self.force_lrat();
        }
        if finalize_clauses {
            self.frat = true;
        }
        self.resize_unit_clauses_idx();
        let internal: *mut Internal = self;
        tracer.connect_internal(internal);
        let p: *mut dyn StatTracer = &mut *tracer;
        let r = TracerRef(tracer_addr(p));
        self.proof.as_mut().unwrap().connect(p);
        self.stat_tracers.push(tracer);
        r
    }

    /// C++ overload for `FileTracer *` (renamed).  `finalize_clauses` defaults to `false` in C++.
    pub fn connect_proof_tracer_file(&mut self, mut tracer: Box<dyn FileTracer>, antecedents: bool, finalize_clauses: bool) -> TracerRef {
        self.new_proof_on_demand();
        if antecedents {
            self.force_lrat();
        }
        if finalize_clauses {
            self.frat = true;
        }
        self.resize_unit_clauses_idx();
        let internal: *mut Internal = self;
        tracer.connect_internal(internal);
        let p: *mut dyn FileTracer = &mut *tracer;
        let r = TracerRef(tracer_addr(p));
        self.proof.as_mut().unwrap().connect(p);
        self.file_tracers.push(tracer);
        r
    }

    /// C++ returns `bool` (`Some` == `true`).
    pub fn disconnect_proof_tracer(&mut self, tracer: TracerRef) -> Option<Box<dyn Tracer>> {
        let pos = self.tracers.iter().position(|t| tracer_addr(&**t as *const dyn Tracer) == tracer.0);
        if let Some(pos) = pos {
            let res = self.tracers.remove(pos);
            debug_assert!(self.proof.is_some());
            self.proof.as_mut().unwrap().disconnect(tracer);
            return Some(res);
        }
        None
    }

    /// C++ overload for `StatTracer *` (renamed).
    pub fn disconnect_proof_tracer_stat(&mut self, tracer: TracerRef) -> Option<Box<dyn StatTracer>> {
        let pos = self.stat_tracers.iter().position(|t| tracer_addr(&**t as *const dyn StatTracer) == tracer.0);
        if let Some(pos) = pos {
            let res = self.stat_tracers.remove(pos);
            debug_assert!(self.proof.is_some());
            self.proof.as_mut().unwrap().disconnect(tracer);
            return Some(res);
        }
        None
    }

    /// C++ overload for `FileTracer *` (renamed).
    pub fn disconnect_proof_tracer_file(&mut self, tracer: TracerRef) -> Option<Box<dyn FileTracer>> {
        let pos = self.file_tracers.iter().position(|t| tracer_addr(&**t as *const dyn FileTracer) == tracer.0);
        if let Some(pos) = pos {
            let res = self.file_tracers.remove(pos);
            debug_assert!(self.proof.is_some());
            self.proof.as_mut().unwrap().disconnect(tracer);
            return Some(res);
        }
        None
    }

    /// Start write proof file (takes ownership of the file).
    pub fn trace(&mut self, file: Box<File>) {
        let internal: *mut Internal = self;
        if self.opts.veripb != 0 {
            log!(self, "PROOF connecting VeriPB tracer");
            let antecedents = self.opts.veripb == 1 || self.opts.veripb == 2;
            let deletions = self.opts.veripb == 2 || self.opts.veripb == 4;
            let ft: Box<dyn FileTracer> =
                Box::new(VeripbTracer::new(internal, file, self.opts.binary != 0, antecedents, deletions));
            self.connect_proof_tracer_file(ft, antecedents, false);
        } else if self.opts.frat != 0 {
            log!(self, "PROOF connecting FRAT tracer");
            let antecedents = self.opts.frat == 1;
            self.resize_unit_clauses_idx();
            let ft: Box<dyn FileTracer> =
                Box::new(FratTracer::new(internal, file, self.opts.binary != 0, self.opts.frat == 1));
            self.connect_proof_tracer_file(ft, antecedents, true);
        } else if self.opts.lrat != 0 {
            log!(self, "PROOF connecting LRAT tracer");
            let ft: Box<dyn FileTracer> = Box::new(LratTracer::new(internal, file, self.opts.binary != 0));
            self.connect_proof_tracer_file(ft, true, false);
        } else if self.opts.idrup != 0 {
            log!(self, "PROOF connecting IDRUP tracer");
            let ft: Box<dyn FileTracer> = Box::new(IdrupTracer::new(internal, file, self.opts.binary != 0));
            self.connect_proof_tracer_file(ft, true, false);
        } else if self.opts.lidrup != 0 {
            log!(self, "PROOF connecting LIDRUP tracer");
            let ft: Box<dyn FileTracer> = Box::new(LidrupTracer::new(internal, file, self.opts.binary != 0));
            self.connect_proof_tracer_file(ft, true, false);
        } else {
            log!(self, "PROOF connecting DRAT tracer");
            let ft: Box<dyn FileTracer> = Box::new(DratTracer::new(internal, file, self.opts.binary != 0));
            self.connect_proof_tracer_file(ft, false, false);
        }
    }

    /// Enable proof checking.
    pub fn check(&mut self) {
        self.new_proof_on_demand();
        let internal: *mut Internal = self;
        if self.opts.checkproof > 1 {
            let mut lratchecker: Box<dyn StatTracer> = Box::new(LratChecker::new(internal));
            log!(self, "PROOF connecting LRAT proof checker");
            self.force_lrat();
            self.frat = true;
            self.resize_unit_clauses_idx();
            let p: *mut dyn StatTracer = &mut *lratchecker;
            self.proof.as_mut().unwrap().connect(p);
            self.stat_tracers.push(lratchecker);
        }
        if self.opts.checkproof == 1 || self.opts.checkproof == 3 {
            let mut checker: Box<dyn StatTracer> = Box::new(Checker::new(internal));
            log!(self, "PROOF connecting proof checker");
            let p: *mut dyn StatTracer = &mut *checker;
            self.proof.as_mut().unwrap().connect(p);
            self.stat_tracers.push(checker);
        }
    }

    /// We want to close a proof trace and stop checking as soon we are
    /// done.  (`print` defaults to `false` in C++.)
    pub fn close_trace(&mut self, print: bool) {
        for tracer in self.file_tracers.iter_mut() {
            tracer.close(print);
        }
    }

    /// We can flush a proof trace file before actually closing it.
    /// (`print` defaults to `false` in C++.)
    pub fn flush_trace(&mut self, print: bool) {
        for tracer in self.file_tracers.iter_mut() {
            tracer.flush(print);
        }
    }
}

impl Proof {
    pub fn disconnect(&mut self, t: TracerRef) {
        self.tracers.retain(|&p| tracer_addr(p) != t.0);
    }

    /*----------------------------------------------------------------------*/

    #[inline]
    pub fn add_literal(&mut self, internal_lit: i32) {
        // SAFETY: 'internal' owns the proof and is alive.
        let external_lit = unsafe { (*self.internal).externalize(internal_lit) };
        self.clause.push(external_lit);
    }

    /// C++ overload `Proof::add_literals` (renamed).
    #[inline]
    pub fn add_literals_clause(&mut self, c: CRef) {
        for i in 0..c.size() as usize {
            self.add_literal(c.lit(i));
        }
    }

    #[inline]
    pub fn add_literals(&mut self, c: &[i32]) {
        for &lit in c {
            self.add_literal(lit);
        }
    }

    /*----------------------------------------------------------------------*/

    pub fn add_original_clause(&mut self, id: i64, r: bool, c: &[i32]) {
        log!(self.internal, c, "PROOF adding original internal clause");
        self.add_literals(c);
        self.clause_id = id;
        self.redundant = r;
        self.emit_add_original_clause(false);
    }

    /// `restore` defaults to `false` in C++
    pub fn add_external_original_clause(&mut self, id: i64, r: bool, c: &[i32], restore: bool) {
        // literals of c are already external
        debug_assert!(self.clause.is_empty());
        for &lit in c {
            self.clause.push(lit);
        }
        self.clause_id = id;
        self.redundant = r;
        self.emit_add_original_clause(restore);
    }

    pub fn delete_external_original_clause(&mut self, id: i64, r: bool, c: &[i32]) {
        // literals of c are already external
        debug_assert!(self.clause.is_empty());
        for &lit in c {
            self.clause.push(lit);
        }
        self.clause_id = id;
        self.redundant = r;
        self.emit_delete_clause();
    }

    pub fn add_derived_empty_clause(&mut self, id: i64, chain: &[i64]) {
        log!(self.internal, "PROOF adding empty clause");
        debug_assert!(self.clause.is_empty());
        debug_assert!(self.proof_chain.is_empty());
        for &cid in chain {
            self.proof_chain.push(cid);
        }
        self.clause_id = id;
        self.redundant = false;
        self.emit_add_derived_clause();
    }

    pub fn add_derived_unit_clause(&mut self, id: i64, internal_unit: i32, chain: &[i64]) {
        log!(self.internal, "PROOF adding unit clause {}", internal_unit);
        debug_assert!(self.proof_chain.is_empty());
        debug_assert!(self.clause.is_empty());
        self.add_literal(internal_unit);
        for &cid in chain {
            self.proof_chain.push(cid);
        }
        self.clause_id = id;
        self.redundant = false;
        self.emit_add_derived_clause();
    }

    /*----------------------------------------------------------------------*/

    pub fn add_derived_clause(&mut self, c: CRef, chain: &[i64]) {
        log!(self.internal, c, "PROOF adding to proof derived");
        debug_assert!(self.clause.is_empty());
        debug_assert!(self.proof_chain.is_empty());
        self.add_literals_clause(c);
        for &cid in chain {
            self.proof_chain.push(cid);
        }
        self.clause_id = c.id();
        self.redundant = c.redundant();
        self.emit_add_derived_clause();
    }

    pub fn add_derived_rat_clause(&mut self, c: CRef, w: i32, chain: &[i64]) {
        log!(self.internal, c, "PROOF adding to proof derived witness {}", w);
        debug_assert!(self.clause.is_empty());
        debug_assert!(self.proof_chain.is_empty());
        self.add_literals_clause(c);
        for &cid in chain {
            self.proof_chain.push(cid);
        }
        self.clause_id = c.id();
        self.redundant = c.redundant();
        self.witness = w;
        self.emit_add_derived_clause();
    }

    /// C++ overload `Proof::add_derived_clause` (renamed).
    pub fn add_derived_clause_lits(&mut self, id: i64, r: bool, c: &[i32], chain: &[i64]) {
        log!(self.internal, c, "PROOF adding derived clause");
        debug_assert!(self.clause.is_empty());
        debug_assert!(self.proof_chain.is_empty());
        for &lit in c {
            self.add_literal(lit);
        }
        for &cid in chain {
            self.proof_chain.push(cid);
        }
        self.clause_id = id;
        self.redundant = r;
        self.emit_add_derived_clause();
    }

    /// C++ overload `Proof::add_derived_rat_clause` (renamed).
    pub fn add_derived_rat_clause_lits(&mut self, id: i64, r: bool, l: i32, c: &[i32], chain: &[i64]) {
        log!(self.internal, c, "PROOF adding derived witness {} clause", l);
        debug_assert!(self.clause.is_empty());
        debug_assert!(self.proof_chain.is_empty());
        for &lit in c {
            self.add_literal(lit);
        }
        for &cid in chain {
            self.proof_chain.push(cid);
        }
        self.clause_id = id;
        self.redundant = r;
        self.witness = l;
        self.emit_add_derived_clause();
    }

    pub fn add_assumption_clause(&mut self, id: i64, c: &[i32], chain: &[i64]) {
        // literals of c are already external
        debug_assert!(self.clause.is_empty());
        debug_assert!(self.proof_chain.is_empty());
        for &lit in c {
            self.clause.push(lit);
        }
        for &cid in chain {
            self.proof_chain.push(cid);
        }
        self.clause_id = id;
        self.emit_add_assumption_clause();
    }

    pub fn add_assumption(&mut self, a: i32) {
        // a is already external
        debug_assert!(self.clause.is_empty());
        debug_assert!(self.proof_chain.is_empty());
        self.clause.push(a);
        self.emit_add_assumption();
    }

    pub fn add_constraint(&mut self, c: &[i32]) {
        // literals of c are already external
        debug_assert!(self.clause.is_empty());
        debug_assert!(self.proof_chain.is_empty());
        for &lit in c {
            self.clause.push(lit);
        }
        self.emit_add_constraint();
    }

    /// C++ overload `Proof::add_assumption_clause` (renamed).
    pub fn add_assumption_clause_unit(&mut self, id: i64, lit: i32, chain: &[i64]) {
        debug_assert!(self.clause.is_empty());
        debug_assert!(self.proof_chain.is_empty());
        self.clause.push(lit);
        for &cid in chain {
            self.proof_chain.push(cid);
        }
        self.clause_id = id;
        self.emit_add_assumption_clause();
    }

    pub fn delete_clause(&mut self, c: CRef) {
        log!(self.internal, c, "PROOF deleting from proof");
        self.clause.clear(); // Can be non-empty if an allocation fails during adding.
        self.add_literals_clause(c);
        self.clause_id = c.id();
        self.redundant = c.redundant();
        self.emit_delete_clause(); // Increments 'statistics.deleted'.
    }

    /// C++ overload `Proof::delete_clause` (renamed).
    pub fn delete_clause_lits(&mut self, id: i64, r: bool, c: &[i32]) {
        log!(self.internal, c, "PROOF deleting from proof");
        debug_assert!(self.clause.is_empty());
        self.add_literals(c);
        self.clause_id = id;
        self.redundant = r;
        self.emit_delete_clause(); // Increments 'statistics.deleted'.
    }

    pub fn weaken_minus(&mut self, c: CRef) {
        log!(self.internal, c, "PROOF weaken minus of");
        debug_assert!(self.clause.is_empty());
        self.add_literals_clause(c);
        self.clause_id = c.id();
        self.emit_weaken_minus();
    }

    /// C++ overload `Proof::weaken_minus` (renamed).
    pub fn weaken_minus_lits(&mut self, id: i64, c: &[i32]) {
        log!(self.internal, c, "PROOF deleting from proof");
        debug_assert!(self.clause.is_empty());
        self.add_literals(c);
        self.clause_id = id;
        self.emit_weaken_minus();
    }

    pub fn weaken_plus(&mut self, c: CRef) {
        self.weaken_minus(c);
        self.delete_clause(c); // Increments 'statistics.deleted'.
    }

    /// C++ overload `Proof::weaken_plus` (renamed).
    pub fn weaken_plus_lits(&mut self, id: i64, c: &[i32]) {
        self.weaken_minus_lits(id, c);
        self.delete_clause_lits(id, false, c); // Increments 'statistics.deleted'.
    }

    pub fn delete_unit_clause(&mut self, id: i64, lit: i32) {
        log!(self.internal, "PROOF deleting unit from proof {}", lit);
        debug_assert!(self.clause.is_empty());
        self.add_literal(lit);
        self.clause_id = id;
        self.redundant = false;
        self.emit_delete_clause();
    }

    pub fn finalize_clause(&mut self, c: CRef) {
        log!(self.internal, c, "PROOF finalizing clause");
        debug_assert!(self.clause.is_empty());
        self.add_literals_clause(c);
        self.clause_id = c.id();
        self.emit_finalize_clause();
    }

    /// C++ overload `Proof::finalize_clause` (renamed).
    pub fn finalize_clause_lits(&mut self, id: i64, c: &[i32]) {
        log!(self.internal, c, "PROOF finalizing clause");
        debug_assert!(self.clause.is_empty());
        for &lit in c {
            self.add_literal(lit);
        }
        self.clause_id = id;
        self.emit_finalize_clause();
    }

    pub fn finalize_unit(&mut self, id: i64, lit: i32) {
        log!(self.internal, "PROOF finalizing clause {}", lit);
        debug_assert!(self.clause.is_empty());
        self.add_literal(lit);
        self.clause_id = id;
        self.emit_finalize_clause();
    }

    pub fn finalize_external_unit(&mut self, id: i64, lit: i32) {
        log!(self.internal, "PROOF finalizing clause {}", lit);
        debug_assert!(self.clause.is_empty());
        self.clause.push(lit);
        self.clause_id = id;
        self.emit_finalize_clause();
    }

    /*----------------------------------------------------------------------*/

    // During garbage collection clauses are shrunken by removing falsified
    // literals. To avoid copying the clause, we provide a specialized
    // tracing function here, which traces the required 'add' and 'remove'
    // operations.

    pub fn flush_clause(&mut self, c: CRef) {
        log!(self.internal, c, "PROOF flushing falsified literals in");
        debug_assert!(self.clause.is_empty());
        // SAFETY: 'internal' owns the proof and is alive.
        let antecedents = unsafe { (*self.internal).lrat || (*self.internal).frat };
        for i in 0..c.size() as usize {
            let internal_lit = c.lit(i);
            // SAFETY: see above.
            if unsafe { (*self.internal).fixed(internal_lit) } < 0 {
                if antecedents {
                    // SAFETY: see above.
                    let id = unsafe { (*self.internal).unit_id(-internal_lit) };
                    self.proof_chain.push(id);
                }
                continue;
            }
            self.add_literal(internal_lit);
        }
        self.proof_chain.push(c.id());
        self.redundant = c.redundant();
        // SAFETY: see above.
        let id = unsafe {
            (*self.internal).clause_id += 1;
            (*self.internal).clause_id
        };
        self.clause_id = id;
        self.emit_add_derived_clause();
        self.delete_clause(c);
        c.set_id(id);
    }

    // While strengthening clauses, e.g., through self-subsuming
    // resolutions, during subsumption checking, we have a similar
    // situation, except that we have to remove exactly one literal.  Again
    // the following function allows to avoid copying the clause and instead
    // provides tracing of the required 'add' and 'remove' operations.

    pub fn strengthen_clause(&mut self, c: CRef, remove: i32, chain: &[i64]) {
        log!(self.internal, c, "PROOF strengthen by removing {} in", remove);
        debug_assert!(self.clause.is_empty());
        for i in 0..c.size() as usize {
            let internal_lit = c.lit(i);
            if internal_lit == remove {
                continue;
            }
            self.add_literal(internal_lit);
        }
        // SAFETY: 'internal' owns the proof and is alive.
        let id = unsafe {
            (*self.internal).clause_id += 1;
            (*self.internal).clause_id
        };
        self.clause_id = id;
        self.redundant = c.redundant();
        for &cid in chain {
            self.proof_chain.push(cid);
        }
        self.emit_add_derived_clause();
        self.delete_clause(c);
        c.set_id(id);
    }

    pub fn otfs_strengthen_clause(&mut self, c: CRef, old: &[i32], chain: &[i64]) {
        log!(self.internal, c, "PROOF otfs strengthen");
        debug_assert!(self.clause.is_empty());
        for i in 0..c.size() as usize {
            let internal_lit = c.lit(i);
            self.add_literal(internal_lit);
        }
        // SAFETY: 'internal' owns the proof and is alive.
        let id = unsafe {
            (*self.internal).clause_id += 1;
            (*self.internal).clause_id
        };
        self.clause_id = id;
        self.redundant = c.redundant();
        for &cid in chain {
            self.proof_chain.push(cid);
        }
        self.emit_add_derived_clause();
        self.delete_clause_lits(c.id(), c.redundant(), old);
        c.set_id(id);
    }

    pub fn strengthen(&mut self, id: i64) {
        self.clause_id = id;
        self.emit_strengthen();
    }

    /*----------------------------------------------------------------------*/

    /// `restore` defaults to `false` in C++
    /// C++ overload `Proof::add_original_clause` (renamed).
    pub fn emit_add_original_clause(&mut self, restore: bool) {
        log!(self.internal, &self.clause, "PROOF adding original external clause");
        debug_assert!(self.clause_id != 0);
        for &tracer in &self.tracers {
            // SAFETY: connected tracers are owned by 'Internal' and alive.
            unsafe { (*tracer).add_original_clause(self.clause_id, false, &self.clause, restore) };
        }
        self.clause.clear();
        self.clause_id = 0;
    }

    /// C++ overload `Proof::add_derived_clause` (renamed).
    pub fn emit_add_derived_clause(&mut self) {
        log!(
            self.internal,
            &self.clause,
            "PROOF adding derived external clause (redundant: {})",
            self.redundant as i32
        );
        debug_assert!(self.clause_id != 0);
        for &tracer in &self.tracers {
            // SAFETY: connected tracers are owned by 'Internal' and alive.
            unsafe {
                (*tracer).add_derived_clause(
                    self.clause_id,
                    self.redundant,
                    self.witness,
                    &self.clause,
                    &self.proof_chain,
                )
            };
        }
        self.proof_chain.clear();
        self.clause.clear();
        self.clause_id = 0;
        self.witness = 0;
    }

    /// C++ overload `Proof::delete_clause` (renamed).
    pub fn emit_delete_clause(&mut self) {
        log!(self.internal, &self.clause, "PROOF deleting external clause");
        for &tracer in &self.tracers {
            // SAFETY: connected tracers are owned by 'Internal' and alive.
            unsafe { (*tracer).delete_clause(self.clause_id, self.redundant, &self.clause) };
        }
        self.clause.clear();
        self.clause_id = 0;
    }

    /// C++ overload `Proof::demote_clause` (renamed).
    pub fn emit_demote_clause(&mut self) {
        log!(self.internal, &self.clause, "PROOF demoting external clause");
        debug_assert!(!self.redundant);
        for &tracer in &self.tracers {
            // SAFETY: connected tracers are owned by 'Internal' and alive.
            unsafe { (*tracer).demote_clause(self.clause_id as u64, &self.clause) };
        }
        self.clause.clear();
        self.clause_id = 0;
    }

    /// C++ overload `Proof::weaken_minus` (renamed).
    pub fn emit_weaken_minus(&mut self) {
        log!(self.internal, &self.clause, "PROOF marking as clause to restore");
        for &tracer in &self.tracers {
            // SAFETY: connected tracers are owned by 'Internal' and alive.
            unsafe { (*tracer).weaken_minus(self.clause_id, &self.clause) };
        }
        self.clause.clear();
        self.clause_id = 0;
    }

    /// C++ overload `Proof::strengthen` (renamed).
    pub fn emit_strengthen(&mut self) {
        log!(self.internal, "PROOF strengthen clause with id {}", self.clause_id);
        for &tracer in &self.tracers {
            // SAFETY: connected tracers are owned by 'Internal' and alive.
            unsafe { (*tracer).strengthen(self.clause_id) };
        }
        self.clause_id = 0;
    }

    /// C++ overload `Proof::finalize_clause` (renamed).
    pub fn emit_finalize_clause(&mut self) {
        for &tracer in &self.tracers {
            // SAFETY: connected tracers are owned by 'Internal' and alive.
            unsafe { (*tracer).finalize_clause(self.clause_id, &self.clause) };
        }
        self.clause.clear();
        self.clause_id = 0;
    }

    /// C++ overload `Proof::add_assumption_clause` (renamed).
    pub fn emit_add_assumption_clause(&mut self) {
        log!(self.internal, &self.clause, "PROOF adding assumption clause");
        for &tracer in &self.tracers {
            // SAFETY: connected tracers are owned by 'Internal' and alive.
            unsafe { (*tracer).add_assumption_clause(self.clause_id, &self.clause, &self.proof_chain) };
        }
        self.proof_chain.clear();
        self.clause.clear();
        self.clause_id = 0;
    }

    /// C++ overload `Proof::add_assumption` (renamed).
    pub fn emit_add_assumption(&mut self) {
        log!(self.internal, &self.clause, "PROOF adding assumption");
        debug_assert!(self.clause.len() == 1);
        let lit = *self.clause.last().unwrap();
        for &tracer in &self.tracers {
            // SAFETY: connected tracers are owned by 'Internal' and alive.
            unsafe { (*tracer).add_assumption(lit) };
        }
        self.clause.clear();
    }

    /// C++ overload `Proof::add_constraint` (renamed).
    pub fn emit_add_constraint(&mut self) {
        log!(self.internal, &self.clause, "PROOF adding constraint");
        for &tracer in &self.tracers {
            // SAFETY: connected tracers are owned by 'Internal' and alive.
            unsafe { (*tracer).add_constraint(&self.clause) };
        }
        self.clause.clear();
    }

    pub fn reset_assumptions(&mut self) {
        log!(self.internal, "PROOF reset assumptions");
        for &tracer in &self.tracers {
            // SAFETY: connected tracers are owned by 'Internal' and alive.
            unsafe { (*tracer).reset_assumptions() };
        }
    }

    pub fn report_status(&mut self, status: i32, id: i64) {
        log!(self.internal, "PROOF reporting status {}", status);
        for &tracer in &self.tracers {
            // SAFETY: connected tracers are owned by 'Internal' and alive.
            unsafe { (*tracer).report_status(status, id) };
        }
    }

    pub fn begin_proof(&mut self, id: i64) {
        log!(self.internal, &self.clause, "PROOF begin proof");
        for &tracer in &self.tracers {
            // SAFETY: connected tracers are owned by 'Internal' and alive.
            unsafe { (*tracer).begin_proof(id) };
        }
    }

    pub fn solve_query(&mut self) {
        log!(self.internal, &self.clause, "PROOF solve query");
        for &tracer in &self.tracers {
            // SAFETY: connected tracers are owned by 'Internal' and alive.
            unsafe { (*tracer).solve_query() };
        }
    }

    pub fn conclude_unsat(&mut self, con: ConclusionType, conclusion: &[i64]) {
        log!(self.internal, &self.clause, "PROOF conclude unsat");
        for &tracer in &self.tracers {
            // SAFETY: connected tracers are owned by 'Internal' and alive.
            unsafe { (*tracer).conclude_unsat(con, conclusion) };
        }
    }

    pub fn conclude_sat(&mut self, model: &[i32]) {
        log!(self.internal, &self.clause, "PROOF conclude sat");
        for &tracer in &self.tracers {
            // SAFETY: connected tracers are owned by 'Internal' and alive.
            unsafe { (*tracer).conclude_sat(model) };
        }
    }

    pub fn conclude_unknown(&mut self, trail: &[i32]) {
        log!(self.internal, &self.clause, "PROOF conclude unknown");
        for &tracer in &self.tracers {
            // SAFETY: connected tracers are owned by 'Internal' and alive.
            unsafe { (*tracer).conclude_unknown(trail) };
        }
    }
}

impl Proof {
    /// `Proof (Internal *)`.
    pub fn new(internal: *mut Internal) -> Proof {
        let proof = Proof {
            internal,
            clause: Vec::new(),
            proof_chain: Vec::new(),
            clause_id: 0,
            redundant: false,
            witness: 0,
            tracers: Vec::new(),
            file_tracers: Vec::new(),
        };
        // SAFETY: 'internal' owns the proof.
        log!(unsafe { &*internal }, "PROOF new");
        proof
    }
}

impl Drop for Proof {
    /// `~Proof ()`.
    fn drop(&mut self) {
        log!(self.internal, "PROOF delete");
    }
}

/*------------------------------------------------------------------------*/

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::solver::{SATISFIABLE, UNKNOWN, UNSATISFIABLE};
    use std::sync::atomic::{AtomicUsize, Ordering};

    static COUNTER: AtomicUsize = AtomicUsize::new(0);

    /// Unique path of a temporary proof file.
    pub(crate) fn temp_path(tag: &str) -> String {
        let n = COUNTER.fetch_add(1, Ordering::Relaxed);
        let dir = std::env::temp_dir();
        format!("{}/cadical-rs-p9-{}-{}-{}.proof", dir.display(), std::process::id(), tag, n)
    }

    /// `File::write` without compression: open a plain file for writing.
    pub(crate) fn open_write_file(internal: *mut Internal, path: &str) -> Box<File> {
        let cpath = std::ffi::CString::new(path).unwrap();
        // SAFETY: valid C strings.
        let fp = unsafe { libc::fopen(cpath.as_ptr(), c"w".as_ptr()) };
        assert!(!fp.is_null());
        Box::new(File::new(internal, true, 1, 0, fp, path))
    }

    /// Name of the environment variable selecting the test case to run in
    /// a child process (for tests of fatal errors which abort).
    const CHILD_ENV: &str = "CADICAL_RS_P9_CHILD";

    /// Are we the child process running 'test'?
    pub(crate) fn in_child(test: &str) -> bool {
        std::env::var(CHILD_ENV).as_deref() == Ok(test)
    }

    /// Run the test 'test' (full path) in a child process.
    pub(crate) fn run_child(test: &str) -> std::process::Output {
        let exe = std::env::current_exe().unwrap();
        std::process::Command::new(exe)
            .args([test, "--exact", "--nocapture", "--test-threads", "1"])
            .env(CHILD_ENV, test)
            .output()
            .unwrap()
    }

    /// Runs 'case' in a child process (as test 'test') and checks that it
    /// aborts with a fatal error message 'expected' (exact 'stderr' text
    /// after 'cadical: fatal error: ' as printed by the C++ checkers).
    pub(crate) fn expect_fatal(test: &str, expected: &str, case: impl FnOnce()) {
        if in_child(test) {
            case();
            std::process::exit(0);
        }
        let out = run_child(test);
        let stderr = String::from_utf8_lossy(&out.stderr);
        #[cfg(unix)]
        {
            use std::os::unix::process::ExitStatusExt;
            assert_eq!(out.status.signal(), Some(libc::SIGABRT), "stderr: {}", stderr);
        }
        let full = format!("cadical: fatal error: {}\n", expected);
        assert!(stderr.contains(&full), "expected:\n{}\ngot:\n{}", full, stderr);
    }

    /// Runs 'case' in a child process (as test 'test') and returns its
    /// 'stdout' (checking that it succeeded).
    pub(crate) fn child_stdout(test: &str, case: impl FnOnce()) -> String {
        if in_child(test) {
            case();
            std::process::exit(0);
        }
        let out = run_child(test);
        assert!(out.status.success(), "stderr: {}", String::from_utf8_lossy(&out.stderr));
        String::from_utf8_lossy(&out.stdout).into_owned()
    }

    /// Same event sequence as 'scenario' in the C++ driver.
    pub(crate) fn scenario(t: &mut dyn FileTracer) {
        t.begin_proof(4);
        t.add_original_clause(1, false, &[1, 2], false);
        t.add_original_clause(2, false, &[-1, 2], false);
        t.add_original_clause(3, false, &[1, -2], false);
        t.add_original_clause(4, false, &[-1, -2, 3], false);
        t.add_derived_clause(5, true, 0, &[2], &[1, 2]);
        t.add_derived_clause(6, false, 0, &[1], &[3, 5]);
        t.delete_clause(1, false, &[1, 2]);
        t.delete_clause(5, true, &[2]);
        t.weaken_minus(4, &[-1, -2, 3]);
        t.delete_clause(4, false, &[-1, -2, 3]);
        t.add_original_clause(4, false, &[-1, -2, 3], true);
        t.add_derived_clause(7, false, 0, &[-1000, 200, 70000, -2000000], &[-3, 6, 130, 300000]);
        t.add_derived_clause(8, false, 5, &[5, 1], &[6]);
        t.strengthen(8);
        t.weaken_minus(7, &[-1000, 200, 70000, -2000000]);
        t.weaken_minus(8, &[5, 1]);
        t.delete_clause(7, false, &[-1000, 200, 70000, -2000000]);
        t.delete_clause(8, false, &[5, 1]);
        t.delete_clause(3, false, &[1, -2]);
        t.add_original_clause(8, false, &[5, 1], true);
        t.add_original_clause(7, false, &[-1000, 200, 70000, -2000000], true);
        t.add_assumption(3);
        t.add_assumption(-4);
        t.solve_query();
        t.add_assumption_clause(9, &[-3, 4], &[2, 6]);
        t.add_assumption_clause(11, &[-3], &[2]);
        t.conclude_unsat(ConclusionType::ASSUMPTIONS, &[9]);
        t.reset_assumptions();
        t.report_status(UNSATISFIABLE, 0);
        t.solve_query();
        t.add_assumption_clause(12, &[-4], &[6]);
        t.conclude_unsat(ConclusionType::CONSTRAINT, &[11, 12]);
        t.report_status(SATISFIABLE, 0);
        t.conclude_sat(&[1, -2, 3, -4]);
        t.report_status(UNKNOWN, 0);
        t.conclude_unknown(&[1, 2]);
        t.finalize_clause(6, &[1]);
        t.add_derived_clause(10, false, 0, &[], &[6, 2]);
        t.conclude_unsat(ConclusionType::CONFLICT, &[10]);
        t.report_status(UNSATISFIABLE, 10);
    }

    pub(crate) fn new_tracer(internal: *mut Internal, fmt: &str, file: Box<File>, binary: bool) -> Box<dyn FileTracer> {
        match fmt {
            "drat" => Box::new(DratTracer::new(internal, file, binary)),
            "lrat" => Box::new(LratTracer::new(internal, file, binary)),
            "frat1" => Box::new(FratTracer::new(internal, file, binary, true)),
            "frat2" => Box::new(FratTracer::new(internal, file, binary, false)),
            "idrup" => Box::new(IdrupTracer::new(internal, file, binary)),
            "lidrup" => Box::new(LidrupTracer::new(internal, file, binary)),
            _ => {
                assert!(fmt.starts_with("veripb"));
                let v = fmt.as_bytes()[6] - b'0';
                let antecedents = v == 1 || v == 2;
                let deletions = v == 2 || v == 4;
                Box::new(VeripbTracer::new(internal, file, binary, antecedents, deletions))
            }
        }
    }

    fn show(bytes: &[u8]) -> String {
        bytes.iter().map(|&b| if (32..127).contains(&b) || b == b'\n' { (b as char).to_string() } else { format!("\\x{:02x}", b) }).collect()
    }

    #[test]
    fn tracers_match_cpp_reference() {
        let mut internal = Internal::new();
        let ip: *mut Internal = &mut *internal;
        for &(fmt, binary, expected) in REFERENCE {
            let path = temp_path(fmt);
            let file = open_write_file(ip, &path);
            let mut t = new_tracer(ip, fmt, file, binary);
            t.connect_internal(ip);
            scenario(&mut *t);
            t.flush(false);
            t.close(false);
            assert!(t.closed());
            drop(t);
            let got = std::fs::read(&path).unwrap();
            let _ = std::fs::remove_file(&path);
            assert!(
                got == expected,
                "format {} binary {}:\n--- got\n{}\n--- expected\n{}",
                fmt,
                binary,
                show(&got),
                show(expected)
            );
        }
    }

    /// Drive a tracer connected through 'Internal::trace' via the 'Proof'
    /// layer (external literal API) and check the result.
    #[test]
    fn proof_layer_dispatches_to_file_tracer() {
        let mut internal = Internal::new();
        let ip: *mut Internal = &mut *internal;
        internal.opts.frat = 1;
        internal.opts.binary = 0;
        internal.max_var = 2;
        internal.i2e = vec![0, 1, 2];
        let path = temp_path("proof-frat");
        let file = open_write_file(ip, &path);
        internal.trace(file);
        assert!(internal.lrat);
        assert!(internal.frat);
        assert_eq!(internal.file_tracers.len(), 1);
        {
            let proof = internal.proof.as_mut().unwrap();
            assert_eq!(proof.tracers.len(), 1);
            proof.begin_proof(2);
            proof.add_external_original_clause(1, false, &[1, 2], false);
            proof.add_external_original_clause(2, false, &[-1, 2], false);
            proof.add_derived_clause_lits(3, false, &[2], &[1, 2]);
            proof.add_assumption_clause(4, &[2], &[1, 2]);
            proof.delete_external_original_clause(1, false, &[1, 2]);
            proof.finalize_clause_lits(3, &[2]);
            proof.finalize_external_unit(2, -1);
        }
        internal.flush_trace(false);
        internal.close_trace(false);
        let got = std::fs::read(&path).unwrap();
        let _ = std::fs::remove_file(&path);
        assert_eq!(
            show(&got),
            "o 1  1 2 0\no 2  -1 2 0\na 3  2 0  l 1 2 0\nd 1  1 2 0\nf 3  2 0\nf 2  -1 0\n"
        );

        // Disconnect returns the box and removes it from the proof.
        let r = TracerRef(tracer_addr(&*internal.file_tracers[0] as *const dyn FileTracer));
        let t = internal.disconnect_proof_tracer_file(r);
        assert!(t.is_some());
        assert!(internal.proof.as_ref().unwrap().tracers.is_empty());
        assert!(internal.disconnect_proof_tracer_file(r).is_none());
    }

    /// A tracer recording all events (to check 'Proof' dispatching).
    struct Recorder {
        log: std::rc::Rc<std::cell::RefCell<Vec<String>>>,
    }

    impl Tracer for Recorder {
        fn add_original_clause(&mut self, id: i64, r: bool, c: &[i32], restored: bool) {
            self.log.borrow_mut().push(format!("o {} {} {:?} {}", id, r, c, restored));
        }
        fn add_derived_clause(&mut self, id: i64, r: bool, w: i32, c: &[i32], chain: &[i64]) {
            self.log.borrow_mut().push(format!("a {} {} {} {:?} {:?}", id, r, w, c, chain));
        }
        fn delete_clause(&mut self, id: i64, r: bool, c: &[i32]) {
            self.log.borrow_mut().push(format!("d {} {} {:?}", id, r, c));
        }
        fn weaken_minus(&mut self, id: i64, c: &[i32]) {
            self.log.borrow_mut().push(format!("w {} {:?}", id, c));
        }
        fn strengthen(&mut self, id: i64) {
            self.log.borrow_mut().push(format!("s {}", id));
        }
        fn finalize_clause(&mut self, id: i64, c: &[i32]) {
            self.log.borrow_mut().push(format!("f {} {:?}", id, c));
        }
        fn add_assumption(&mut self, lit: i32) {
            self.log.borrow_mut().push(format!("assume {}", lit));
        }
        fn add_constraint(&mut self, c: &[i32]) {
            self.log.borrow_mut().push(format!("constraint {:?}", c));
        }
        fn report_status(&mut self, status: i32, id: i64) {
            self.log.borrow_mut().push(format!("status {} {}", status, id));
        }
    }

    #[test]
    fn proof_layer_externalizes_and_resets() {
        let mut internal = Internal::new();
        // Internal variable 'i' maps to external variable '10 * i'.
        internal.max_var = 3;
        internal.i2e = vec![0, 10, 20, 30];
        let log = std::rc::Rc::new(std::cell::RefCell::new(Vec::new()));
        let r = internal.connect_proof_tracer(Box::new(Recorder { log: log.clone() }), true, true);
        assert!(internal.lrat && internal.frat);
        {
            let proof = internal.proof.as_mut().unwrap();
            proof.add_original_clause(1, false, &[1, -2]);
            proof.add_derived_clause_lits(2, true, &[-3, 1], &[1]);
            proof.add_derived_rat_clause_lits(3, false, 2, &[2, 3], &[-1, 2]);
            proof.add_derived_unit_clause(4, -1, &[3]);
            proof.add_derived_empty_clause(5, &[4, 1]);
            proof.delete_clause_lits(2, true, &[-3, 1]);
            proof.weaken_plus_lits(3, &[2, 3]);
            proof.delete_unit_clause(4, -1);
            proof.finalize_unit(1, 2);
            proof.finalize_external_unit(6, -7);
            proof.finalize_clause_lits(7, &[3]);
            proof.strengthen(9);
            proof.add_assumption(-20);
            proof.add_constraint(&[10, 30]);
            proof.report_status(20, 5);
        }
        let expected = vec![
            "o 1 false [10, -20] false",
            "a 2 true 0 [-30, 10] [1]",
            "a 3 false 2 [20, 30] [-1, 2]",
            "a 4 false 0 [-10] [3]",
            "a 5 false 0 [] [4, 1]",
            "d 2 true [-30, 10]",
            "w 3 [20, 30]",
            "d 3 false [20, 30]",
            "d 4 false [-10]",
            "f 1 [20]",
            "f 6 [-7]",
            "f 7 [30]",
            "s 9",
            "assume -20",
            "constraint [10, 30]",
            "status 20 5",
        ];
        assert_eq!(*log.borrow(), expected);
        let t = internal.disconnect_proof_tracer(r);
        assert!(t.is_some());
        assert!(internal.proof.as_ref().unwrap().tracers.is_empty());
    }

    /// 'Internal::check' connects both internal checkers which then check
    /// a small LRAT refutation of PHP(3,2) sent through the 'Proof' layer.
    #[test]
    fn internal_check_connects_checkers() {
        let mut internal = Internal::new();
        internal.opts.checkproof = 3;
        internal.max_var = 6;
        internal.i2e = (0..=6).collect();
        internal.check();
        assert!(internal.lrat && internal.frat);
        assert_eq!(internal.stat_tracers.len(), 2);
        let php: [&[i32]; 9] =
            [&[1, 2], &[3, 4], &[5, 6], &[-1, -3], &[-1, -5], &[-3, -5], &[-2, -4], &[-2, -6], &[-4, -6]];
        let proof = internal.proof.as_mut().unwrap();
        assert_eq!(proof.tracers.len(), 2);
        proof.begin_proof(9);
        for (i, c) in php.iter().enumerate() {
            proof.add_external_original_clause(i as i64 + 1, false, c, false);
        }
        proof.add_derived_clause_lits(10, false, &[-1], &[4, 5, 2, 3, 9]);
        proof.add_derived_clause_lits(11, false, &[-3], &[4, 6, 1, 3, 8]);
        proof.add_derived_empty_clause(12, &[10, 11, 1, 2, 7]);
        proof.conclude_unsat(ConclusionType::CONFLICT, &[12]);
        for (i, c) in php.iter().enumerate() {
            proof.finalize_clause_lits(i as i64 + 1, c);
        }
        proof.finalize_clause_lits(10, &[-1]);
        proof.finalize_clause_lits(11, &[-3]);
        proof.finalize_clause_lits(12, &[]);
        proof.report_status(UNSATISFIABLE, 12);
    }

    /// Proofs produced by the C++ tracers (reference build) for
    /// `scenario` (generated with the C++ driver in
    /// /Volumes/Shampoo/cadical-rs/p9-driver/driver.cpp).
    const REFERENCE: &[(&str, bool, &[u8])] = &[
        ("drat", false, b"2 0\n1 0\nd 1 2 0\nd 2 0\nd -1 -2 3 0\n-1000 200 70000 -2000000 0\n5 1 0\nd -1000 200 70000 -2000000 0\nd 5 1 0\nd 1 -2 0\n0\n"),
        ("drat", true, b"a\x04\x00a\x02\x00d\x02\x04\x00d\x04\x00d\x03\x05\x06\x00a\xd1\x0f\x90\x03\xe0\xc5\x08\x81\x92\xf4\x01\x00a\n\x02\x00d\xd1\x0f\x90\x03\xe0\xc5\x08\x81\x92\xf4\x01\x00d\n\x02\x00d\x02\x05\x00a\x00"),
        ("lrat", false, b"5 2 0 1 2 0\n6 1 0 3 5 0\n6 d 1 5 4 0\n7 -1000 200 70000 -2000000 0 -3 6 130 300000 0\n8 5 1 0 6 0\n8 d 7 8 3 0\n10 0 6 2 0\n"),
        ("lrat", true, b"a\n\x04\x00\x02\x04\x00a\x0c\x02\x00\x06\n\x00d\x02\n\x08\x00a\x0e\xd1\x0f\x90\x03\xe0\xc5\x08\x81\x92\xf4\x01\x00\x07\x0c\x84\x02\xc0\xcf$\x00a\x10\n\x02\x00\x0c\x00d\x0e\x10\x06\x00a\x14\x00\x0c\x04\x00"),
        ("frat1", false, b"o 1  1 2 0\no 2  -1 2 0\no 3  1 -2 0\no 4  -1 -2 3 0\na 5  2 0  l 1 2 0\na 6  1 0  l 3 5 0\nd 1  1 2 0\nd 5  2 0\nd 4  -1 -2 3 0\no 4  -1 -2 3 0\na 7  -1000 200 70000 -2000000 0  l -3 6 130 300000 0\na 8  5 1 0  l 6 0\nd 7  -1000 200 70000 -2000000 0\nd 8  5 1 0\nd 3  1 -2 0\no 8  5 1 0\no 7  -1000 200 70000 -2000000 0\nf 6  1 0\na 10  0  l 6 2 0\n"),
        ("frat1", true, b"o\x01\x02\x04\x00o\x02\x03\x04\x00o\x03\x02\x05\x00o\x04\x03\x05\x06\x00a\x05\x04\x00l\x02\x04\x00a\x06\x02\x00l\x06\n\x00d\x01\x02\x04\x00d\x05\x04\x00d\x04\x03\x05\x06\x00o\x04\x03\x05\x06\x00a\x07\xd1\x0f\x90\x03\xe0\xc5\x08\x81\x92\xf4\x01\x00l\x07\x0c\x84\x02\xc0\xcf$\x00a\x08\n\x02\x00l\x0c\x00d\x07\xd1\x0f\x90\x03\xe0\xc5\x08\x81\x92\xf4\x01\x00d\x08\n\x02\x00d\x03\x02\x05\x00o\x08\n\x02\x00o\x07\xd1\x0f\x90\x03\xe0\xc5\x08\x81\x92\xf4\x01\x00f\x06\x02\x00a\n\x00l\x0c\x04\x00"),
        ("frat2", false, b"o 1  1 2 0\no 2  -1 2 0\no 3  1 -2 0\no 4  -1 -2 3 0\na 5  2 0\na 6  1 0\nd 1  1 2 0\nd 5  2 0\nd 4  -1 -2 3 0\no 4  -1 -2 3 0\na 7  -1000 200 70000 -2000000 0\na 8  5 1 0\nd 7  -1000 200 70000 -2000000 0\nd 8  5 1 0\nd 3  1 -2 0\no 8  5 1 0\no 7  -1000 200 70000 -2000000 0\nf 6  1 0\na 10  0\n"),
        ("frat2", true, b"o\x01\x02\x04\x00o\x02\x03\x04\x00o\x03\x02\x05\x00o\x04\x03\x05\x06\x00a\x05\x04\x00a\x06\x02\x00d\x01\x02\x04\x00d\x05\x04\x00d\x04\x03\x05\x06\x00o\x04\x03\x05\x06\x00a\x07\xd1\x0f\x90\x03\xe0\xc5\x08\x81\x92\xf4\x01\x00a\x08\n\x02\x00d\x07\xd1\x0f\x90\x03\xe0\xc5\x08\x81\x92\xf4\x01\x00d\x08\n\x02\x00d\x03\x02\x05\x00o\x08\n\x02\x00o\x07\xd1\x0f\x90\x03\xe0\xc5\x08\x81\x92\xf4\x01\x00f\x06\x02\x00a\n\x00"),
        ("idrup", false, b"i 1 2 0\ni -1 2 0\ni 1 -2 0\ni -1 -2 3 0\nl 2 0\nl 1 0\nd 1 2 0\nd 2 0\nw -1 -2 3 0\nr -1 -2 3 0\nl -1000 200 70000 -2000000 0\nl 5 1 0\nw -1000 200 70000 -2000000 0\nw 5 1 0\nd 1 -2 0\nr 5 1 0\nr -1000 200 70000 -2000000 0\nq 3 -4 0\nu 3 -4 0\ns UNSATISFIABLE\nq 0\nU 2\nu 3 0\nu 4 0\ns SATISFIABLE\nm 1 -2 3 -4 0\ns UNKNOWN\ne 1 2 0\nl 0\nu 0\ns UNSATISFIABLE\n"),
        ("idrup", true, b"i\x02\x04\x00i\x03\x04\x00i\x02\x05\x00i\x03\x05\x06\x00l\x04\x00l\x02\x00d\x02\x04\x00d\x04\x00w\x03\x05\x06\x00r\x03\x05\x06\x00l\xd1\x0f\x90\x03\xe0\xc5\x08\x81\x92\xf4\x01\x00l\n\x02\x00w\xd1\x0f\x90\x03\xe0\xc5\x08\x81\x92\xf4\x01\x00w\n\x02\x00d\x02\x05\x00r\n\x02\x00r\xd1\x0f\x90\x03\xe0\xc5\x08\x81\x92\xf4\x01\x00q\x06\x09\x00u\x06\x09\x00sUNSATISFIABLEq\x00U\x02u\x06\x00u\x08\x00sSATISFIABLEm\x02\x05\x06\x09\x00sUNKNOWNe\x02\x04\x00l\x00u\x00sUNSATISFIABLE"),
        ("lidrup", false, b"i 1 1 2 0\ni 2 -1 2 0\ni 3 1 -2 0\ni 4 -1 -2 3 0\nl 5 2 0 1 2 0\nl 6 1 0 3 5 0\nd 1 5 0\nw 4 0\nr 4 0\nl 7 -1000 200 70000 -2000000 0 -3 6 130 300000 0\nl 8 5 1 0 6 0\nw 7 8 0\nd 3 0\nr 8 7 0\nq 3 -4 0\nu 3 -4 0 2 6 0\ns UNSATISFIABLE\nq 0\nU 2\nu 3 0 2 0\nu 4 0 6 0\ns SATISFIABLE\nm 1 -2 3 -4 0\ns UNKNOWN\ne 1 2 0\nl 10 0 6 2 0\nu 0 10 0\ns UNSATISFIABLE\n"),
        ("lidrup", true, b"i\x02\x02\x04\x00i\x04\x03\x04\x00i\x06\x02\x05\x00i\x08\x03\x05\x06\x00l\n\x04\x00\x02\x04\x00l\x0c\x02\x00\x06\n\x00d\x02\n\x00w\x08\x00r\x08\x00l\x0e\xd1\x0f\x90\x03\xe0\xc5\x08\x81\x92\xf4\x01\x00\x07\x0c\x84\x02\xc0\xcf$\x00l\x10\n\x02\x00\x0c\x00w\x0e\x10\x00d\x06\x00r\x10\x0e\x00q\x06\x09\x00u\x06\x09\x00\x04\x0c\x00sUNSATISFIABLEq\x00U\x04u\x06\x00\x04\x00u\x08\x00\x0c\x00sSATISFIABLEm\x02\x05\x06\x09\x00sUNKNOWNe\x02\x04\x00l\x14\x00\x0c\x04\x00u\x00\x14\x00sUNSATISFIABLE"),
        ("veripb1", false, b"pseudo-Boolean proof version 3.0\nf 4;\npol 2 1 + s;\ne 1 x2 >= 1 : 5;\npol 5 3 + s;\ne 1 x1 >= 1 : 6;\ndel id 1;\ndel id 5;\ndel id 4;\npol 300000 130 + s 6 + s -3 + s;\ne 1 ~x1000 1 x200 1 x70000 1 ~x2000000 >= 1 : 7;\nred 1 x5 1 x1 >= 1 : x5 -> 1;\ndel id 7;\ndel id 8;\ndel id 3;\noutput NONE;\nconclusion UNSAT : 0;\nend pseudo-Boolean proof;\noutput NONE;\nconclusion NONE;\nend pseudo-Boolean proof;\noutput NONE;\nconclusion NONE;\nend pseudo-Boolean proof;\npol 2 6 + s;\ne >= 1 : 10;\noutput NONE;\nconclusion UNSAT : 10;\nend pseudo-Boolean proof;\n"),
        ("veripb1", true, b"pseudo-Boolean proof version 3.0\nf 4;\npol 2 1 + s;\ne 1 x2 >= 1 : 5;\npol 5 3 + s;\ne 1 x1 >= 1 : 6;\ndel id 1;\ndel id 5;\ndel id 4;\npol 300000 130 + s 6 + s -3 + s;\ne 1 ~x1000 1 x200 1 x70000 1 ~x2000000 >= 1 : 7;\nred 1 x5 1 x1 >= 1 : x5 -> 1;\ndel id 7;\ndel id 8;\ndel id 3;\noutput NONE;\nconclusion UNSAT : 0;\nend pseudo-Boolean proof;\noutput NONE;\nconclusion NONE;\nend pseudo-Boolean proof;\noutput NONE;\nconclusion NONE;\nend pseudo-Boolean proof;\npol 2 6 + s;\ne >= 1 : 10;\noutput NONE;\nconclusion UNSAT : 10;\nend pseudo-Boolean proof;\n"),
        ("veripb2", false, b"pseudo-Boolean proof version 3.0\nf 4;\npol 2 1 + s;\ne 1 x2 >= 1 : 5;\npol 5 3 + s;\ne 1 x1 >= 1 : 6;\ncore id 6;\ndelc 1;\ndel id 5;\npol 300000 130 + s 6 + s -3 + s;\ne 1 ~x1000 1 x200 1 x70000 1 ~x2000000 >= 1 : 7;\ncore id 7;\nred 1 x5 1 x1 >= 1 : x5 -> 1;\ncore id 8;\ncore id 8;\ndelc 3;\noutput NONE;\nconclusion UNSAT : 0;\nend pseudo-Boolean proof;\noutput NONE;\nconclusion NONE;\nend pseudo-Boolean proof;\noutput NONE;\nconclusion NONE;\nend pseudo-Boolean proof;\npol 2 6 + s;\ne >= 1 : 10;\ncore id 10;\noutput NONE;\nconclusion UNSAT : 10;\nend pseudo-Boolean proof;\n"),
        ("veripb2", true, b"pseudo-Boolean proof version 3.0\nf 4;\npol 2 1 + s;\ne 1 x2 >= 1 : 5;\npol 5 3 + s;\ne 1 x1 >= 1 : 6;\ncore id 6;\ndelc 1;\ndel id 5;\npol 300000 130 + s 6 + s -3 + s;\ne 1 ~x1000 1 x200 1 x70000 1 ~x2000000 >= 1 : 7;\ncore id 7;\nred 1 x5 1 x1 >= 1 : x5 -> 1;\ncore id 8;\ncore id 8;\ndelc 3;\noutput NONE;\nconclusion UNSAT : 0;\nend pseudo-Boolean proof;\noutput NONE;\nconclusion NONE;\nend pseudo-Boolean proof;\noutput NONE;\nconclusion NONE;\nend pseudo-Boolean proof;\npol 2 6 + s;\ne >= 1 : 10;\ncore id 10;\noutput NONE;\nconclusion UNSAT : 10;\nend pseudo-Boolean proof;\n"),
        ("veripb3", false, b"pseudo-Boolean proof version 3.0\nf 4;\nrup 1 x2 >= 1;\nrup 1 x1 >= 1;\ndel id 1;\ndel id 5;\ndel id 4;\nrup 1 ~x1000 1 x200 1 x70000 1 ~x2000000 >= 1;\nred 1 x5 1 x1 >= 1 : x5 -> 1;\ndel id 7;\ndel id 8;\ndel id 3;\noutput NONE;\nconclusion UNSAT : 0;\nend pseudo-Boolean proof;\noutput NONE;\nconclusion NONE;\nend pseudo-Boolean proof;\noutput NONE;\nconclusion NONE;\nend pseudo-Boolean proof;\nrup >= 1;\noutput NONE;\nconclusion UNSAT : 10;\nend pseudo-Boolean proof;\n"),
        ("veripb3", true, b"pseudo-Boolean proof version 3.0\nf 4;\nrup 1 x2 >= 1;\nrup 1 x1 >= 1;\ndel id 1;\ndel id 5;\ndel id 4;\nrup 1 ~x1000 1 x200 1 x70000 1 ~x2000000 >= 1;\nred 1 x5 1 x1 >= 1 : x5 -> 1;\ndel id 7;\ndel id 8;\ndel id 3;\noutput NONE;\nconclusion UNSAT : 0;\nend pseudo-Boolean proof;\noutput NONE;\nconclusion NONE;\nend pseudo-Boolean proof;\noutput NONE;\nconclusion NONE;\nend pseudo-Boolean proof;\nrup >= 1;\noutput NONE;\nconclusion UNSAT : 10;\nend pseudo-Boolean proof;\n"),
        ("veripb4", false, b"pseudo-Boolean proof version 3.0\nf 4;\nrup 1 x2 >= 1;\nrup 1 x1 >= 1;\ncore id 6;\ndelc 1;\ndel id 5;\nrup 1 ~x1000 1 x200 1 x70000 1 ~x2000000 >= 1;\ncore id 7;\nred 1 x5 1 x1 >= 1 : x5 -> 1;\ncore id 8;\ncore id 8;\ndelc 3;\noutput NONE;\nconclusion UNSAT : 0;\nend pseudo-Boolean proof;\noutput NONE;\nconclusion NONE;\nend pseudo-Boolean proof;\noutput NONE;\nconclusion NONE;\nend pseudo-Boolean proof;\nrup >= 1;\ncore id 10;\noutput NONE;\nconclusion UNSAT : 10;\nend pseudo-Boolean proof;\n"),
        ("veripb4", true, b"pseudo-Boolean proof version 3.0\nf 4;\nrup 1 x2 >= 1;\nrup 1 x1 >= 1;\ncore id 6;\ndelc 1;\ndel id 5;\nrup 1 ~x1000 1 x200 1 x70000 1 ~x2000000 >= 1;\ncore id 7;\nred 1 x5 1 x1 >= 1 : x5 -> 1;\ncore id 8;\ncore id 8;\ndelc 3;\noutput NONE;\nconclusion UNSAT : 0;\nend pseudo-Boolean proof;\noutput NONE;\nconclusion NONE;\nend pseudo-Boolean proof;\noutput NONE;\nconclusion NONE;\nend pseudo-Boolean proof;\nrup >= 1;\ncore id 10;\noutput NONE;\nconclusion UNSAT : 10;\nend pseudo-Boolean proof;\n"),
    ];
}

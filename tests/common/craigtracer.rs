// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2013 Stefan Kupferschmid
// Copyright 2023 Florian Pollitt
// Copyright 2023 Tobias Faller
//
// Rust port of 'cadical/contrib/craigtracer.{hpp,cpp}' (CaDiCraig): a
// proof tracer building Craig interpolants.  In Rust it is a client of the
// public 'Tracer' trait (it needs nothing beyond it).
//
// Porting notes:
// * 'CraigData *' (nullable, owned) -> 'Option<CraigData>' ('CraigData'
//   is a small 'Copy' struct).  The one place where C++ keeps a pointer
//   into 'craig_interpolants' and modifies the stored object in place
//   ('add_assumption_clause' with a proof chain) is ported by copying the
//   entry out and writing it back.
// * 'std::unordered_map::operator[]' default-inserts missing keys; this is
//   mirrored with 'entry (k).or_insert (default)' where C++ uses '[]'.
// * The C++ user keeps a 'CraigTracer *' after 'connect_proof_tracer' to
//   label variables / clauses and to query the interpolant.  With the Rust
//   API the solver owns the connected tracer, so the user shares it
//   through 'Rc<RefCell<CraigTracer>>' and connects a [`SharedTracer`]
//   forwarding wrapper (see [`CraigTracer::connect`]).

#![allow(dead_code)]

use cadical::{ConclusionType, Solver, Tracer, TracerRef};
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::rc::Rc;

// ----------------------------------------------------------------------------
// Minimal AIG implementation used for building Craig interpolants
// ----------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct AigEdge {
    index: i32,
}

impl std::ops::Not for AigEdge {
    type Output = AigEdge;
    fn not(self) -> AigEdge {
        AigEdge { index: self.index ^ 1 }
    }
}

impl AigEdge {
    fn new(index: i32) -> AigEdge {
        AigEdge { index }
    }
    pub fn is_negated(&self) -> bool {
        self.index & 1 != 0
    }
    pub fn is_constant(&self) -> bool {
        (self.index >> 1) == 0
    }
    fn get_node_index(&self) -> usize {
        ((self.index >> 1) - 1) as usize
    }
}

#[derive(Clone, Copy, Debug)]
struct AigNode {
    edge1: AigEdge,
    edge2: AigEdge,
}

impl AigNode {
    fn variable(variable: i32) -> AigNode {
        AigNode { edge1: AigEdge::new(variable), edge2: AigEdge::new(0) }
    }
    fn and(edge1: AigEdge, edge2: AigEdge) -> AigNode {
        AigNode { edge1, edge2 }
    }
    fn is_and(&self) -> bool {
        self.edge2.index != 0
    }
    fn is_variable(&self) -> bool {
        self.edge2.index == 0
    }
    fn get_variable(&self) -> i32 {
        self.edge1.index
    }
}

#[derive(Default)]
struct Aig {
    nodes: Vec<AigNode>,
    var_hash_map: HashMap<i32, i32>,
    and_hash_map: HashMap<(AigEdge, AigEdge), i32>,
}

impl Aig {
    fn get_true() -> AigEdge {
        AigEdge::new(0)
    }
    fn get_false() -> AigEdge {
        AigEdge::new(1)
    }

    fn clear(&mut self) {
        self.nodes.clear();
        self.var_hash_map.clear();
        self.and_hash_map.clear();
    }

    fn create_var(&mut self, variable: i32) -> AigEdge {
        // Try to check if there is a node for the literal already
        if let Some(&idx) = self.var_hash_map.get(&variable) {
            return AigEdge::new(idx);
        }

        // Nodes 0 and 1 are constant nodes and reserved
        // and already factored into the index.
        self.nodes.push(AigNode::variable(variable));
        let idx = (self.nodes.len() << 1) as i32;
        self.var_hash_map.insert(variable, idx);
        AigEdge::new(idx)
    }

    fn create_literal(&mut self, literal: i32) -> AigEdge {
        let edge = self.create_var(literal.abs());
        if literal < 0 {
            !edge
        } else {
            edge
        }
    }

    fn create_and2(&mut self, edge1: AigEdge, edge2: AigEdge) -> AigEdge {
        if edge1 == Aig::get_false() || edge2 == Aig::get_false() {
            return Aig::get_false();
        }
        if edge1 == Aig::get_true() {
            return edge2;
        }
        if edge2 == Aig::get_true() {
            return edge1;
        }
        if edge1 == edge2 {
            return edge1;
        }
        if edge1 == !edge2 {
            return Aig::get_false();
        }

        // Order edge indices to increase hit rate
        let pair = if edge1 > edge2 { (edge2, edge1) } else { (edge1, edge2) };
        if let Some(&idx) = self.and_hash_map.get(&pair) {
            return AigEdge::new(idx);
        }

        // Lookup failed, create new node.
        // Nodes 0 and 1 are constant nodes and reserved
        // and already factored into the index.
        self.nodes.push(AigNode::and(edge1, edge2));
        let idx = (self.nodes.len() << 1) as i32;
        self.and_hash_map.insert(pair, idx);
        AigEdge::new(idx)
    }

    fn create_and(&mut self, mut edges: Vec<AigEdge>) -> AigEdge {
        if edges.is_empty() {
            return Aig::get_true();
        }
        if edges.len() == 1 {
            return edges[0];
        }

        // Tree reduction of edges
        let mut temp_edges: Vec<AigEdge> = Vec::new();
        while edges.len() > 1 {
            temp_edges.reserve((edges.len() / 2) + 1);
            let mut index = 0;
            while index + 1 < edges.len() {
                let e = self.create_and2(edges[index], edges[index + 1]);
                temp_edges.push(e);
                index += 2;
            }
            if edges.len() & 1 != 0 {
                temp_edges.push(*edges.last().unwrap());
            }

            edges = std::mem::take(&mut temp_edges);
        }

        edges[0]
    }

    fn create_or2(&mut self, edge1: AigEdge, edge2: AigEdge) -> AigEdge {
        !self.create_and2(!edge1, !edge2)
    }

    fn create_or(&mut self, mut edges: Vec<AigEdge>) -> AigEdge {
        for edge in edges.iter_mut() {
            *edge = !*edge;
        }
        !self.create_and(edges)
    }

    fn create_cnf(&self, root: AigEdge, cnf: &mut Vec<Vec<i32>>, next_free_index: &mut i32) -> CraigCnfType {
        // The AIG is constant => Handle this simple case.
        if root.is_constant() {
            if root == Aig::get_false() {
                cnf.push(vec![]);
                return CraigCnfType::Constant0;
            }
            return CraigCnfType::Constant1;
        }

        // A fixed single literal => No Tseitin variables are required
        // and we can take a fast path without building an index.
        let node = self.nodes[root.get_node_index()];
        if node.is_variable() {
            let root_literal = node.get_variable() * if root.is_negated() { -1 } else { 1 };
            cnf.push(vec![root_literal]);
            return CraigCnfType::Normal;
        }

        // Create index of pre-existing (external) variables.
        // This index is extended with Tseitin variables are required.
        let mut node_to_var: BTreeMap<usize, i32> = BTreeMap::new();
        for (node_index, node) in self.nodes.iter().enumerate() {
            if node.is_variable() {
                node_to_var.insert(node_index, node.get_variable());
            }
        }

        let mut pending: Vec<usize> = vec![root.get_node_index()];
        while let Some(&node_index) = pending.last() {
            let node = self.nodes[node_index];

            // Check if node was already converted to Tseitin variable.
            if node_to_var.contains_key(&node_index) {
                pending.pop();
                continue;
            }

            // Both edges have to be processed first.
            let edge1 = node.edge1;
            let edge2 = node.edge2;
            let node1_index = edge1.get_node_index();
            let node2_index = edge2.get_node_index();
            let it_node1 = node_to_var.get(&node1_index).copied();
            let it_node2 = node_to_var.get(&node2_index).copied();
            match (it_node1, it_node2) {
                (None, _) => pending.push(node1_index),
                (Some(_), None) => pending.push(node2_index),
                (Some(var1), Some(var2)) => {
                    // Edges have been processed, now do Tseitin
                    // transformation.  This node is guaranteed to not be a
                    // variable as they have been inserted into the mapping
                    // at the start of this method.
                    pending.pop();

                    let tseitin_var = *next_free_index;
                    *next_free_index += 1;
                    node_to_var.insert(node_index, tseitin_var);

                    let lit_edge1 = var1 * if edge1.is_negated() { -1 } else { 1 };
                    let lit_edge2 = var2 * if edge2.is_negated() { -1 } else { 1 };

                    //  x = y * z <-> ( !x + y ) * ( !x + z ) * ( x + !y + !z )
                    cnf.push(vec![-tseitin_var, lit_edge1]);
                    cnf.push(vec![-tseitin_var, lit_edge2]);
                    cnf.push(vec![tseitin_var, -lit_edge1, -lit_edge2]);
                }
            }
        }

        // Finally add the root literal to the CNF since the required tree
        // now has been built and the root Tseitin variable is accessible.
        let root_var = *node_to_var.entry(root.get_node_index()).or_insert(0);
        cnf.push(vec![root_var * if root.is_negated() { -1 } else { 1 }]);
        CraigCnfType::Normal
    }
}

// ----------------------------------------------------------------------------
// Public types
// ----------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CraigCnfType {
    None,
    Constant0,
    Constant1,
    Normal,
}

/// Bit field of interpolant bases (C++ `enum class CraigConstruction`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CraigConstruction(pub u8);

impl CraigConstruction {
    pub const NONE: CraigConstruction = CraigConstruction(0);
    pub const SYMMETRIC: CraigConstruction = CraigConstruction(1);
    pub const ASYMMETRIC: CraigConstruction = CraigConstruction(2);
    pub const DUAL_SYMMETRIC: CraigConstruction = CraigConstruction(4);
    pub const DUAL_ASYMMETRIC: CraigConstruction = CraigConstruction(8);
    pub const ALL: CraigConstruction = CraigConstruction(15);
}

impl std::ops::BitOr for CraigConstruction {
    type Output = CraigConstruction;
    fn bitor(self, other: CraigConstruction) -> CraigConstruction {
        CraigConstruction(self.0 | other.0)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CraigInterpolant {
    None,
    Symmetric,
    Asymmetric,
    DualSymmetric,
    DualAsymmetric,
    Intersection,
    Union,
    Smallest,
    Largest,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub enum CraigVarType {
    #[default]
    ALocal,
    BLocal,
    Global,
}

impl std::fmt::Display for CraigVarType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            CraigVarType::ALocal => "A",
            CraigVarType::BLocal => "B",
            CraigVarType::Global => "G",
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub enum CraigClauseType {
    #[default]
    AClause,
    BClause,
    LClause,
}

impl std::fmt::Display for CraigClauseType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            CraigClauseType::AClause => "A",
            CraigClauseType::BClause => "B",
            CraigClauseType::LClause => "L",
        })
    }
}

#[derive(Clone, Copy, Debug)]
struct CraigData {
    partial_interpolant_sym: AigEdge,
    partial_interpolant_asym: AigEdge,
    partial_interpolant_dual_sym: AigEdge,
    partial_interpolant_dual_asym: AigEdge,
    clause_type: CraigClauseType,
    craig_id: usize,
}

impl CraigData {
    fn is_pure(&self) -> bool {
        self.clause_type != CraigClauseType::LClause
    }
}

// ----------------------------------------------------------------------------
// Computation of Craig interpolants
// ----------------------------------------------------------------------------

pub struct CraigTracer {
    assumptions: BTreeSet<i32>,
    constraint: Vec<i32>,
    assumption_clauses: Vec<i64>,

    marked_history: Vec<i32>,
    marked_lits: HashMap<i32, u8>,

    craig_clause_current_id: i32,
    craig_var_labels: HashMap<i32, CraigVarType>,
    craig_clause_labels: HashMap<i32, CraigClauseType>,
    craig_constraint_label: CraigClauseType,

    craig_clauses: Vec<Vec<i32>>,
    craig_interpolants: Vec<Option<CraigData>>,

    craig_construction: CraigConstruction,
    craig_id: usize,
    craig_interpolant: Option<CraigData>,

    craig_aig_sym: Aig,
    craig_aig_asym: Aig,
    craig_aig_dual_sym: Aig,
    craig_aig_dual_asym: Aig,
}

impl Default for CraigTracer {
    fn default() -> Self {
        CraigTracer::new()
    }
}

impl CraigTracer {
    pub fn new() -> CraigTracer {
        CraigTracer {
            assumptions: BTreeSet::new(),
            constraint: Vec::new(),
            assumption_clauses: Vec::new(),
            marked_history: Vec::new(),
            marked_lits: HashMap::new(),
            craig_clause_current_id: 1,
            craig_var_labels: HashMap::new(),
            craig_clause_labels: HashMap::new(),
            craig_constraint_label: CraigClauseType::LClause,
            craig_clauses: Vec::new(),
            craig_interpolants: Vec::new(),
            craig_construction: CraigConstruction::NONE,
            craig_id: 0,
            craig_interpolant: None,
            craig_aig_sym: Aig::default(),
            craig_aig_asym: Aig::default(),
            craig_aig_dual_sym: Aig::default(),
            craig_aig_dual_asym: Aig::default(),
        }
    }

    /// Rust helper: create a shared tracer and connect it to `solver`
    /// (C++ `solver->connect_proof_tracer (tracer, antecedents)` while
    /// keeping the `tracer` pointer).  Returns the shared tracer and the
    /// handle needed for `disconnect_proof_tracer`.
    pub fn connect(solver: &mut Solver, antecedents: bool) -> (Rc<RefCell<CraigTracer>>, TracerRef) {
        let tracer = Rc::new(RefCell::new(CraigTracer::new()));
        let r = solver.connect_proof_tracer(Box::new(SharedTracer(tracer.clone())), antecedents, false);
        (tracer, r)
    }

    // ====== BEGIN CRAIG INTERFACE ==========================================

    /// A bit field that configures the Craig interpolant bases to be built.
    pub fn set_craig_construction(&mut self, craig_construction: CraigConstruction) {
        assert!(self.craig_clauses.is_empty());
        self.craig_construction = craig_construction;
    }

    fn clear_craig_interpolant(&mut self) {
        self.craig_interpolant = None;
    }

    fn has_craig_interpolant(&self) -> bool {
        self.craig_interpolant.is_some()
    }

    /// Add variable of A, B or G type.  This has to be called before
    /// adding clauses using the variables.
    pub fn label_variable(&mut self, id: i32, variable_type: CraigVarType) {
        assert!(id > 0);
        self.craig_var_labels.insert(id, variable_type);
        self.marked_lits.insert(id, 0);
    }

    /// Add clause type of A or B.  This has to be called right before
    /// adding the respective clause that this type applies to.
    pub fn label_clause(&mut self, id: i32, clause_type: CraigClauseType) {
        assert!(id > 0);
        self.craig_clause_labels.insert(id, clause_type);
    }

    /// Set constraint type to A or B.  This has to be done before calling
    /// solve.
    pub fn label_constraint(&mut self, clause_type: CraigClauseType) {
        self.craig_constraint_label = clause_type;
    }

    fn var_label(&mut self, lit: i32) -> CraigVarType {
        // 'craig_var_labels[abs (lit)]' (default inserts 'A_LOCAL').
        *self.craig_var_labels.entry(lit.abs()).or_default()
    }

    fn create_interpolant_for_assumption(&mut self, literal: i32) -> CraigData {
        assert!(self.craig_var_labels.contains_key(&literal.abs()));

        let var_type = self.var_label(literal);
        let craig_id = self.craig_id;
        self.craig_id += 1;
        match var_type {
            CraigVarType::ALocal => CraigData {
                partial_interpolant_sym: Aig::get_false(),
                partial_interpolant_asym: Aig::get_false(),
                partial_interpolant_dual_sym: Aig::get_true(),
                partial_interpolant_dual_asym: Aig::get_false(),
                clause_type: CraigClauseType::AClause,
                craig_id,
            },
            CraigVarType::BLocal => CraigData {
                partial_interpolant_sym: Aig::get_true(),
                partial_interpolant_asym: Aig::get_true(),
                partial_interpolant_dual_sym: Aig::get_false(),
                partial_interpolant_dual_asym: Aig::get_true(),
                clause_type: CraigClauseType::BClause,
                craig_id,
            },
            CraigVarType::Global => CraigData {
                partial_interpolant_sym: Aig::get_true(),
                partial_interpolant_asym: Aig::get_true(),
                partial_interpolant_dual_sym: Aig::get_false(),
                partial_interpolant_dual_asym: Aig::get_false(),
                clause_type: CraigClauseType::LClause,
                craig_id,
            },
        }
    }

    fn create_interpolant_for_clause(&mut self, clause: &[i32], clause_type: CraigClauseType) -> CraigData {
        let mut result = CraigData {
            partial_interpolant_sym: Aig::get_true(),
            partial_interpolant_asym: Aig::get_true(),
            partial_interpolant_dual_sym: Aig::get_true(),
            partial_interpolant_dual_asym: Aig::get_true(),
            clause_type,
            craig_id: self.craig_id,
        };
        self.craig_id += 1;

        if self.is_construction_enabled(CraigConstruction::SYMMETRIC) {
            if clause_type == CraigClauseType::AClause {
                result.partial_interpolant_sym = Aig::get_false();
            } else if clause_type == CraigClauseType::BClause {
                result.partial_interpolant_sym = Aig::get_true();
            }
        }
        if self.is_construction_enabled(CraigConstruction::ASYMMETRIC) {
            if clause_type == CraigClauseType::AClause {
                let mut literals = Vec::new();
                for &lit in clause {
                    if self.var_label(lit) == CraigVarType::Global {
                        literals.push(self.craig_aig_asym.create_literal(lit));
                    }
                }
                result.partial_interpolant_asym = self.craig_aig_asym.create_or(literals);
            } else if clause_type == CraigClauseType::BClause {
                result.partial_interpolant_asym = Aig::get_true();
            }
        }
        if self.is_construction_enabled(CraigConstruction::DUAL_SYMMETRIC) {
            if clause_type == CraigClauseType::AClause {
                result.partial_interpolant_dual_sym = Aig::get_true();
            } else if clause_type == CraigClauseType::BClause {
                result.partial_interpolant_dual_sym = Aig::get_false();
            }
        }
        if self.is_construction_enabled(CraigConstruction::DUAL_ASYMMETRIC) {
            if clause_type == CraigClauseType::AClause {
                result.partial_interpolant_dual_asym = Aig::get_false();
            } else if clause_type == CraigClauseType::BClause {
                let mut literals = Vec::new();
                for &lit in clause {
                    if self.var_label(lit) == CraigVarType::Global {
                        literals.push(self.craig_aig_dual_asym.create_literal(-lit));
                    }
                }
                result.partial_interpolant_dual_asym = self.craig_aig_dual_asym.create_and(literals);
            }
        }

        result
    }

    fn extend_interpolant_with_resolution(&mut self, result: &mut CraigData, literal: i32, craig_data: &CraigData) {
        if result.clause_type != craig_data.clause_type {
            result.clause_type = CraigClauseType::LClause;
        }

        if self.is_construction_enabled(CraigConstruction::SYMMETRIC) {
            let label = self.var_label(literal);
            let aig = &mut self.craig_aig_sym;
            if label == CraigVarType::ALocal {
                result.partial_interpolant_sym =
                    aig.create_or2(result.partial_interpolant_sym, craig_data.partial_interpolant_sym);
            } else if label == CraigVarType::BLocal {
                result.partial_interpolant_sym =
                    aig.create_and2(result.partial_interpolant_sym, craig_data.partial_interpolant_sym);
            } else {
                let l1 = aig.create_literal(literal);
                let o1 = aig.create_or2(result.partial_interpolant_sym, l1);
                let l2 = aig.create_literal(-literal);
                let o2 = aig.create_or2(craig_data.partial_interpolant_sym, l2);
                result.partial_interpolant_sym = aig.create_and2(o1, o2);
            }
        }
        if self.is_construction_enabled(CraigConstruction::ASYMMETRIC) {
            let label = self.var_label(literal);
            let aig = &mut self.craig_aig_asym;
            if label == CraigVarType::ALocal {
                result.partial_interpolant_asym =
                    aig.create_or2(result.partial_interpolant_asym, craig_data.partial_interpolant_asym);
            } else {
                result.partial_interpolant_asym =
                    aig.create_and2(result.partial_interpolant_asym, craig_data.partial_interpolant_asym);
            }
        }
        if self.is_construction_enabled(CraigConstruction::DUAL_SYMMETRIC) {
            let label = self.var_label(literal);
            let aig = &mut self.craig_aig_dual_sym;
            if label == CraigVarType::ALocal {
                result.partial_interpolant_dual_sym =
                    aig.create_and2(result.partial_interpolant_dual_sym, craig_data.partial_interpolant_dual_sym);
            } else if label == CraigVarType::BLocal {
                result.partial_interpolant_dual_sym =
                    aig.create_or2(result.partial_interpolant_dual_sym, craig_data.partial_interpolant_dual_sym);
            } else {
                let l1 = aig.create_literal(-literal);
                let a1 = aig.create_and2(result.partial_interpolant_dual_sym, l1);
                let l2 = aig.create_literal(literal);
                let a2 = aig.create_and2(craig_data.partial_interpolant_dual_sym, l2);
                result.partial_interpolant_dual_sym = aig.create_or2(a1, a2);
            }
        }
        if self.is_construction_enabled(CraigConstruction::DUAL_ASYMMETRIC) {
            let label = self.var_label(literal);
            let aig = &mut self.craig_aig_dual_asym;
            if label == CraigVarType::BLocal {
                result.partial_interpolant_dual_asym =
                    aig.create_and2(result.partial_interpolant_dual_asym, craig_data.partial_interpolant_dual_asym);
            } else {
                result.partial_interpolant_dual_asym =
                    aig.create_or2(result.partial_interpolant_dual_asym, craig_data.partial_interpolant_dual_asym);
            }
        }
    }

    /// Builds the Craig interpolant specified and writes the result to the
    /// output vector.  Required Tseitin variables for CNF creation will
    /// start from the `next_free_variable` provided.  Returns the resulting
    /// CNF type (see the C++ header for details).
    ///
    /// require (UNSATISFIED)
    pub fn create_craig_interpolant(
        &mut self,
        interpolant: CraigInterpolant,
        cnf: &mut Vec<Vec<i32>>,
        next_free_variable: &mut i32,
    ) -> CraigCnfType {
        cnf.clear();

        let craig_interpolant = match self.craig_interpolant {
            None => return CraigCnfType::None,
            Some(ci) => ci,
        };

        let mut build_cnf_sym = false;
        let mut build_cnf_asym = false;
        let mut build_cnf_dual_sym = false;
        let mut build_cnf_dual_asym = false;
        match interpolant {
            CraigInterpolant::None => {}
            CraigInterpolant::Symmetric => {
                build_cnf_sym = self.is_construction_enabled(CraigConstruction::SYMMETRIC);
            }
            CraigInterpolant::Asymmetric => {
                build_cnf_asym = self.is_construction_enabled(CraigConstruction::ASYMMETRIC);
            }
            CraigInterpolant::DualSymmetric => {
                build_cnf_dual_sym = self.is_construction_enabled(CraigConstruction::DUAL_SYMMETRIC);
            }
            CraigInterpolant::DualAsymmetric => {
                build_cnf_dual_asym = self.is_construction_enabled(CraigConstruction::DUAL_ASYMMETRIC);
            }
            CraigInterpolant::Intersection
            | CraigInterpolant::Union
            | CraigInterpolant::Smallest
            | CraigInterpolant::Largest => {
                build_cnf_sym = self.is_construction_enabled(CraigConstruction::SYMMETRIC);
                build_cnf_asym = self.is_construction_enabled(CraigConstruction::ASYMMETRIC);
                build_cnf_dual_sym = self.is_construction_enabled(CraigConstruction::DUAL_SYMMETRIC);
                build_cnf_dual_asym = self.is_construction_enabled(CraigConstruction::DUAL_ASYMMETRIC);
            }
        }

        let mut craig_cnf_sym: Vec<Vec<i32>> = Vec::new();
        let mut craig_cnf_asym: Vec<Vec<i32>> = Vec::new();
        let mut craig_cnf_dual_sym: Vec<Vec<i32>> = Vec::new();
        let mut craig_cnf_dual_asym: Vec<Vec<i32>> = Vec::new();
        let mut craig_cnf_type_sym = CraigCnfType::None;
        let mut craig_cnf_type_asym = CraigCnfType::None;
        let mut craig_cnf_type_dual_sym = CraigCnfType::None;
        let mut craig_cnf_type_dual_asym = CraigCnfType::None;

        if build_cnf_sym {
            craig_cnf_type_sym = self.craig_aig_sym.create_cnf(
                craig_interpolant.partial_interpolant_sym,
                &mut craig_cnf_sym,
                next_free_variable,
            );
        }
        if build_cnf_asym {
            craig_cnf_type_asym = self.craig_aig_asym.create_cnf(
                craig_interpolant.partial_interpolant_asym,
                &mut craig_cnf_asym,
                next_free_variable,
            );
        }
        if build_cnf_dual_sym {
            craig_cnf_type_dual_sym = self.craig_aig_dual_sym.create_cnf(
                craig_interpolant.partial_interpolant_dual_sym,
                &mut craig_cnf_dual_sym,
                next_free_variable,
            );
        }
        if build_cnf_dual_asym {
            craig_cnf_type_dual_asym = self.craig_aig_dual_asym.create_cnf(
                craig_interpolant.partial_interpolant_dual_asym,
                &mut craig_cnf_dual_asym,
                next_free_variable,
            );
        }

        // Dual Craig interpolants have to be inverted.  However, the
        // construction rules for the dual asymmetric interpolant already
        // incorporates the negation.  So only the dual symmetric
        // interpolant needs to be negated.
        if craig_cnf_type_dual_sym == CraigCnfType::Constant1 {
            craig_cnf_dual_sym = vec![vec![]];
            craig_cnf_type_dual_sym = CraigCnfType::Constant0;
        } else if craig_cnf_type_dual_sym == CraigCnfType::Constant0 {
            craig_cnf_dual_sym = vec![];
            craig_cnf_type_dual_sym = CraigCnfType::Constant1;
        } else if craig_cnf_type_dual_sym == CraigCnfType::Normal {
            let last = craig_cnf_dual_sym.last_mut().unwrap();
            last[0] = -last[0];
        }

        match interpolant {
            CraigInterpolant::None => {
                *cnf = vec![];
                return CraigCnfType::None;
            }
            CraigInterpolant::Symmetric => {
                *cnf = craig_cnf_sym;
                return craig_cnf_type_sym;
            }
            CraigInterpolant::Asymmetric => {
                *cnf = craig_cnf_asym;
                return craig_cnf_type_asym;
            }
            CraigInterpolant::DualSymmetric => {
                *cnf = craig_cnf_dual_sym;
                return craig_cnf_type_dual_sym;
            }
            CraigInterpolant::DualAsymmetric => {
                *cnf = craig_cnf_dual_asym;
                return craig_cnf_type_dual_asym;
            }
            _ => {}
        }

        let mut craig_cnfs: Vec<(Vec<Vec<i32>>, CraigCnfType)> = Vec::new();
        if craig_cnf_type_sym != CraigCnfType::None {
            craig_cnfs.push((craig_cnf_sym, craig_cnf_type_sym));
        }
        if craig_cnf_type_asym != CraigCnfType::None {
            craig_cnfs.push((craig_cnf_asym, craig_cnf_type_asym));
        }
        if craig_cnf_type_dual_sym != CraigCnfType::None {
            craig_cnfs.push((craig_cnf_dual_sym, craig_cnf_type_dual_sym));
        }
        if craig_cnf_type_dual_asym != CraigCnfType::None {
            craig_cnfs.push((craig_cnf_dual_asym, craig_cnf_type_dual_asym));
        }

        if craig_cnfs.is_empty() {
            return CraigCnfType::None;
        } else if craig_cnfs.len() == 1 {
            let (c, t) = craig_cnfs.pop().unwrap();
            *cnf = c;
            return t;
        }

        // We have at least two Craig interpolants for the following
        // computations.
        match interpolant {
            CraigInterpolant::Union => {
                let mut all_constant_one = true;
                for it in craig_cnfs.iter_mut() {
                    if it.1 == CraigCnfType::Constant0 {
                        *cnf = std::mem::take(&mut it.0);
                        return CraigCnfType::Constant0;
                    }
                    all_constant_one &= it.1 == CraigCnfType::Constant1;
                }
                if all_constant_one {
                    *cnf = vec![];
                    return CraigCnfType::Constant1;
                }

                // Create trigger (t) that enforces all CNF parts.
                let craig_trigger = *next_free_variable;
                *next_free_variable += 1;
                let mut craig_trigger_clause = vec![craig_trigger];
                for it in craig_cnfs.iter_mut() {
                    if it.1 == CraigCnfType::Normal {
                        let n = it.0.len();
                        let last = it.0[n - 1][0];
                        cnf.extend(it.0.drain(..n - 1));
                        // The positive trigger implies that all CNF parts
                        // are enabled: (t -> t_1) = (-t v t_1)
                        cnf.push(vec![-craig_trigger, last]);
                        // The negative trigger implies that at least one of
                        // the CNF parts is not enabled.
                        craig_trigger_clause.push(-last);
                    }
                }

                cnf.push(craig_trigger_clause);
                cnf.push(vec![craig_trigger]);

                CraigCnfType::Normal
            }
            CraigInterpolant::Intersection => {
                let mut all_constant_zero = true;
                for it in craig_cnfs.iter_mut() {
                    if it.1 == CraigCnfType::Constant1 {
                        *cnf = std::mem::take(&mut it.0);
                        return CraigCnfType::Constant1;
                    }
                    all_constant_zero &= it.1 == CraigCnfType::Constant0;
                }
                if all_constant_zero {
                    *cnf = vec![vec![]];
                    return CraigCnfType::Constant0;
                }

                // Create trigger (t) that enforces all CNF parts.
                let craig_trigger = *next_free_variable;
                *next_free_variable += 1;
                let mut craig_trigger_clause = vec![-craig_trigger];
                for it in craig_cnfs.iter_mut() {
                    if it.1 == CraigCnfType::Normal {
                        let n = it.0.len();
                        let last = it.0[n - 1][0];
                        cnf.extend(it.0.drain(..n - 1));
                        // The positive trigger implies that one of the CNF
                        // parts is enabled.
                        craig_trigger_clause.push(last);
                        // The negative trigger implies that at all CNF parts
                        // are not enabled: (-t -> -t_1) = (t v -t_1)
                        cnf.push(vec![craig_trigger, -last]);
                    }
                }

                cnf.push(craig_trigger_clause);
                cnf.push(vec![craig_trigger]);

                CraigCnfType::Normal
            }
            CraigInterpolant::Smallest => {
                // 'std::min_element' returns the first minimum.
                let mut best = 0;
                for i in 1..craig_cnfs.len() {
                    if craig_cnfs[i].0.len() < craig_cnfs[best].0.len() {
                        best = i;
                    }
                }
                let (c, t) = craig_cnfs.swap_remove(best);
                *cnf = c;
                t
            }
            CraigInterpolant::Largest => {
                // 'std::max_element' returns the first maximum.
                let mut best = 0;
                for i in 1..craig_cnfs.len() {
                    if craig_cnfs[best].0.len() < craig_cnfs[i].0.len() {
                        best = i;
                    }
                }
                let (c, t) = craig_cnfs.swap_remove(best);
                *cnf = c;
                t
            }
            _ => unreachable!("Seleted craig interpolation type not supported!"),
        }
    }

    // ====== END CRAIG INTERFACE ============================================

    fn is_construction_enabled(&self, construction: CraigConstruction) -> bool {
        construction.0 & self.craig_construction.0 != 0
    }

    fn mark_literal(&mut self, literal: i32) -> u8 {
        let index = literal.abs();
        let mask: u8 = if literal < 0 { 2 } else { 1 };

        let entry = self.marked_lits.entry(index).or_insert(0);
        let was_marked = *entry;
        if was_marked & mask == 0 {
            *entry |= mask;
        }
        if was_marked == 0 {
            self.marked_history.push(index);
        }
        was_marked & !mask
    }

    fn unmark_all(&mut self) {
        for index in self.marked_history.drain(..) {
            self.marked_lits.insert(index, 0);
        }
    }

    fn interpolant_of(&self, id: i64) -> CraigData {
        self.craig_interpolants[(id - 1) as usize].expect("missing partial interpolant")
    }
}

impl Tracer for CraigTracer {
    fn add_original_clause(&mut self, id: i64, _redundant: bool, c: &[i32], restore: bool) {
        assert!(id > 0);

        if restore {
            self.craig_clauses[(id - 1) as usize] = c.to_vec();
            return;
        }

        let original_id = self.craig_clause_current_id;
        self.craig_clause_current_id += 1;
        assert!(self.craig_clause_labels.contains_key(&original_id));
        for l in c {
            assert!(self.craig_var_labels.contains_key(&l.abs()));
        }
        let clause_label = self.craig_clause_labels[&original_id];
        let interpolant = self.create_interpolant_for_clause(c, clause_label);

        assert!(self.craig_clauses.len() as i64 == id - 1);
        self.craig_clauses.push(c.to_vec());
        self.craig_interpolants.push(Some(interpolant));
    }

    // TODO: print fatal error if witness (3rd argument) is true.
    fn add_derived_clause(&mut self, id: i64, _redundant: bool, _witness: i32, c: &[i32], proof_chain: &[i64]) {
        assert!(!proof_chain.is_empty());
        for &clause in proof_chain {
            assert!(self.craig_interpolants[(clause - 1) as usize].is_some());
        }
        // Mark literals of conflicting clause.
        let last = *proof_chain.last().unwrap();
        let conflicting = self.craig_clauses[(last - 1) as usize].clone();
        for &l in &conflicting {
            self.mark_literal(l);
        }

        // Find pivot literal of each clause that was resolved with
        // and extend Craig interpolant for it.
        let mut interpolant = self.interpolant_of(last);
        for i in (0..proof_chain.len() - 1).rev() {
            let antecedent = self.craig_clauses[(proof_chain[i] - 1) as usize].clone();
            for &l in &antecedent {
                // Function mark_literal returns true if inverse literal was
                // marked before and marks literal l for the following
                // resolvent literal checks.
                if self.mark_literal(l) == 0 {
                    continue;
                }

                let other = self.interpolant_of(proof_chain[i]);
                self.extend_interpolant_with_resolution(&mut interpolant, -l, &other);
            }
        }
        self.unmark_all();
        assert!(self.craig_clauses.len() as i64 == id - 1);
        self.craig_clauses.push(c.to_vec());
        self.craig_interpolants.push(Some(interpolant));
    }

    fn add_assumption_clause(&mut self, id: i64, c: &[i32], proof_chain: &[i64]) {
        let mut interpolant: Option<CraigData> = None;

        if !proof_chain.is_empty() {
            // We have a resolution of multiple clauses and therefore reuse
            // the existing code to build our Craig interpolant.
            self.add_derived_clause(id, true, 0, c, proof_chain);
            // C++ keeps a pointer to the stored interpolant and modifies it
            // in place; we copy it and write it back below.
            interpolant = self.craig_interpolants[(id - 1) as usize];
        } else {
            assert!(c.len() == 2);
            let c0_is_assumption = self.assumptions.contains(&-c[0]);
            let c1_is_assumption = self.assumptions.contains(&-c[1]);

            if !c0_is_assumption || !c1_is_assumption {
                let l = if c0_is_assumption { -c[1] } else { -c[0] };
                assert!(self.craig_clauses.len() as i64 == id - 1);
                self.craig_clauses.push(vec![l]);
                let data = self.create_interpolant_for_assumption(-l);
                self.craig_interpolants.push(Some(data));
                self.assumption_clauses.push(id);
                return;
            }
        }

        for &lit in c {
            let is_assumption = self.assumptions.contains(&-lit);
            if !is_assumption {
                continue;
            }

            let other = self.create_interpolant_for_assumption(-lit);
            if let Some(mut data) = interpolant {
                self.extend_interpolant_with_resolution(&mut data, lit, &other);
                interpolant = Some(data);
            } else {
                interpolant = Some(other);
            }
        }

        if proof_chain.is_empty() {
            assert!(self.craig_clauses.len() as i64 == id - 1);
            self.craig_clauses.push(c.to_vec());
            self.craig_interpolants.push(interpolant);
        } else {
            self.craig_interpolants[(id - 1) as usize] = interpolant;
        }
        self.assumption_clauses.push(id);
    }

    fn delete_clause(&mut self, id: i64, _redundant: bool, _c: &[i32]) {
        assert!(self.craig_clauses.len() as i64 >= id - 1);
        self.craig_clauses[(id - 1) as usize].clear();
    }

    fn add_assumption(&mut self, lit: i32) {
        self.assumptions.insert(lit);
    }

    fn add_constraint(&mut self, c: &[i32]) {
        self.constraint = c.to_vec();
    }

    fn reset_assumptions(&mut self) {
        let ids = self.assumption_clauses.clone();
        for id in ids {
            let clause = self.craig_clauses[(id - 1) as usize].clone();
            Tracer::delete_clause(self, id, true, &clause);
        }
        self.assumptions.clear();
        self.constraint.clear();
        self.assumption_clauses.clear();
    }

    fn conclude_unsat(&mut self, conclusion: ConclusionType, proof_chain: &[i64]) {
        self.craig_interpolant = None;

        let interpolant = match conclusion {
            ConclusionType::CONFLICT => {
                // There is a single global conflict.  The proof_chain
                // contains a single empty clause.
                assert!(proof_chain.len() == 1);
                assert!(self.craig_clauses[(proof_chain[0] - 1) as usize].is_empty());
                self.interpolant_of(proof_chain[0])
            }
            ConclusionType::ASSUMPTIONS => {
                // One or more constraints are responsible for the conflict.
                // The proof_chain contains a single clause with failing
                // assumptions.
                assert!(proof_chain.len() == 1);
                assert!(!self.craig_clauses[(proof_chain[0] - 1) as usize].is_empty());
                self.interpolant_of(proof_chain[0])
            }
            ConclusionType::CONSTRAINT => {
                // The constraint clause is responsible for the conflict.

                // Mark literals of conflicting clause.
                let constraint = self.constraint.clone();
                for &l in &constraint {
                    self.mark_literal(l);
                }

                // Find pivot literal of each clause that was resolved with
                // and extend Craig interpolant for it.
                let label = self.craig_constraint_label;
                let mut interpolant = self.create_interpolant_for_clause(&constraint, label);
                for i in (0..proof_chain.len()).rev() {
                    let antecedent = self.craig_clauses[(proof_chain[i] - 1) as usize].clone();
                    for &l in &antecedent {
                        if self.mark_literal(l) == 0 {
                            continue;
                        }

                        let other = self.interpolant_of(proof_chain[i]);
                        self.extend_interpolant_with_resolution(&mut interpolant, -l, &other);
                    }
                }

                self.unmark_all();
                interpolant
            }
        };

        self.craig_interpolant = Some(interpolant);
    }
}

/// Forwards all `Tracer` events to a shared `Rc<RefCell<T>>`, so that the
/// user can keep access to a tracer owned by the solver.  (Due to the
/// orphan rule this newtype is needed in user code; see the API notes for
/// a proposal to provide it in the library.)
pub struct SharedTracer<T: Tracer>(pub Rc<RefCell<T>>);

impl<T: Tracer> Tracer for SharedTracer<T> {
    fn add_original_clause(&mut self, id: i64, redundant: bool, clause: &[i32], restored: bool) {
        self.0.borrow_mut().add_original_clause(id, redundant, clause, restored)
    }
    fn add_derived_clause(&mut self, id: i64, redundant: bool, witness: i32, clause: &[i32], chain: &[i64]) {
        self.0.borrow_mut().add_derived_clause(id, redundant, witness, clause, chain)
    }
    fn delete_clause(&mut self, id: i64, redundant: bool, clause: &[i32]) {
        self.0.borrow_mut().delete_clause(id, redundant, clause)
    }
    fn demote_clause(&mut self, id: u64, clause: &[i32]) {
        self.0.borrow_mut().demote_clause(id, clause)
    }
    fn weaken_minus(&mut self, id: i64, clause: &[i32]) {
        self.0.borrow_mut().weaken_minus(id, clause)
    }
    fn strengthen(&mut self, id: i64) {
        self.0.borrow_mut().strengthen(id)
    }
    fn report_status(&mut self, status: i32, id: i64) {
        self.0.borrow_mut().report_status(status, id)
    }
    fn finalize_clause(&mut self, id: i64, clause: &[i32]) {
        self.0.borrow_mut().finalize_clause(id, clause)
    }
    fn begin_proof(&mut self, reserved_ids: i64) {
        self.0.borrow_mut().begin_proof(reserved_ids)
    }
    fn solve_query(&mut self) {
        self.0.borrow_mut().solve_query()
    }
    fn add_assumption(&mut self, lit: i32) {
        self.0.borrow_mut().add_assumption(lit)
    }
    fn add_constraint(&mut self, clause: &[i32]) {
        self.0.borrow_mut().add_constraint(clause)
    }
    fn reset_assumptions(&mut self) {
        self.0.borrow_mut().reset_assumptions()
    }
    fn add_assumption_clause(&mut self, id: i64, clause: &[i32], chain: &[i64]) {
        self.0.borrow_mut().add_assumption_clause(id, clause, chain)
    }
    fn conclude_unsat(&mut self, conclusion: ConclusionType, ids: &[i64]) {
        self.0.borrow_mut().conclude_unsat(conclusion, ids)
    }
    fn conclude_sat(&mut self, model: &[i32]) {
        self.0.borrow_mut().conclude_sat(model)
    }
    fn conclude_unknown(&mut self, trail: &[i32]) {
        self.0.borrow_mut().conclude_unknown(trail)
    }
    fn notify_equivalence(&mut self, lit: i32, other: i32) {
        self.0.borrow_mut().notify_equivalence(lit, other)
    }
}

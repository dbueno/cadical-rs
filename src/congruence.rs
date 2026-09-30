//! Port of `congruence.hpp` and `congruence.cpp`: congruence closure
//! (gate extraction and equivalent literal substitution, SAT 2024).
//!
//! Gates are heap allocated (`Box::into_raw`) and referenced by raw
//! `*mut Gate` pointers as in C++ (they are shared between the hash table,
//! the occurrence lists `gtab` and the `garbage` stack).

use std::collections::VecDeque;

use crate::clause::CRef;
use crate::internal::Internal;

pub type LRAT_ID = i64;

pub const LD_MAX_ARITY: u32 = 26;
pub const MAX_ARITY: u32 = (1 << LD_MAX_ARITY) - 1;

/// `enum class Gate_Type : int8_t`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(i8)]
pub enum Gate_Type {
    And_Gate = 0,
    XOr_Gate = 1,
    ITE_Gate = 2,
}

/// Wrapper when we are looking for implication in if-then-else gates.
#[derive(Clone, Copy, Debug)]
pub struct lit_implication {
    pub first: i32,
    pub second: i32,
    pub clause: CRef,
}

impl lit_implication {
    pub fn new(f: i32, s: i32, id: CRef) -> Self {
        lit_implication { first: f, second: s, clause: id }
    }
    pub fn new2(f: i32, s: i32) -> Self {
        lit_implication { first: f, second: s, clause: CRef::NULL }
    }
    pub fn swap(&mut self) {
        std::mem::swap(&mut self.first, &mut self.second);
    }
}

impl Default for lit_implication {
    fn default() -> Self {
        lit_implication { first: 0, second: 0, clause: CRef::NULL }
    }
}

/// Wrapper when we are looking for equivalence for if-then-else-gate.
/// They are produced by merging implication.
#[derive(Clone, Copy, Debug)]
pub struct lit_equivalence {
    pub first: i32,
    pub second: i32,
    pub first_clause: CRef,
    pub second_clause: CRef,
}

impl lit_equivalence {
    pub fn check_invariant(&self) {
        debug_assert!(!self.second_clause.is_null());
        debug_assert!(!self.first_clause.is_null());
        debug_assert!(self.first_clause.lits().contains(&self.first));
        debug_assert!(self.second_clause.lits().contains(&self.second));
        debug_assert!(self.first_clause.lits().contains(&-self.second));
        debug_assert!(self.second_clause.lits().contains(&-self.first));
    }
    pub fn new(f: i32, f_id: CRef, s: i32, s_id: CRef) -> Self {
        lit_equivalence { first: f, second: s, first_clause: f_id, second_clause: s_id }
    }
    pub fn new2(f: i32, s: i32) -> Self {
        lit_equivalence { first: f, second: s, first_clause: CRef::NULL, second_clause: CRef::NULL }
    }
    pub fn swap(&mut self) -> lit_equivalence {
        std::mem::swap(&mut self.first, &mut self.second);
        std::mem::swap(&mut self.first_clause, &mut self.second_clause);
        *self
    }
    pub fn negate_both(&mut self) -> lit_equivalence {
        self.first = -self.first;
        self.second = -self.second;
        std::mem::swap(&mut self.first_clause, &mut self.second_clause);
        *self
    }
}

impl Default for lit_equivalence {
    fn default() -> Self {
        lit_equivalence::new2(0, 0)
    }
}

pub type lit_implications = Vec<lit_implication>;
pub type lit_equivalences = Vec<lit_equivalence>;

#[derive(Clone, Copy, Debug)]
pub struct LitClausePair {
    /// Current literal from the gate.
    pub current_lit: i32,
    pub clause: CRef,
}

impl LitClausePair {
    pub fn new(lit: i32, cl: CRef) -> Self {
        LitClausePair { current_lit: lit, clause: cl }
    }
}

impl Default for LitClausePair {
    fn default() -> Self {
        LitClausePair { current_lit: 0, clause: CRef::NULL }
    }
}

#[derive(Clone, Copy, Debug, Default)]
pub struct LitIdPair {
    /// Current literal from the gate.
    pub lit: i32,
    pub id: LRAT_ID,
}

impl LitIdPair {
    pub fn new(l: i32, i: LRAT_ID) -> Self {
        LitIdPair { lit: l, id: i }
    }
}

/// Sorting the scheduled clauses is way faster if we compute and save the
/// clause size in the schedule to avoid pointer access to clauses during
/// sorting.
#[derive(Clone, Copy, Debug, Default)]
pub struct ClauseSize {
    pub size: usize,
    pub clause: CRef,
}

impl ClauseSize {
    pub fn new(s: i32, c: CRef) -> Self {
        ClauseSize { size: s as usize, clause: c }
    }
    pub fn from_clause(c: CRef) -> Self {
        ClauseSize { size: c.size() as usize, clause: c }
    }
}

/// `smaller_clause_size_rank`.
#[inline]
pub fn smaller_clause_size_rank(a: &ClauseSize) -> usize {
    a.size
}

/// `enum Special_Gate` (bit flags stored in `Gate::degenerated_gate`).
#[allow(non_snake_case)]
pub mod Special_Gate {
    pub const NORMAL: i8 = 0;
    pub const NO_PLUS_THEN: i8 = 1 << 0;
    pub const NO_NEG_THEN: i8 = 1 << 1;
    pub const NO_THEN: i8 = NO_PLUS_THEN + NO_NEG_THEN;
    pub const NO_PLUS_ELSE: i8 = 1 << 2;
    pub const NO_NEG_ELSE: i8 = 1 << 3;
    /// a = (a & b)
    pub const DEGENERATED_AND: i8 = 1 << 4;
    /// false = (a & b)
    pub const DEGENERATED_AND_LHS_FALSE: i8 = 1 << 5;
    pub const NO_ELSE: i8 = NO_PLUS_ELSE + NO_NEG_ELSE;
    pub const COND_LHS: i8 = NO_NEG_THEN + NO_PLUS_ELSE;
    pub const UCOND_LHS: i8 = NO_PLUS_THEN + NO_NEG_ELSE;
}

#[inline]
pub fn ite_flags_no_then_clauses(flag: i8) -> bool {
    (flag & Special_Gate::NO_THEN) == Special_Gate::NO_THEN
}
#[inline]
pub fn ite_flags_no_else_clauses(flag: i8) -> bool {
    (flag & Special_Gate::NO_ELSE) == Special_Gate::NO_ELSE
}
#[inline]
pub fn ite_flags_neg_cond_lhs(flag: i8) -> bool {
    (flag & Special_Gate::UCOND_LHS) == Special_Gate::UCOND_LHS
}
#[inline]
pub fn ite_flags_cond_lhs(flag: i8) -> bool {
    (flag & Special_Gate::COND_LHS) == Special_Gate::COND_LHS
}

/// `std::string special_gate_str (int8_t f)`.
pub fn special_gate_str(f: i8) -> &'static str {
    use Special_Gate::*;
    match f {
        NORMAL => "",
        NO_PLUS_ELSE => "{no +e}",
        NO_PLUS_THEN => "{no +t}",
        NO_NEG_ELSE => "{no -e}",
        NO_NEG_THEN => "{no -t}",
        NO_ELSE => "{no e}",
        NO_THEN => "{no t}",
        COND_LHS => "{no -t +e}",
        UCOND_LHS => "{no +t -e}",
        DEGENERATED_AND => "{AND/bin}",
        DEGENERATED_AND_LHS_FALSE => "{AND/bin;lhs=-1}",
        _ => {
            debug_assert!(false);
            "BROKEN GATE"
        }
    }
}

/// `std::string string_of_gate (Gate_Type t)`.
pub fn string_of_gate(t: Gate_Type) -> &'static str {
    match t {
        Gate_Type::And_Gate => "And",
        Gate_Type::XOr_Gate => "XOr",
        Gate_Type::ITE_Gate => "ITE",
    }
}

/// `std::optional` replacement (C++ `my_dummy_optional`).
#[derive(Clone, Copy, Debug)]
pub struct my_dummy_optional {
    pub content: LitClausePair,
}

impl Default for my_dummy_optional {
    fn default() -> Self {
        my_dummy_optional { content: LitClausePair::new(0, CRef::NULL) }
    }
}

impl my_dummy_optional {
    /// `bool operator() () const`.
    #[inline]
    pub fn is_set(&self) -> bool {
        self.content.current_lit != 0
    }
    /// `operator= (LitClausePair p)`.
    #[inline]
    pub fn set(&mut self, p: LitClausePair) -> my_dummy_optional {
        self.content = p;
        *self
    }
    #[inline]
    pub fn reset(&mut self) {
        self.content = LitClausePair::new(0, CRef::NULL);
    }
}

/// The core structure of this algorithm: the gate.  It is composed of a
/// left-hand side and an array of right-hand side.
#[derive(Clone, Debug)]
pub struct Gate {
    #[cfg(feature = "logging")]
    pub id: u64,
    pub lhs: i32,
    pub tag: Gate_Type,
    pub garbage: bool,
    pub indexed: bool,
    pub marked: bool,
    pub shrunken: bool,
    pub pos_lhs_ids: Vec<LitClausePair>,
    pub neg_lhs_ids: my_dummy_optional,
    pub degenerated_gate: i8,
    pub rhs: Vec<i32>,
}

impl Default for Gate {
    /// `new Gate ()` (value initialized).
    fn default() -> Self {
        Gate {
            #[cfg(feature = "logging")]
            id: 0,
            lhs: 0,
            tag: Gate_Type::And_Gate,
            garbage: false,
            indexed: false,
            marked: false,
            shrunken: false,
            pos_lhs_ids: Vec::new(),
            neg_lhs_ids: my_dummy_optional::default(),
            degenerated_gate: Special_Gate::NORMAL,
            rhs: Vec::new(),
        }
    }
}

impl Gate {
    #[inline]
    pub fn arity(&self) -> usize {
        self.rhs.len()
    }
    /// `bool operator== (Gate const &lhs)`.
    #[inline]
    pub fn equals(&self, other: &Gate) -> bool {
        self.tag == other.tag && self.rhs == other.rhs
    }
}

pub type GOccs = Vec<*mut Gate>;

/// `GateEqualTo`.
#[inline]
pub fn gate_equal_to(lhs: *const Gate, rhs: *const Gate) -> bool {
    // SAFETY: gates in the table are alive.
    unsafe { (*lhs).rhs == (*rhs).rhs && (*lhs).tag == (*rhs).tag }
}

#[derive(Clone, Copy, Debug)]
pub struct CompactBinary {
    pub clause: CRef,
    pub id: LRAT_ID,
    pub lit1: i32,
    pub lit2: i32,
}

impl CompactBinary {
    pub fn new(c: CRef, i: LRAT_ID, l1: i32, l2: i32) -> Self {
        CompactBinary { clause: c, id: i, lit1: l1, lit2: l2 }
    }
}

impl Default for CompactBinary {
    fn default() -> Self {
        CompactBinary { clause: CRef::NULL, id: 0, lit1: 0, lit2: 0 }
    }
}

/// `struct Hash` (the hash function of the gates table; its
/// `operator()` is defined in 'congruence.cpp').
#[derive(Clone, Copy, Debug)]
pub struct Hash {
    pub nonces: [u64; 16],
}

#[derive(Clone, Copy, Debug, Default)]
pub struct Rewrite {
    pub src: i32,
    pub dst: i32,
    pub id1: LRAT_ID,
    pub id2: LRAT_ID,
}

impl Rewrite {
    pub fn new(src: i32, dst: i32, id1: LRAT_ID, id2: LRAT_ID) -> Self {
        Rewrite { src, dst, id1, id2 }
    }
}


/*------------------------------------------------------------------------*/
// Port of libc++ 21 '__hash_table' with unique keys (the implementation of
// 'std::unordered_set').  The congruence closure looks up gates in a
// 'unordered_set<Gate *, Hash, GateEqualTo>' whose behaviour depends on the
// bucket and node order (which duplicate is found through 'equal_range',
// the order of deleting gates in 'reset_closure' and hence the log), so we
// reproduce the libc++ data structure exactly: a singly linked list of
// nodes (which store their hash value) starting at a before-begin node,
// and buckets pointing to the node *before* the first node of the bucket.
//
// Nodes live in an arena ('nodes'), index 'HT_FIRST' is '__first_node_',
// 'HT_NIL' is 'nullptr'.  Iterators are node indices ('Option<usize>',
// 'None' is 'end ()').  Node indices stay valid across rehashing (as node
// pointers do in C++).

const HT_NIL: usize = usize::MAX;
const HT_FIRST: usize = 0;

#[derive(Clone, Copy, Debug)]
struct HtNode<K: Copy> {
    next: usize,
    hash: usize,
    value: K,
}

/// `std::__is_hash_power2`.
#[inline(always)]
fn ht_is_hash_power2(bc: usize) -> bool {
    bc > 2 && (bc & (bc - 1)) == 0
}

/// `std::__constrain_hash`.
#[inline(always)]
fn ht_constrain_hash(h: usize, bc: usize) -> usize {
    if (bc & bc.wrapping_sub(1)) == 0 {
        h & bc.wrapping_sub(1)
    } else if h < bc {
        h
    } else {
        h % bc
    }
}

/// `std::__next_hash_pow2`.
#[inline(always)]
fn ht_next_hash_pow2(n: usize) -> usize {
    if n < 2 {
        n
    } else {
        1usize << (usize::BITS - (n - 1).leading_zeros())
    }
}

/// `std::__next_prime` (libc++ 'src/hash.cpp'): the smallest prime which
/// is not smaller than 'n' (and '0' for '0').  libc++ uses a table of the
/// primes up to 211 and then trial division over a wheel of 210, which
/// yields the same result.
fn ht_next_prime(n: usize) -> usize {
    const SMALL_PRIMES: [usize; 48] = [
        0, 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83,
        89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179,
        181, 191, 193, 197, 199, 211,
    ];
    if n <= 211 {
        let pos = SMALL_PRIMES.partition_point(|&p| p < n);
        return SMALL_PRIMES[pos];
    }
    let is_prime = |m: usize| -> bool {
        if m % 2 == 0 {
            return false;
        }
        let mut d = 3usize;
        while d <= m / d {
            if m % d == 0 {
                return false;
            }
            d += 2;
        }
        true
    };
    let mut m = n;
    while !is_prime(m) {
        m += 1;
    }
    m
}

/// `std::unordered_set` (libc++ 21) with unique keys.  Hashing and
/// equality are supplied by the caller at each operation (the hash value
/// is stored in the node as in libc++, so stale hashes behave identically).
#[derive(Clone, Debug)]
pub struct LibcxxHashSet<K: Copy> {
    nodes: Vec<HtNode<K>>,
    free: Vec<usize>,
    buckets: Vec<usize>,
    size: usize,
    max_load_factor: f32,
}

impl<K: Copy> LibcxxHashSet<K> {
    /// `unordered_set (n, hash)`; 'sentinel' is only used to fill the
    /// value slot of the before-begin node.
    pub fn new(n: usize, sentinel: K) -> Self {
        let mut s = LibcxxHashSet {
            nodes: vec![HtNode { next: HT_NIL, hash: 0, value: sentinel }],
            free: Vec::new(),
            buckets: Vec::new(),
            size: 0,
            max_load_factor: 1.0,
        };
        s.rehash(n);
        s
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.size
    }
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.size == 0
    }
    #[inline]
    pub fn bucket_count(&self) -> usize {
        self.buckets.len()
    }
    /// `begin ()`.
    #[inline]
    pub fn begin(&self) -> Option<usize> {
        let n = self.nodes[HT_FIRST].next;
        if n == HT_NIL {
            None
        } else {
            Some(n)
        }
    }
    /// `++it`.
    #[inline]
    pub fn next(&self, it: usize) -> Option<usize> {
        let n = self.nodes[it].next;
        if n == HT_NIL {
            None
        } else {
            Some(n)
        }
    }
    /// `*it`.
    #[inline]
    pub fn get(&self, it: usize) -> K {
        self.nodes[it].value
    }
    /// All elements in iteration order.
    pub fn elements(&self) -> Vec<K> {
        let mut res = Vec::with_capacity(self.size);
        let mut it = self.begin();
        while let Some(n) = it {
            res.push(self.nodes[n].value);
            it = self.next(n);
        }
        res
    }

    fn alloc_node(&mut self, hash: usize, value: K) -> usize {
        if let Some(i) = self.free.pop() {
            self.nodes[i] = HtNode { next: HT_NIL, hash, value };
            i
        } else {
            self.nodes.push(HtNode { next: HT_NIL, hash, value });
            self.nodes.len() - 1
        }
    }

    /// `__rehash_unique (n)` (`rehash (n)`).
    pub fn rehash(&mut self, n: usize) {
        let mut n = n;
        if n == 1 {
            n = 2;
        } else if (n & n.wrapping_sub(1)) != 0 {
            n = ht_next_prime(n);
        }
        let bc = self.bucket_count();
        if n > bc {
            self.do_rehash(n);
        } else if n < bc {
            let needed = ((self.size as f32) / self.max_load_factor).ceil() as usize;
            n = std::cmp::max(
                n,
                if ht_is_hash_power2(bc) { ht_next_hash_pow2(needed) } else { ht_next_prime(needed) },
            );
            if n < bc {
                self.do_rehash(n);
            }
        }
    }

    /// `__reserve_unique (n)` (`reserve (n)`).
    pub fn reserve(&mut self, n: usize) {
        let m = ((n as f32) / self.max_load_factor).ceil() as usize;
        self.rehash(m);
    }

    /// `__do_rehash<true> (nbc)`.
    fn do_rehash(&mut self, nbc: usize) {
        self.buckets = vec![HT_NIL; nbc];
        if nbc == 0 {
            return;
        }
        let mut pp = HT_FIRST;
        let mut cp = self.nodes[pp].next;
        if cp == HT_NIL {
            return;
        }
        let mut chash = ht_constrain_hash(self.nodes[cp].hash, nbc);
        self.buckets[chash] = pp;
        let mut phash = chash;
        pp = cp;
        cp = self.nodes[cp].next;
        while cp != HT_NIL {
            chash = ht_constrain_hash(self.nodes[cp].hash, nbc);
            if chash == phash {
                pp = cp;
            } else if self.buckets[chash] == HT_NIL {
                self.buckets[chash] = pp;
                pp = cp;
                phash = chash;
            } else {
                let np = cp;
                self.nodes[pp].next = self.nodes[np].next;
                let b = self.buckets[chash];
                self.nodes[np].next = self.nodes[b].next;
                self.nodes[b].next = cp;
            }
            cp = self.nodes[pp].next;
        }
    }

    /// `find (k)` where 'hash' is the hash of 'k' and 'eq (x)' is
    /// 'key_eq () (x, k)'.
    pub fn find<F: FnMut(K) -> bool>(&self, hash: usize, mut eq: F) -> Option<usize> {
        let bc = self.bucket_count();
        if bc != 0 && self.size != 0 {
            let chash = ht_constrain_hash(hash, bc);
            let mut nd = self.buckets[chash];
            if nd != HT_NIL {
                nd = self.nodes[nd].next;
                while nd != HT_NIL
                    && (self.nodes[nd].hash == hash
                        || ht_constrain_hash(self.nodes[nd].hash, bc) == chash)
                {
                    if self.nodes[nd].hash == hash && eq(self.nodes[nd].value) {
                        return Some(nd);
                    }
                    nd = self.nodes[nd].next;
                }
            }
        }
        None
    }

    /// `insert (k)` (`__emplace_unique_key_args`), returns the iterator and
    /// whether the value was inserted.
    pub fn insert<F: FnMut(K) -> bool>(&mut self, hash: usize, value: K, mut eq: F) -> (usize, bool) {
        let mut bc = self.bucket_count();
        let mut chash = 0usize;
        if bc != 0 {
            chash = ht_constrain_hash(hash, bc);
            let mut nd = self.buckets[chash];
            if nd != HT_NIL {
                nd = self.nodes[nd].next;
                while nd != HT_NIL
                    && (self.nodes[nd].hash == hash
                        || ht_constrain_hash(self.nodes[nd].hash, bc) == chash)
                {
                    if self.nodes[nd].hash == hash && eq(self.nodes[nd].value) {
                        return (nd, false);
                    }
                    nd = self.nodes[nd].next;
                }
            }
        }
        let h = self.alloc_node(hash, value);
        if ((self.size + 1) as f32) > (bc as f32) * self.max_load_factor || bc == 0 {
            let a = 2 * bc + (!ht_is_hash_power2(bc)) as usize;
            let b = (((self.size + 1) as f32) / self.max_load_factor).ceil() as usize;
            self.rehash(std::cmp::max(a, b));
            bc = self.bucket_count();
            chash = ht_constrain_hash(hash, bc);
        }
        let pn = self.buckets[chash];
        if pn == HT_NIL {
            let pn = HT_FIRST;
            self.nodes[h].next = self.nodes[pn].next;
            self.nodes[pn].next = h;
            self.buckets[chash] = pn;
            let nx = self.nodes[h].next;
            if nx != HT_NIL {
                let nh = ht_constrain_hash(self.nodes[nx].hash, bc);
                self.buckets[nh] = h;
            }
        } else {
            self.nodes[h].next = self.nodes[pn].next;
            self.nodes[pn].next = h;
        }
        self.size += 1;
        (h, true)
    }

    /// `erase (it)` (`remove (it)`), returns the iterator following 'it'.
    pub fn erase(&mut self, cn: usize) -> Option<usize> {
        debug_assert!(cn != HT_FIRST && cn != HT_NIL);
        let bc = self.bucket_count();
        let chash = ht_constrain_hash(self.nodes[cn].hash, bc);
        let mut pn = self.buckets[chash];
        while self.nodes[pn].next != cn {
            pn = self.nodes[pn].next;
        }
        if pn == HT_FIRST || ht_constrain_hash(self.nodes[pn].hash, bc) != chash {
            let nx = self.nodes[cn].next;
            if nx == HT_NIL || ht_constrain_hash(self.nodes[nx].hash, bc) != chash {
                self.buckets[chash] = HT_NIL;
            }
        }
        let nx = self.nodes[cn].next;
        if nx != HT_NIL {
            let nhash = ht_constrain_hash(self.nodes[nx].hash, bc);
            if nhash != chash {
                self.buckets[nhash] = pn;
            }
        }
        self.nodes[pn].next = nx;
        self.nodes[cn].next = HT_NIL;
        self.size -= 1;
        self.free.push(cn);
        if nx == HT_NIL {
            None
        } else {
            Some(nx)
        }
    }

    /// `clear ()` (keeps the bucket count).
    pub fn clear(&mut self) {
        if self.size > 0 {
            self.nodes.truncate(1);
            self.nodes[HT_FIRST].next = HT_NIL;
            self.free.clear();
            for b in self.buckets.iter_mut() {
                *b = HT_NIL;
            }
            self.size = 0;
        }
    }
}

/*------------------------------------------------------------------------*/

/// `typedef unordered_set<Gate *, Hash, GateEqualTo> GatesTable`, mirroring
/// the libc++ implementation (see [`LibcxxHashSet`]).  Iterators
/// (`GatesTable::iterator`) are `Option<usize>` node indices (`None` is
/// `end ()`).
#[derive(Clone, Debug)]
pub struct GatesTable {
    pub hash: Hash,
    pub set: LibcxxHashSet<*mut Gate>,
}

/// `GatesTable::iterator` (`None` is `end ()`).
pub type GatesIterator = Option<usize>;

impl GatesTable {
    /// `find (g)`.
    pub fn find(&self, g: *const Gate) -> GatesIterator {
        let h = self.hash.hash(g);
        self.set.find(h, |x| gate_equal_to(x, g))
    }
    /// `count (g)`.
    pub fn count(&self, g: *const Gate) -> usize {
        self.find(g).is_some() as usize
    }
    /// `insert (g)`.
    pub fn insert(&mut self, g: *mut Gate) -> bool {
        let h = self.hash.hash(g);
        self.set.insert(h, g, |x| gate_equal_to(x, g)).1
    }
    /// `erase (it)`.
    pub fn erase(&mut self, it: usize) -> GatesIterator {
        self.set.erase(it)
    }
    /// `*it`.
    pub fn get(&self, it: usize) -> *mut Gate {
        self.set.get(it)
    }
    /// `clear ()`.
    pub fn clear(&mut self) {
        self.set.clear()
    }
    /// The gates in iteration order.
    pub fn gates(&self) -> Vec<*mut Gate> {
        self.set.elements()
    }
}

/// The congruence closure state.
pub struct Closure {
    pub dummy_search_gate: *mut Gate,
    pub internal: *mut Internal,
    pub extra_clauses: Vec<CRef>,
    pub binaries: Vec<CompactBinary>,
    pub offsetsize: Vec<(usize, usize)>,
    pub full_watching: bool,
    pub nonces: [u64; 16],
    pub scheduled: Vec<bool>,
    pub marks: Vec<i8>,
    /// Remember the ids and the literal.  2 and 4 are only used for lrat
    /// proofs, but we need 1 to promote binary clauses to irredundant.
    pub mu1_ids: Vec<LitClausePair>,
    pub mu2_ids: Vec<LitClausePair>,
    pub mu4_ids: Vec<LitClausePair>,
    /// Result of definitions.
    pub lits: Vec<i32>,
    /// Stack for storing RHS.
    pub rhs: Vec<i32>,
    /// Stack for storing unsimplified version (XOR, ITEs) for DRAT proof.
    pub unsimplified: Vec<i32>,
    /// Store clauses to be able to delete them properly.
    pub chain: Vec<i32>,
    /// Storing partial clauses.
    pub clause: Vec<i32>,
    /// Count for large clauses to complement internal->noccs.
    pub glargecounts: Vec<u64>,
    /// Count for large clauses to complement internal->noccs.
    pub gnew_largecounts: Vec<u64>,
    pub table: GatesTable,
    pub condbin: [lit_implications; 2],
    pub condeq: [lit_equivalences; 2],
    pub new_unwatched_binary_clauses: Vec<CRef>,
    // LRAT proofs
    pub resolvent_analyzed: Vec<i32>,
    /// Storing LRAT chain (`mutable` in C++).
    pub lrat_chain: Vec<LRAT_ID>,
    #[cfg(feature = "logging")]
    pub fresh_id: u64,
    /// Union-find.
    pub representant: Vec<i32>,
    /// Union-find.
    pub eager_representant: Vec<i32>,
    /// LRAT version of union-find.
    pub representant_id: Vec<LRAT_ID>,
    /// LRAT version of union-find.
    pub eager_representant_id: Vec<LRAT_ID>,
    pub lazy_propagated_idx: Vec<i8>,
    // proof production
    pub lrat_chain_and_gate: Vec<LitClausePair>,
    // occs
    pub gtab: Vec<GOccs>,
    pub garbage: Vec<*mut Gate>,
    /// Next trail position to propagate.
    pub units: usize,
    // schedule
    pub schedule: VecDeque<i32>,
}

impl Drop for Closure {
    /// `~Closure () { delete dummy_search_gate; }`
    fn drop(&mut self) {
        if !self.dummy_search_gate.is_null() {
            // SAFETY: allocated with 'Box::into_raw' in 'Closure::new'.
            unsafe { drop(Box::from_raw(self.dummy_search_gate)) };
            self.dummy_search_gate = std::ptr::null_mut();
        }
    }
}

/*------------------------------------------------------------------------*/
// Port of 'congruence.cpp'.

#[allow(unused_imports)]
use crate::prelude::*;
use crate::radix::{msort, rsort};

/// Access a gate through its raw pointer (gates are heap allocated and
/// shared between the table, the occurrence lists and the garbage stack as
/// in C++).  Never keep the returned reference across a call that might
/// access the same gate.
#[inline(always)]
#[allow(clippy::mut_from_ref)]
fn gt<'a>(g: *mut Gate) -> &'a mut Gate {
    debug_assert!(!g.is_null());
    // SAFETY: gate pointers handled by the closure point to live gates.
    unsafe { &mut *g }
}

#[inline(always)]
fn new_gate() -> *mut Gate {
    Box::into_raw(Box::new(Gate::default()))
}

#[inline(always)]
fn delete_gate(g: *mut Gate) {
    // SAFETY: gates are allocated with 'new_gate' and deleted only once.
    unsafe { drop(Box::from_raw(g)) }
}

/// `std::find (begin (*c), end (*c), lit) != end (*c)`.
#[inline]
fn clause_contains(c: CRef, lit: i32) -> bool {
    c.lits().contains(&lit)
}

fn update_ite_flags(g: *mut Gate) {
    let g = gt(g);
    let mut f = g.degenerated_gate;
    let lhs = g.lhs;
    let cond = g.rhs[0];
    let then_lit = g.rhs[1];
    let else_lit = g.rhs[2];

    if lhs == cond {
        f |= Special_Gate::NO_NEG_THEN;
        f |= Special_Gate::NO_PLUS_ELSE;
    }
    if lhs == -cond {
        f |= Special_Gate::NO_PLUS_THEN;
        f |= Special_Gate::NO_NEG_ELSE;
    }
    if lhs == then_lit {
        f |= Special_Gate::NO_PLUS_THEN;
        f |= Special_Gate::NO_NEG_THEN;
    }
    if lhs == else_lit {
        f |= Special_Gate::NO_PLUS_ELSE;
        f |= Special_Gate::NO_NEG_ELSE;
    }
    g.degenerated_gate = f;
    debug_assert!(lhs != -then_lit);
    debug_assert!(lhs != -else_lit);
    debug_assert!(cond != then_lit);
    debug_assert!(cond != else_lit);
    debug_assert!(cond != -then_lit);
    debug_assert!(cond != -else_lit);
}

fn check_correct_ite_flags(g: *const Gate) {
    #[cfg(debug_assertions)]
    {
        // SAFETY: live gate.
        let g = unsafe { &*g };
        let f = g.degenerated_gate;
        let lhs = g.lhs;
        let cond = g.rhs[0];
        let then_lit = g.rhs[1];
        let else_lit = g.rhs[2];
        debug_assert!(g.pos_lhs_ids.len() == 4);
        if g.pos_lhs_ids[0].clause.is_null() {
            debug_assert!((f & Special_Gate::NO_PLUS_THEN) != 0);
        }
        if g.pos_lhs_ids[1].clause.is_null() {
            debug_assert!((f & Special_Gate::NO_NEG_THEN) != 0);
        }
        if g.pos_lhs_ids[2].clause.is_null() {
            debug_assert!((f & Special_Gate::NO_PLUS_ELSE) != 0);
        }
        if g.pos_lhs_ids[3].clause.is_null() {
            debug_assert!((f & Special_Gate::NO_NEG_ELSE) != 0);
        }
        if lhs == cond {
            debug_assert!((f & Special_Gate::NO_NEG_THEN) != 0);
            debug_assert!((f & Special_Gate::NO_PLUS_ELSE) != 0);
        }
        if lhs == -cond {
            debug_assert!((f & Special_Gate::NO_PLUS_THEN) != 0);
            debug_assert!((f & Special_Gate::NO_NEG_ELSE) != 0);
        }
        if lhs == then_lit {
            debug_assert!((f & Special_Gate::NO_PLUS_THEN) != 0);
            debug_assert!((f & Special_Gate::NO_NEG_THEN) != 0);
        }
        if lhs == else_lit {
            debug_assert!((f & Special_Gate::NO_PLUS_ELSE) != 0);
            debug_assert!((f & Special_Gate::NO_NEG_ELSE) != 0);
        }
        debug_assert!(lhs != -then_lit);
        debug_assert!(lhs != -else_lit);
        debug_assert!(cond != then_lit);
        debug_assert!(cond != else_lit);
        debug_assert!(cond != -then_lit);
        debug_assert!(cond != -else_lit);
    }
    #[cfg(not(debug_assertions))]
    let _ = g;
}

/*------------------------------------------------------------------------*/

#[inline]
fn hash_lits(nonces: &[u64; 16], lits: &[i32], tag: Gate_Type) -> usize {
    let tag = tag as i8 as u64;
    let mut hash: u64 = (tag << 4) | (tag >> 50);
    let mut n = tag as usize;
    debug_assert!(n < 16);
    for &lit in lits {
        hash = hash.wrapping_add(lit as i64 as u64);
        hash = hash.wrapping_mul(nonces[n]);
        n += 1;
        hash = (hash << 4) | (hash >> 60);
        if n == 16 {
            n = 0;
        }
    }
    hash ^= hash >> 32;
    hash as usize
}

impl Hash {
    /// `size_t Hash::operator() (const Gate *const g) const`.
    pub fn hash(&self, g: *const Gate) -> usize {
        // SAFETY: live gate.
        let g = unsafe { &*g };
        hash_lits(&self.nonces, &g.rhs, g.tag)
    }
}

impl GatesTable {
    /// `GatesTable (128, Hash (nonces))`.
    pub fn new(bucket_count: usize, hash: Hash) -> GatesTable {
        GatesTable { hash, set: LibcxxHashSet::new(bucket_count, std::ptr::null_mut()) }
    }
}

fn gate_contains(g: *mut Gate, lit: i32) -> bool {
    gt(g).rhs.contains(&lit)
}

/// `std::is_sorted (begin, end, less)`.
fn is_sorted_by<T, F: FnMut(&T, &T) -> bool>(v: &[T], mut less: F) -> bool {
    for i in 1..v.len() {
        if less(&v[i], &v[i - 1]) {
            return false;
        }
    }
    true
}

/*------------------------------------------------------------------------*/

#[inline]
fn compact_binary_rank(internal: &Internal, a: &CompactBinary) -> u64 {
    ((internal.vlit(a.lit1) as u64) << 32).wrapping_add(internal.vlit(a.lit2) as u64)
}

#[inline]
fn sort_literals_by_var_rank(internal: &Internal, a: i32) -> u64 {
    internal.vlit(a) as u64
}

#[inline]
fn sort_literals_by_var_rank_except(internal: &Internal, lhs: i32, except: i32, a: i32) -> u64 {
    let res: u64;
    if a.abs() == except.abs() {
        res = 1 - (a > 0) as u64;
    } else if a.abs() == lhs.abs() {
        res = 3 - (a > 0) as u64;
    } else {
        res = internal.vlit(a).wrapping_add(2) as u64; // probably +2 enough
    }
    !res
}

#[inline]
fn sort_literals_by_var_smaller_except(internal: &Internal, lhs: i32, except: i32, a: i32, b: i32) -> bool {
    sort_literals_by_var_rank_except(internal, lhs, except, a)
        < sort_literals_by_var_rank_except(internal, lhs, except, b)
}

#[inline]
fn sort_literals_by_var_smaller(internal: &Internal, a: i32, b: i32) -> bool {
    sort_literals_by_var_rank(internal, a) < sort_literals_by_var_rank(internal, b)
}

#[inline]
fn congruence_occurrences_rank(internal: &Internal, a: i32) -> u64 {
    let mut res: u64 = internal.noccs(-a) as u64;
    res <<= 32;
    res |= a as i64 as u64;
    res
}

#[inline]
fn litpair_rank(internal: &Internal, a: &lit_implication) -> u64 {
    let lita = internal.vlit(a.first) as u64;
    let litb = internal.vlit(a.second) as u64;
    (lita << 32).wrapping_add(litb)
}

#[inline]
fn litequivalence_rank(internal: &Internal, a: &lit_equivalence) -> u64 {
    let lita = internal.vlit(a.first) as u64;
    let litb = internal.vlit(a.second) as u64;
    (lita << 32).wrapping_add(litb)
}

fn parity_lits(lits: &[i32]) -> bool {
    let mut res: u32 = 0;
    for &lit in lits {
        res ^= (lit < 0) as u32;
    }
    res != 0
}

fn inc_lits(lits: &mut [i32]) {
    let mut carry = true;
    let mut i = 0;
    while i < lits.len() && carry {
        let lit = lits[i];
        carry = lit < 0;
        lits[i] = -lit;
        i += 1;
    }
}

#[cfg(debug_assertions)]
fn is_tautological_ite_gate(g: *mut Gate) -> bool {
    let g = gt(g);
    debug_assert!(g.tag == Gate_Type::ITE_Gate);
    debug_assert!(g.arity() == 3);
    let cond_lit = g.rhs[0];
    let then_lit = g.rhs[1];
    let else_lit = g.rhs[2];
    cond_lit == then_lit || cond_lit == else_lit
}

fn skip_ite_gate(g: *mut Gate) -> bool {
    debug_assert!(gt(g).tag == Gate_Type::ITE_Gate);
    gt(g).garbage
}

fn check_ite_lits_normalized(lits: &[i32]) {
    debug_assert!(lits[0] > 0);
    debug_assert!(lits[1] > 0);
    debug_assert!(lits[0] != lits[1]);
    debug_assert!(lits[0] != lits[2]);
    debug_assert!(lits[1] != lits[2]);
    debug_assert!(lits[0] != -lits[1]);
    debug_assert!(lits[0] != -lits[2]);
    debug_assert!(lits[1] != -lits[2]);
    let _ = lits;
}

/*------------------------------------------------------------------------*/

impl Closure {
    /// `Closure (Internal *)`.
    pub fn new(internal: *mut Internal) -> Closure {
        #[cfg(feature = "logging")]
        // SAFETY: 'internal' is the live owner of this closure.
        let fresh_id = unsafe { (*internal).clause_id } as u64;
        let dummy = new_gate();
        gt(dummy).lhs = 0;
        gt(dummy).garbage = false;
        Closure {
            dummy_search_gate: dummy,
            internal,
            extra_clauses: Vec::new(),
            binaries: Vec::new(),
            offsetsize: Vec::new(),
            full_watching: false,
            nonces: [0; 16],
            scheduled: Vec::new(),
            marks: Vec::new(),
            mu1_ids: Vec::new(),
            mu2_ids: Vec::new(),
            mu4_ids: Vec::new(),
            lits: Vec::new(),
            rhs: Vec::new(),
            unsimplified: Vec::new(),
            chain: Vec::new(),
            clause: Vec::new(),
            glargecounts: Vec::new(),
            gnew_largecounts: Vec::new(),
            table: GatesTable::new(128, Hash { nonces: [0; 16] }),
            condbin: [Vec::new(), Vec::new()],
            condeq: [Vec::new(), Vec::new()],
            new_unwatched_binary_clauses: Vec::new(),
            resolvent_analyzed: Vec::new(),
            lrat_chain: Vec::new(),
            #[cfg(feature = "logging")]
            fresh_id,
            representant: Vec::new(),
            eager_representant: Vec::new(),
            representant_id: Vec::new(),
            eager_representant_id: Vec::new(),
            lazy_propagated_idx: Vec::new(),
            lrat_chain_and_gate: Vec::new(),
            gtab: Vec::new(),
            garbage: Vec::new(),
            units: 0,
            schedule: VecDeque::new(),
        }
    }

    /// The owning 'Internal' (C++ 'Internal *const internal').
    #[inline(always)]
    #[allow(clippy::mut_from_ref)]
    fn int<'a>(&self) -> &'a mut Internal {
        // SAFETY: the closure lives inside 'Internal::extract_gates' and
        // its internal pointer is valid for its whole life time.
        unsafe { &mut *self.internal }
    }

    #[inline(always)]
    fn lrat(&self) -> bool {
        self.int().lrat
    }

    #[inline(always)]
    fn vlit(&self, lit: i32) -> usize {
        self.int().vlit(lit) as usize
    }

    #[inline(always)]
    fn val(&self, lit: i32) -> i8 {
        self.int().val(lit)
    }

    /// Value of 'marked (lit)'.
    #[inline(always)]
    fn mk(&self, lit: i32) -> i8 {
        debug_assert!(self.vlit(lit) < self.marks.len());
        self.marks[self.vlit(lit)]
    }

    /// 'marked (lit) = v'.
    #[inline(always)]
    fn set_mk(&mut self, lit: i32, v: i8) {
        debug_assert!(self.vlit(lit) < self.marks.len());
        let i = self.vlit(lit);
        self.marks[i] = v;
    }

    /// 'simplify_and_add_to_proof_chain (unsimplified)' on the member
    /// 'unsimplified' (which the callee does not modify).
    fn simplify_and_add_unsimplified_to_proof_chain(&mut self, delete_id: LRAT_ID) -> LRAT_ID {
        let mut u = self.unsimplified.clone();
        self.simplify_and_add_to_proof_chain(&mut u, delete_id)
    }

    /// 'push_id_and_rewriting_lrat_unit (c, rewrite1, lrat_chain, ...)'
    /// with the member 'lrat_chain' as target (the callee only restores
    /// its temporary modifications of 'lrat_chain').
    fn push_id_and_rewriting_lrat_unit_self(
        &mut self,
        c: CRef,
        rewrite1: Rewrite,
        insert_id_after: bool,
        rewrite2: Rewrite,
        except_lhs: i32,
        except_lhs2: i32,
    ) {
        let mut chain = std::mem::take(&mut self.lrat_chain);
        self.push_id_and_rewriting_lrat_unit(c, rewrite1, &mut chain, insert_id_after, rewrite2, except_lhs, except_lhs2);
        debug_assert!(self.lrat_chain.is_empty());
        self.lrat_chain = chain;
    }

    /// Same for 'push_id_and_rewriting_lrat_full'.
    fn push_id_and_rewriting_lrat_full_self(
        &mut self,
        c: CRef,
        rewrite1: Rewrite,
        insert_id_after: bool,
        rewrite2: Rewrite,
        except_lhs: i32,
        except_lhs2: i32,
    ) {
        let mut chain = std::mem::take(&mut self.lrat_chain);
        self.push_id_and_rewriting_lrat_full(c, rewrite1, &mut chain, insert_id_after, rewrite2, except_lhs, except_lhs2);
        debug_assert!(self.lrat_chain.is_empty());
        self.lrat_chain = chain;
    }

    pub fn lazy_propagated(&mut self, lit: i32) -> &mut i8 {
        let i = self.int().vidx(lit) as usize;
        &mut self.lazy_propagated_idx[i]
    }

    /*----------------------------------------------------------------------*/

    pub fn find_binary(&mut self, lit: i32, other: i32) -> bool {
        let internal: &Internal = self.int();
        let (mut lit, mut other) = (lit, other);
        if internal.vlit(lit) > internal.vlit(other) {
            std::mem::swap(&mut lit, &mut other);
        }
        let offsize = self.offsetsize[internal.vlit(lit) as usize];
        let offset = offsize.0;
        let size = offsize.1;
        debug_assert!(size <= self.binaries.len());
        let target = CompactBinary::new(CRef::NULL, 0, lit, other);
        let target_rank = compact_binary_rank(internal, &target);
        let range = &self.binaries[offset..size];
        let pos = offset + range.partition_point(|x| compact_binary_rank(internal, x) < target_rank);
        // search_binary only returns a bool
        let found = pos != size && self.binaries[pos].lit1 == lit && self.binaries[pos].lit2 == other;
        if found {
            log!(self.internal, "found binary [{}] {} {}", self.binaries[pos].id, lit, other);
            if internal.lrat {
                let id = self.binaries[pos].id;
                self.lrat_chain.push(id);
            }
        }
        found
    }

    pub fn extract_binaries(&mut self) {
        if self.int().opts.congruencebinaries == 0 {
            return;
        }
        if self.int().terminated_asynchronously(1) {
            return;
        }
        start!(self.int(), extractbinaries);
        let max_var = self.int().max_var as usize;
        self.offsetsize.resize(max_var * 2 + 3, (0, 0));

        // in kissat this is done during watch clearing. TODO: consider doing
        // this too.
        let n = self.int().clauses.len();
        for i in 0..n {
            let c = self.int().clauses[i];
            if c.garbage() {
                continue;
            }
            if c.redundant() && c.size() != 2 {
                continue;
            }
            if c.size() > 2 {
                continue;
            }
            if self.int().terminated_asynchronously(1) {
                stop!(self.int(), extractbinaries);
                return;
            }
            debug_assert!(c.size() == 2);
            let lit = c.lit(0);
            let other = c.lit(1);
            let already_sorted = self.int().vlit(lit) < self.int().vlit(other);
            self.binaries.push(CompactBinary::new(
                c,
                c.id(),
                if already_sorted { lit } else { other },
                if already_sorted { other } else { lit },
            ));
        }
        if self.int().terminated_asynchronously(1) {
            stop!(self.int(), extractbinaries);
            return;
        }
        {
            let internal: &Internal = self.int();
            msort(
                internal.opts.radixsortlim as usize,
                &mut self.binaries,
                |a| compact_binary_rank(internal, a),
                |a, b| compact_binary_rank(internal, a) < compact_binary_rank(internal, b),
            );
        }

        {
            let size = self.binaries.len();
            let mut i = 0;
            while i < size {
                let bin = self.binaries[i];
                let lit = bin.lit1;
                let mut j = i;
                while j < size && self.binaries[j].lit1 == lit {
                    j += 1;
                }
                debug_assert!(j >= i);
                debug_assert!(j <= size);
                let v = self.vlit(lit);
                self.offsetsize[v] = (i, j);
                i = j;
            }
        }

        let mut extracted: usize = 0;
        let mut already_present: usize = 0;
        let mut duplicated: usize = 0;

        let size = self.int().clauses.len();
        for i in 0..size {
            if self.int().terminated_asynchronously(1) {
                stop!(self.int(), extractbinaries);
                return;
            }
            // binary clauses are appended, so reallocation possible
            let d = self.int().clauses[i];
            if d.garbage() {
                continue;
            }
            if d.redundant() {
                continue;
            }
            if d.size() != 3 {
                continue;
            }
            let a = d.lit(0);
            let b = d.lit(1);
            let c = d.lit(2);
            if self.val(a) != 0 {
                continue;
            }
            if self.val(b) != 0 {
                continue;
            }
            if self.val(c) != 0 {
                continue;
            }
            let l;
            let k;
            if self.find_binary(-a, b) || self.find_binary(-a, c) {
                l = b;
                k = c;
            } else if self.find_binary(-b, a) || self.find_binary(-b, c) {
                l = a;
                k = c;
            } else if self.find_binary(-c, a) || self.find_binary(-c, b) {
                l = a;
                k = b;
            } else {
                continue;
            }
            log!(self.internal, d, "strengthening");
            if !self.find_binary(l, k) {
                if self.lrat() {
                    self.lrat_chain.push(d.id());
                }
                self.add_binary_clause(l, k);
                extracted += 1;
            } else {
                already_present += 1;
                if self.lrat() {
                    self.lrat_chain.clear();
                }
            }
        }
        self.lrat_chain.clear();

        self.offsetsize.clear();

        // kissat has code to remove duplicates, which we have already removed
        // before starting congruence
        if self.int().terminated_asynchronously(1) {
            stop!(self.int(), extractbinaries);
            return;
        }
        {
            let internal: &Internal = self.int();
            msort(
                internal.opts.radixsortlim as usize,
                &mut self.binaries,
                |a| compact_binary_rank(internal, a),
                |a, b| compact_binary_rank(internal, a) < compact_binary_rank(internal, b),
            );
        }
        let new_size = self.binaries.len();
        {
            let mut i = 0usize;
            for j in 1..new_size {
                debug_assert!(i < j);
                if self.binaries[i].lit1 == self.binaries[j].lit1 && self.binaries[i].lit2 == self.binaries[j].lit2 {
                    // subsuming later clause
                    let (ci, cj) = (self.binaries[i].clause, self.binaries[j].clause);
                    self.subsume_clause(ci, cj); // the local one is specialized
                    duplicated += 1;
                } else {
                    i += 1;
                    self.binaries[i] = self.binaries[j];
                }
            }
            debug_assert!(i <= new_size);
            self.binaries.truncate(i);
        }
        self.binaries.clear();
        stop!(self.int(), extractbinaries);
        verbose!(
            self.internal,
            2,
            "[congruence-{}] extracted {} binaries (plus {} already present and {} duplicates)",
            self.int().stats.congruence.rounds,
            extracted,
            already_present,
            duplicated
        );
    }

    /*----------------------------------------------------------------------*/
    // marking structure for congruence closure, by reference

    pub fn marked(&mut self, lit: i32) -> &mut i8 {
        debug_assert!(self.vlit(lit) < self.marks.len());
        let i = self.vlit(lit);
        &mut self.marks[i]
    }

    pub fn unmark_all(&mut self) {
        let n = self.int().analyzed.len();
        for i in 0..n {
            let lit = self.int().analyzed[i];
            debug_assert!(self.mk(lit) != 0);
            self.set_mk(lit, 0);
        }
        self.int().analyzed.clear();
    }

    pub fn set_mu1_reason(&mut self, lit: i32, c: CRef) {
        debug_assert!((self.mk(lit) & 1) != 0);
        log!(self.internal, c, "mu1 {} -> {}", lit, c.id());
        let i = self.vlit(lit);
        self.mu1_ids[i] = LitClausePair::new(lit, c);
    }

    pub fn set_mu2_reason(&mut self, lit: i32, c: CRef) {
        debug_assert!((self.mk(lit) & 2) != 0);
        if !self.lrat() {
            return;
        }
        log!(self.internal, c, "mu2 {} -> {}", lit, c.id());
        let i = self.vlit(lit);
        self.mu2_ids[i] = LitClausePair::new(lit, c);
    }

    pub fn set_mu4_reason(&mut self, lit: i32, c: CRef) {
        debug_assert!((self.mk(lit) & 4) != 0);
        if !self.lrat() {
            return;
        }
        log!(self.internal, c, "mu4 {} -> {}", lit, c.id());
        let i = self.vlit(lit);
        self.mu4_ids[i] = LitClausePair::new(lit, c);
    }

    pub fn marked_mu1(&self, lit: i32) -> LitClausePair {
        self.mu1_ids[self.vlit(lit)]
    }

    pub fn marked_mu2(&mut self, lit: i32) -> LitClausePair {
        self.mu2_ids[self.vlit(lit)]
    }

    pub fn marked_mu4(&mut self, lit: i32) -> LitClausePair {
        self.mu4_ids[self.vlit(lit)]
    }

    /// `except2` defaults to `0` in C++
    pub fn sort_literals_by_var_except(&mut self, rhs: &mut Vec<i32>, lhs: i32, except2: i32) {
        let internal: &Internal = self.int();
        msort(
            internal.opts.radixsortlim as usize,
            rhs,
            |&a| sort_literals_by_var_rank_except(internal, lhs, except2, a),
            |&a, &b| sort_literals_by_var_smaller_except(internal, lhs, except2, a, b),
        );
    }

    pub fn sort_literals_by_var(&mut self, rhs: &mut Vec<i32>) {
        let internal: &Internal = self.int();
        msort(
            internal.opts.radixsortlim as usize,
            rhs,
            |&a| sort_literals_by_var_rank(internal, a),
            |&a, &b| sort_literals_by_var_smaller(internal, a, b),
        );
    }

    /*----------------------------------------------------------------------*/

    /// C++ overload `Closure::representative` (renamed).
    pub fn representative_mut(&mut self, lit: i32) -> &mut i32 {
        debug_assert!(self.vlit(lit) < self.representant.len());
        let i = self.vlit(lit);
        &mut self.representant[i]
    }

    pub fn representative(&self, lit: i32) -> i32 {
        debug_assert!(self.vlit(lit) < self.representant.len());
        self.representant[self.vlit(lit)]
    }

    /// C++ overload `Closure::eager_representative` (renamed).
    pub fn eager_representative_mut(&mut self, lit: i32) -> &mut i32 {
        debug_assert!(self.vlit(lit) < self.eager_representant.len());
        let i = self.vlit(lit);
        &mut self.eager_representant[i]
    }

    pub fn eager_representative(&self, lit: i32) -> i32 {
        debug_assert!(self.vlit(lit) < self.eager_representant.len());
        self.eager_representant[self.vlit(lit)]
    }

    pub fn find_lrat_representative_with_marks(&mut self, lit: i32) -> i32 {
        let mut res;
        let mut nxt = lit;
        loop {
            res = nxt;
            nxt = self.representative(nxt);
            if nxt != res {
                log!(self.internal, "{} has reason {}", res, self.representative_id(res) as u64);
                let id = self.representative_id(res);
                self.lrat_chain.push(id);
            }
            if !(nxt != res || self.mk(nxt) != 0 || self.mk(-nxt) != 0) {
                break;
            }
        }
        nxt
    }

    pub fn find_representative(&mut self, lit: i32) -> i32 {
        let mut res;
        let mut nxt = lit;
        loop {
            res = nxt;
            nxt = self.representative(nxt);
            if nxt == res {
                break;
            }
        }
        res
    }

    pub fn find_representative_and_compress_no_proofs(&mut self, lit: i32) -> i32 {
        let mut res;
        let mut nxt = lit;
        loop {
            res = nxt;
            nxt = self.representative(nxt);
            if nxt == res {
                break;
            }
        }
        *self.representative_mut(lit) = res;
        *self.representative_mut(-lit) = -res;
        res
    }

    pub fn find_representative_already_compressed(&mut self, lit: i32) -> i32 {
        let res = self.representative(lit);
        debug_assert!(self.representative(res) == res);
        res
    }

    /// `update_eager` defaults to `true` in C++
    pub fn find_representative_and_compress(&mut self, lit: i32, update_eager: bool) -> i32 {
        log!(self.internal, "finding representative of {}", lit);
        let mut res;
        let mut nxt = lit;
        let mut path_length = 0;
        loop {
            res = nxt;
            nxt = self.representative(nxt);
            path_length += 1;
            log!(self.internal, "updating {} -> {}", res, nxt);
            if nxt == res {
                break;
            }
        }

        if path_length > 2 {
            log!(
                self.internal,
                "learning new rewriting from {} to {} (current path length: {})",
                lit,
                res,
                path_length
            );
            if update_eager {
                *self.eager_representative_mut(lit) = res;
            }
            if self.lrat() {
                self.produce_representative_lrat(lit);
                let equiv = self.add_tmp_binary_clause(-lit, res);

                if !equiv.is_null() {
                    *self.representative_id_mut(lit) = equiv.id();
                    if update_eager {
                        *self.eager_representative_id_mut(lit) = equiv.id();
                    }
                }
            }
            if self.lrat() {
                self.lrat_chain.clear();
            }
        } else if path_length == 2 {
            if update_eager {
                log!(self.internal, "updating information {} -> {} in eager", lit, res);
                *self.eager_representative_mut(lit) = res;
                if self.lrat() {
                    let id = self.representative_id(lit);
                    *self.eager_representative_id_mut(lit) = id;
                }
                debug_assert!(!self.lrat() || self.eager_representative_id(lit) != 0);
            }
        }

        if lit != res {
            *self.representative_mut(lit) = res;
        }
        log!(self.internal, "representative of {} is {}", lit, res);
        res
    }

    pub fn push_lrat_unit(&mut self, lit: i32) {
        if !self.lrat() {
            return;
        }
        debug_assert!(self.val(lit) > 0);
        let id = self.int().unit_id(lit);
        self.lrat_chain.push(id);
    }

    pub fn find_eager_representative(&self, lit: i32) -> i32 {
        let mut res;
        let mut nxt = lit;
        loop {
            res = nxt;
            nxt = self.eager_representative(nxt);
            if nxt == res {
                break;
            }
        }
        res
    }

    pub fn find_eager_representative_and_compress(&mut self, lit: i32) -> i32 {
        if !self.lrat() {
            return self.find_representative(lit);
        }
        let mut res;
        let mut nxt = lit;
        let mut path_length = 0;
        loop {
            res = nxt;
            nxt = self.eager_representative(nxt);
            path_length += 1;
            if nxt == res {
                break;
            }
        }

        //  assert (res == find_representative (lit));
        // we have to do path compression to support LRAT proofs
        if path_length > 2 {
            log!(
                self.internal,
                "learning new rewriting from {} to {} (current path length: {})",
                lit,
                res,
                path_length
            );
            let mut tmp_lrat_chain: Vec<LRAT_ID> = Vec::new();
            if self.lrat() {
                tmp_lrat_chain = std::mem::take(&mut self.lrat_chain);
                self.lrat_chain.clear();
                self.produce_eager_representative_lrat(lit);
            }
            *self.eager_representative_mut(lit) = res;
            let equiv = self.add_tmp_binary_clause(-lit, res);
            equiv.set_hyper(true);

            if self.lrat() && !equiv.is_null() {
                *self.eager_representative_id_mut(lit) = equiv.id();
            }
            if self.lrat() {
                self.lrat_chain = tmp_lrat_chain;
            }
        } else if path_length == 2 {
            log!(
                self.internal,
                "duplicated information {} -> {} to eager with clause {}",
                lit,
                res,
                self.eager_representative_id(lit) as u64
            );
            debug_assert!(self.eager_representative(lit) == res);
            debug_assert!(!self.lrat() || self.eager_representative_id(lit) != 0);
        }
        debug_assert!(self.int().clause.is_empty());
        res
    }

    pub fn find_representative_and_compress_both(&mut self, lit: i32) {
        self.find_representative_and_compress(lit, false);
        self.find_representative_and_compress(-lit, false);
    }

    pub fn import_lazy_and_find_eager_representative_and_compress_both(&mut self, lit: i32) {
        self.find_representative_and_compress(lit, true);
        self.find_eager_representative_and_compress(lit);
        self.find_representative_and_compress(-lit, true);
        self.find_eager_representative_and_compress(-lit);
    }

    pub fn produce_representative_lrat(&mut self, lit: i32) {
        debug_assert!(self.lrat());
        log!(
            self.internal,
            "production of LRAT chain for {} with representative {}",
            lit,
            self.representative_id(lit) as u64
        );
        debug_assert!(self.lrat());
        debug_assert!(self.lrat_chain.is_empty());
        let mut res;
        let mut nxt = lit;
        debug_assert!(nxt != self.representative(nxt));
        loop {
            res = nxt;
            nxt = self.representative(nxt);
            if nxt != res {
                log!(self.internal, "{} has reason {}", res, self.representative_id(res) as u64);
                let id = self.representative_id(res);
                self.lrat_chain.push(id);
            }
            if nxt == res {
                break;
            }
        }
    }

    pub fn produce_eager_representative_lrat(&mut self, lit: i32) {
        debug_assert!(self.lrat());
        log!(
            self.internal,
            "production of LRAT chain for {} with representative {}",
            lit,
            self.eager_representative_id(lit) as u64
        );
        debug_assert!(self.lrat());
        debug_assert!(self.lrat_chain.is_empty());
        let mut res;
        let mut nxt = lit;
        debug_assert!(nxt != self.eager_representative(nxt));
        loop {
            res = nxt;
            nxt = self.eager_representative(nxt);
            if nxt != res {
                log!(self.internal, "{} has reason {}", res, self.eager_representative_id(res) as u64);
                let id = self.eager_representative_id(res);
                self.lrat_chain.push(id);
            }
            if nxt == res {
                break;
            }
        }
    }

    pub fn find_representative_lrat(&mut self, lit: i32) -> i64 {
        if !self.lrat() {
            return 0;
        }
        let res = lit;
        #[cfg(debug_assertions)]
        {
            let nxt = self.representative(res);
            debug_assert!(nxt == self.representative(res));
        }
        log!(
            self.internal,
            "checking for existing LRAT chain for {} with clause {}",
            lit,
            self.eager_representative_id(res) as u64
        );
        debug_assert!(self.representative_id(res) != 0);
        self.representative_id(res)
    }

    pub fn find_eager_representative_lrat(&self, lit: i32) -> i64 {
        if !self.lrat() {
            return 0;
        }
        let res = lit;
        #[cfg(debug_assertions)]
        {
            let nxt = self.eager_representative(res);
            debug_assert!(nxt == self.eager_representative(res));
        }
        log!(
            self.internal,
            "checking for existing LRAT chain for {} with clause {}",
            lit,
            self.eager_representative_id(res) as u64
        );
        debug_assert!(self.eager_representative_id(res) != 0);
        self.eager_representative_id(res)
    }

    /// C++ overload `Closure::eager_representative_id` (renamed).
    pub fn eager_representative_id_mut(&mut self, lit: i32) -> &mut i64 {
        debug_assert!(self.vlit(lit) < self.eager_representant_id.len());
        let i = self.vlit(lit);
        &mut self.eager_representant_id[i]
    }

    pub fn eager_representative_id(&self, lit: i32) -> i64 {
        debug_assert!(self.vlit(lit) < self.eager_representant_id.len());
        self.eager_representant_id[self.vlit(lit)]
    }

    /// C++ overload `Closure::representative_id` (renamed).
    pub fn representative_id_mut(&mut self, lit: i32) -> &mut i64 {
        debug_assert!(self.vlit(lit) < self.representant_id.len());
        let i = self.vlit(lit);
        &mut self.representant_id[i]
    }

    pub fn representative_id(&self, lit: i32) -> i64 {
        debug_assert!(self.vlit(lit) < self.representant_id.len());
        self.representant_id[self.vlit(lit)]
    }

    pub fn mark_garbage(&mut self, g: *mut Gate) {
        log!(self.internal, g, "marking as garbage");
        debug_assert!(!gt(g).garbage);
        gt(g).garbage = true;
        self.garbage.push(g);
    }

    /// C++ overload `Closure::remove_gate (GatesTable::iterator)` (renamed).
    pub fn remove_gate_at(&mut self, git: GatesIterator) -> bool {
        debug_assert!(git.is_some());
        debug_assert!(!self.int().unsat);
        let it = git.expect("remove_gate called with end () iterator");
        let g = self.table.get(it);
        gt(g).indexed = false;
        log!(self.internal, g, "removing from hash table");
        self.table.erase(it);
        true
    }

    pub fn remove_gate(&mut self, g: *mut Gate) -> bool {
        if !gt(g).indexed {
            return false;
        }
        debug_assert!(!self.int().unsat);
        debug_assert!(self.table.find(g).is_some());
        let it = self.table.find(g).expect("gate not found in table");
        self.table.erase(it);
        gt(g).indexed = false;
        log!(self.internal, g, "removing from hash table");
        true
    }

    pub fn index_gate(&mut self, g: *mut Gate) {
        debug_assert!(!gt(g).indexed);
        debug_assert!(!self.int().unsat);
        debug_assert!(gt(g).arity() > 1);
        log!(self.internal, g, "adding to hash table");
        self.table.insert(g);
        gt(g).indexed = true;
        debug_assert!(self.table.find(g).is_some());
    }

    /// `except_lhs` defaults to `0` in C++
    /// `remove_units` defaults to `true` in C++
    /// `allow_tautology_in_input` defaults to `false` in C++
    pub fn produce_rewritten_clause_lrat_and_clean(
        &mut self,
        litIds: &mut Vec<LitClausePair>,
        except_lhs: i32,
        remove_units: bool,
        allow_tautology_in_input: bool,
    ) {
        debug_assert!(self.int().lrat_chain.is_empty());
        for i in 0..litIds.len() {
            debug_assert!(!litIds[i].clause.is_null() || allow_tautology_in_input);
            let _ = allow_tautology_in_input;
            if litIds[i].clause.is_null() {
                continue;
            }
            let c = litIds[i].clause;
            litIds[i].clause = self.produce_rewritten_clause_lrat(c, except_lhs, remove_units, false);
            let l = litIds[i].current_lit;
            litIds[i].current_lit = self.find_eager_representative(l);
        }
        litIds.retain(|p| !p.clause.is_null());
    }

    /// `except_lhs` defaults to `0` in C++
    /// `remove_units` defaults to `true` in C++
    /// C++ overload `Closure::produce_rewritten_clause_lrat_and_clean` (renamed).
    pub fn produce_rewritten_clause_lrat_and_clean_optional(
        &mut self,
        litIds: &mut my_dummy_optional,
        except_lhs: i32,
        remove_units: bool,
    ) {
        debug_assert!(self.int().lrat_chain.is_empty());
        if litIds.is_set() {
            debug_assert!(!litIds.content.clause.is_null());
            let c = litIds.content.clause;
            litIds.content.clause = self.produce_rewritten_clause_lrat(c, except_lhs, remove_units, false);
            let l = litIds.content.current_lit;
            litIds.content.current_lit = self.find_eager_representative(l);
            if litIds.content.clause.is_null() {
                litIds.reset();
            }
        }
    }

    /// `remove_units` defaults to `true` in C++
    /// C++ overload `Closure::produce_rewritten_clause_lrat_and_clean` (renamed).
    pub fn produce_rewritten_clause_lrat_and_clean_positions(
        &mut self,
        litIds: &mut Vec<LitClausePair>,
        except_lhs: i32,
        old_position1: &mut usize,
        old_position2: &mut usize,
        remove_units: bool,
    ) {
        debug_assert!(self.int().lrat_chain.is_empty());
        debug_assert!(*old_position1 != *old_position2);
        let mut j = 0usize;
        let mut i = 0usize;
        while i < litIds.len() {
            debug_assert!(j <= i);
            if litIds[i].clause.is_null() {
                log!(self.internal, "empty clause {}", i);
                if i == *old_position1 {
                    *old_position1 = usize::MAX;
                }
                if i == *old_position2 {
                    *old_position2 = usize::MAX;
                }
                i += 1;
                continue;
            }
            let c = litIds[i].clause;
            litIds[j].clause = self.produce_rewritten_clause_lrat(c, except_lhs, remove_units, false);
            let l = litIds[i].current_lit;
            litIds[j].current_lit = self.find_eager_representative(l);
            if i == *old_position1 {
                if !litIds[j].clause.is_null() {
                    *old_position1 = j;
                } else {
                    *old_position1 = usize::MAX;
                }
            }
            if i == *old_position2 {
                if !litIds[j].clause.is_null() {
                    *old_position2 = j;
                } else {
                    *old_position2 = usize::MAX;
                }
            }
            if !litIds[j].clause.is_null() {
                j += 1;
            }
            i += 1;
        }
        litIds.resize(j, LitClausePair::default());
    }

    pub fn compute_rewritten_clause_lrat_simple(&mut self, c: CRef, except: i32) {
        debug_assert!(self.int().clause.is_empty());
        debug_assert!(self.int().lrat_chain.is_empty());
        debug_assert!(self.clause.is_empty());
        debug_assert!(self.lrat_chain.is_empty());
        let mut changed = false;
        let mut tautology = false;
        let size = c.size() as usize;
        for i in 0..size {
            let lit = c.lit(i);
            log!(self.internal, "checking if {} is required", lit);
            if self.int().marked2(lit) {
                continue;
            }
            if self.int().marked2(-lit) {
                tautology = true;
                break;
            }
            if lit == except || lit == -except {
                self.int().mark2(lit);
                self.clause.push(lit);
                continue;
            }
            if self.val(lit) < 0 {
                log!(self.internal, "found unit {}, removing it", -lit);
                let id = self.int().unit_id(-lit);
                self.lrat_chain.push(id);
                changed = true;
                continue;
            }
            if self.val(lit) > 0 {
                log!(self.internal, "found positive unit, so clause is subsumed by unit");
                tautology = true;
            }
            let other = self.find_eager_representative_and_compress(lit);
            let marked = self.int().marked2(other);
            let neg_marked = self.int().marked2(-other);
            if !marked {
                self.int().mark2(other);
            }
            if neg_marked {
                tautology = true;
                log!(self.internal, "tautology due to {} -> {}", lit, other);
            } else if lit == other && marked {
                changed = true;
                log!(self.internal, "{} -> {} already in", lit, other);
            } else if lit != other {
                if !marked {
                    self.clause.push(other);
                }
                changed = true;
                let id = self.eager_representative_id(lit);
                self.lrat_chain.push(id);
            } else if !marked {
                self.clause.push(lit);
            }
        }

        for i in 0..size {
            let lit = c.lit(i);
            self.int().unmark(lit);
        }

        for i in 0..self.clause.len() {
            let lit = self.clause[i];
            self.int().unmark(lit);
        }

        self.lrat_chain.push(c.id());
        if tautology {
            log!(self.internal, "generated clause is a tautology");
            self.lrat_chain.clear();
            self.clause.clear();
        } else if changed && self.clause.len() == 1 {
            log!(self.internal, &self.lrat_chain, "LRAT chain");
        } else {
            log!(self.internal, c, "oops this should not happen");
            debug_assert!(false);
        }
    }

    /// Allocates the temporary clause with the literals 'lits' (shared part
    /// of 'new_tmp_clause').
    fn new_tmp_clause_lits(&mut self, lits: &[i32]) -> CRef {
        let clear = false;
        debug_assert!(self.int().clause.len() <= i32::MAX as usize);
        let size = lits.len() as i32;
        debug_assert!(size >= 2);

        let bytes = Clause::bytes_for(size);
        let c = CRef::alloc(size);

        self.int().clause_id += 1;
        c.set_id(self.int().clause_id);

        c.set_conditioned(false);
        c.set_covered(false);
        c.set_enqueued(false);
        c.set_frozen(false);
        c.set_garbage(false);
        c.set_gate(false);
        c.set_hyper(false);
        c.set_instantiated(false);
        c.set_moved(false);
        c.set_reason(false);
        c.set_redundant(false);
        c.set_transred(false);
        c.set_subsume(false);
        c.set_swept(false);
        c.set_flushed(false);
        c.set_vivified(false);
        c.set_vivify(false);
        c.set_used(0);

        c.set_glue(size);
        c.set_size(size);
        c.set_pos(2);

        for i in 0..size as usize {
            c.set_lit(i, lits[i]);
        }

        // Just checking that we did not mess up our sophisticated memory
        // layout.  This might be compiler dependent though.  Crucial for
        // correctness.
        debug_assert!(c.bytes() == bytes);
        let _ = bytes;

        log!(self.internal, c, "new pointer {:p}", c.as_ptr());

        let _ = clear;

        if let Some(proof) = self.int().proof.as_mut() {
            proof.add_derived_clause(c, &self.lrat_chain);
        }
        self.extra_clauses.push(c);
        debug_assert!(self.int().lrat_chain.is_empty());
        c
    }

    /// `new_tmp_clause (internal->clause)` (the literals are already in
    /// 'internal->clause', so there is nothing to swap).
    fn new_tmp_clause_internal(&mut self) -> CRef {
        debug_assert!(self.lrat());
        debug_assert!(!self.int().clause.is_empty());
        debug_assert!(!self.lrat_chain.is_empty());
        log!(self.internal, &self.int().clause, "learn new tmp clause");
        debug_assert!(self.int().clause.len() >= 2);
        if self.int().external().solution.is_some() {
            self.int().external().check_learned_clause();
        }
        let lits = self.int().clause.clone();
        self.new_tmp_clause_lits(&lits)
    }

    pub fn new_tmp_clause(&mut self, clause: &mut Vec<i32>) -> CRef {
        debug_assert!(self.lrat());
        debug_assert!(!clause.is_empty());
        debug_assert!(!self.lrat_chain.is_empty());

        log!(self.internal, &*clause, "learn new tmp clause");
        debug_assert!(clause.len() >= 2);
        if self.int().external().solution.is_some() {
            std::mem::swap(clause, &mut self.int().clause);
            self.int().external().check_learned_clause();
            std::mem::swap(clause, &mut self.int().clause);
        }
        let lits = clause.clone();
        self.new_tmp_clause_lits(&lits)
    }

    pub fn new_clause(&mut self) -> CRef {
        debug_assert!(self.int().clause.is_empty() || self.clause.is_empty());
        let mut clear = false;
        if self.int().clause.is_empty() {
            std::mem::swap(&mut self.int().clause, &mut self.clause);
            clear = true;
        }

        let c = self.int().new_clause(false, 0);

        if clear {
            self.int().clause.clear();
        }

        if let Some(proof) = self.int().proof.as_mut() {
            proof.add_derived_clause(c, &self.lrat_chain);
        }

        c
    }

    // TODO we here duplicate the arguments of push_id_and_rewriting_lrat but
    // we probably do not need that.
    /// `except_lhs` defaults to `0` in C++
    /// `remove_units` defaults to `true` in C++
    /// C++ overload `Closure::produce_rewritten_clause_lrat` (renamed).
    pub fn produce_rewritten_clause_lrat_pairs(&mut self, litIds: &mut Vec<LitClausePair>, except_lhs: i32, remove_units: bool) {
        debug_assert!(self.int().lrat_chain.is_empty());
        for i in 0..litIds.len() {
            if litIds[i].clause.is_null() {
                continue;
            }
            let c = litIds[i].clause;
            litIds[i].clause = self.produce_rewritten_clause_lrat(c, except_lhs, remove_units, false);
            let l = litIds[i].current_lit;
            litIds[i].current_lit = self.find_eager_representative(l);
        }
    }

    /// `except_lhs` defaults to `0` in C++
    /// `remove_units` defaults to `true` in C++
    /// `fail_on_unit` defaults to `false` in C++
    pub fn produce_rewritten_clause_lrat(&mut self, c: CRef, except_lhs: i32, remove_units: bool, fail_on_unit: bool) -> CRef {
        debug_assert!(self.int().clause.is_empty());
        debug_assert!(self.int().lrat_chain.is_empty());
        let tmp_lrat = std::mem::take(&mut self.lrat_chain);
        self.lrat_chain.clear();
        log!(self.internal, c, "rewriting clause for LRAT proof, except for rewriting {}", except_lhs);
        debug_assert!(self.int().clause.is_empty());
        debug_assert!(self.lrat_chain.is_empty());
        let mut changed = false;
        let mut tautology = false;
        let size = c.size() as usize;
        for i in 0..size {
            let lit = c.lit(i);
            log!(self.internal, "checking if {} is required", lit);
            if self.int().marked2(lit) {
                continue;
            }
            if self.int().marked2(-lit) {
                tautology = true;
                break;
            }
            if lit == except_lhs || lit == -except_lhs {
                self.int().mark2(lit);
                self.clause.push(lit);
                continue;
            }
            if self.val(lit) < 0 {
                if remove_units || *self.lazy_propagated(lit) != 0 {
                    log!(self.internal, "found unit {}, removing it", -lit);
                    let id = self.int().unit_id(-lit);
                    self.lrat_chain.push(id);
                    changed = true;
                    continue;
                } else {
                    log!(self.internal, "found unit {}, but ignoring it", -lit);
                }
            }
            if self.val(lit) > 0 {
                log!(self.internal, "found positive unit {}, so clause is subsumed by unit", lit);
                if remove_units || *self.lazy_propagated(lit) != 0 {
                    tautology = true;
                }
            }
            let other = self.find_eager_representative_and_compress(lit);
            let marked = self.int().marked2(other);
            let neg_marked = self.int().marked2(-other);
            if !marked {
                self.int().mark2(other);
            }
            if neg_marked {
                tautology = true;
                log!(self.internal, "tautology due to {} -> {}", lit, other);
            } else if lit == other && marked {
                changed = true;
                log!(self.internal, "{} -> {} already in", lit, other);
            } else if lit != other {
                if !marked {
                    self.clause.push(other);
                }
                changed = true;
                let id = self.eager_representative_id(lit);
                self.lrat_chain.push(id);
            } else if !marked {
                self.clause.push(lit);
            }
        }

        for i in 0..size {
            let lit = c.lit(i);
            self.int().unmark(lit);
        }

        for i in 0..self.clause.len() {
            let lit = self.clause[i];
            self.int().unmark(lit);
        }

        self.lrat_chain.push(c.id());
        let d: CRef;
        debug_assert!(self.int().clause.is_empty());
        if tautology {
            log!(self.internal, "generated clause is a tautology");
            d = CRef::NULL;
            self.lrat_chain.clear();
        } else if changed && self.clause.len() == 1 {
            log!(self.internal, &self.lrat_chain, "LRAT chain");
            if fail_on_unit {
                d = CRef::NULL;
                debug_assert!(false, "rewriting produced a unit clause");
            } else {
                d = c;
            }
        } else if changed {
            log!(self.internal, &self.lrat_chain, "LRAT Chain");
            let mut cl = std::mem::take(&mut self.clause);
            d = self.new_tmp_clause(&mut cl);
            self.clause = cl;
            log!(self.internal, d, "rewritten clause to");
        } else {
            log!(self.internal, c, "clause is unchanged, so giving up");
            self.lrat_chain.clear();
            d = c;
        }
        self.clause.clear();
        self.lrat_chain = tmp_lrat;
        debug_assert!(self.int().clause.is_empty());
        d
    }

    /// C++ overload `Closure::push_id_on_chain` (renamed).
    pub fn push_id_on_chain_rewrite(&mut self, chain: &mut Vec<i64>, rewrite: Rewrite, lit: i32) {
        log!(
            self.internal,
            "adding reason {} for rewriting {} marked",
            if lit == rewrite.src { rewrite.id1 } else { rewrite.id2 },
            lit
        );
        chain.push(if lit == rewrite.src { rewrite.id1 } else { rewrite.id2 });
    }

    /// `insert_id_after` defaults to `true` in C++
    /// `rewrite2` defaults to `Rewrite ()` in C++
    /// `except_lhs` defaults to `0` in C++
    /// `except_lhs2` defaults to `0` in C++
    pub fn push_id_and_rewriting_lrat_unit(
        &mut self,
        c: CRef,
        rewrite1: Rewrite,
        chain: &mut Vec<i64>,
        insert_id_after: bool,
        rewrite2: Rewrite,
        except_lhs: i32,
        except_lhs2: i32,
    ) {
        log!(
            self.internal,
            c,
            "computing normalized LRAT chain for clause to produce unit, rewriting except for {} ({}, {}) and {} ({}, {}) and skipping {} and {}",
            rewrite1.src,
            rewrite1.id1 as u64,
            rewrite1.id2 as u64,
            rewrite2.src,
            rewrite2.id1 as u64,
            rewrite2.id2 as u64,
            except_lhs,
            except_lhs2
        );
        debug_assert!(!c.is_null());
        let mut units: Vec<LRAT_ID> = Vec::new();
        let mut rewriting: Vec<LRAT_ID> = Vec::new();
        let size = c.size() as usize;
        for i in 0..size {
            let other = c.lit(i);
            // unclear how to achieve this in the simplify context where other ==
            // g->lhs might be set assert (internal->val (other) <= 0 || other ==
            // except);
            if other == except_lhs || other == -except_lhs {
                // do nothing;
            } else if other == except_lhs2 || other == -except_lhs2 {
                // do nothing;
            } else if self.val(other) < 0 {
                log!(self.internal, "found unit {}", -other);
                let id = self.int().unit_id(-other);
                units.push(id);
            } else if other == rewrite1.src && rewrite1.id1 != 0 {
                self.push_id_on_chain_rewrite(&mut rewriting, rewrite1, other);
            } else if other == -rewrite1.src && rewrite1.id2 != 0 {
                self.push_id_on_chain_rewrite(&mut rewriting, rewrite1, other);
            } else if other == rewrite2.src && rewrite2.id1 != 0 {
                self.push_id_on_chain_rewrite(&mut rewriting, rewrite2, other);
            } else if other == -rewrite2.src && rewrite2.id2 != 0 {
                self.push_id_on_chain_rewrite(&mut rewriting, rewrite2, other);
            } else if other != self.find_eager_representative_and_compress(other) {
                #[cfg(any(feature = "logging", debug_assertions))]
                {
                    let rewritten_other = self.eager_representative(other);
                    debug_assert!(other != rewritten_other);
                    log!(
                        self.internal,
                        "reason for representative of {} {} is {}",
                        other,
                        rewritten_other,
                        self.find_eager_representative_lrat(other) as u64
                    );
                    let _ = rewritten_other;
                }
                let id = self.find_eager_representative_lrat(other);
                rewriting.push(id);
            } else {
                log!(self.internal, "no rewriting needed for {}", other);
            }
        }
        for id in units {
            chain.push(id);
        }

        if !insert_id_after {
            chain.push(c.id());
        }
        for id in rewriting {
            chain.push(id);
        }

        if insert_id_after {
            chain.push(c.id());
        }
    }

    // Note: it is important that the Rewrite takes over the normal
    // rewriting, because we can force rewriting that way that have not been
    // done eagerly yet.
    /// `insert_id_after` defaults to `true` in C++
    /// `rewrite2` defaults to `Rewrite ()` in C++
    /// `except_lhs` defaults to `0` in C++
    /// `except_lhs2` defaults to `0` in C++
    pub fn push_id_and_rewriting_lrat_full(
        &mut self,
        c: CRef,
        rewrite1: Rewrite,
        chain: &mut Vec<i64>,
        insert_id_after: bool,
        rewrite2: Rewrite,
        except_lhs: i32,
        except_lhs2: i32,
    ) {
        log!(
            self.internal,
            c,
            "computing normalized LRAT chain for clause, rewriting except for {} ({}, {}) and {} ({}, {}) and skipping {} and {}",
            rewrite1.src,
            rewrite1.id1 as u64,
            rewrite1.id2 as u64,
            rewrite2.src,
            rewrite2.id1 as u64,
            rewrite2.id2 as u64,
            except_lhs,
            except_lhs2
        );
        debug_assert!(!c.is_null());
        if !insert_id_after {
            chain.push(c.id());
        }
        let size = c.size() as usize;
        for i in 0..size {
            let other = c.lit(i);
            // unclear how to achieve this in the simplify context where other ==
            // g->lhs might be set assert (internal->val (other) <= 0 || other ==
            // except);
            if other == except_lhs {
                // do nothing;
            } else if other == except_lhs2 {
                // do nothing;
            } else if self.val(other) < 0 {
                log!(self.internal, "found unit {}", -other);
                let id = self.int().unit_id(-other);
                debug_assert!(id != 0);
                chain.push(id);
            } else if other == rewrite1.src && rewrite1.id1 != 0 {
                self.push_id_on_chain_rewrite(chain, rewrite1, other);
            } else if other == -rewrite1.src && rewrite1.id2 != 0 {
                self.push_id_on_chain_rewrite(chain, rewrite1, other);
            } else if other == rewrite2.src && rewrite2.id1 != 0 {
                self.push_id_on_chain_rewrite(chain, rewrite2, other);
            } else if other == -rewrite2.src && rewrite2.id2 != 0 {
                self.push_id_on_chain_rewrite(chain, rewrite2, other);
            } else {
                debug_assert!(other == self.find_eager_representative(other));
                log!(self.internal, "no rewriting needed for {}", other);
            }
        }
        if insert_id_after {
            chain.push(c.id());
        }
    }

    // Note: it is important that the Rewrite takes over the normal
    // rewriting, because we can force rewriting that way that have not been
    // done eagerly yet.
    pub fn push_id_on_chain(&mut self, chain: &mut Vec<i64>, c: CRef) {
        debug_assert!(!c.is_null());
        chain.push(c.id());
        log!(self.internal, &self.lrat_chain, "chain");
    }

    /// C++ overload `Closure::push_id_on_chain` (renamed).
    pub fn push_id_on_chain_optional(&mut self, chain: &mut Vec<i64>, c: &my_dummy_optional) {
        debug_assert!(c.is_set());
        let litId = c.content;
        chain.push(litId.clause.id());
        log!(self.internal, &self.lrat_chain, "chain");
    }

    /// C++ overload `Closure::push_id_on_chain` (renamed).
    pub fn push_id_on_chain_pairs(&mut self, chain: &mut Vec<i64>, reasons: &[LitClausePair]) {
        for &litId in reasons {
            log!(
                self.internal,
                litId.clause,
                "found lrat in gate {} from {}",
                litId.current_lit,
                litId.clause.id()
            );
            self.push_id_on_chain(chain, litId.clause);
        }
        log!(self.internal, &self.lrat_chain, "chain from {} reasons", reasons.len());
    }

    pub fn learn_congruence_unit_when_lhs_set(&mut self, g: *mut Gate, src: i32, id1: i64, id2: i64, dst: i32) {
        if !self.lrat() {
            return;
        }
        log!(self.internal, "calculating LRAT chain learn_congruence_unit_when_lhs_set");
        debug_assert!(!gt(g).pos_lhs_ids.is_empty());
        debug_assert!(self.int().analyzed.is_empty());
        debug_assert!(self.val(gt(g).lhs) < 0);
        match gt(g).tag {
            Gate_Type::And_Gate => {
                log!(self.internal, &self.lrat_chain, "lrat");
                log!(self.internal, &self.lrat_chain, "lrat");
                if gt(g).neg_lhs_ids.is_set() {
                    let c = gt(g).neg_lhs_ids.content.clause;
                    self.push_id_and_rewriting_lrat_unit_self(
                        c,
                        Rewrite::new(src, dst, id1, id2),
                        true,
                        Rewrite::default(),
                        0,
                        0,
                    );
                } else {
                    debug_assert!(
                        gt(g).degenerated_gate == Special_Gate::DEGENERATED_AND
                            || gt(g).degenerated_gate == Special_Gate::DEGENERATED_AND_LHS_FALSE
                    );
                    debug_assert!(gt(g).pos_lhs_ids.len() == 1);
                    let c = gt(g).pos_lhs_ids[0].clause;
                    self.push_id_and_rewriting_lrat_unit_self(
                        c,
                        Rewrite::new(src, dst, id1, id2),
                        true,
                        Rewrite::default(),
                        0,
                        0,
                    );
                }
                log!(self.internal, &self.lrat_chain, "lrat");
            }
            Gate_Type::XOr_Gate | Gate_Type::ITE_Gate => {
                debug_assert!(false);
            }
        }
    }

    // Something very important here: as we are producing a unit, we cannot
    // simplify or rewrite the clauses as this will produce units.
    //
    // For special cases, you have to be careful as the reasons are not
    // eagerly reduced. Therefore, we need to filter to keep only the reasons
    // we are interested (usually the ones where we have a clash).
    pub fn learn_congruence_unit_falsifies_lrat_chain(
        &mut self,
        g: *mut Gate,
        src: i32,
        dst: i32,
        clashing: i32,
        falsified: i32,
        unit: i32,
    ) {
        if !self.lrat() {
            return;
        }
        debug_assert!(unit != 0);
        debug_assert!(!gt(g).pos_lhs_ids.is_empty());
        debug_assert!(self.int().analyzed.is_empty());
        debug_assert!(self.lrat_chain.is_empty());
        let mut proof_chain: Vec<LRAT_ID> = Vec::new();
        debug_assert!(gt(g).tag == Gate_Type::And_Gate);
        let degenerated = gt(g).degenerated_gate == Special_Gate::DEGENERATED_AND
            || gt(g).degenerated_gate == Special_Gate::DEGENERATED_AND_LHS_FALSE;
        if clashing != 0 {
            log!(self.internal, "clashing {} where -lhs={}", clashing, -gt(g).lhs);
            // Example: -2 = 1&3 and 3=2
            // The proof consists in taking the binary clause of the clashing
            // literal
            if clashing == -gt(g).lhs {
                let n = gt(g).pos_lhs_ids.len();
                for i in 0..n {
                    let litId = gt(g).pos_lhs_ids[i];
                    log!(
                        self.internal,
                        litId.clause,
                        "found lrat in gate {} from {} (looking for {})",
                        litId.current_lit,
                        litId.clause.id(),
                        falsified
                    );
                    if litId.current_lit == clashing {
                        let degenerated = gt(g).degenerated_gate == Special_Gate::DEGENERATED_AND
                            || gt(g).degenerated_gate == Special_Gate::DEGENERATED_AND_LHS_FALSE;
                        let e = if degenerated { 0 } else { -gt(g).lhs };
                        self.push_id_and_rewriting_lrat_unit(
                            litId.clause,
                            Rewrite::default(),
                            &mut proof_chain,
                            true,
                            Rewrite::default(),
                            e,
                            0,
                        );
                    }
                }
                debug_assert!(!proof_chain.is_empty());
            } else {
                // Example: 3 = (-1&2) and 2=1
                // The proof consists in taking the binary clause with the
                // rewrites Example where the rewrite must be before:
                // 2: 3v2
                // 9: -2v1
                // 6: 3v1
                // The chain cannot start by 9
                if degenerated {
                    log!(self.internal, "{} {} {}", src, dst, gt(g).lhs);
                    if src == gt(g).lhs || dst == gt(g).lhs {
                        log!(self.internal, "degenerated AND gate with dst=lhs");
                        let n = gt(g).pos_lhs_ids.len();
                        for i in 0..n {
                            let litId = gt(g).pos_lhs_ids[i];
                            log!(self.internal, litId.clause, "definition clause {} ->", litId.current_lit);
                            if litId.current_lit == clashing {
                                self.push_id_and_rewriting_lrat_unit(
                                    litId.clause,
                                    Rewrite::default(),
                                    &mut proof_chain,
                                    true,
                                    Rewrite::default(),
                                    0,
                                    0,
                                );
                                log!(self.internal, &proof_chain, "produced lrat chain so far");
                            }
                        }
                        debug_assert!(!proof_chain.is_empty());
                    } else {
                        log!(
                            self.internal,
                            "degenerated AND gate with conflict without LHS for {}",
                            loglit!(self.internal, unit)
                        );
                        let n = gt(g).pos_lhs_ids.len();
                        for i in 0..n {
                            let litId = gt(g).pos_lhs_ids[i];
                            log!(self.internal, litId.clause, "definition clause {} ->", litId.current_lit);
                            let insert_after = !clause_contains(litId.clause, unit);
                            let lhs = gt(g).lhs;
                            self.push_id_and_rewriting_lrat_unit(
                                litId.clause,
                                Rewrite::default(),
                                &mut proof_chain,
                                insert_after,
                                Rewrite::default(),
                                lhs,
                                0,
                            );
                            log!(self.internal, &proof_chain, "produced lrat chain so far");
                        }
                    }
                } else {
                    log!(self.internal, "normal AND gate");
                    let n = gt(g).pos_lhs_ids.len();
                    for i in 0..n {
                        let litId = gt(g).pos_lhs_ids[i];
                        let insert_after = !clause_contains(litId.clause, unit);
                        let degenerated = gt(g).degenerated_gate == Special_Gate::DEGENERATED_AND
                            || gt(g).degenerated_gate == Special_Gate::DEGENERATED_AND_LHS_FALSE;
                        let e = if degenerated { 0 } else { -gt(g).lhs };
                        self.push_id_and_rewriting_lrat_unit(
                            litId.clause,
                            Rewrite::default(),
                            &mut proof_chain,
                            insert_after,
                            Rewrite::default(),
                            e,
                            0,
                        );
                        log!(self.internal, &proof_chain, "produced lrat chain so far");
                    }
                }
            }
            log!(self.internal, &proof_chain, "produced lrat chain");
        } else if falsified != 0 {
            log!(self.internal, "falsifies {}", falsified);
            // Example is 3=(1&2) with 2=false or 3=(1&4) with 4=2 and 2=false
            // (can happen when the unit was derived in the middle of the
            // rewriting)
            let n = gt(g).pos_lhs_ids.len();
            for i in 0..n {
                let litId = gt(g).pos_lhs_ids[i];
                log!(
                    self.internal,
                    litId.clause,
                    "found lrat in gate {} from {} (looking for {})",
                    litId.current_lit,
                    litId.clause.id(),
                    falsified
                );
                if litId.current_lit == falsified || (litId.current_lit == src && dst == falsified) {
                    let lhs = gt(g).lhs;
                    self.push_id_and_rewriting_lrat_unit(
                        litId.clause,
                        Rewrite::default(),
                        &mut proof_chain,
                        true,
                        Rewrite::default(),
                        -dst,
                        -lhs,
                    );
                }
            }
        } else {
            debug_assert!(unit != 0);
            // Example is 1 = 2&3 where 2 and 3 are false
            if gt(g).neg_lhs_ids.is_set() {
                let c = gt(g).neg_lhs_ids.content.clause;
                self.push_id_and_rewriting_lrat_unit(
                    c,
                    Rewrite::default(),
                    &mut proof_chain,
                    true,
                    Rewrite::default(),
                    0,
                    0,
                );
            }
            log!(self.internal, &proof_chain, "produced lrat chain");
        }
        self.lrat_chain = proof_chain;
        let _ = unit;
    }

    pub fn fully_propagate(&mut self) -> bool {
        if self.int().unsat {
            return false;
        }
        log!(self.internal, "fully propagating");
        debug_assert!(self.int().watching());
        debug_assert!(self.full_watching);
        let no_conflict = self.int().propagate();

        if no_conflict {
            return true;
        }
        self.int().learn_empty_clause();
        if self.lrat() {
            self.lrat_chain.clear();
        }

        false
    }

    /// `delay_propagation` defaults to `false` in C++
    /// `force_propagation` defaults to `false` in C++
    pub fn learn_congruence_unit(&mut self, lit: i32, delay_propagation: bool, force_propagation: bool) -> bool {
        if self.int().unsat {
            return false;
        }
        log!(self.internal, &self.lrat_chain, "assigning due to LRAT chain");
        let val_lit = self.val(lit);
        if val_lit > 0 {
            log!(self.internal, "already set lit {}", lit);
            if self.lrat() {
                self.lrat_chain.clear();
            }
            if force_propagation {
                return self.fully_propagate();
            }
            return true;
        }
        log!(self.internal, "adding unit {}", loglit!(self.internal, lit));
        self.int().stats.congruence.units += 1;
        debug_assert!(!self.lrat() || !self.lrat_chain.is_empty());
        if val_lit < 0 {
            if self.lrat() {
                debug_assert!(self.int().lrat_chain.is_empty());
                let id = self.int().unit_id(-lit);
                log!(self.internal, "for literal {} adding unit {}", loglit!(self.internal, -lit), id);
                self.int().lrat_chain.push(id);
                for i in 0..self.lrat_chain.len() {
                    let id = self.lrat_chain[i];
                    self.int().lrat_chain.push(id);
                }
                self.lrat_chain.clear();
            }
            self.int().learn_empty_clause();
            return false;
        }

        debug_assert!(self.int().lrat_chain.is_empty());
        std::mem::swap(&mut self.int().lrat_chain, &mut self.lrat_chain);
        self.int().assign_unit(lit);
        debug_assert!(self.lrat_chain.is_empty());
        debug_assert!(self.int().lrat_chain.is_empty());
        if delay_propagation {
            false
        } else {
            self.fully_propagate()
        }
    }

    // for merging the literals there are many cases
    // TODO: LRAT does not work if the LHS is not in normal form and if the
    // representative is also in the gate.
    /// `extra_reasons_lit` defaults to `{}` in C++
    /// `extra_reasons_ulit` defaults to `{}` in C++
    /// C++ overload `Closure::merge_literals` (renamed).
    pub fn merge_literals_gates(
        &mut self,
        g: *mut Gate,
        h: *mut Gate,
        lit: i32,
        other: i32,
        extra_reasons_lit: &[i64],
        extra_reasons_ulit: &[i64],
    ) -> bool {
        debug_assert!(!self.int().unsat);
        debug_assert!(gt(g).lhs == lit);
        debug_assert!(g == h || gt(h).lhs == other);
        log!(self.internal, "merging literals {} and {}", loglit!(self.internal, lit), loglit!(self.internal, other));
        let repr_lit = self.find_representative_and_compress(lit, false);
        let repr_other = self.find_representative_and_compress(other, false);
        self.find_representative_and_compress(-lit, false);
        self.find_representative_and_compress(-other, false);
        log!(self.internal, "merging literals {} [={}] and {} [={}]", lit, repr_lit, other, repr_other);

        if repr_lit == repr_other {
            log!(self.internal, "already merged {} and {}", lit, other);
            if self.lrat() {
                self.lrat_chain.clear();
            }
            return false;
        }

        let val_lit = self.val(lit) as i32;
        let val_other = self.val(other) as i32;
        if val_lit != 0 {
            if val_lit == val_other {
                log!(self.internal, "not merging lits {} and {} assigned to same value", lit, other);
                if self.lrat() {
                    self.lrat_chain.clear();
                }
                return false;
            }
        }

        // This is a special case where we actually cannot produce an LRAT
        // proof
        // 2 = (3 & 4)
        // false = (3 & 4)
        if gt(g).degenerated_gate == Special_Gate::DEGENERATED_AND_LHS_FALSE
            || gt(h).degenerated_gate == Special_Gate::DEGENERATED_AND_LHS_FALSE
        {
            log!(self.internal, "merging special AND case with both side < 0");
            debug_assert!(self.val(gt(g).lhs) < 0 || self.val(gt(h).lhs) < 0);
            debug_assert!(self.val(gt(g).lhs) != self.val(gt(h).lhs));
            self.lrat_chain =
                if extra_reasons_lit.is_empty() { extra_reasons_ulit.to_vec() } else { extra_reasons_lit.to_vec() };
            let unass = if self.val(gt(g).lhs) < 0 { gt(h).lhs } else { gt(g).lhs };
            self.learn_congruence_unit(-unass, false, false);
            return false;
        }

        log!(
            self.internal,
            "special case {} {} {} {}",
            (gt(g).degenerated_gate == Special_Gate::DEGENERATED_AND) as i32,
            (self.val(gt(h).lhs) < 0) as i32,
            (gt(h).degenerated_gate == Special_Gate::DEGENERATED_AND) as i32,
            (self.val(gt(g).lhs) < 0) as i32
        );
        if (gt(g).degenerated_gate == Special_Gate::DEGENERATED_AND_LHS_FALSE && self.val(gt(h).lhs) < 0)
            || (gt(h).degenerated_gate == Special_Gate::DEGENERATED_AND_LHS_FALSE && self.val(gt(g).lhs) < 0)
        {
            log!(self.internal, "merging special AND case");
            debug_assert!(self.val(gt(g).lhs) < 0 || self.val(gt(h).lhs) < 0);
            debug_assert!(self.val(gt(g).lhs) != self.val(gt(h).lhs));
            self.lrat_chain =
                if extra_reasons_lit.is_empty() { extra_reasons_ulit.to_vec() } else { extra_reasons_lit.to_vec() };
            let unass = if self.val(gt(g).lhs) < 0 { gt(h).lhs } else { gt(g).lhs };
            self.learn_congruence_unit(-unass, false, false);
            return false;
        }

        self.really_merge_literals(lit, other, repr_lit, repr_other, extra_reasons_lit, extra_reasons_ulit)
    }

    /// `extra_reasons_lit` defaults to `{}` in C++
    /// `extra_reasons_ulit` defaults to `{}` in C++
    pub fn really_merge_literals(
        &mut self,
        lit: i32,
        other: i32,
        repr_lit: i32,
        repr_other: i32,
        extra_reasons_lit: &[i64],
        extra_reasons_ulit: &[i64],
    ) -> bool {
        // For LRAT we need to distinguish more cases for a more regular
        // reconstruction.
        //
        // 1. if lit = -other, then we learn lit and -lit to derive false
        //
        // 2. otherwise, we learn the new clauses lit = -other (which are two
        // real clauses).
        //
        //    2a. if repr_lit = -repr_other, we learn the units repr_lit and
        //    -repr_lit to derive false
        //
        //    2b. otherwise, we learn the equivalences repr_lit = -repr_other
        //    (which are two real clauses)
        //
        // Without LRAT this is easier, as we directly learn the conclusion
        // (either false or the equivalence). The steps can also not be
        // merged because repr_lit can appear in the gate and hence in the
        // resolution chain.
        let val_lit = self.val(lit) as i32;
        let val_other = self.val(other) as i32;

        let mut smaller_repr = repr_lit;
        let mut larger_repr = repr_other;
        let mut smaller = lit;
        let mut larger = other;
        let mut val_smaller = val_lit;
        let mut val_larger = val_other;
        let mut smaller_chain: &[i64] = extra_reasons_ulit;
        let mut larger_chain: &[i64] = extra_reasons_lit;

        if val_lit != 0 && val_lit == val_other {
            log!(self.internal, "not merging lits {} and {} assigned to same value", lit, other);
            if self.lrat() {
                self.lrat_chain.clear();
            }
            return false;
        }
        if repr_lit == repr_other {
            log!(
                self.internal,
                "already merged {} and {}",
                loglit!(self.internal, lit),
                loglit!(self.internal, other)
            );
            return false;
        }
        if smaller_repr.abs() > larger_repr.abs() {
            std::mem::swap(&mut smaller_repr, &mut larger_repr);
            std::mem::swap(&mut smaller, &mut larger);
            std::mem::swap(&mut smaller_chain, &mut larger_chain);
            std::mem::swap(&mut val_smaller, &mut val_larger);
        }
        let _ = val_smaller;

        debug_assert!(self.find_representative(smaller_repr) == smaller_repr);
        debug_assert!(self.find_representative(larger_repr) == larger_repr);
        if lit == -other {
            debug_assert!(self.lrat_chain.is_empty());
            log!(self.internal, "merging clashing {} and {}", lit, other);
            if self.int().proof.is_some() {
                if self.lrat() {
                    for &id in smaller_chain {
                        self.lrat_chain.push(id);
                    }
                }
                self.unsimplified.push(smaller);
                let id = self.simplify_and_add_unsimplified_to_proof_chain(0);

                if self.lrat() {
                    self.int().lrat_chain.push(id);
                    for &id in larger_chain {
                        self.int().lrat_chain.push(id);
                    }
                    log!(self.internal, &self.int().lrat_chain, "lrat chain");
                }
            }
            self.int().learn_empty_clause();
            self.delete_proof_chain();
            return false;
        }

        log!(
            self.internal,
            "merging {} and {} first and then the equivalences of {} and {} with LRAT",
            loglit!(self.internal, lit),
            loglit!(self.internal, other),
            loglit!(self.internal, repr_lit),
            loglit!(self.internal, repr_other)
        );
        let mut eq1_tmp = CRef::NULL;
        if self.lrat() {
            self.lrat_chain = smaller_chain.to_vec();
            eq1_tmp = self.add_tmp_binary_clause(-larger, smaller);
        }
        debug_assert!(!self.lrat() || !eq1_tmp.is_null());

        let mut eq2_tmp = CRef::NULL;
        if self.lrat() {
            self.lrat_chain = larger_chain.to_vec();
            log!(self.internal, &self.lrat_chain, "lrat chain");

            eq2_tmp = self.add_tmp_binary_clause(larger, -smaller);
            // the order in the clause is important for the
            // repr_lit == -repr_other to get the right chain
        }
        debug_assert!(!self.lrat() || !eq2_tmp.is_null());
        if self.lrat() {
            self.lrat_chain.clear();
        }

        if repr_lit == -repr_other {
            // now derive empty clause
            let mut rew1 = Rewrite::default();
            let mut rew2 = Rewrite::default();
            let mut eq1 = eq1_tmp; // == -larger, smaller
            let mut eq2 = eq2_tmp;
            if self.lrat() {
                if val_larger < 0 {
                    std::mem::swap(&mut eq1, &mut eq2);
                }

                // no need to calculate push_id_and_rewriting_lrat here because
                // all the job is done by the arguments already
                rew1 = Rewrite::new(
                    if lit == repr_lit { 0 } else { lit },
                    repr_lit,
                    if lit == repr_lit { 0 } else { self.representative_id(lit) },
                    if lit == repr_lit { 0 } else { self.representative_id(-lit) },
                );
                rew2 = Rewrite::new(
                    if other == repr_other { 0 } else { other },
                    repr_other,
                    if other == repr_other { 0 } else { self.representative_id(other) },
                    if other == repr_other { 0 } else { self.representative_id(-other) },
                );
                self.push_id_and_rewriting_lrat_unit_self(eq1, rew1, true, rew2, 0, 0);
                std::mem::swap(&mut self.int().lrat_chain, &mut self.lrat_chain);
            }
            debug_assert!(val_larger == self.val(larger_repr) as i32);
            if val_larger == 0 {
                // not assigned, first assign one
                self.int().assign_unit(-larger_repr);
                if self.lrat() {
                    self.int().lrat_chain.clear();

                    if larger != larger_repr {
                        self.push_lrat_unit(-larger_repr);
                    }
                    // no need to calculate push_id_and_rewriting_lrat here
                    // because all the job is done by the arguments already
                    self.push_id_and_rewriting_lrat_unit_self(
                        eq2,
                        rew1,
                        true,
                        rew2,
                        if larger != larger_repr { larger_repr } else { 0 },
                        0,
                    );
                    log!(self.internal, &self.lrat_chain, "lrat chain");
                    std::mem::swap(&mut self.int().lrat_chain, &mut self.lrat_chain);
                }
            }
            self.int().learn_empty_clause();
            if self.lrat() {
                self.int().lrat_chain.clear();
            }
            return false;
        }

        if val_lit != 0 {
            if val_lit == val_other {
                log!(
                    self.internal,
                    "not merging lits {} and {} assigned to same value",
                    loglit!(self.internal, lit),
                    loglit!(self.internal, other)
                );
                if self.lrat() {
                    self.lrat_chain.clear();
                }
                return false;
            }
            if val_lit == -val_other {
                log!(
                    self.internal,
                    "merging lits {} and {} assigned to inconsistent value",
                    loglit!(self.internal, lit),
                    loglit!(self.internal, other)
                );
                debug_assert!(self.lrat_chain.is_empty());
                if self.lrat() {
                    let c;
                    // eq1 == -larger, smaller
                    // eq2 == larger, -smaller
                    if lit == smaller {
                        if val_lit < 0 {
                            c = eq1_tmp;
                        } else {
                            c = eq2_tmp;
                        }
                    } else if val_lit < 0 {
                        c = eq2_tmp;
                    } else {
                        c = eq1_tmp;
                    }
                    let pos = if val_lit < 0 { other } else { lit };
                    let neg = if val_lit < 0 { -lit } else { -other };
                    self.push_lrat_unit(pos);
                    self.push_lrat_unit(neg);
                    self.lrat_chain.push(c.id());
                    log!(self.internal, &self.lrat_chain, "chain");
                    std::mem::swap(&mut self.int().lrat_chain, &mut self.lrat_chain);
                }
                self.int().learn_empty_clause();
                if self.lrat() {
                    self.lrat_chain.clear();
                }
                return false;
            }

            debug_assert!(val_other == 0);
            log!(
                self.internal,
                "merging assigned {} and unassigned {}",
                loglit!(self.internal, lit),
                loglit!(self.internal, other)
            );
            debug_assert!(self.lrat_chain.is_empty());
            let unit = if val_lit < 0 { -other } else { other };
            if self.lrat() {
                let c;
                if lit == smaller {
                    if val_lit < 0 {
                        c = eq1_tmp;
                    } else {
                        c = eq2_tmp;
                    }
                } else if val_lit < 0 {
                    c = eq2_tmp;
                } else {
                    c = eq1_tmp;
                }
                self.push_id_and_rewriting_lrat_unit_self(c, Rewrite::default(), true, Rewrite::default(), unit, 0);
            }
            self.learn_congruence_unit(unit, false, false);
            if self.lrat() {
                self.lrat_chain.clear();
            }
            return false;
        }

        if val_lit == 0 && val_other != 0 {
            log!(
                self.internal,
                "merging unassigned {} and assigned {}",
                loglit!(self.internal, lit),
                loglit!(self.internal, other)
            );
            debug_assert!(self.lrat_chain.is_empty());
            let unit = if val_other < 0 { -lit } else { lit };
            if self.lrat() {
                let c;
                // eq1 == -larger, smaller
                // eq2 == larger, -smaller
                if lit == smaller {
                    // opposite of case above
                    if val_other < 0 {
                        c = eq2_tmp; // other == larger ==> eq2 == other , unit
                    } else {
                        c = eq1_tmp; // other == larger ==> eq1 == -other , unit
                    }
                } else if val_other < 0 {
                    c = eq1_tmp; // lit == larger ==> eq1 == unit, other
                } else {
                    c = eq2_tmp; // lit == larger ==> eq2 == unit, -other
                }
                self.push_id_and_rewriting_lrat_unit_self(c, Rewrite::default(), true, Rewrite::default(), lit, unit);
            }
            self.learn_congruence_unit(unit, false, false);
            if self.lrat() {
                self.lrat_chain.clear();
            }
            return false;
        }

        let eq1_repr;
        let eq2_repr;
        if smaller_repr != smaller || larger != larger_repr {
            if self.lrat() {
                self.lrat_chain.clear();
                let rew1 = Rewrite::new(
                    if smaller_repr != smaller { smaller } else { 0 },
                    if smaller_repr != smaller { smaller_repr } else { 0 },
                    if smaller_repr != smaller { self.representative_id(smaller) } else { 0 },
                    if smaller_repr != smaller { self.representative_id(-smaller) } else { 0 },
                );
                let rew2 = Rewrite::new(
                    if larger_repr != larger { larger } else { 0 },
                    if larger_repr != larger { larger_repr } else { 0 },
                    if larger_repr != larger { self.representative_id(larger) } else { 0 },
                    if larger_repr != larger { self.representative_id(-larger) } else { 0 },
                );
                self.push_id_and_rewriting_lrat_full_self(eq1_tmp, rew1, true, rew2, 0, 0);
            }
            eq1_repr = self.learn_binary_tmp_or_full_clause(-larger_repr, smaller_repr);
        } else if self.lrat() {
            eq1_repr = self.maybe_promote_tmp_binary_clause(eq1_tmp);
        } else {
            eq1_repr = self.maybe_add_binary_clause(-larger_repr, smaller_repr);
        }

        if self.lrat() {
            self.lrat_chain.clear();
        }

        if smaller_repr != smaller || larger != larger_repr {
            if self.lrat() {
                self.lrat_chain.clear();
                // eq2 = larger, -smaller
                let rew1 = Rewrite::new(
                    if smaller_repr != smaller { smaller } else { 0 },
                    if smaller_repr != smaller { smaller_repr } else { 0 },
                    if smaller_repr != smaller { self.representative_id(smaller) } else { 0 },
                    if smaller_repr != smaller { self.representative_id(-smaller) } else { 0 },
                );
                let rew2 = Rewrite::new(
                    if larger_repr != larger { larger } else { 0 },
                    if larger_repr != larger { larger_repr } else { 0 },
                    if larger_repr != larger { self.representative_id(larger) } else { 0 },
                    if larger_repr != larger { self.representative_id(-larger) } else { 0 },
                );
                self.push_id_and_rewriting_lrat_full_self(eq2_tmp, rew1, true, rew2, 0, 0);
            }

            eq2_repr = self.learn_binary_tmp_or_full_clause(larger_repr, -smaller_repr);
        } else if self.lrat() {
            eq2_repr = self.maybe_promote_tmp_binary_clause(eq2_tmp);
        } else {
            eq2_repr = self.maybe_add_binary_clause(larger_repr, -smaller_repr);
        }
        self.lrat_chain.clear();

        if self.lrat() {
            *self.representative_id_mut(larger_repr) = eq1_repr.id();
            debug_assert!(clause_contains(eq1_repr, -larger_repr));
            *self.representative_id_mut(-larger_repr) = eq2_repr.id();
            debug_assert!(clause_contains(eq2_repr, larger_repr));
        }
        log!(self.internal, "updating {} -> {}", larger_repr, smaller_repr);
        *self.representative_mut(larger_repr) = smaller_repr;
        *self.representative_mut(-larger_repr) = -smaller_repr;
        self.schedule_literal(larger_repr);
        self.int().stats.congruence.congruent += 1;
        debug_assert!(self.lrat_chain.is_empty());
        true
    }

    // Variant when there are no gates
    // TODO: this is exactly the same as the other function without the gates.
    // Kill the arguments!
    /// `extra_reasons_lit` defaults to `{}` in C++
    /// `extra_reasons_ulit` defaults to `{}` in C++
    pub fn merge_literals(&mut self, lit: i32, other: i32, extra_reasons_lit: &[i64], extra_reasons_ulit: &[i64]) -> bool {
        debug_assert!(!self.int().unsat);
        log!(self.internal, "merging literals {} and {}", loglit!(self.internal, lit), loglit!(self.internal, other));
        // TODO: this should not update_eager but still calculate the LRAT
        // chain below!
        let repr_lit = self.find_representative_and_compress(lit, false);
        let repr_other = self.find_representative_and_compress(other, false);
        self.find_representative_and_compress(-lit, false);
        self.find_representative_and_compress(-other, false);
        log!(
            self.internal,
            "merging literals {} [={}] and {} [={}]",
            loglit!(self.internal, lit),
            repr_lit,
            loglit!(self.internal, other),
            repr_other
        );
        log!(self.internal, &self.lrat_chain, "lrat chain beginning of merge");

        if repr_lit == repr_other {
            log!(
                self.internal,
                "already merged {} and {}",
                loglit!(self.internal, lit),
                loglit!(self.internal, other)
            );
            return false;
        }

        self.really_merge_literals(lit, other, repr_lit, repr_other, extra_reasons_lit, extra_reasons_ulit)
    }

    pub fn promote_clause(&mut self, c: CRef) {
        if self.lrat() {
            self.check_not_tmp_binary_clause(c);
        }
        if c.is_null() {
            return;
        }
        if !c.redundant() {
            return;
        }
        log!(self.internal, c, "turning redundant subsuming clause into irredundant clause");
        c.set_redundant(false);
        if let Some(proof) = self.int().proof.as_mut() {
            proof.strengthen(c.id());
        }
        let internal = self.int();
        internal.stats.current.irredundant += 1;
        internal.stats.added.irredundant += 1;
        internal.stats.irrlits += c.size() as i64;
        debug_assert!(internal.stats.current.redundant > 0);
        internal.stats.current.redundant -= 1;
        debug_assert!(internal.stats.added.redundant > 0);
        internal.stats.added.redundant -= 1;
        // ... and keep 'stats.added.total'.
    }

    // This function is rather tricky for LRAT. If you have 2 = 1 and 3=4 you
    // cannot add 2=3. You really to connect the representatives directly
    // therefore you actually need to learn the clauses 2->3->4 and -2->1 and
    // vice-versa
    pub fn merge_literals_equivalence(&mut self, lit: i32, other: i32, c1: CRef, c2: CRef) -> bool {
        debug_assert!(!self.int().unsat);
        let id1: LRAT_ID = if !c1.is_null() { c1.id() } else { 0 };
        let id2: LRAT_ID = if !c2.is_null() { c2.id() } else { 0 };
        if self.lrat() {
            debug_assert!(!c1.is_null());
            debug_assert!(!c2.is_null());
            debug_assert!(c1.size() == 2);
            debug_assert!(c2.size() == 2);
            debug_assert!(c1.lit(0) == lit || c1.lit(1) == lit);
            debug_assert!(c2.lit(0) == other || c2.lit(1) == other);
            debug_assert!(c1.lit(0) == -other || c1.lit(1) == -other);
            debug_assert!(c2.lit(0) == -lit || c2.lit(1) == -lit);
            self.check_not_tmp_binary_clause(c1);
            self.check_not_tmp_binary_clause(c2);
        }
        let repr_lit = self.find_representative(lit);
        let repr_other = self.find_representative(other);
        self.find_representative_and_compress_both(lit);
        self.find_representative_and_compress_both(other);
        log!(self.internal, "merging literals {} [={}] and {} [={}] lrat", lit, repr_lit, other, repr_other);

        if repr_lit == repr_other {
            log!(self.internal, "already merged {} and {}", lit, other);
            return false;
        }
        let val_lit = self.val(lit) as i32;
        let val_other = self.val(other) as i32;

        if val_lit != 0 {
            if val_lit == val_other {
                log!(self.internal, "not merging lits {} and {} assigned to same value", lit, other);
                return false;
            }
            if val_lit == -val_other {
                if self.lrat() {
                    let a = self.int().unit_id(lit);
                    self.lrat_chain.push(a);
                    let b = self.int().unit_id(other);
                    self.lrat_chain.push(b);
                }
                log!(self.internal, "merging lits {} and {} assigned to inconsistent value", lit, other);
                self.int().learn_empty_clause();
                return false;
            }

            debug_assert!(val_other == 0);
            log!(self.internal, "merging assigned {} and unassigned {}", lit, other);
            let unit = if val_lit < 0 { -other } else { other };
            if self.lrat() {
                let id = self.int().unit_id(unit);
                self.lrat_chain.push(id);
            }
            if val_lit < 0 {
                self.lrat_chain.push(c2.id());
            } else {
                self.lrat_chain.push(c1.id());
            }
            self.learn_congruence_unit(unit, false, false);
            return false;
        }

        if val_lit == 0 && val_other != 0 {
            log!(self.internal, "merging assigned {} and unassigned {}", other, lit);
            let unit = if val_other < 0 { -lit } else { lit };
            if self.lrat() {
                let id = self.int().unit_id(if val_other < 0 { -other } else { other });
                self.lrat_chain.push(id);
            }
            if val_lit < 0 {
                self.lrat_chain.push(c1.id());
            } else {
                self.lrat_chain.push(c2.id());
            }
            self.learn_congruence_unit(unit, false, false);
            return false;
        }

        let mut smaller_repr = repr_lit;
        let mut larger_repr = repr_other;
        let mut smaller = lit;
        let mut larger = other;

        if smaller_repr.abs() > larger_repr.abs() {
            std::mem::swap(&mut smaller_repr, &mut larger_repr);
            std::mem::swap(&mut smaller, &mut larger);
        }

        debug_assert!(self.find_representative(smaller_repr) == smaller_repr);
        debug_assert!(self.find_representative(larger_repr) == larger_repr);

        if repr_lit == -repr_other {
            log!(
                self.internal,
                "merging clashing {} [={}] and {}[={}], smaller: {}",
                lit,
                repr_lit,
                other,
                repr_other,
                smaller
            );
            if self.lrat() {
                let rew1 = Rewrite::new(
                    lit,
                    if lit == repr_lit { 0 } else { repr_lit },
                    if lit == repr_lit { 0 } else { self.find_representative_lrat(lit) },
                    if lit == repr_lit { 0 } else { self.find_representative_lrat(-lit) },
                );
                let rew2 = Rewrite::new(
                    other,
                    if other == repr_other { 0 } else { repr_other },
                    if other == repr_other { 0 } else { self.find_representative_lrat(other) },
                    if other == repr_other { 0 } else { self.find_representative_lrat(-other) },
                );
                self.push_id_and_rewriting_lrat_unit_self(c1, rew1, true, rew2, 0, 0);
                log!(self.internal, &self.lrat_chain, "lrat chain");
                std::mem::swap(&mut self.int().lrat_chain, &mut self.lrat_chain);
            }
            self.int().assign_unit(repr_lit);
            if self.lrat() {
                self.lrat_chain.clear();
                let id = self.int().unit_id(repr_lit);
                debug_assert!(id != 0);
                self.lrat_chain.push(id);
                if lit != repr_lit {
                    let repr_id2 = self.find_representative_lrat(-lit);
                    self.lrat_chain.push(repr_id2);
                }
                self.lrat_chain.push(id2);
                if other != repr_other {
                    let repr_larger_id2 = self.find_representative_lrat(other);
                    self.lrat_chain.push(repr_larger_id2);
                }
                log!(self.internal, &self.lrat_chain, "lrat chain");
                std::mem::swap(&mut self.int().lrat_chain, &mut self.lrat_chain);
            }
            self.int().learn_empty_clause();
            return false;
        }

        log!(self.internal, "merging {} [={}] and {} [={}]", lit, repr_lit, other, repr_other);
        self.promote_clause(c1);
        self.promote_clause(c2);
        let learn_clause = (lit != repr_lit) || (other != repr_other);
        if learn_clause {
            if self.lrat() {
                if lit != repr_lit {
                    log!(self.internal, "adding chain for lit {} -> {}", lit, repr_lit);
                    let id = self.find_representative_lrat(lit);
                    self.lrat_chain.push(id);
                }
                if other != repr_other {
                    log!(self.internal, "adding chain for lit {} -> {}", -other, -repr_other);
                    let id = self.find_representative_lrat(-other);
                    self.lrat_chain.push(id);
                }
                self.lrat_chain.push(id1);
            }
            let eq1 = self.learn_binary_tmp_or_full_clause(repr_lit, -repr_other);

            if self.lrat() {
                self.lrat_chain.clear();
                if lit != repr_lit {
                    let id = self.find_representative_lrat(-lit);
                    self.lrat_chain.push(id);
                }
                if other != repr_other {
                    let id = self.find_representative_lrat(other);
                    self.lrat_chain.push(id);
                }
                self.lrat_chain.push(id2);
            }
            let eq2 = self.learn_binary_tmp_or_full_clause(-repr_lit, repr_other);
            if self.lrat() {
                self.lrat_chain.clear();
                if smaller_repr == repr_lit {
                    debug_assert!(larger_repr == repr_other);
                    *self.representative_id_mut(-larger_repr) = eq2.id();
                    debug_assert!(clause_contains(eq2, larger_repr));
                    *self.representative_id_mut(larger_repr) = eq1.id();
                    debug_assert!(clause_contains(eq1, -larger_repr));
                } else {
                    debug_assert!(larger_repr == repr_lit);
                    *self.representative_id_mut(-larger_repr) = eq1.id();
                    debug_assert!(clause_contains(eq1, larger_repr));
                    *self.representative_id_mut(larger_repr) = eq2.id();
                    debug_assert!(clause_contains(eq2, -larger_repr));
                }
            }
        } else if self.lrat() {
            log!(self.internal, "not learning new clause, using already existing one");
            if smaller_repr == repr_lit {
                log!(
                    self.internal,
                    "setting ids of {}: {}; {}: {} (case 1)",
                    larger,
                    id1 as u64,
                    -larger,
                    id2 as u64
                );
                *self.representative_id_mut(-larger_repr) = id2;
                *self.representative_id_mut(larger_repr) = id1;
            } else {
                log!(
                    self.internal,
                    "setting ids of {}: {}; {}: {} (case 2)",
                    larger,
                    id2 as u64,
                    -larger,
                    id1 as u64
                );
                *self.representative_id_mut(-larger_repr) = id1;
                *self.representative_id_mut(larger_repr) = id2;
            }
        }

        log!(self.internal, "updating {} -> {}", larger_repr, smaller_repr);
        *self.representative_mut(larger_repr) = smaller_repr;
        *self.representative_mut(-larger_repr) = -smaller_repr;
        self.schedule_literal(larger_repr);
        self.int().stats.congruence.congruent += 1;
        let _ = larger;
        true
    }

    /*----------------------------------------------------------------------*/

    pub fn goccs(&mut self, lit: i32) -> &mut GOccs {
        let i = self.vlit(lit);
        &mut self.gtab[i]
    }

    pub fn connect_goccs(&mut self, g: *mut Gate, lit: i32) {
        log!(self.internal, g, "connect {} to", lit);
        // incorrect for ITE
        // assert (std::find(begin (goccs (lit)), end (goccs (lit)), g) ==
        // std::end (goccs (lit)));
        self.goccs(lit).push(g);
    }

    pub fn largecount(&mut self, lit: i32) -> &mut u64 {
        debug_assert!(self.vlit(lit) < self.glargecounts.len());
        let i = self.vlit(lit);
        &mut self.glargecounts[i]
    }

    /*----------------------------------------------------------------------*/
    // Initialization

    pub fn init_closure(&mut self) {
        let max_var = self.int().max_var as usize;
        self.representant.resize(2 * max_var + 3, 0);
        self.eager_representant.resize(2 * max_var + 3, 0);
        if self.lrat() {
            self.eager_representant_id.resize(2 * max_var + 3, 0);
            self.representant_id.resize(2 * max_var + 3, 0);
            self.lazy_propagated_idx.resize(max_var + 1, 0);
            let n = self.int().trail.len();
            for i in 0..n {
                let lit = self.int().trail[i];
                *self.lazy_propagated(lit) = 1;
            }
        }
        self.marks.resize(2 * max_var + 3, 0);
        self.mu1_ids.resize(2 * max_var + 3, LitClausePair::default());
        if self.lrat() {
            self.mu2_ids.resize(2 * max_var + 3, LitClausePair::default());
            self.mu4_ids.resize(2 * max_var + 3, LitClausePair::default());
        }
        #[cfg(debug_assertions)]
        {
            for it in self.mu1_ids.iter_mut() {
                it.current_lit = 0;
                it.clause = CRef::NULL;
            }
            for it in self.mu2_ids.iter_mut() {
                it.current_lit = 0;
                it.clause = CRef::NULL;
            }
            for it in self.mu4_ids.iter_mut() {
                it.current_lit = 0;
                it.clause = CRef::NULL;
            }
        }
        self.scheduled.resize(max_var + 1, false);
        self.gtab.resize(2 * max_var + 3, Vec::new());
        for v in self.int().vars() {
            *self.representative_mut(v) = v;
            *self.representative_mut(-v) = -v;
            *self.eager_representative_mut(v) = v;
            *self.eager_representative_mut(-v) = -v;
        }
        self.units = self.int().propagated;
        let mut rand = Random::new(self.int().stats.congruence.rounds as u64);
        for n in self.nonces.iter_mut() {
            *n = 1u64 | rand.next();
        }
        // The C++ 'Hash' object keeps a reference to 'nonces'.
        self.table.hash.nonces = self.nonces;
        #[cfg(feature = "logging")]
        {
            self.fresh_id = self.int().clause_id as u64;
        }
        self.int().init_noccs();
        self.int().init_occs();
    }

    pub fn init_and_gate_extraction(&mut self) {
        log!(self.internal, "[gate-extraction]");
        let n = self.int().clauses.len();
        for i in 0..n {
            let c = self.int().clauses[i];
            if c.garbage() {
                continue;
            }
            if c.redundant() && c.size() != 2 {
                continue;
            }
            if c.size() > 2 {
                continue;
            }
            debug_assert!(c.size() == 2);
            let lit = c.lit(0);
            let other = c.lit(1);
            *self.int().noccs_mut(lit) += 1;
            *self.int().noccs_mut(other) += 1;
            self.int().watch_clause(c);
        }
    }

    /*----------------------------------------------------------------------*/

    pub fn check_and_gate_implied(&mut self, g: *mut Gate) {
        debug_assert!(self.int().clause.is_empty());
        debug_assert!(gt(g).tag == Gate_Type::And_Gate);
        if self.int().opts.check == 0 {
            return;
        }
        if self.lrat() {
            debug_assert!(gt(g).degenerated_gate != Special_Gate::NORMAL || gt(g).neg_lhs_ids.is_set());
            #[cfg(debug_assertions)]
            {
                let n = gt(g).pos_lhs_ids.len();
                for i in 0..n {
                    let c = gt(g).pos_lhs_ids[i];
                    let mut found = false;
                    for j in 0..c.clause.size() as usize {
                        let lit = c.clause.lit(j);
                        if self.find_eager_representative(lit) == c.current_lit {
                            found = true;
                            break;
                        }
                    }
                    debug_assert!(found);
                }
            }
            return;
        }
        log!(self.internal, g, "checking implied");
        let lhs = gt(g).lhs;
        let not_lhs = -lhs;
        let n = gt(g).rhs.len();
        for i in 0..n {
            let other = gt(g).rhs[i];
            self.check_binary_implied(not_lhs, other);
        }
        self.int().clause = gt(g).rhs.clone();
        self.check_implied();
        self.int().clause.clear();
    }

    pub fn delete_proof_chain(&mut self) {
        if self.int().proof.is_none() {
            debug_assert!(self.chain.is_empty());
            return;
        }
        if self.chain.is_empty() {
            return;
        }
        log!(self.internal, "starting deletion of proof chain");
        debug_assert!(self.int().clause.is_empty());
        let mut id1: u32 = u32::MAX;
        let mut id2: u32 = u32::MAX;
        let mut id: LRAT_ID = 0;

        log!(self.internal, &self.chain, "chain:");
        for i in 0..self.chain.len() {
            let lit = self.chain[i];
            log!(self.internal, "reading {} from chain", lit);
            if id1 == u32::MAX {
                id1 = lit as u32;
                id = id1 as LRAT_ID;
                continue;
            }
            if id2 == u32::MAX {
                id2 = lit as u32;
                id = ((id1 as LRAT_ID) << 32) + id2 as LRAT_ID;
                continue;
            }
            if lit != 0 {
                // parsing the id first
                log!(self.internal, "found {} as literal in chain", lit);
                self.int().clause.push(lit);
            } else {
                debug_assert!(id != 0);
                let internal = self.int();
                let proof = internal.proof.as_mut().unwrap();
                proof.delete_clause_lits(id, false, &internal.clause);
                internal.clause.clear();
                id = 0;
                id1 = u32::MAX;
                id2 = u32::MAX;
            }
        }
        debug_assert!(self.int().clause.is_empty());
        self.chain.clear();
        log!(self.internal, "finished deletion of proof chain");
    }

    /*----------------------------------------------------------------------*/
    // Simplification

    pub fn skip_and_gate(&mut self, g: *mut Gate) -> bool {
        debug_assert!(gt(g).tag == Gate_Type::And_Gate);
        if gt(g).garbage {
            return true;
        }
        let lhs = gt(g).lhs;
        if self.val(lhs) > 0 {
            self.mark_garbage(g);
            return true;
        }

        debug_assert!(gt(g).arity() > 1);
        false
    }

    pub fn skip_xor_gate(&mut self, g: *mut Gate) -> bool {
        debug_assert!(gt(g).tag == Gate_Type::XOr_Gate);
        if gt(g).garbage {
            return true;
        }
        debug_assert!(gt(g).arity() > 1);
        false
    }

    /// `falsifies` defaults to `0` in C++
    /// `clashing` defaults to `0` in C++
    pub fn shrink_and_gate(&mut self, g: *mut Gate, falsifies: i32, clashing: i32) {
        if falsifies != 0 {
            gt(g).rhs.resize(1, 0);
            gt(g).rhs[0] = falsifies;
        } else if clashing != 0 {
            log!(self.internal, g, "gate before clashing on {}", clashing);
            gt(g).rhs.resize(2, 0);
            gt(g).rhs[0] = clashing;
            gt(g).rhs[1] = -clashing;
            log!(self.internal, g, "gate after clashing on {}", clashing);
        }
        gt(g).shrunken = true;
    }

    pub fn update_and_gate_unit_build_lrat_chain(
        &mut self,
        g: *mut Gate,
        src: i32,
        id1: i64,
        id2: i64,
        dst: i32,
        extra_reasons_lit: &mut Vec<i64>,
        extra_reasons_ulit: &mut Vec<i64>,
    ) {
        log!(self.internal, "generate chain for gate boiling down to unit");
        if gt(g).lhs == gt(g).rhs[0] {
            // do not try to produce LRAT chains, we will not need them anyway
            return;
        }

        if !gt(g).neg_lhs_ids.is_set() {
            if gt(g).degenerated_gate == Special_Gate::DEGENERATED_AND
                || gt(g).degenerated_gate == Special_Gate::DEGENERATED_AND_LHS_FALSE
            {
                // can happen for 4 = AND 3 4 (degenerated with only the clause
                // -4 3) with a rewriting 4 -> 1 (unchanged clause) and later 1
                // -> 3 (unchanged clause) but you do not know anymore from the
                // gate that it is degenerated
                debug_assert!(gt(g).pos_lhs_ids.len() == 1);
                let c = gt(g).pos_lhs_ids[0].clause;
                self.push_id_and_rewriting_lrat_unit(
                    c,
                    Rewrite::default(),
                    extra_reasons_ulit,
                    true,
                    Rewrite::default(),
                    0,
                    0,
                );
                return;
            }
            debug_assert!(gt(g).lhs == gt(g).rhs[0] || (gt(g).lhs == src && gt(g).rhs[0] == dst));
            // either degenerated or empty A = A
            debug_assert!(gt(g).pos_lhs_ids.len() <= 1);
            return;
        }
        debug_assert!(gt(g).neg_lhs_ids.is_set());
        debug_assert!(!gt(g).pos_lhs_ids.is_empty());

        let repr_lit = self.find_representative(gt(g).lhs);
        let repr_other = self.find_representative(gt(g).rhs[0]);
        if repr_lit == repr_other {
            log!(self.internal, "skipping already merged");
            return;
        }

        let c = gt(g).neg_lhs_ids.content.clause;
        let lhs = gt(g).lhs;
        self.push_id_and_rewriting_lrat_unit(
            c,
            Rewrite::default(),
            extra_reasons_ulit,
            true,
            Rewrite::default(),
            lhs,
            -dst,
        );
        log!(self.internal, &*extra_reasons_ulit, "lrat chain for negative side");

        self.lrat_chain.clear();

        debug_assert!(!gt(g).pos_lhs_ids.is_empty());
        let n = gt(g).pos_lhs_ids.len();
        for i in 0..n {
            let litId = gt(g).pos_lhs_ids[i];
            let lhs = gt(g).lhs;
            self.push_id_and_rewriting_lrat_unit(
                litId.clause,
                Rewrite::new(src, dst, id1, id2),
                extra_reasons_lit,
                true,
                Rewrite::default(),
                -lhs,
                dst,
            );
        }
        log!(self.internal, &*extra_reasons_lit, "lrat chain for positive side");
    }

    /// `remove_units` defaults to `true` in C++
    pub fn update_and_gate_build_lrat_chain(
        &mut self,
        g: *mut Gate,
        h: *mut Gate,
        extra_reasons_lit: &mut Vec<i64>,
        extra_reasons_ulit: &mut Vec<i64>,
        remove_units: bool,
    ) {
        debug_assert!(g != h);
        log!(self.internal, g, "merging");
        log!(self.internal, h, "with");
        // If the LHS are identical, do not even attempt to build the LRAT
        // chain
        if self.find_representative(gt(g).lhs) == self.find_representative(gt(h).lhs) {
            return;
        }
        // set to same value, don't do anything
        if self.val(gt(g).lhs) != 0 && self.val(gt(g).lhs) == self.val(gt(h).lhs) {
            return;
        }
        let g_tautology = gate_contains(g, gt(g).lhs);
        let h_tautology = gate_contains(h, gt(h).lhs);

        if g_tautology && h_tautology {
            log!(self.internal, "both gates are a tautology");
            // special case: actually we have an equivalence due to binary
            // clauses and all gate clauses (except one binary) are actually
            // tautologies
            let n = gt(g).pos_lhs_ids.len();
            for i in 0..n {
                if gt(g).pos_lhs_ids[i].current_lit == gt(h).lhs {
                    debug_assert!(extra_reasons_lit.is_empty());
                    log!(self.internal, gt(g).pos_lhs_ids[i].clause, "binary clause to push into the reason");
                    let c = gt(g).pos_lhs_ids[i].clause;
                    let lhs = gt(g).lhs;
                    let d = self.produce_rewritten_clause_lrat(c, lhs, remove_units, false);
                    gt(g).pos_lhs_ids[i].clause = d;
                    debug_assert!(!d.is_null());
                    extra_reasons_lit.push(d.id());
                }
            }
            debug_assert!(!extra_reasons_lit.is_empty());
            debug_assert!(extra_reasons_lit.len() == 1);

            let n = gt(h).pos_lhs_ids.len();
            for i in 0..n {
                if gt(h).pos_lhs_ids[i].current_lit == gt(g).lhs {
                    debug_assert!(extra_reasons_ulit.is_empty());
                    debug_assert!(!gt(h).pos_lhs_ids[i].clause.is_null());
                    log!(self.internal, gt(h).pos_lhs_ids[i].clause, "binary clause to push into the reason");
                    let c = gt(h).pos_lhs_ids[i].clause;
                    let lhs = gt(h).lhs;
                    let d = self.produce_rewritten_clause_lrat(c, lhs, remove_units, false);
                    gt(h).pos_lhs_ids[i].clause = d;
                    debug_assert!(!d.is_null());
                    extra_reasons_ulit.push(d.id());
                }
            }
            debug_assert!(!extra_reasons_ulit.is_empty());
            debug_assert!(extra_reasons_ulit.len() == 1);
            return;
        }

        let produce_unit_due_to_both_degenerated = (g_tautology
            && self.val(gt(h).lhs) < 0
            && gt(h).degenerated_gate == Special_Gate::DEGENERATED_AND_LHS_FALSE)
            || (h_tautology
                && self.val(gt(g).lhs) < 0
                && gt(g).degenerated_gate == Special_Gate::DEGENERATED_AND_LHS_FALSE);

        if produce_unit_due_to_both_degenerated {
            log!(self.internal, "one gate is a tautology and the other is a unit: producing reason for unit");
            let tauto = if g_tautology { g } else { h };
            let other = if g_tautology { h } else { g };
            debug_assert!((gt(tauto).degenerated_gate & Special_Gate::DEGENERATED_AND) != 0);
            log!(self.internal, tauto, "starting lrat from tauto gate");
            let n = gt(tauto).pos_lhs_ids.len();
            for i in 0..n {
                let c = gt(tauto).pos_lhs_ids[i].clause;
                let lhs = gt(tauto).lhs;
                let d = self.produce_rewritten_clause_lrat(c, lhs, remove_units, false);
                gt(tauto).pos_lhs_ids[i].clause = d;
                if !d.is_null() {
                    extra_reasons_lit.push(d.id());
                }
            }
            log!(self.internal, tauto, "now creating lrat with other gate");
            // if tauto can also be a tautology: neg_lhs_ids
            // otherwise the clause is in pos_lhs_ids
            let n = gt(other).pos_lhs_ids.len();
            for i in 0..n {
                debug_assert!(extra_reasons_ulit.is_empty());
                debug_assert!(!gt(other).pos_lhs_ids[i].clause.is_null());
                log!(self.internal, gt(other).pos_lhs_ids[i].clause, "binary clause to push into the reason");
                let c = gt(other).pos_lhs_ids[i].clause;
                let d = self.produce_rewritten_clause_lrat(c, 0, remove_units, false);
                gt(other).pos_lhs_ids[i].clause = d;
                if !d.is_null() {
                    extra_reasons_lit.push(d.id());
                }
            }
            if gt(other).neg_lhs_ids.is_set() {
                let litId = gt(other).neg_lhs_ids.content;
                if litId.current_lit == gt(tauto).lhs || litId.current_lit == -gt(tauto).lhs || true {
                    debug_assert!(extra_reasons_ulit.is_empty());
                    debug_assert!(!litId.clause.is_null());
                    log!(self.internal, litId.clause, "binary clause to push into the reason");
                    let d = self.produce_rewritten_clause_lrat(litId.clause, 0, remove_units, false);
                    gt(other).neg_lhs_ids.content.clause = d;
                    if !d.is_null() {
                        extra_reasons_lit.push(d.id());
                    }
                }
            }
            return;
        }

        if g_tautology || h_tautology {
            // special case: actually we have an equivalence due to binary
            // clauses and some of the clauses from the gate are actually
            // tautologies
            debug_assert!(g_tautology != h_tautology);
            let tauto = if g_tautology { g } else { h };
            let other = if g_tautology { h } else { g };
            log!(self.internal, tauto, "one gate is a tautology");
            debug_assert!(tauto != other);
            debug_assert!(tauto == h || tauto == g);

            let (extra_reasons_tauto, extra_reasons_other): (&mut Vec<i64>, &mut Vec<i64>) =
                if !g_tautology { (extra_reasons_lit, extra_reasons_ulit) } else { (extra_reasons_ulit, extra_reasons_lit) };

            // one direction: the binary clause already exists
            let n = gt(other).pos_lhs_ids.len();
            for i in 0..n {
                if gt(other).pos_lhs_ids[i].current_lit == gt(tauto).lhs {
                    debug_assert!(!gt(other).pos_lhs_ids[i].clause.is_null());
                    debug_assert!(extra_reasons_tauto.is_empty());
                    log!(self.internal, gt(other).pos_lhs_ids[i].clause, "binary clause to push into the reason");
                    let c = gt(other).pos_lhs_ids[i].clause;
                    let lhs = gt(other).lhs;
                    let d = self.produce_rewritten_clause_lrat(c, lhs, remove_units, false);
                    gt(other).pos_lhs_ids[i].clause = d;
                    debug_assert!(!d.is_null());
                    extra_reasons_tauto.push(d.id());
                }
            }
            debug_assert!(!extra_reasons_tauto.is_empty());

            // other direction, we have to resolve
            log!(self.internal, tauto, "now the other direction");
            // The C++ code erases (remove_if/erase) the null clauses of
            // 'tauto->pos_lhs_ids' while iterating over it with a range-based
            // for loop, whose iterators still cover the original length (the
            // vector never reallocates when shrinking).  We reproduce that
            // exactly by iterating over the original number of slots of the
            // buffer (whose stale tail keeps the moved-from values).
            let original_len = gt(tauto).pos_lhs_ids.len();
            let mut cur_len = original_len;
            let buf: *mut LitClausePair = gt(tauto).pos_lhs_ids.as_mut_ptr();
            for i in 0..original_len {
                // SAFETY: 'i < original_len <= capacity' and the slots were
                // initialized (LitClausePair is Copy, erasing never frees).
                let slot = unsafe { &mut *buf.add(i) };
                debug_assert!(!slot.clause.is_null());
                log!(
                    self.internal,
                    slot.clause,
                    "binary clause from {} to push into the reason [avoiding {}]",
                    slot.current_lit,
                    gt(tauto).lhs
                );
                if slot.current_lit != gt(tauto).lhs {
                    log!(self.internal, slot.clause, "binary clause to push into the reason");
                    debug_assert!(!slot.clause.is_null());
                    let c = slot.clause;
                    let lhs = gt(tauto).lhs;
                    let d = self.produce_rewritten_clause_lrat(c, lhs, remove_units, false);
                    // SAFETY: as above.
                    let slot = unsafe { &mut *buf.add(i) };
                    slot.clause = d;
                    if d.is_null() {
                        // degenerated but does not know yet
                        continue;
                    }
                    debug_assert!(!d.is_null());
                    extra_reasons_other.push(d.id());
                }
                // tauto->pos_lhs_ids.erase (remove_if (..., !p.clause), end)
                let mut k = 0usize;
                for j in 0..cur_len {
                    // SAFETY: 'j < cur_len <= original_len'.
                    let p = unsafe { *buf.add(j) };
                    if !p.clause.is_null() {
                        if k != j {
                            // SAFETY: 'k < j'.
                            unsafe { *buf.add(k) = p };
                        }
                        k += 1;
                    }
                }
                cur_len = k;
            }
            // SAFETY: 'cur_len <= original_len' initialized elements.
            unsafe { gt(tauto).pos_lhs_ids.set_len(cur_len) };
            debug_assert!(!extra_reasons_other.is_empty());
            let mut opt = gt(other).neg_lhs_ids;
            let lhs = gt(other).lhs;
            self.produce_rewritten_clause_lrat_and_clean_optional(&mut opt, lhs, remove_units);
            gt(other).neg_lhs_ids = opt;
            debug_assert!(gt(other).neg_lhs_ids.is_set());
            let c = gt(other).neg_lhs_ids.content.clause;
            self.push_id_on_chain(extra_reasons_other, c);
            debug_assert!(!extra_reasons_tauto.is_empty());
            debug_assert!(!extra_reasons_other.is_empty());
            return;
        }

        let g_degenerated = gt(g).degenerated_gate == Special_Gate::DEGENERATED_AND
            || gt(g).degenerated_gate == Special_Gate::DEGENERATED_AND_LHS_FALSE;
        let h_degenerated = gt(h).degenerated_gate == Special_Gate::DEGENERATED_AND
            || gt(h).degenerated_gate == Special_Gate::DEGENERATED_AND_LHS_FALSE;

        debug_assert!(!(g_degenerated && h_degenerated));
        if g_degenerated || h_degenerated {
            let tauto = if g_degenerated { g } else { h };
            let other = if g_degenerated { h } else { g };
            log!(self.internal, tauto, "one gate is degenerated");
            debug_assert!(tauto != other);
            debug_assert!(tauto == h || tauto == g);

            let extra_reasons_tauto: &mut Vec<i64> = if !g_tautology { extra_reasons_lit } else { extra_reasons_ulit };

            // start with the other clauses for LRAT
            let lhs = gt(other).lhs;
            self.produce_rewritten_clause_lrat_and_clean(&mut gt(other).pos_lhs_ids, lhs, true, false);
            let n = gt(other).pos_lhs_ids.len();
            for i in 0..n {
                let c = gt(other).pos_lhs_ids[i].clause;
                log!(self.internal, c, "pushing clause from other");
                self.push_id_on_chain(extra_reasons_tauto, c);
            }
            // one direction: the binary clause already exists
            let lhs = gt(other).lhs;
            self.produce_rewritten_clause_lrat_and_clean(&mut gt(tauto).pos_lhs_ids, lhs, true, false);
            let n = gt(tauto).pos_lhs_ids.len();
            for i in 0..n {
                let c = gt(tauto).pos_lhs_ids[i].clause;
                log!(self.internal, c, "pushing clause from tauto");
                self.push_id_on_chain(extra_reasons_tauto, c);
            }
            log!(self.internal, &*extra_reasons_tauto, "lrat chain for positive side");
            return;
        }

        // default: resolve all clauses
        // first rewrite
        let hl = gt(h).lhs;
        self.produce_rewritten_clause_lrat_and_clean(&mut gt(h).pos_lhs_ids, -hl, remove_units, false);
        debug_assert!(self.int().clause.is_empty());
        let mut opt = gt(h).neg_lhs_ids;
        self.produce_rewritten_clause_lrat_and_clean_optional(&mut opt, -hl, remove_units);
        gt(h).neg_lhs_ids = opt;
        debug_assert!(self.int().clause.is_empty());
        let gl = gt(g).lhs;
        self.produce_rewritten_clause_lrat_and_clean(&mut gt(g).pos_lhs_ids, -gl, remove_units, false);
        debug_assert!(self.int().clause.is_empty());
        let mut opt = gt(g).neg_lhs_ids;
        self.produce_rewritten_clause_lrat_and_clean_optional(&mut opt, -gl, remove_units);
        gt(g).neg_lhs_ids = opt;
        debug_assert!(self.int().clause.is_empty());

        let hp = gt(h).pos_lhs_ids.clone();
        self.push_id_on_chain_pairs(extra_reasons_ulit, &hp);
        let gn = gt(g).neg_lhs_ids;
        self.push_id_on_chain_optional(extra_reasons_ulit, &gn);
        self.lrat_chain.clear();
        log!(self.internal, &*extra_reasons_ulit, "lrat chain for negative side");

        let gp = gt(g).pos_lhs_ids.clone();
        self.push_id_on_chain_pairs(extra_reasons_lit, &gp);
        let hn = gt(h).neg_lhs_ids;
        self.push_id_on_chain_optional(extra_reasons_lit, &hn);

        self.lrat_chain.clear();
        log!(self.internal, &*extra_reasons_lit, "lrat chain for positive side");
        debug_assert!(!extra_reasons_lit.is_empty());
        debug_assert!(!extra_reasons_ulit.is_empty());
    }

    /// `falsifies` defaults to `0` in C++
    /// `clashing` defaults to `0` in C++
    pub fn update_and_gate(
        &mut self,
        g: *mut Gate,
        it: GatesIterator,
        src: i32,
        dst: i32,
        id1: i64,
        id2: i64,
        falsifies: i32,
        clashing: i32,
    ) {
        log!(self.internal, g, "update and gate of arity {}", gt(g).arity());
        debug_assert!(self.lrat_chain.is_empty());
        let mut garbage = true;
        if gt(g).arity() == 1 && self.val(gt(g).lhs) != 0 && self.val(gt(g).lhs) == self.val(gt(g).rhs[0]) {
            self.mark_garbage(g);
            return;
        }
        if falsifies != 0 || clashing != 0 {
            let mut unit = -gt(g).lhs;
            if unit == src {
                unit = dst;
            } else if unit == -src {
                unit = -dst;
            }
            if self.lrat() {
                self.learn_congruence_unit_falsifies_lrat_chain(g, src, dst, clashing, falsifies, unit);
            }
            let mut other = -unit;
            if gt(g).degenerated_gate == Special_Gate::DEGENERATED_AND
                || gt(g).degenerated_gate == Special_Gate::DEGENERATED_AND_LHS_FALSE
            {
                other = self.find_eager_representative_and_compress(-unit);
                if self.lrat() && -unit != other {
                    debug_assert!(self.int().lrat_chain.is_empty());
                    let id = self.eager_representative_id(-unit);
                    self.int().lrat_chain.push(id);
                    for i in 0..self.lrat_chain.len() {
                        let id = self.lrat_chain[i];
                        self.int().lrat_chain.push(id);
                    }
                    self.lrat_chain.clear();
                    std::mem::swap(&mut self.int().lrat_chain, &mut self.lrat_chain);
                }
            }
            let _ = other;
            self.learn_congruence_unit(unit, false, false);
            if self.lrat() {
                self.lrat_chain.clear();
            }
        } else if gt(g).arity() == 1 {
            let v = self.val(gt(g).lhs);
            if v > 0 {
                if self.lrat() {
                    let lhs = gt(g).lhs;
                    self.learn_congruence_unit_falsifies_lrat_chain(g, src, dst, 0, 0, lhs);
                }
                let r = gt(g).rhs[0];
                self.learn_congruence_unit(r, false, false);
                if self.lrat() {
                    self.lrat_chain.clear();
                }
            } else if v < 0 {
                if self.lrat() {
                    self.learn_congruence_unit_when_lhs_set(g, src, id1, id2, dst);
                }
                let r = gt(g).rhs[0];
                self.learn_congruence_unit(-r, false, false);
                if self.lrat() {
                    self.lrat_chain.clear();
                }
            } else {
                let mut extra_reasons_lit: Vec<LRAT_ID> = Vec::new();
                let mut extra_reasons_ulit: Vec<LRAT_ID> = Vec::new();
                if self.lrat() {
                    let r = gt(g).rhs[0];
                    self.update_and_gate_unit_build_lrat_chain(
                        g,
                        src,
                        id1,
                        id2,
                        r,
                        &mut extra_reasons_lit,
                        &mut extra_reasons_ulit,
                    );
                }
                let (lhs, r) = (gt(g).lhs, gt(g).rhs[0]);
                if self.merge_literals_gates(g, g, lhs, r, &extra_reasons_lit, &extra_reasons_ulit) {
                    self.int().stats.congruence.unaries += 1;
                    self.int().stats.congruence.unary_and += 1;
                }
            }
        } else {
            debug_assert!(gt(g).arity() > 1);
            self.sort_literals_by_var(&mut gt(g).rhs);
            let h = self.find_and_lits(&mut gt(g).rhs, g);
            debug_assert!(g != h);
            if !h.is_null() {
                debug_assert!(garbage);
                let mut extra_reasons_lit2: Vec<LRAT_ID> = Vec::new();
                let mut extra_reasons_ulit2: Vec<LRAT_ID> = Vec::new();
                if self.lrat() {
                    self.update_and_gate_build_lrat_chain(g, h, &mut extra_reasons_lit2, &mut extra_reasons_ulit2, true);
                }
                let (gl, hl) = (gt(g).lhs, gt(h).lhs);
                if self.merge_literals_gates(g, h, gl, hl, &extra_reasons_lit2, &extra_reasons_ulit2) {
                    self.int().stats.congruence.ands += 1;
                }
            } else {
                if gt(g).indexed {
                    debug_assert!(it.is_some());
                    log!(self.internal, g, "removing from table");
                    let it = it.expect("indexed gate without table iterator");
                    self.table.erase(it);
                }
                log!(self.internal, g, "inserting gate into table");
                debug_assert!(self.table.count(g) == 0);
                self.table.insert(g);
                gt(g).indexed = true;
                garbage = false;
                if self.lrat() {
                    self.lrat_chain.clear();
                }
            }
        }

        if garbage && !self.int().unsat {
            self.mark_garbage(g);
        }
    }

    pub fn update_xor_gate(&mut self, g: *mut Gate, git: GatesIterator) {
        debug_assert!(gt(g).tag == Gate_Type::XOr_Gate);
        debug_assert!(!self.int().unsat && self.chain.is_empty());
        log!(self.internal, g, "updating");
        let mut garbage = true;
        debug_assert!(gt(g).arity() == 0 || self.int().clause.is_empty());
        debug_assert!(self.clause.is_empty());
        if gt(g).arity() == 0 {
            if !self.int().clause.is_empty() {
                debug_assert!(
                    self.int().proof.is_none()
                        || (self.int().clause.len() == 1 && *self.int().clause.last().unwrap() == -gt(g).lhs)
                );
                debug_assert!(!self.lrat() || !self.lrat_chain.is_empty());
                self.int().clause.clear();
            } else if self.lrat() {
                let src = gt(g).pos_lhs_ids.clone();
                let lhs = gt(g).lhs;
                self.simplify_unit_xor_lrat_clauses(&src, lhs);
                debug_assert!(!self.clause.is_empty() && *self.clause.last().unwrap() == -gt(g).lhs);
                self.clause.clear();
            }

            if self.lrat() && self.val(-gt(g).lhs) < 0 {
                let id = self.int().unit_id(gt(g).lhs);
                self.int().lrat_chain.push(id);
                for i in 0..self.lrat_chain.len() {
                    let id = self.lrat_chain[i];
                    self.int().lrat_chain.push(id);
                }
                self.lrat_chain.clear();
                self.int().learn_empty_clause();
            } else {
                let lhs = gt(g).lhs;
                self.learn_congruence_unit(-lhs, false, false);
            }

            debug_assert!(self.clause.is_empty());
        } else if gt(g).arity() == 1 {
            let mut reasons_implication: Vec<LRAT_ID> = Vec::new();
            let mut reasons_back: Vec<LRAT_ID> = Vec::new();
            if self.lrat() {
                let mut first: Vec<LitClausePair> = Vec::new();
                let src = gt(g).pos_lhs_ids.clone();
                let lhs = gt(g).lhs;
                self.simplify_and_sort_xor_lrat_clauses(&src, &mut first, lhs, 0, false);
                gt(g).pos_lhs_ids = first;
                debug_assert!(gt(g).pos_lhs_ids.len() == 2);
                reasons_implication.push(gt(g).pos_lhs_ids[0].clause.id());
                reasons_back.push(gt(g).pos_lhs_ids[1].clause.id());
            }
            let v = self.val(gt(g).lhs);
            if v > 0 {
                if self.lrat() {
                    let lhs = gt(g).lhs;
                    self.push_lrat_unit(lhs);
                    self.lrat_chain.push(gt(g).pos_lhs_ids[0].clause.id());
                }
                let r = gt(g).rhs[0];
                self.learn_congruence_unit(r, false, false);
            } else if v < 0 {
                if self.lrat() {
                    let lhs = gt(g).lhs;
                    self.push_lrat_unit(-lhs);
                    self.lrat_chain.push(gt(g).pos_lhs_ids[1].clause.id());
                }
                let r = gt(g).rhs[0];
                self.learn_congruence_unit(-r, false, false);
            } else {
                let (lhs, r) = (gt(g).lhs, gt(g).rhs[0]);
                if self.merge_literals(lhs, r, &reasons_implication, &reasons_back) {
                    self.int().stats.congruence.unaries += 1;
                    self.int().stats.congruence.unary_and += 1;
                }
            }
            debug_assert!(self.clause.is_empty());
        } else {
            let h = self.find_xor_gate(g);
            if !h.is_null() {
                debug_assert!(garbage);
                let mut reasons_implication: Vec<LRAT_ID> = Vec::new();
                let mut reasons_back: Vec<LRAT_ID> = Vec::new();
                let clauses2 = gt(h).pos_lhs_ids.clone();
                let (gl, hl) = (gt(g).lhs, gt(h).lhs);
                self.add_xor_matching_proof_chain(g, gl, &clauses2, hl, &mut reasons_implication, &mut reasons_back);
                let (gl, hl) = (gt(g).lhs, gt(h).lhs);
                if self.merge_literals_gates(g, h, gl, hl, &reasons_implication, &reasons_back) {
                    self.int().stats.congruence.xors += 1;
                }
                self.delete_proof_chain();
            } else {
                if gt(g).indexed {
                    self.remove_gate_at(git);
                }
                log!(self.internal, g, "reinserting in table");
                self.table.insert(g);
                gt(g).indexed = true;
                debug_assert!(self.table.find(g).is_some());
                garbage = false;
            }
            debug_assert!(self.clause.is_empty());
        }
        if garbage && !self.int().unsat {
            self.mark_garbage(g);
        }
        debug_assert!(self.clause.is_empty());
    }

    pub fn simplify_and_gate(&mut self, g: *mut Gate) {
        if self.skip_and_gate(g) {
            return;
        }
        let git: GatesIterator = if gt(g).indexed { self.table.find(g) } else { None };
        debug_assert!(!gt(g).indexed || git.is_some());
        log!(self.internal, g, "simplifying");
        let mut falsifies = 0;
        let mut it = 0usize;
        let mut ulhs_in_rhs = false;
        if gt(g).degenerated_gate != Special_Gate::NORMAL {
            let old_lhs = gt(g).lhs;
            let l = self.find_eager_representative(old_lhs);
            gt(g).lhs = l;
            for c in gt(g).pos_lhs_ids.iter_mut() {
                if c.current_lit == old_lhs {
                    c.current_lit = l;
                }
                if c.current_lit == -old_lhs {
                    c.current_lit = -l;
                }
            }
        }
        let n = gt(g).rhs.len();
        for i in 0..n {
            let lit = gt(g).rhs[i];
            let v = self.val(lit);
            if v > 0 {
                continue;
            }
            if v < 0 {
                falsifies = lit;
                continue;
            }
            if lit == -gt(g).lhs {
                ulhs_in_rhs = true;
            }
            gt(g).rhs[it] = lit;
            it += 1;
            if lit == gt(g).lhs {
                gt(g).degenerated_gate = Special_Gate::DEGENERATED_AND;
            }
            if lit == -gt(g).lhs {
                gt(g).degenerated_gate = Special_Gate::DEGENERATED_AND;
            }
        }

        if self.lrat() {
            // updating reasons
            let mut i = 0usize;
            let size = gt(g).pos_lhs_ids.len();
            for j in 0..size {
                log!(self.internal, "looking at {} [{} {}]", gt(g).pos_lhs_ids[j].current_lit, i, j);
                gt(g).pos_lhs_ids[i] = gt(g).pos_lhs_ids[j];
                if gt(g).degenerated_gate == 0
                    && self.val(gt(g).pos_lhs_ids[i].current_lit) != 0
                    && gt(g).pos_lhs_ids[i].current_lit != falsifies
                {
                    continue;
                }
                log!(self.internal, "keeping {} [{} {}]", gt(g).pos_lhs_ids[i].current_lit, i, j);
                i += 1;
            }
            log!(self.internal, "resizing to {}", i);
            gt(g).pos_lhs_ids.resize(i, LitClausePair::default());
        }

        // can be equal when ITE are converted to ands leading to
        debug_assert!(it <= gt(g).rhs.len());
        log!(self.internal, g, "shrunken");

        gt(g).shrunken = true;
        gt(g).rhs.resize(it, 0);

        log!(self.internal, g, "shrunken");
        self.shrink_and_gate(g, falsifies, 0);

        self.update_and_gate(g, git, 0, 0, 0, 0, falsifies, 0);
        self.int().stats.congruence.simplified_ands += 1;
        self.int().stats.congruence.simplified += 1;

        if ulhs_in_rhs {
            // missing in Kissat, TODO: port back
            debug_assert!(gate_contains(g, -gt(g).lhs));
            if self.lrat() {
                let n = gt(g).pos_lhs_ids.len();
                for i in 0..n {
                    let litId = gt(g).pos_lhs_ids[i];
                    if litId.current_lit == gt(g).lhs {
                        self.compute_rewritten_clause_lrat_simple(litId.clause, 0);
                        break;
                    }
                }
            }
            let lhs = gt(g).lhs;
            self.learn_congruence_unit(-lhs, false, false);
        }
    }

    pub fn simplify_gate(&mut self, g: *mut Gate) -> bool {
        match gt(g).tag {
            Gate_Type::And_Gate => self.simplify_and_gate(g),
            Gate_Type::XOr_Gate => self.simplify_xor_gate(g),
            Gate_Type::ITE_Gate => self.simplify_ite_gate(g),
        }
        debug_assert!(self.lrat_chain.is_empty());
        !self.int().unsat
    }

    pub fn simplify_gates(&mut self, lit: i32) -> bool {
        let idx = self.vlit(lit);
        let n = self.gtab[idx].len();
        for i in 0..n {
            let g = self.gtab[idx][i];
            debug_assert!(self.lrat_chain.is_empty());
            debug_assert!(self.clause.is_empty());
            if !self.simplify_gate(g) {
                return false;
            }
        }
        true
    }

    /*----------------------------------------------------------------------*/
    // AND gates

    /// `except` defaults to `nullptr` in C++
    pub fn find_and_lits(&mut self, rhs: &mut Vec<i32>, except: *mut Gate) -> *mut Gate {
        debug_assert!({
            let internal: &Internal = self.int();
            is_sorted_by(rhs, |&a, &b| sort_literals_by_var_smaller(internal, a, b))
        });
        self.find_gate_lits(rhs, Gate_Type::And_Gate, except)
    }

    // search for the gate in the hash-table.  We cannot use find, as we might
    // be changing a gate, so there might be 2 gates with the same LHS (the
    // one we are changing and the other we are looking for)
    /// `except` defaults to `nullptr` in C++
    pub fn find_gate_lits(&mut self, rhs: &mut Vec<i32>, typ: Gate_Type, except: *mut Gate) -> *mut Gate {
        let dummy = self.dummy_search_gate;
        #[cfg(feature = "logging")]
        {
            gt(dummy).id = 0;
        }
        let mut h: *mut Gate = std::ptr::null_mut();
        gt(dummy).tag = typ;
        // 'rhs' might be the right-hand side of a gate in the table ('g->rhs'),
        // which the table then sees swapped (as in C++), so only use raw
        // pointers while the table is searched.
        let rhs_ptr: *mut Vec<i32> = rhs;
        // SAFETY: both vectors are alive and distinct.
        unsafe { std::ptr::swap(&mut (*dummy).rhs, rhs_ptr) };
        debug_assert!(gt(dummy).lhs == 0);
        debug_assert!(!gt(dummy).garbage);

        if except.is_null() || !gt(except).indexed {
            let git = self.table.find(dummy);
            if let Some(it) = git {
                h = self.table.get(it);
            }
            debug_assert!(except.is_null() || h != except);
        } else {
            // equal_range for unique keys is [find (k), next (find (k)))
            if let Some(it) = self.table.find(dummy) {
                let x = self.table.get(it);
                log!(self.internal, x, "checking gate in the table");
                if x != except && gt(x).tag == typ && gt(x).rhs == gt(dummy).rhs {
                    h = x;
                }
            }
        }

        // SAFETY: as above.
        unsafe { std::ptr::swap(&mut (*dummy).rhs, rhs_ptr) };
        if !h.is_null() {
            log!(self.internal, dummy, "searching");
            log!(self.internal, h, "already existing");
            h
        } else {
            log!(self.internal, &gt(dummy).rhs, "gate not found in table");
            std::ptr::null_mut()
        }
    }

    pub fn new_and_gate(&mut self, base_clause: CRef, lhs: i32) -> *mut Gate {
        self.rhs.clear();

        for i in 0..self.lits.len() {
            let lit = self.lits[i];
            if lhs != lit {
                debug_assert!(lhs != -lit);
                self.rhs.push(-lit);
            }
        }

        debug_assert!(self.rhs.len() + 1 == self.lits.len());
        let mut rhs = std::mem::take(&mut self.rhs);
        self.sort_literals_by_var(&mut rhs);

        let h = self.find_and_lits(&mut rhs, std::ptr::null_mut());
        self.rhs = rhs;
        let g = new_gate();
        gt(g).lhs = lhs;
        gt(g).tag = Gate_Type::And_Gate;
        if self.lrat() {
            gt(g).neg_lhs_ids.set(LitClausePair::new(lhs, base_clause));
            for i in 0..self.lrat_chain_and_gate.len() {
                let x = self.lrat_chain_and_gate[i];
                gt(g).pos_lhs_ids.push(x);
            }
            #[cfg(feature = "logging")]
            {
                let mut result: Vec<LRAT_ID> = gt(g).pos_lhs_ids.iter().map(|x| x.clause.id()).collect();
                log!(self.internal, &result, "lrat chain positive ({}):", lhs);
                result.clear();
                if gt(g).neg_lhs_ids.is_set() {
                    let c = gt(g).neg_lhs_ids.content;
                    result.push(c.clause.id());
                }
                log!(self.internal, &result, "lrat chain negative ({}):", lhs);
            }
        }

        if self.lrat() {
            self.lrat_chain_and_gate.clear();
        }

        if !h.is_null() {
            let mut reasons_lrat_src: Vec<LRAT_ID> = Vec::new();
            let mut reasons_lrat_usrc: Vec<LRAT_ID> = Vec::new();
            if self.lrat() {
                self.merge_and_gate_lrat_produce_lrat(g, h, &mut reasons_lrat_src, &mut reasons_lrat_usrc, true);
            }
            let hl = gt(h).lhs;
            if self.merge_literals_gates(g, h, lhs, hl, &reasons_lrat_src, &reasons_lrat_usrc) {
                log!(self.internal, "found merged literals");
                self.int().stats.congruence.ands += 1;
            }
            delete_gate(g);
            return std::ptr::null_mut();
        } else {
            gt(g).rhs = self.rhs.clone();
            // otherwise we need intermediate clauses
            debug_assert!(!self.lrat() || gt(g).pos_lhs_ids.len() == gt(g).arity());
            gt(g).garbage = false;
            gt(g).indexed = true;
            gt(g).shrunken = false;

            self.table.insert(g);
            self.int().stats.congruence.gates += 1;
            #[cfg(feature = "logging")]
            {
                gt(g).id = self.fresh_id;
                self.fresh_id += 1;
            }
            log!(self.internal, g, "creating new");
            let n = gt(g).rhs.len();
            for i in 0..n {
                let lit = gt(g).rhs[i];
                self.connect_goccs(g, lit);
            }
        }
        self.int().stats.congruence.and_gates += 1;
        g
    }

    pub fn find_first_and_gate(&mut self, base_clause: CRef, lhs: i32) -> *mut Gate {
        debug_assert!(self.int().analyzed.is_empty());
        let not_lhs = -lhs;
        log!(self.internal, "trying to find AND gate with first LHS {}", lhs);
        log!(
            self.internal,
            "negated LHS {} occurs in {} binary clauses",
            not_lhs,
            self.int().occs(not_lhs).len()
        );
        let mut matched: u32 = 0;

        let arity = self.lits.len() - 1;

        let n = self.int().watches(not_lhs).len();
        for i in 0..n {
            let w = self.int().watches(not_lhs)[i];
            log!(self.internal, w.clause, "checking clause for candidates");
            debug_assert!(w.binary());
            debug_assert!(w.clause.size() == 2);
            debug_assert!(w.clause.lit(0) == -lhs || w.clause.lit(1) == -lhs);
            let other = w.blit;
            let mark = self.mk(other);
            if mark != 0 {
                log!(self.internal, "marking {} mu2", other);
                matched += 1;
                debug_assert!(!(mark & 2) != 0);
                self.set_mk(other, mark | 2);
                self.int().analyzed.push(other);
                self.set_mu2_reason(other, w.clause);
                if self.lrat() {
                    self.lrat_chain_and_gate.push(LitClausePair::new(other, w.clause));
                }
            }
        }

        log!(self.internal, "found {} initial LHS candidates", self.int().analyzed.len());
        if (matched as usize) < arity {
            if self.lrat() {
                self.lrat_chain_and_gate.clear();
            }
            return std::ptr::null_mut();
        }

        let g = self.new_and_gate(base_clause, lhs);

        if self.lrat() {
            self.lrat_chain_and_gate.clear();
        }
        g
    }

    pub fn learn_binary_tmp_or_full_clause(&mut self, a: i32, b: i32) -> CRef {
        let mut eq1;
        if self.lrat() {
            eq1 = self.add_tmp_binary_clause(a, b);
            eq1 = self.maybe_promote_tmp_binary_clause(eq1);
        } else {
            eq1 = self.maybe_add_binary_clause(a, b);
        }
        eq1
    }

    pub fn maybe_add_binary_clause(&mut self, a: i32, b: i32) -> CRef {
        debug_assert!(self.int().clause.is_empty());
        debug_assert!(self.int().lrat_chain.is_empty());
        debug_assert!(!self.lrat());
        debug_assert!(self.lrat_chain.is_empty());
        log!(self.internal, "learning binary clause {} {}", a, b);
        if self.int().unsat {
            return CRef::NULL;
        }
        if a == -b {
            return CRef::NULL;
        }
        if !self.lrat() {
            let a_value = self.val(a);
            if a_value > 0 {
                return CRef::NULL;
            }
            let b_value = self.val(b);
            if b_value > 0 {
                return CRef::NULL;
            }
            let mut unit = 0;
            if a == b {
                unit = a;
            } else if a_value < 0 && b_value == 0 {
                unit = b;
            } else if a_value == 0 && b_value < 0 {
                unit = a;
            }
            if unit != 0 {
                log!(self.internal, "clause reduced to unit {}", unit);
                self.learn_congruence_unit(unit, false, false);
                return CRef::NULL;
            }
            debug_assert!(a_value == 0);
            debug_assert!(b_value == 0);
        }
        self.add_binary_clause(a, b)
    }

    pub fn add_binary_clause(&mut self, a: i32, b: i32) -> CRef {
        debug_assert!(self.int().clause.is_empty());
        self.int().clause.push(a);
        self.int().clause.push(b);
        if self.lrat() {
            debug_assert!(!self.lrat_chain.is_empty());
            debug_assert!(self.int().lrat_chain.is_empty());
            std::mem::swap(&mut self.int().lrat_chain, &mut self.lrat_chain);
        }
        log!(self.internal, &self.int().lrat_chain, "chain");
        let full_watching = self.full_watching;
        let res = self.int().new_hyper_ternary_resolved_clause_and_watch(false, full_watching);
        let already_sorted = self.int().vlit(a) < self.int().vlit(b);
        self.binaries.push(CompactBinary::new(
            res,
            res.id(),
            if already_sorted { a } else { b },
            if already_sorted { b } else { a },
        ));
        if !self.full_watching {
            self.new_unwatched_binary_clauses.push(res);
        }
        log!(self.internal, res, "learning clause");
        self.int().clause.clear();
        if self.lrat() {
            self.int().lrat_chain.clear();
        }
        debug_assert!(self.int().clause.is_empty());
        debug_assert!(self.int().lrat_chain.is_empty());
        res
    }

    pub fn check_not_tmp_binary_clause(&mut self, c: CRef) {
        #[cfg(debug_assertions)]
        {
            debug_assert!(self.lrat());
            debug_assert!(self.int().lrat_chain.is_empty());
            debug_assert!(c.size() == 2);
            if self.val(c.lit(0)) != 0 || self.val(c.lit(1)) != 0 {
                return;
            }
            debug_assert!(!self.extra_clauses.contains(&c));
        }
        let _ = c;
    }

    pub fn maybe_promote_tmp_binary_clause(&mut self, c: CRef) -> CRef {
        debug_assert!(self.lrat());
        debug_assert!(self.int().lrat_chain.is_empty());
        debug_assert!(c.size() == 2);
        log!(self.internal, c, "promoting tmp");
        #[cfg(debug_assertions)]
        {
            debug_assert!(self.extra_clauses.contains(&c));
        }
        if self.val(c.lit(0)) != 0 || self.val(c.lit(1)) != 0 {
            return c;
        }
        self.lrat_chain.push(c.id());
        let res = self.add_binary_clause(c.lit(0), c.lit(1));
        log!(self.internal, res, "promoted to");
        res
    }

    pub fn add_tmp_binary_clause(&mut self, a: i32, b: i32) -> CRef {
        debug_assert!(self.int().clause.is_empty());
        debug_assert!(self.int().lrat_chain.is_empty());
        debug_assert!(self.lrat());
        log!(self.internal, "learning tmp binary clause {} {}", a, b);
        if self.int().unsat {
            return CRef::NULL;
        }
        if a == -b {
            return CRef::NULL;
        }
        debug_assert!(self.int().clause.is_empty());
        self.int().clause.push(a);
        self.int().clause.push(b);
        if self.lrat() {
            debug_assert!(!self.lrat_chain.is_empty());
            debug_assert!(self.int().lrat_chain.is_empty());
        }
        log!(self.internal, &self.lrat_chain, "chain");
        let res = self.new_tmp_clause_internal();
        self.int().clause.clear();
        if self.lrat() {
            self.lrat_chain.clear();
        }
        debug_assert!(self.int().clause.is_empty());
        debug_assert!(self.int().lrat_chain.is_empty());
        log!(self.internal, res, "promoted to");
        res
    }

    pub fn find_remaining_and_gate(&mut self, base_clause: CRef, lhs: i32) -> *mut Gate {
        let not_lhs = -lhs;

        if self.mk(not_lhs) < 2 {
            log!(self.internal, "skipping no-candidate LHS {} ({})", lhs, self.mk(not_lhs));
            return std::ptr::null_mut();
        }

        log!(self.internal, "trying to find AND gate with remaining LHS {}", loglit!(self.internal, lhs));
        log!(
            self.internal,
            "negated LHS {} occurs times in {} binary clauses",
            loglit!(self.internal, not_lhs),
            self.int().noccs(-lhs)
        );

        let arity = self.lits.len() - 1;
        let mut matched: usize = 0;
        debug_assert!(1 < arity);

        let n = self.int().watches(not_lhs).len();
        for i in 0..n {
            let w = self.int().watches(not_lhs)[i];
            debug_assert!(w.binary());
            #[cfg(feature = "logging")]
            {
                let c = w.clause;
                log!(self.internal, c, "checking");
                debug_assert!(c.size() == 2);
                debug_assert!(c.lit(0) == not_lhs || c.lit(1) == not_lhs);
            }
            let other = w.blit;
            let mark = self.mk(other);
            if mark == 0 {
                continue;
            }
            matched += 1;
            if (mark & 2) == 0 {
                self.lrat_chain_and_gate.push(LitClausePair::new(other, w.clause));
                log!(self.internal, "pushing {} -> {}", other, w.clause.id());
                continue;
            }
            log!(self.internal, "marking {} mu4", other);
            debug_assert!((mark & 4) == 0);
            self.set_mk(other, mark | 4);
            self.lrat_chain_and_gate.push(LitClausePair::new(other, w.clause));
            if self.lrat() {
                self.set_mu4_reason(other, w.clause);
            }
        }

        {
            let mut q = 0usize;
            debug_assert!(!self.int().analyzed.is_empty());
            debug_assert!(self.mk(not_lhs) == 3);
            let n = self.int().analyzed.len();
            for i in 0..n {
                let lit = self.int().analyzed[i];
                let mark = self.mk(lit);
                if lit == not_lhs {
                    self.set_mk(lit, 1);
                    continue;
                }

                debug_assert!((mark & 3) == 3);
                if (mark & 4) != 0 {
                    self.set_mk(lit, 3);
                    self.int().analyzed[q] = lit;
                    q += 1;
                    log!(self.internal, "keeping LHS candidate {}", -lit);
                } else {
                    log!(self.internal, "dropping LHS candidate {}", -lit);
                    self.set_mk(lit, 1);
                }
            }
            debug_assert!(q != self.int().analyzed.len());
            debug_assert!(self.mk(not_lhs) == 1);
            self.int().analyzed.truncate(q);
            log!(self.internal, "after filtering {} LHS candidate remain", self.int().analyzed.len());
        }

        if matched < arity {
            if self.lrat() {
                self.lrat_chain_and_gate.clear();
            }
            return std::ptr::null_mut();
        }

        if !self.lrat() {
            self.lrat_chain_and_gate.clear();
        }
        self.new_and_gate(base_clause, lhs)
    }

    pub fn extract_and_gates_with_base_clause(&mut self, c: CRef) {
        debug_assert!(!c.garbage());
        debug_assert!(self.lrat_chain.is_empty());
        log!(self.internal, c, "extracting and gates with clause");
        let mut size: u32 = 0;
        let arity_limit: u32 = std::cmp::min(self.int().opts.congruenceandarity as u32, MAX_ARITY);
        let size_limit: u32 = arity_limit + 1;
        let mut max_negbincount: usize = 0;
        self.lits.clear();

        let csize = c.size() as usize;
        for i in 0..csize {
            let lit = c.lit(i);
            let v = self.val(lit);
            if v < 0 {
                // push_lrat_unit (-lit);
                continue;
            }
            if v > 0 {
                debug_assert!(self.int().level == 0);
                log!(self.internal, c, "found satisfied clause");
                self.int().mark_garbage(c);
                if self.lrat() {
                    self.lrat_chain.clear();
                }
                return;
            }
            size += 1;
            if size > size_limit {
                log!(self.internal, c, "clause is actually too large, thus skipping");
                if self.lrat() {
                    self.lrat_chain.clear();
                }
                return;
            }
            let count = self.int().noccs(-lit) as usize;
            if count == 0 {
                log!(self.internal, c, "{} negated does not occur in any binary clause, thus skipping", lit);
                if self.lrat() {
                    self.lrat_chain.clear();
                }
                return;
            }

            if count > max_negbincount {
                max_negbincount = count;
            }
            self.lits.push(lit);
        }

        if size < 3 {
            log!(self.internal, c, "is actually too small, thus skipping");
            if self.lrat() {
                self.lrat_chain.clear();
            }
            debug_assert!(self.lrat_chain.is_empty());
            return;
        }

        let arity = (size - 1) as usize;
        if max_negbincount < arity {
            log!(self.internal, c, "all literals have less than {} negated occurrencesthus skipping", arity);
            if self.lrat() {
                self.lrat_chain.clear();
            }
            return;
        }

        self.int().analyzed.clear();
        let mut reduced: usize = 0;
        let clause_size = self.lits.len();
        for i in 0..clause_size {
            let lit = self.lits[i];
            let count = self.int().noccs(-lit) as u32;
            self.set_mk(-lit, 1);
            self.set_mu1_reason(-lit, c);
            if (count as usize) < arity {
                if reduced < i {
                    self.lits[i] = self.lits[reduced];
                    self.lits[reduced] = lit;
                    reduced += 1;
                } else if reduced == i {
                    reduced += 1;
                }
            }
        }
        let reduced_size = clause_size - reduced;
        debug_assert!(reduced_size != 0);
        log!(self.internal, c, "trying as base arity {} AND gate", arity);
        debug_assert!(reduced_size <= self.lits.len());
        {
            let internal: &Internal = self.int();
            msort(
                internal.opts.radixsortlim as usize,
                &mut self.lits[..reduced_size],
                |&a| congruence_occurrences_rank(internal, a),
                |&a, &b| congruence_occurrences_rank(internal, a) < congruence_occurrences_rank(internal, b),
            );
        }
        let mut first = true;
        let mut extracted: u32 = 0;

        for i in 0..clause_size {
            debug_assert!(self.lrat_chain.is_empty());
            if self.int().unsat {
                break;
            }
            if c.garbage() {
                break;
            }
            let lhs = self.lits[i];
            log!(
                self.internal,
                "trying LHS candidate literal {} with {} negated occurrences",
                loglit!(self.internal, lhs),
                self.int().noccs(-lhs)
            );

            if first {
                first = false;
                debug_assert!(self.int().analyzed.is_empty());
                if !self.find_first_and_gate(c, lhs).is_null() {
                    debug_assert!(self.lrat_chain.is_empty());
                    extracted += 1;
                }
            } else if self.int().analyzed.is_empty() {
                log!(self.internal, "early abort AND gate search");
                break;
            } else if !self.find_remaining_and_gate(c, lhs).is_null() {
                debug_assert!(self.lrat_chain.is_empty());
                extracted += 1;
            }
        }

        self.unmark_all();
        log!(self.internal, &self.lits, "finish unmarking");
        for i in 0..self.lits.len() {
            let lit = self.lits[i];
            self.set_mk(-lit, 0);
        }
        self.lrat_chain_and_gate.clear();
        if extracted != 0 {
            log!(self.internal, c, "extracted {} with arity {} AND base", extracted, arity);
        }
    }

    pub fn reset_and_gate_extraction(&mut self) {
        self.int().clear_noccs();
        self.int().clear_watches();
    }

    pub fn extract_and_gates(&mut self) {
        debug_assert!(!self.full_watching);
        if self.int().opts.congruenceand == 0 {
            return;
        }
        if self.int().terminated_asynchronously(1) {
            return;
        }
        start!(self.int(), extractands);

        let max_var = self.int().max_var as usize;
        self.marks.resize(max_var * 2 + 3, 0);
        self.init_and_gate_extraction();
        let gates_before = self.int().stats.congruence.and_gates;
        let size = self.int().clauses.len();
        let mut i = 0;
        while i < size && !self.int().terminated_asynchronously(1) {
            // we can learn new binary clauses, but so no for loop
            debug_assert!(self.lrat_chain.is_empty());
            let c = self.int().clauses[i];
            i += 1;
            if c.garbage() {
                continue;
            }
            if c.size() == 2 {
                continue;
            }
            if c.hyper() {
                continue;
            }
            if c.redundant() {
                continue;
            }
            self.extract_and_gates_with_base_clause(c);
            debug_assert!(self.lrat_chain.is_empty());
        }

        verbose!(
            self.internal,
            2,
            "[congruence-{}] found {} AND gates",
            self.int().stats.congruence.rounds,
            (self.int().stats.congruence.and_gates - gates_before) as u64
        );
        self.reset_and_gate_extraction();
        stop!(self.int(), extractands);
    }

    /*----------------------------------------------------------------------*/
    // XOR gates

    pub fn new_largecounts(&mut self, lit: i32) -> &mut u64 {
        debug_assert!(self.vlit(lit) < self.gnew_largecounts.len());
        let i = self.vlit(lit);
        &mut self.gnew_largecounts[i]
    }

    pub fn largecounts(&mut self, lit: i32) -> &mut u64 {
        debug_assert!(self.vlit(lit) < self.glargecounts.len());
        let i = self.vlit(lit);
        &mut self.glargecounts[i]
    }

    pub fn check_ternary(&mut self, a: i32, b: i32, c: i32) {
        debug_assert!(self.int().clause.is_empty());
        if self.int().opts.check == 0 {
            return;
        }
        if self.lrat() {
            return;
        }
        let internal = self.int();
        debug_assert!(internal.clause.is_empty());
        internal.clause.push(a);
        internal.clause.push(b);
        internal.clause.push(c);
        internal.external().check_learned_clause();
        if internal.proof.is_some() {
            internal.clause_id += 1;
            let id: LRAT_ID = internal.clause_id;
            let proof = internal.proof.as_mut().unwrap();
            proof.add_derived_clause_lits(id, false, &internal.clause, &[]);
            proof.delete_clause_lits(id, false, &internal.clause);
        }

        internal.clause.clear();
    }

    pub fn check_binary_implied(&mut self, a: i32, b: i32) {
        debug_assert!(self.int().clause.is_empty());
        if self.int().opts.check == 0 {
            return;
        }
        if self.lrat() {
            return;
        }
        debug_assert!(self.int().clause.is_empty());
        self.int().clause.push(a);
        self.int().clause.push(b);
        self.check_implied();
        self.int().clause.clear();
    }

    pub fn check_implied(&mut self) {
        if self.int().opts.check == 0 {
            return;
        }
        if self.lrat() {
            return;
        }
        self.int().external().check_learned_clause();
    }

    pub fn add_xor_shrinking_proof_chain(&mut self, g: *mut Gate, pivot: i32) {
        debug_assert!(self.int().clause.is_empty());
        debug_assert!(self.clause.is_empty());
        if self.int().proof.is_none() {
            return;
        }
        log!(self.internal, g, "starting XOR shrinking proof chain");
        let mut first: Vec<LitClausePair> = Vec::new();
        let mut newclauses: Vec<LitClausePair> = Vec::new();
        if self.lrat() {
            let src = gt(g).pos_lhs_ids.clone();
            let lhs = gt(g).lhs;
            self.simplify_and_sort_xor_lrat_clauses(&src, &mut first, lhs, pivot, false);
            let lhs = gt(g).lhs;
            self.gate_sort_lrat_reasons(&mut first, pivot, lhs, false);
        }

        let lhs = gt(g).lhs;
        self.int().clause.push(-lhs);
        let n = gt(g).rhs.len();
        for i in 0..n {
            let lit = gt(g).rhs[i];
            self.int().clause.push(lit);
        }

        let parity = lhs > 0;
        debug_assert!(parity == parity_lits(&self.int().clause));
        let size = self.int().clause.len();
        let end: u32 = 1u32 << (size - 1);
        debug_assert!(!self.lrat() || first.len() == 2 * end as usize);
        #[cfg(feature = "logging")]
        {
            for pair in first.iter() {
                log!(self.internal, pair.clause, "key {}", pair.current_lit);
            }
        }
        let mut i: u32 = 0;
        while i != end {
            while i != 0 && parity != parity_lits(&self.int().clause) {
                inc_lits(&mut self.int().clause);
            }
            log!(self.internal, &self.int().clause, "xor shrinking clause");
            if !self.lrat() {
                self.int().clause.push(pivot);
                self.check_and_add_internal_clause_to_proof_chain();
                self.int().clause.pop();
                self.int().clause.push(-pivot);
                self.check_and_add_internal_clause_to_proof_chain();
                self.int().clause.pop();
            }
            if self.lrat() {
                debug_assert!(self.lrat_chain.is_empty());
                self.lrat_chain.push(first[2 * i as usize].clause.id());
                self.lrat_chain.push(first[2 * i as usize + 1].clause.id());
            }
            if self.int().clause.len() > 1 {
                if self.lrat() {
                    let c = self.new_tmp_clause_internal();
                    newclauses.push(LitClausePair::new(0, c));
                    self.lrat_chain.clear();
                } else {
                    self.check_and_add_internal_clause_to_proof_chain();
                }
            }
            if self.int().clause.len() == 1 {
                return;
            }
            inc_lits(&mut self.int().clause);
            i += 1;
        }
        std::mem::swap(&mut gt(g).pos_lhs_ids, &mut newclauses);

        self.int().clause.clear();
    }

    pub fn check_xor_gate_implied(&mut self, g: *mut Gate) {
        debug_assert!(self.int().clause.is_empty());
        debug_assert!(gt(g).tag == Gate_Type::XOr_Gate);
        if self.lrat() {
            return;
        }
        if self.int().opts.check == 0 {
            return;
        }
        let lhs = gt(g).lhs;
        log!(self.internal, g, "checking implied");
        let internal = self.int();
        debug_assert!(internal.clause.is_empty());
        for &other in gt(g).rhs.iter() {
            debug_assert!(other > 0);
            internal.clause.push(other);
        }
        internal.clause.push(-lhs);
        let arity = gt(g).arity() as u32;
        let end: u32 = 1u32 << arity;
        let parity = lhs > 0;

        let mut i: u32 = 0;
        while i != end {
            while i != 0 && parity_lits(&internal.clause) != parity {
                inc_lits(&mut internal.clause);
            }
            internal.external().check_learned_clause();
            if internal.proof.is_some() {
                internal.clause_id += 1;
                let id = internal.clause_id;
                let proof = internal.proof.as_mut().unwrap();
                proof.add_derived_clause_lits(id, false, &internal.clause, &[]);
                proof.delete_clause_lits(id, false, &internal.clause);
            }
            inc_lits(&mut internal.clause);
            i += 1;
        }
        internal.clause.clear();
    }

    pub fn find_xor_lits(&mut self, rhs: &mut Vec<i32>) -> *mut Gate {
        debug_assert!({
            let internal: &Internal = self.int();
            is_sorted_by(rhs, |&a, &b| sort_literals_by_var_smaller(internal, a, b))
        });
        self.find_gate_lits(rhs, Gate_Type::XOr_Gate, std::ptr::null_mut())
    }

    pub fn find_xor_gate(&mut self, g: *mut Gate) -> *mut Gate {
        debug_assert!(gt(g).tag == Gate_Type::XOr_Gate);
        debug_assert!({
            let internal: &Internal = self.int();
            is_sorted_by(&gt(g).rhs, |&a, &b| sort_literals_by_var_smaller(internal, a, b))
        });
        self.find_gate_lits(&mut gt(g).rhs, Gate_Type::XOr_Gate, std::ptr::null_mut())
    }

    pub fn reset_xor_gate_extraction(&mut self) {
        self.int().clear_occs();
    }

    pub fn normalize_ite_lits_gate(&mut self, g: *mut Gate) -> bool {
        debug_assert!(gt(g).rhs.len() == 3);
        if self.lrat() {
            check_correct_ite_flags(g);
        }
        log!(self.internal, &gt(g).rhs, "RHS = ");
        if gt(g).rhs[0] < 0 {
            let rhs = &mut gt(g).rhs;
            rhs[0] = -rhs[0];
            rhs.swap(1, 2);
            if self.lrat() {
                let g = gt(g);
                debug_assert!(g.pos_lhs_ids.len() == 4);
                g.pos_lhs_ids.swap(0, 2);
                g.pos_lhs_ids.swap(1, 3);
                let flag = g.degenerated_gate;
                let plus_then = flag & Special_Gate::NO_PLUS_THEN;
                let neg_then = flag & Special_Gate::NO_NEG_THEN;
                let plus_else = flag & Special_Gate::NO_PLUS_ELSE;
                let neg_else = flag & Special_Gate::NO_NEG_ELSE;
                g.degenerated_gate = (if plus_then != 0 { Special_Gate::NO_PLUS_ELSE } else { Special_Gate::NORMAL })
                    | (if neg_then != 0 { Special_Gate::NO_NEG_ELSE } else { Special_Gate::NORMAL })
                    | (if plus_else != 0 { Special_Gate::NO_PLUS_THEN } else { Special_Gate::NORMAL })
                    | (if neg_else != 0 { Special_Gate::NO_NEG_THEN } else { Special_Gate::NORMAL });
                debug_assert!(g.pos_lhs_ids[0].current_lit == g.rhs[1]);
                debug_assert!(g.pos_lhs_ids[2].current_lit == g.rhs[2]);
                check_correct_ite_flags(g);
            }
        }
        if gt(g).rhs[1] > 0 {
            return false;
        }
        if self.lrat() {
            check_correct_ite_flags(g);
        }
        {
            let rhs = &mut gt(g).rhs;
            rhs[1] = -rhs[1];
            rhs[2] = -rhs[2];
        }
        log!(self.internal, &gt(g).rhs, "RHS = ");
        if self.lrat() {
            let g = gt(g);
            debug_assert!(g.pos_lhs_ids.len() == 4);
            g.pos_lhs_ids.swap(0, 1);
            g.pos_lhs_ids.swap(2, 3);
            let flag = g.degenerated_gate;
            let plus_then = flag & Special_Gate::NO_PLUS_THEN;
            let neg_then = flag & Special_Gate::NO_NEG_THEN;
            let plus_else = flag & Special_Gate::NO_PLUS_ELSE;
            let neg_else = flag & Special_Gate::NO_NEG_ELSE;
            g.degenerated_gate = (if plus_then != 0 { Special_Gate::NO_NEG_THEN } else { Special_Gate::NORMAL })
                | (if neg_then != 0 { Special_Gate::NO_PLUS_THEN } else { Special_Gate::NORMAL })
                | (if plus_else != 0 { Special_Gate::NO_NEG_ELSE } else { Special_Gate::NORMAL })
                | (if neg_else != 0 { Special_Gate::NO_PLUS_ELSE } else { Special_Gate::NORMAL });
            debug_assert!(g.pos_lhs_ids[0].current_lit == g.rhs[1]);
            debug_assert!(g.pos_lhs_ids[2].current_lit == g.rhs[2]);
            // incorrect as we have not negated the LHS yet!
            // check_correct_ite_flags (g);
        }

        log!(self.internal, &gt(g).rhs, "g/RHS = ");
        true
    }

    pub fn find_ite_gate(&mut self, g: *mut Gate, negate_lhs: &mut bool) -> *mut Gate {
        *negate_lhs = self.normalize_ite_lits_gate(g);
        log!(self.internal, g, "post normalize");
        self.find_gate_lits(&mut gt(g).rhs, Gate_Type::ITE_Gate, g)
    }

    /// `check_and_add_to_proof_chain (internal->clause)`.
    fn check_and_add_internal_clause_to_proof_chain(&mut self) -> LRAT_ID {
        self.int().external().check_learned_clause();
        self.int().clause_id += 1;
        let id: LRAT_ID = self.int().clause_id;
        if self.int().proof.is_some() {
            if self.lrat() {
                debug_assert!(self.int().lrat_chain.is_empty());
                debug_assert!(!self.lrat_chain.is_empty());
            }
            let internal = self.int();
            let proof = internal.proof.as_mut().unwrap();
            proof.add_derived_clause_lits(id, true, &internal.clause, &self.lrat_chain);
            self.lrat_chain.clear();
        }
        id
    }

    pub fn check_and_add_to_proof_chain(&mut self, clause: &mut Vec<i32>) -> i64 {
        self.int().external().check_learned_clause();
        self.int().clause_id += 1;
        let id: LRAT_ID = self.int().clause_id;
        if self.int().proof.is_some() {
            if self.lrat() {
                debug_assert!(self.int().lrat_chain.is_empty());
                debug_assert!(!self.lrat_chain.is_empty());
            }
            let proof = self.int().proof.as_mut().unwrap();
            proof.add_derived_clause_lits(id, true, clause, &self.lrat_chain);
            self.lrat_chain.clear();
        }
        id
    }

    pub fn add_clause_to_chain(&mut self, unsimplified: Vec<i32>, id: i64) {
        let id2_higher: u32 = (id >> 32) as u32;
        let id2_lower: u32 = (id & (u32::MAX as LRAT_ID)) as u32;
        debug_assert!(id == ((id2_higher as LRAT_ID) << 32) + id2_lower as LRAT_ID);
        self.chain.push(id2_higher as i32);
        self.chain.push(id2_lower as i32);
        log!(self.internal, &unsimplified, "pushing to chain");
        self.chain.extend_from_slice(&unsimplified);
        self.chain.push(0);
    }

    /// `delete_id` defaults to `0` in C++
    pub fn simplify_and_add_to_proof_chain(&mut self, unsimplified: &mut Vec<i32>, delete_id: i64) -> i64 {
        debug_assert!(self.int().clause.is_empty());
        #[cfg(debug_assertions)]
        {
            for &lit in unsimplified.iter() {
                debug_assert!((self.mk(lit) & 4) == 0);
            }
        }

        let mut trivial = false;
        for i in 0..unsimplified.len() {
            let lit = unsimplified[i];
            let lit_mark = self.mk(lit);
            if (lit_mark & 4) != 0 {
                continue;
            }
            let not_lit_mark = self.mk(-lit);
            if (not_lit_mark & 4) != 0 {
                trivial = true;
                break;
            }
            self.set_mk(lit, lit_mark | 4);
            self.int().clause.push(lit);
        }
        let n = self.int().clause.len();
        for i in 0..n {
            let lit = self.int().clause[i];
            let mark = self.mk(lit);
            debug_assert!((mark & 4) != 0);
            self.set_mk(lit, mark & !4);
        }

        let mut id: LRAT_ID = 0;
        if !trivial {
            if delete_id != 0 {
                if self.int().proof.is_some() {
                    let internal = self.int();
                    let proof = internal.proof.as_mut().unwrap();
                    proof.delete_clause_lits(delete_id, true, &internal.clause);
                    self.lrat_chain.clear();
                }
            } else {
                id = self.check_and_add_internal_clause_to_proof_chain();
                debug_assert!(id > 0);
                let clause = self.int().clause.clone();
                self.add_clause_to_chain(clause, id);
            }
        } else {
            log!(self.internal, "skipping trivial proof");
            self.lrat_chain.clear();
        }
        self.int().clause.clear();
        id
    }

    /*----------------------------------------------------------------------*/

    pub fn add_ite_turned_and_binary_clauses(&mut self, g: *mut Gate) {
        if self.int().proof.is_none() {
            return;
        }
        if self.lrat() {
            return;
        }
        log!(self.internal, "starting ITE turned AND supporting binary clauses");
        debug_assert!(self.unsimplified.is_empty());
        debug_assert!(self.chain.is_empty());
        let not_lhs = -gt(g).lhs;
        self.unsimplified.push(not_lhs);
        self.unsimplified.push(gt(g).rhs[0]);
        self.simplify_and_add_unsimplified_to_proof_chain(0);
        self.unsimplified.pop();
        self.unsimplified.push(gt(g).rhs[1]);
        self.simplify_and_add_unsimplified_to_proof_chain(0);
        self.unsimplified.clear();
    }

    pub fn simplify_unit_xor_lrat_clauses(&mut self, source: &[LitClausePair], lhs: i32) {
        debug_assert!(self.lrat());
        for &pair in source {
            self.compute_rewritten_clause_lrat_simple(pair.clause, lhs);
            if !self.lrat_chain.is_empty() {
                break;
            }
        }
        debug_assert!(self.clause.len() == 1);
    }

    /// `except2` defaults to `0` in C++
    /// `flip` defaults to `0` in C++
    pub fn simplify_and_sort_xor_lrat_clauses(
        &mut self,
        source: &[LitClausePair],
        target: &mut Vec<LitClausePair>,
        lhs: i32,
        except2: i32,
        flip: bool,
    ) {
        debug_assert!(self.lrat());
        for &pair in source {
            let c = self.produce_rewritten_clause_lrat(pair.clause, lhs, true, false);
            if !c.is_null() {
                target.push(LitClausePair::new(0, c));
            }
        }
        self.gate_sort_lrat_reasons(target, lhs, except2, flip);
    }

    pub fn add_xor_matching_proof_chain(
        &mut self,
        g: *mut Gate,
        lhs1: i32,
        clauses2: &[LitClausePair],
        lhs2: i32,
        to_lrat: &mut Vec<i64>,
        back_lrat: &mut Vec<i64>,
    ) {
        if self.int().proof.is_none() {
            return;
        }
        if lhs1 == lhs2 {
            return;
        }
        debug_assert!(self.unsimplified.is_empty());
        self.unsimplified.reserve(gt(g).arity());
        let n = gt(g).rhs.len();
        for i in 0..n {
            let lit = gt(g).rhs[i];
            self.unsimplified.push(lit);
        }
        let mut first: Vec<LitClausePair> = Vec::new();
        let mut second: Vec<LitClausePair> = Vec::new();
        if self.lrat() {
            let src = gt(g).pos_lhs_ids.clone();
            self.simplify_and_sort_xor_lrat_clauses(&src, &mut first, lhs1, 0, false);
            self.simplify_and_sort_xor_lrat_clauses(clauses2, &mut second, lhs2, 0, true);
            gt(g).pos_lhs_ids = first.clone();
        }
        log!(self.internal, "starting XOR matching proof");
        // for lrat
        let mut first_ids: Vec<LitIdPair> = Vec::new();
        let mut second_ids: Vec<LitIdPair> = Vec::new();
        for &pair in first.iter() {
            let first = (pair.current_lit & 1) != 0;
            let mut rest = pair.current_lit >> 1;
            rest &= !(1i32.wrapping_shl((gt(g).arity() as u32).wrapping_sub(1)));
            if first == (lhs1 > 0) {
                first_ids.push(LitIdPair::new(rest, pair.clause.id()));
            } else {
                second_ids.push(LitIdPair::new(rest, pair.clause.id()));
            }
            log!(self.internal, pair.clause, "key {}", pair.current_lit);
        }
        for &pair in second.iter() {
            let first = (pair.current_lit & 1) != 0;
            let mut rest = pair.current_lit >> 1;
            rest &= !(1i32.wrapping_shl((gt(g).arity() as u32).wrapping_sub(1)));
            if first == (lhs2 < 0) {
                first_ids.push(LitIdPair::new(rest, pair.clause.id()));
            } else {
                second_ids.push(LitIdPair::new(rest, pair.clause.id()));
            }
            log!(self.internal, pair.clause, "key {}", pair.current_lit);
        }
        loop {
            let mut first_tmp: Vec<LitIdPair> = Vec::new();
            let mut second_tmp: Vec<LitIdPair> = Vec::new();
            debug_assert!(!self.unsimplified.is_empty());
            self.unsimplified.pop();
            let size = self.unsimplified.len();
            debug_assert!(size < 32);
            let off: usize = 1usize << size;
            for _i in 0..off {
                let mut n: i32 = 0;
                if self.lrat() {
                    let u = self.unsimplified.clone();
                    n = self.number_from_xor_reason_reversed(&u) as i32;
                    debug_assert!(self.lrat_chain.is_empty());
                    for pair in first_ids.iter() {
                        if pair.lit == n {
                            self.lrat_chain.push(pair.id);
                        }
                    }
                    debug_assert!(self.lrat_chain.len() == 2);
                }
                self.unsimplified.push(-lhs1);
                self.unsimplified.push(lhs2);
                let id1 = self.simplify_and_add_unsimplified_to_proof_chain(0);
                let new_len = self.unsimplified.len() - 2;
                self.unsimplified.truncate(new_len);
                if self.lrat() {
                    n &= !(1i32.wrapping_shl((self.unsimplified.len() as u32).wrapping_sub(1)));
                    let rest: i32 = n;
                    first_tmp.push(LitIdPair::new(rest, id1));
                    let u = self.unsimplified.clone();
                    n = self.number_from_xor_reason_reversed(&u) as i32;
                    self.lrat_chain.clear();
                    for pair in second_ids.iter() {
                        if pair.lit == n {
                            self.lrat_chain.push(pair.id);
                        }
                    }
                    debug_assert!(self.lrat_chain.len() == 2);
                }
                self.unsimplified.push(lhs1);
                self.unsimplified.push(-lhs2);
                let id2 = self.simplify_and_add_unsimplified_to_proof_chain(0);
                let new_len = self.unsimplified.len() - 2;
                self.unsimplified.truncate(new_len);
                if self.lrat() {
                    self.lrat_chain.clear();
                    n &= !(1i32.wrapping_shl((self.unsimplified.len() as u32).wrapping_sub(1)));
                    let rest: i32 = n;
                    second_tmp.push(LitIdPair::new(rest, id2));
                }
                inc_lits(&mut self.unsimplified);
            }
            if self.lrat() {
                std::mem::swap(&mut first_ids, &mut first_tmp);
                std::mem::swap(&mut second_ids, &mut second_tmp);
            }
            if self.unsimplified.is_empty() {
                break;
            }
        }
        if self.lrat() {
            debug_assert!(first_ids.len() == 1);
            debug_assert!(second_ids.len() == 1);
            to_lrat.push(first_ids.last().unwrap().id);
            back_lrat.push(second_ids.last().unwrap().id);
        }
        debug_assert!(!self.lrat() || to_lrat.len() == 1);
        debug_assert!(!self.lrat() || back_lrat.len() == 1);
        log!(self.internal, "finished XOR matching proof");
        debug_assert!(self.unsimplified.is_empty());
    }

    // this function needs to either put the clauses from
    // lrat_chain_and_gate into g->pos_neg_ids or clear it or do something
    // with it if you merge gates.
    pub fn new_xor_gate(&mut self, glauses: &[LitClausePair], lhs: i32) -> *mut Gate {
        self.rhs.clear();
        self.rhs.reserve(self.lits.len());
        for i in 0..self.lits.len() {
            let lit = self.lits[i];
            if lhs != lit && -lhs != lit {
                debug_assert!(lit > 0);
                self.rhs.push(lit);
            }
        }
        debug_assert!(self.rhs.len() + 1 == self.lits.len());
        let mut rhs = std::mem::take(&mut self.rhs);
        self.sort_literals_by_var(&mut rhs);
        let mut g = self.find_xor_lits(&mut rhs);
        self.rhs = rhs;
        if !g.is_null() {
            self.check_xor_gate_implied(g);
            let mut reasons_implication: Vec<LRAT_ID> = Vec::new();
            let mut reasons_back: Vec<LRAT_ID> = Vec::new();
            let gl = gt(g).lhs;
            self.add_xor_matching_proof_chain(g, gl, glauses, lhs, &mut reasons_implication, &mut reasons_back);
            let gl = gt(g).lhs;
            if self.merge_literals(gl, lhs, &reasons_implication, &reasons_back) {
                self.int().stats.congruence.xors += 1;
            }
            self.delete_proof_chain();
            debug_assert!(self.int().unsat || self.chain.is_empty());
        } else {
            g = new_gate();
            gt(g).lhs = lhs;
            gt(g).tag = Gate_Type::XOr_Gate;
            gt(g).rhs = self.rhs.clone();
            gt(g).garbage = false;
            gt(g).indexed = true;
            gt(g).shrunken = false;
            if self.lrat() {
                for &pair in glauses {
                    gt(g).pos_lhs_ids.push(pair);
                }
            }
            self.table.insert(g);
            self.int().stats.congruence.gates += 1;
            #[cfg(feature = "logging")]
            {
                gt(g).id = self.fresh_id;
                self.fresh_id += 1;
            }
            log!(self.internal, g, "creating new");
            self.check_xor_gate_implied(g);
            let n = gt(g).rhs.len();
            for i in 0..n {
                let lit = gt(g).rhs[i];
                self.connect_goccs(g, lit);
            }
        }
        self.int().stats.congruence.xor_gates += 1;
        g
    }

    pub fn number_from_xor_reason_reversed(&mut self, rhs: &[i32]) -> u32 {
        let mut n: u32 = 0;
        debug_assert!({
            let internal: &Internal = self.int();
            let rev: Vec<i32> = rhs.iter().rev().copied().collect();
            is_sorted_by(&rev, |&a, &b| sort_literals_by_var_smaller_except(internal, 0, 0, a, b))
        });
        debug_assert!(rhs.len() <= 32);
        for &lit in rhs.iter().rev() {
            n = n.wrapping_mul(2);
            n = n.wrapping_add(!(lit > 0) as u32);
        }
        n
    }

    /// `except` defaults to `0` in C++
    /// `flip` defaults to `0` in C++
    pub fn number_from_xor_reason(&mut self, rhs: &[i32], lhs: i32, except: i32, flip: bool) -> u32 {
        let mut n: u32 = 0;
        debug_assert!({
            let internal: &Internal = self.int();
            is_sorted_by(rhs, |&a, &b| sort_literals_by_var_smaller_except(internal, lhs, except, a, b))
        });
        let _ = (lhs, except);
        debug_assert!(rhs.len() <= 32);
        let mut flip = flip;
        for &lit in rhs {
            n = n.wrapping_mul(2);
            n = n.wrapping_add(((!(lit > 0)) as i32 ^ flip as i32) as u32);
            flip = false;
        }
        n
    }

    // this is how I planned to sort it and produce the number
    // Look at this first
    /// `except2` defaults to `0` in C++
    /// `flip` defaults to `0` in C++
    /// C++ overload `Closure::gate_sort_lrat_reasons` (renamed).
    pub fn gate_sort_lrat_reason(&mut self, litId: &mut LitClausePair, lhs: i32, except2: i32, flip: bool) {
        debug_assert!(self.clause.is_empty());
        self.clause.extend_from_slice(litId.clause.lits());
        let mut cl = std::mem::take(&mut self.clause);
        self.sort_literals_by_var_except(&mut cl, lhs, except2);
        litId.current_lit = self.number_from_xor_reason(&cl, lhs, except2, flip) as i32;
        cl.clear();
        self.clause = cl;
    }

    // this is how I planned to sort it and produce the number
    // Look at this first
    /// `except2` defaults to `0` in C++
    /// `flip` defaults to `0` in C++
    pub fn gate_sort_lrat_reasons(&mut self, xs: &mut Vec<LitClausePair>, lhs: i32, except2: i32, flip: bool) {
        debug_assert!(self.clause.is_empty());
        debug_assert!(!xs.is_empty());
        for i in 0..xs.len() {
            let mut p = xs[i];
            self.gate_sort_lrat_reason(&mut p, lhs, except2, flip);
            xs[i] = p;
        }

        rsort(xs, |a: &LitClausePair| a.current_lit as usize);

        #[cfg(debug_assertions)]
        {
            if xs.len() > 1 {
                for x in xs.iter() {
                    debug_assert!(x.clause.size() == xs[1].clause.size());
                }
            }
        }
    }

    pub fn init_xor_gate_extraction(&mut self, candidates: &mut Vec<CRef>) {
        let arity_limit = self.int().opts.congruencexorarity as u32;
        debug_assert!(arity_limit < 32); // we use unsigned int.
        let size_limit = arity_limit + 1;
        let vsize = self.int().vsize;
        self.glargecounts.resize(2 * vsize, 0);

        let nclauses = self.int().clauses.len();
        'next_clause: for ci in 0..nclauses {
            let c = self.int().clauses[ci];
            log!(self.internal, c, "considering clause for XOR");
            if c.redundant() {
                continue;
            }
            if c.garbage() {
                continue;
            }
            if c.size() < 3 {
                continue;
            }
            let mut size: u32 = 0;
            let csize = c.size() as usize;
            for i in 0..csize {
                let lit = c.lit(i);
                let v = self.val(lit);
                if v < 0 {
                    continue;
                }
                if v > 0 {
                    log!(self.internal, c, "satisfied by {}", lit);
                    self.int().mark_garbage(c);
                    continue 'next_clause;
                }
                if size == size_limit {
                    continue 'next_clause;
                }
                size += 1;
            }

            if size < 3 {
                continue;
            }
            for i in 0..csize {
                let lit = c.lit(i);
                if self.val(lit) != 0 {
                    continue;
                }
                *self.largecounts(lit) += 1;
            }

            log!(self.internal, c, "considering clause for XOR as candidate");
            candidates.push(c);
        }

        log!(self.internal, "considering {} out of {}", candidates.len(), self.int().irredundant());
        let rounds = self.int().opts.congruencexorcounts as u32;
        #[cfg(feature = "logging")]
        let original_size = candidates.len();
        log!(self.internal, "resizing glargecounts to size {}", self.glargecounts.len());
        for round in 0..rounds {
            log!(self.internal, "round {} of XOR extraction", round);
            let mut removed: usize = 0;
            self.gnew_largecounts.resize(2 * vsize, 0);
            let cand_size = candidates.len() as u32;
            let mut j = 0usize;
            'next_candidate: for i in 0..cand_size as usize {
                let c = candidates[i];
                log!(self.internal, c, "considering");
                let mut size: u32 = 0;
                let csize = c.size() as usize;
                for k in 0..csize {
                    let lit = c.lit(k);
                    if self.val(lit) == 0 {
                        size += 1;
                    }
                }
                debug_assert!(3 <= size);
                debug_assert!(size <= size_limit);
                let arity = size - 1;
                let needed_clauses: u32 = 1u32 << (arity - 1);
                for k in 0..csize {
                    let lit = c.lit(k);
                    if *self.largecounts(lit) < needed_clauses as u64 {
                        log!(self.internal, c, "not enough occurrences, so ignoring");
                        removed += 1;
                        continue 'next_candidate;
                    }
                }
                for k in 0..csize {
                    let lit = c.lit(k);
                    if self.val(lit) == 0 {
                        *self.new_largecounts(lit) += 1;
                    }
                }
                candidates[j] = candidates[i];
                j += 1;
            }
            candidates.truncate(j);
            self.glargecounts = std::mem::take(&mut self.gnew_largecounts);
            self.gnew_largecounts.clear();
            log!(self.internal, "moving counts {}", self.glargecounts.len());
            if removed == 0 {
                break;
            }

            log!(
                self.internal,
                "after round {}, {} ({} %) remain",
                round,
                candidates.len(),
                candidates.len() / (1 + original_size) * 100
            );
        }

        for &c in candidates.iter() {
            if self.int().terminated_asynchronously(1) {
                return;
            }
            let csize = c.size() as usize;
            for k in 0..csize {
                let lit = c.lit(k);
                self.int().occs_mut(lit).push(c);
            }
        }

        verbose!(
            self.internal,
            2,
            "connected {} large clauses {}%",
            candidates.len(),
            crate::format::fmt_f(
                percent(candidates.len() as f64, self.int().stats.current.irredundant as f64),
                0
            )
        );
    }

    pub fn find_large_xor_side_clause(&mut self, lits: &mut Vec<i32>) -> CRef {
        let mut least_occurring_literal: u32 = 0;
        let mut count_least_occurring: u32 = u32::MAX;
        let size_lits = lits.len();
        #[cfg(any(feature = "logging", debug_assertions))]
        let arity = (size_lits - 1) as u32;
        #[cfg(debug_assertions)]
        let count_limit: u32 = 1u32 << (arity - 1);
        log!(self.internal, &*lits, "trying to find arity {} XOR side clause", arity);
        for i in 0..lits.len() {
            let lit = lits[i];
            debug_assert!(self.val(lit) == 0);
            self.set_mk(lit, 1);
            let count = *self.largecount(lit) as u32;
            #[cfg(debug_assertions)]
            debug_assert!(count_limit <= count);
            if count >= count_least_occurring {
                continue;
            }
            count_least_occurring = count;
            least_occurring_literal = lit as u32;
        }
        let least_occurring_literal = least_occurring_literal as i32;
        let mut res = CRef::NULL;
        debug_assert!(least_occurring_literal != 0);
        log!(
            self.internal,
            "searching XOR side clause watched by {}#{}",
            least_occurring_literal,
            count_least_occurring
        );
        log!(self.internal, "searching for size {}", size_lits);
        let n = self.int().occs(least_occurring_literal).len();
        for k in 0..n {
            let c = self.int().occs(least_occurring_literal)[k];
            log!(self.internal, c, "checking");
            debug_assert!(c.size() != 2); // TODO kissat has break
            if c.garbage() {
                continue;
            }
            if (c.size() as usize) < size_lits {
                continue;
            }
            let mut found: usize = 0;
            let csize = c.size() as usize;
            for m in 0..csize {
                let other = c.lit(m);
                let value = self.val(other);
                if value < 0 {
                    continue;
                }
                if value > 0 {
                    log!(self.internal, c, "found satisfied {} in", other);
                    self.int().mark_garbage(c);
                    debug_assert!(c.garbage());
                    break;
                }
                if self.mk(other) != 0 {
                    found += 1;
                } else {
                    log!(self.internal, "not marked {}", other);
                    found = 0;
                    break;
                }
            }
            if found == size_lits && !c.garbage() {
                res = c;
                break;
            } else {
                log!(self.internal, "too few literals");
            }
        }
        for i in 0..lits.len() {
            let lit = lits[i];
            self.set_mk(lit, 0);
        }
        if !res.is_null() {
            log!(self.internal, res, "found matching XOR side");
        } else {
            log!(self.internal, "no matching XOR side clause found");
        }
        res
    }

    pub fn extract_xor_gates_with_base_clause(&mut self, c: CRef) {
        log!(self.internal, c, "checking clause");
        self.lits.clear();
        let mut smallest = 0;
        let mut largest = 0;
        let arity_limit = self.int().opts.congruencexorarity as u32;
        let size_limit = arity_limit + 1;
        let mut negated: u32 = 0;
        let mut size: u32 = 0;
        let mut first = true;
        let csize = c.size() as usize;
        for i in 0..csize {
            let lit = c.lit(i);
            let v = self.val(lit);
            if v < 0 {
                continue;
            }
            if v > 0 {
                self.int().mark_garbage(c);
                return;
            }
            if size == size_limit {
                log!(self.internal, c, "size limit reached");
                return;
            }

            if first {
                largest = lit;
                smallest = lit;
                first = false;
            } else {
                debug_assert!(smallest != 0);
                debug_assert!(largest != 0);
                if self.int().vlit(lit) < self.int().vlit(smallest) {
                    log!(self.internal, "new smallest {}", lit);
                    smallest = lit;
                }
                if self.int().vlit(lit) > self.int().vlit(largest) {
                    if largest < 0 {
                        log!(self.internal, c, "not largest {} (largest: {}) occurs negated in XOR base", lit, largest);
                        return;
                    }
                    largest = lit;
                }
            }
            if lit < 0 && self.int().vlit(lit) < self.int().vlit(largest) {
                log!(self.internal, c, "negated literal {} not largest in XOR base", lit);
                return;
            }
            if lit < 0 {
                let was = negated;
                negated += 1;
                if was != 0 {
                    log!(self.internal, c, "more than one negated literal in XOR base");
                    return;
                }
            }
            self.lits.push(lit);
            size += 1;
        }
        debug_assert!(size as usize == self.lits.len());
        if size < 3 {
            log!(self.internal, c, "short XOR base clause");
            return;
        }

        log!(self.internal, "double checking if possible");
        let arity = size - 1;
        let needed_clauses: u32 = 1u32 << (arity - 1);
        for i in 0..self.lits.len() {
            let mut lit = self.lits[i];
            let mut sign = 0;
            while sign != 2 {
                let count = *self.largecount(lit) as u32;
                if count < needed_clauses {
                    log!(
                        self.internal,
                        c,
                        "literal {} in XOR base clause only occurs {} times in large clause thus skipping",
                        lit,
                        count
                    );
                    return;
                }
                sign += 1;
                lit = -lit;
            }
        }

        log!(self.internal, "checking for XOR side clauses");
        debug_assert!(smallest != 0 && largest != 0);
        let end: u32 = 1u32 << arity;
        debug_assert!(negated == parity_lits(&self.lits) as u32);
        let mut found: u32 = 0;
        let mut glauses: Vec<LitClausePair> = Vec::new();
        glauses.push(LitClausePair::new(0, c));
        let mut i: u32 = 0;
        while i != end {
            while i != 0 && parity_lits(&self.lits) as u32 != negated {
                inc_lits(&mut self.lits);
            }
            if i != 0 {
                // the clause must be stored
                // you can use `lrat_chain_and_gate` for this
                let mut lits = std::mem::take(&mut self.lits);
                let d = self.find_large_xor_side_clause(&mut lits);
                self.lits = lits;
                if d.is_null() {
                    return;
                }
                debug_assert!(!d.redundant());
                glauses.push(LitClausePair::new(i as i32, d));
            } else {
                debug_assert!(!c.redundant());
            }
            inc_lits(&mut self.lits);
            found += 1;
            i += 1;
        }

        while parity_lits(&self.lits) as u32 != negated {
            inc_lits(&mut self.lits);
        }
        log!(self.internal, &self.lits, "found all needed {} matching clauses:", found);
        debug_assert!(found == 1u32 << arity);
        let _ = found;
        if negated != 0 {
            let mut p = 0usize;
            let mut lit;
            loop {
                lit = self.lits[p];
                if lit <= 0 {
                    break;
                }
                p += 1;
            }
            log!(self.internal, "flipping RHS literal {}", lit);
            self.lits[p] = -lit;
        }
        log!(self.internal, &self.lits, "normalized negations");
        let mut extracted: u32 = 0;
        for k in 0..self.lits.len() {
            let mut lhs = self.lits[k];
            if negated == 0 {
                lhs = -lhs;
            }
            let g = self.new_xor_gate(&glauses, lhs);
            if !g.is_null() {
                extracted += 1;
            }
            if self.int().unsat {
                break;
            }
        }
        if extracted == 0 {
            log!(self.internal, "no arity {} XOR gate extracted", arity);
        }
    }

    pub fn extract_xor_gates(&mut self) {
        debug_assert!(!self.full_watching);
        if self.int().opts.congruencexor == 0 {
            return;
        }
        if self.int().terminated_asynchronously(1) {
            return;
        }
        start!(self.int(), extractxors);
        let gates_before = self.int().stats.congruence.xor_gates;
        log!(self.internal, "starting extracting XOR");
        let mut candidates: Vec<CRef> = Vec::new();
        self.init_xor_gate_extraction(&mut candidates);
        for &c in candidates.iter() {
            if self.int().unsat {
                break;
            }
            if self.int().terminated_asynchronously(1) {
                stop!(self.int(), extractxors);
                return;
            }
            if c.garbage() {
                continue;
            }
            self.extract_xor_gates_with_base_clause(c);
        }
        verbose!(
            self.internal,
            2,
            "[congruence-{}] found {} XOR gates",
            self.int().stats.congruence.rounds,
            self.int().stats.congruence.xor_gates - gates_before
        );
        self.reset_xor_gate_extraction();
        stop!(self.int(), extractxors);
    }

    /*----------------------------------------------------------------------*/

    pub fn find_units(&mut self) {
        if self.int().terminated_asynchronously(1) {
            return;
        }
        let mut units: usize = 0;
        for v in self.int().vars() {
            'restart: loop {
                if !self.int().flags(v).active() {
                    break 'restart;
                }
                let mut sgn = -1;
                while sgn <= 1 {
                    let lit = v * sgn;
                    let n = self.int().watches(lit).len();
                    for i in 0..n {
                        let w = self.int().watches(lit)[i];
                        if !w.binary() {
                            break;
                        }
                        let other = w.blit;
                        if self.mk(-other) != 0 {
                            log!(
                                self.internal,
                                w.clause,
                                "binary clause {} {} and {} {} give unit {}",
                                lit,
                                other,
                                lit,
                                -other,
                                lit
                            );
                            units += 1;
                            if self.lrat() {
                                self.lrat_chain.push(w.clause.id());
                                let id = self.marked_mu1(-other).clause.id();
                                self.lrat_chain.push(id);
                            }
                            let failed = !self.learn_congruence_unit(lit, false, false);
                            self.unmark_all();
                            if failed {
                                return;
                            } else {
                                continue 'restart;
                            }
                        }
                        if self.mk(other) != 0 {
                            continue;
                        }
                        self.set_mk(other, 1);
                        self.set_mu1_reason(other, w.clause);
                        self.int().analyzed.push(other);
                    }
                    self.unmark_all();
                    sgn += 2;
                }
                debug_assert!(self.int().analyzed.is_empty());
                break 'restart;
            }
        }
        log!(self.internal, "found {} units", units);
        let _ = units;
    }

    pub fn find_equivalences(&mut self) {
        debug_assert!(!self.int().unsat);
        if self.int().terminated_asynchronously(1) {
            return;
        }
        for v in self.int().vars() {
            'restart: loop {
                if !self.int().flags(v).active() {
                    break 'restart;
                }
                let lit = v;
                let n = self.int().watches(lit).len();
                for i in 0..n {
                    let w = self.int().watches(lit)[i];
                    if !w.binary() {
                        break;
                    }
                    debug_assert!(w.size == 2);
                    let other = w.blit;
                    if self.int().vlit(lit) > self.int().vlit(other) {
                        continue;
                    }
                    if self.mk(other) != 0 {
                        continue;
                    }
                    self.int().analyzed.push(other);
                    self.set_mk(other, 1);
                    self.set_mu1_reason(other, w.clause);
                }

                if self.int().analyzed.is_empty() {
                    break 'restart;
                }

                let n = self.int().watches(-lit).len();
                for i in 0..n {
                    let w = self.int().watches(-lit)[i];
                    if !w.binary() {
                        break; // binary clauses are first
                    }
                    let other = w.blit;
                    if self.int().vlit(-lit) > self.int().vlit(other) {
                        continue;
                    }
                    debug_assert!(-lit != other);
                    log!(self.internal, "binary clause {} {}", -lit, other);
                    if self.mk(-other) != 0 {
                        let lit_repr = self.find_representative(lit);
                        let other_repr = self.find_representative(other);
                        log!(
                            self.internal,
                            "found equivalence {} {} with {} and {} as the representative",
                            lit,
                            other,
                            lit_repr,
                            other_repr
                        );
                        if lit_repr != other_repr {
                            // if (internal->lrat) {
                            //   // This cannot work
                            //   // if you have 2 = 1 and 3=4
                            //   // you cannot add 2=3. You really to connect
                            //   // the representatives directly therefore you
                            //   // actually need to learn the clauses 2->3->4
                            //   // and -2->1 and vice-versa
                            // }
                            let mu1 = self.marked_mu1(-other).clause;
                            self.promote_clause(mu1);
                            self.promote_clause(w.clause);
                            log!(self.internal, w.clause, "merging");
                            log!(self.internal, self.marked_mu1(-other).clause, "with");
                            let c1 = if self.lrat() { self.marked_mu1(-other).clause } else { CRef::NULL };
                            if self.merge_literals_equivalence(lit, other, c1, w.clause) {}
                            self.unmark_all();
                            if self.int().unsat {
                                return;
                            } else {
                                continue 'restart;
                            }
                        }
                    }
                }
                self.unmark_all();
                break 'restart;
            }
        }
        debug_assert!(self.int().analyzed.is_empty());
        // force removal of memory
        self.mu1_ids.clear();
        shrink_vector(&mut self.mu1_ids);
        verbose!(
            self.internal,
            2,
            "[congruence-{}] found {} equivalences",
            self.int().stats.congruence.rounds,
            self.schedule.len()
        );
    }

    /*----------------------------------------------------------------------*/
    // Initialization

    pub fn rewrite_and_gate(&mut self, g: *mut Gate, dst: i32, src: i32, id1: i64, id2: i64) {
        if self.skip_and_gate(g) {
            return;
        }
        if !gate_contains(g, src) {
            return;
        }
        if self.val(src) != 0 {
            // In essence the code below does the same thing as
            // simplify_and_gate but the necessary LRAT chain are different.
            self.simplify_and_gate(g);
            return;
        }
        debug_assert!(src != 0);
        debug_assert!(dst != 0);
        debug_assert!(self.val(src) == self.val(dst));
        log!(self.internal, g, "rewriting {} into {} in", src, dst);
        let git: GatesIterator = if gt(g).indexed { self.table.find(g) } else { None };
        debug_assert!(!gt(g).indexed || git.is_some());
        let mut clashing = 0;
        let mut falsifies = 0;
        let mut dst_count: u32 = 0;
        let mut not_dst_count: u32 = 0;
        let mut q = 0usize;
        if gt(g).degenerated_gate != Special_Gate::NORMAL {
            let l = self.find_eager_representative(gt(g).lhs);
            gt(g).lhs = l;
            log!(self.internal, g, "updating LHS to");
        }
        let n = gt(g).rhs.len();
        for i in 0..n {
            let mut lit = gt(g).rhs[i];
            if lit == -gt(g).lhs || (lit == src && dst == -gt(g).lhs) {
                log!(self.internal, "found negated LHS literal {}", lit);
                clashing = lit;
                gt(g).degenerated_gate = Special_Gate::DEGENERATED_AND;
                break;
            }
            if lit == src {
                lit = dst;
                gt(g).rhs[i] = dst;
            }
            if lit == gt(g).lhs {
                gt(g).degenerated_gate = Special_Gate::DEGENERATED_AND;
            }
            if -lit == gt(g).lhs {
                gt(g).degenerated_gate = Special_Gate::DEGENERATED_AND;
            }
            let val = self.val(lit);
            if val > 0 {
                continue;
            }
            if val < 0 {
                log!(self.internal, "found falsifying literal {}", lit);
                falsifies = lit;
                break;
            }
            if lit == dst {
                if not_dst_count != 0 {
                    log!(self.internal, "clashing literals {} and {}", -dst, dst);
                    clashing = dst;
                    break;
                }
                let was = dst_count;
                dst_count += 1;
                if was != 0 {
                    continue;
                }
            }
            if lit == -dst {
                if dst_count != 0 {
                    debug_assert!(not_dst_count == 0);
                    log!(self.internal, "clashing literals {} and {}", dst, -dst);
                    clashing = -dst;
                    break;
                }
                debug_assert!(not_dst_count == 0);
                not_dst_count += 1;
            }
            gt(g).rhs[q] = lit;
            q += 1;
        }
        log!(self.internal, &self.lrat_chain, "lrat chain after rewriting");

        if q != gt(g).rhs.len() {
            gt(g).rhs.resize(q, 0);
            gt(g).shrunken = true;
        }

        if self.lrat() {
            // updating reasons in the chain.
            #[cfg(feature = "logging")]
            {
                for litId in gt(g).pos_lhs_ids.clone() {
                    log!(self.internal, litId.clause, "{} ->", litId.current_lit);
                }
            }
            // We remove all assigned literals except the falsified literal
            // such that we can produce an LRAT chain
            //
            // Obviously there are exceptions that make everything more
            // complicated, in particular when we do not need the gate
            // anymore, like in: 3 := And 1@0+=1 3 Then assertion will fail
            // (like the `assert (i)`) but it does not matter.
            let mut i = 0usize;
            let size = gt(g).pos_lhs_ids.len();
            let mut found = false;
            debug_assert!(falsifies == 0 || clashing == 0);
            let orig_falsifies = if falsifies == dst { src } else { falsifies };
            let orig_clashing = if clashing == -dst {
                -src
            } else if clashing == dst {
                src
            } else {
                clashing
            };
            let keep_clashing = clashing;
            log!(
                self.internal,
                "keeping chain for falsifies: {} aka {} and clashing: {} aka {}",
                falsifies,
                orig_falsifies,
                clashing,
                orig_clashing
            );
            // We do not need all the clauses. Therefore, we keep only the
            // ones required by clashing.
            for j in 0..size {
                log!(
                    self.internal,
                    gt(g).pos_lhs_ids[j].clause,
                    "looking at {} [{} {}] with val {}",
                    gt(g).pos_lhs_ids[j].current_lit,
                    i,
                    j,
                    self.val(gt(g).pos_lhs_ids[i].current_lit)
                );
                gt(g).pos_lhs_ids[i] = gt(g).pos_lhs_ids[j];
                // if the gate is not normal, we rewrite the LHS. Therefore, we
                // also have to update the literal here.
                let mut curr = gt(g).pos_lhs_ids[i].current_lit;
                if gt(g).degenerated_gate != Special_Gate::NORMAL && self.find_eager_representative(curr) == gt(g).lhs {
                    curr = self.find_eager_representative(curr);
                    gt(g).pos_lhs_ids[i].current_lit = curr;
                }
                if keep_clashing != 0
                    && curr != orig_clashing
                    && curr != -orig_clashing
                    && curr != keep_clashing
                    && curr != -keep_clashing
                {
                    continue;
                }
                if self.val(curr) != 0 && curr != src && curr != orig_falsifies {
                    continue;
                }
                if curr == dst {
                    if !found {
                        found = true;
                    } else {
                        continue; // we have already one defining clause
                    }
                }

                log!(
                    self.internal,
                    "maybe keeping {} [{} {}], src: {}, found: {}",
                    gt(g).pos_lhs_ids[i].current_lit,
                    i,
                    j,
                    src,
                    found as i32
                );
                if gt(g).pos_lhs_ids[i].current_lit == src {
                    if !found {
                        gt(g).pos_lhs_ids[i].current_lit = dst;
                        found = true;
                    } else {
                        continue; // we have already one defining clause
                    }
                }
                log!(self.internal, "keeping {} [{} {}]", gt(g).pos_lhs_ids[i].current_lit, i, j);
                i += 1;
            }
            log!(self.internal, "resizing to {}", i);
            debug_assert!(i != 0 || (gt(g).arity() == 1 && gt(g).rhs[0] == gt(g).lhs));
            gt(g).pos_lhs_ids.resize(i, LitClausePair::default());
        }

        debug_assert!(dst_count <= 2);
        debug_assert!(not_dst_count <= 1);

        self.shrink_and_gate(g, falsifies, clashing);
        log!(self.internal, g, "rewritten as");
        debug_assert!(
            !self.lrat() || !gt(g).pos_lhs_ids.is_empty() || (gt(g).arity() == 1 && gt(g).rhs[0] == gt(g).lhs)
        );
        //  check_and_gate_implied (g);
        self.update_and_gate(g, git, src, dst, id1, id2, falsifies, clashing);
        self.int().stats.congruence.rewritten_ands += 1;
    }

    pub fn rewrite_gate(&mut self, g: *mut Gate, dst: i32, src: i32, id1: i64, id2: i64) -> bool {
        match gt(g).tag {
            Gate_Type::And_Gate => self.rewrite_and_gate(g, dst, src, id1, id2),
            Gate_Type::XOr_Gate => self.rewrite_xor_gate(g, dst, src),
            Gate_Type::ITE_Gate => self.rewrite_ite_gate(g, dst, src),
        }
        debug_assert!(self.int().unsat || self.lrat_chain.is_empty());
        !self.int().unsat
    }

    pub fn rewrite_gates(&mut self, dst: i32, src: i32, id1: i64, id2: i64) -> bool {
        let sidx = self.vlit(src);
        let n = self.gtab[sidx].len();
        for i in 0..n {
            let g = self.gtab[sidx][i];
            debug_assert!(self.lrat_chain.is_empty());
            if !self.rewrite_gate(g, dst, src, id1, id2) {
                return false;
            } else if !gt(g).garbage && gate_contains(g, dst) {
                self.goccs(dst).push(g);
            }
        }
        self.goccs(src).clear();

        #[cfg(debug_assertions)]
        {
            for occs in self.gtab.iter() {
                for &g in occs.iter() {
                    debug_assert!(!g.is_null());
                    debug_assert!(gt(g).garbage || !gate_contains(g, src));
                }
            }
        }
        debug_assert!(self.lrat_chain.is_empty());
        true
    }

    pub fn rewriting_lhs(&mut self, g: *mut Gate, dst: i32) -> bool {
        if dst != gt(g).lhs && dst != -gt(g).lhs {
            return false;
        }
        self.mark_garbage(g);
        true
    }

    // update to produce proofs
    pub fn rewrite_xor_gate(&mut self, g: *mut Gate, dst: i32, src: i32) {
        if self.skip_xor_gate(g) {
            return;
        }
        if self.rewriting_lhs(g, dst) {
            return;
        }
        if !gate_contains(g, src) {
            return;
        }
        log!(self.internal, g, "rewriting ({} -> {})", src, dst);
        self.check_xor_gate_implied(g);
        let git: GatesIterator = if gt(g).indexed { self.table.find(g) } else { None };
        let mut j = 0usize;
        let mut dst_count = 0usize;
        let original_dst_negated = dst < 0;
        let dst = self.int().vidx(dst);
        let mut negate: u32 = original_dst_negated as u32;
        let size = gt(g).rhs.len();
        for i in 0..size {
            let mut lit = gt(g).rhs[i];
            debug_assert!(lit > 0);
            if lit == src {
                lit = dst;
            }
            let v = self.val(lit);
            if v > 0 {
                negate ^= 1;
            }
            if v != 0 {
                continue;
            }
            if lit == dst {
                dst_count += 1;
            }
            log!(self.internal, "keeping value {}", lit);
            gt(g).rhs[j] = lit;
            j += 1;
        }
        if negate != 0 {
            log!(self.internal, "flipping LHS {}", gt(g).lhs);
            gt(g).lhs = -gt(g).lhs;
        }
        debug_assert!(dst_count <= 2);
        if dst_count == 2 {
            log!(self.internal, "destination found twice, removing");
            let mut k = 0usize;
            for i in 0..j {
                let lit = gt(g).rhs[i];
                if lit != dst {
                    gt(g).rhs[k] = gt(g).rhs[i];
                    k += 1;
                }
            }
            debug_assert!(k == j - 2);
            gt(g).rhs.resize(k, 0);
            gt(g).shrunken = true;
            debug_assert!({
                let internal: &Internal = self.int();
                is_sorted_by(&gt(g).rhs, |&a, &b| sort_literals_by_var_smaller(internal, a, b))
            });
        } else if j != size {
            gt(g).shrunken = true;
            gt(g).rhs.resize(j, 0);
            self.sort_literals_by_var(&mut gt(g).rhs);
        } else {
            debug_assert!(j == size);
            self.sort_literals_by_var(&mut gt(g).rhs);
        }

        debug_assert!(self.clause.is_empty());
        // LRAT for add_xor_shrinking_proof_chain
        // this should be unnecessary...
        // TODO check if really unnecessary
        if dst_count > 1 {
            self.add_xor_shrinking_proof_chain(g, dst);
        }
        debug_assert!(self.int().clause.len() <= 1);
        self.update_xor_gate(g, git);

        if !gt(g).garbage && !self.int().unsat && original_dst_negated && dst_count == 1 {
            self.connect_goccs(g, dst);
        }

        self.check_xor_gate_implied(g);
        self.int().stats.congruence.rewritten_xors += 1;
    }

    // update to produce proofs
    pub fn simplify_xor_gate(&mut self, g: *mut Gate) {
        log!(self.internal, g, "simplifying");
        if self.skip_xor_gate(g) {
            return;
        }
        self.check_xor_gate_implied(g);
        let mut negate: u32 = 0;
        let git: GatesIterator = if gt(g).indexed { self.table.find(g) } else { None };
        let size = gt(g).arity();
        let mut j = 0usize;
        for i in 0..size {
            let lit = gt(g).rhs[i];
            debug_assert!(lit > 0);
            let v = self.val(lit);
            if v > 0 {
                negate ^= 1;
            }
            if v == 0 {
                gt(g).rhs[j] = lit;
                j += 1;
            }
        }
        if negate != 0 {
            log!(self.internal, "flipping LHS literal {}", gt(g).lhs);
            gt(g).lhs = -gt(g).lhs;
        }
        if j != size {
            log!(self.internal, "shrunken gate");
            gt(g).shrunken = true;
            gt(g).rhs.resize(j, 0);
            debug_assert!({
                let internal: &Internal = self.int();
                is_sorted_by(&gt(g).rhs, |&a, &b| sort_literals_by_var_smaller(internal, a, b))
            });
        }

        self.check_xor_gate_implied(g);
        debug_assert!(self.clause.is_empty());
        self.update_xor_gate(g, git);
        log!(self.internal, g, "simplified");
        self.check_xor_gate_implied(g);
        self.int().stats.congruence.simplified += 1;
        self.int().stats.congruence.simplified_xors += 1;
    }

    /*----------------------------------------------------------------------*/
    // propagation of clauses and simplification

    pub fn schedule_literal(&mut self, lit: i32) {
        let idx = lit.abs() as usize;
        if self.scheduled[idx] {
            return;
        }
        self.scheduled[idx] = true;
        self.schedule.push_back(lit);
        debug_assert!(lit != self.find_representative(lit));
        log!(self.internal, "scheduled literal {}", lit);
    }

    pub fn propagate_unit(&mut self, lit: i32) -> bool {
        log!(self.internal, "propagation of congruence unit {}", lit);
        if self.lrat() {
            *self.lazy_propagated(lit) = 1;
        }
        self.simplify_gates(lit) && self.simplify_gates(-lit)
    }

    pub fn propagate_units(&mut self) -> bool {
        // units are added during propagation, so reloading
        while self.units != self.int().trail.len() {
            log!(self.internal, "propagating {} over gates", self.int().trail[self.units]);
            let lit = self.int().trail[self.units];
            self.units += 1;
            if !self.propagate_unit(lit) {
                return false;
            }
        }
        true
    }

    // The replacement has to be done eagerly, not lazily to make sure that
    // the gates are in normalized form. Otherwise, some merges might be
    // missed.
    pub fn propagate_equivalence(&mut self, lit: i32) -> bool {
        if self.val(lit) != 0 {
            return true;
        }
        log!(self.internal, "propagating literal {}", lit);
        self.import_lazy_and_find_eager_representative_and_compress_both(lit);
        let repr = self.find_eager_representative_and_compress(lit);
        let id1 = self.find_eager_representative_lrat(lit);
        let id2 = self.find_eager_representative_lrat(-lit);
        debug_assert!(self.lrat_chain.is_empty());
        self.rewrite_gates(repr, lit, id1, id2) && self.rewrite_gates(-repr, -lit, id2, id1)
    }

    pub fn propagate_units_and_equivalences(&mut self) -> usize {
        if self.int().terminated_asynchronously(1) {
            return 0;
        }
        start!(self.int(), congruencemerge);
        let mut propagated: usize = 0;
        log!(self.internal, "propagating at least {} units", self.schedule.len());
        debug_assert!(self.lrat_chain.is_empty());
        while self.propagate_units() && !self.schedule.is_empty() {
            if self.int().terminated_asynchronously(1) {
                return 0;
            }
            debug_assert!(!self.int().unsat);
            debug_assert!(self.lrat_chain.is_empty());
            propagated += 1;
            let lit = *self.schedule.front().unwrap();
            self.schedule.pop_front();
            self.scheduled[lit.abs() as usize] = false;
            if !self.propagate_equivalence(lit) {
                break;
            }
        }

        debug_assert!(self.int().unsat || self.schedule.is_empty());
        debug_assert!(self.int().unsat || self.lrat_chain.is_empty());

        log!(self.internal, "propagated {} congruence units", self.units);
        log!(self.internal, "propagated {} congruence equivalences", propagated);

        #[cfg(debug_assertions)]
        {
            if !self.int().unsat {
                for oi in 0..self.gtab.len() {
                    for gi in 0..self.gtab[oi].len() {
                        let g = self.gtab[oi][gi];
                        if gt(g).garbage {
                            continue;
                        }
                        debug_assert!(
                            gt(g).tag == Gate_Type::ITE_Gate
                                || gt(g).tag == Gate_Type::XOr_Gate
                                || !gate_contains(g, -gt(g).lhs)
                        );
                        for &lit in gt(g).rhs.iter() {
                            debug_assert!(self.val(lit) == 0);
                            debug_assert!(self.representative(lit) == lit);
                        }
                    }
                }
                for g in self.table.gates() {
                    if gt(g).garbage {
                        continue;
                    }
                    if gt(g).tag == Gate_Type::And_Gate {
                        // assert (find_and_lits(g->arity, g->rhs));
                    }
                }
            }
        }
        stop!(self.int(), congruencemerge);
        propagated
    }

    pub fn reset_closure(&mut self) {
        self.scheduled.clear();
        let mut it = self.table.set.begin();
        while let Some(node) = it {
            let g = self.table.get(node);
            debug_assert!(gt(g).indexed);
            log!(self.internal, g, "deleting");
            if !gt(g).garbage {
                delete_gate(g);
            }
            it = self.table.set.next(node);
        }
        self.table.clear();

        for occ in self.gtab.iter_mut() {
            occ.clear();
        }
        self.gtab.clear();

        for &gate in self.garbage.iter() {
            delete_gate(gate);
        }
        self.garbage.clear();

        if self.lrat() {
            debug_assert!(self.int().proof.is_some());
            for i in 0..self.extra_clauses.len() {
                let c = self.extra_clauses[i];
                debug_assert!(!c.garbage());
                self.int().proof.as_mut().unwrap().delete_clause(c);
                // SAFETY: temporary clauses are allocated with 'CRef::alloc'
                // in 'new_tmp_clause' and only freed here.
                unsafe { c.dealloc() };
            }
            self.extra_clauses.clear();
        } else {
            debug_assert!(self.extra_clauses.is_empty());
        }
    }

    pub fn reset_extraction(&mut self) {
        self.full_watching = true;
        if !self.int().unsat && !self.int().propagate() {
            self.int().learn_empty_clause();
            return;
        }

        self.new_unwatched_binary_clauses.clear();
        self.int().clear_watches();
        self.int().connect_watches(false);
    }

    pub fn forward_subsume_matching_clauses(&mut self) {
        start!(self.int(), congruencematching);
        self.reset_closure();
        let mut matchable: Vec<i8> = Vec::new();
        matchable.resize(self.int().max_var as usize + 1, 0);
        let mut count_matchable: usize = 0;
        for idx in self.int().vars() {
            if !self.int().flags(idx).active() {
                let _ = self.find_representative_and_compress_no_proofs(idx);
                continue;
            }
            let lit = idx;
            let repr = self.find_representative_and_compress_no_proofs(lit);
            if lit == repr {
                continue;
            }
            let repr_idx = self.int().vidx(repr) as usize;
            if matchable[idx as usize] == 0 {
                log!(self.internal, "matchable {}", idx);
                matchable[idx as usize] = 1;
                count_matchable += 1;
            }

            if matchable[repr_idx] == 0 {
                log!(self.internal, "matchable {}", repr_idx);
                matchable[repr_idx] = 1;
                count_matchable += 1;
            }
        }

        verbose!(
            self.internal,
            3,
            "congruence found {} matchable variables {}%",
            count_matchable,
            crate::format::fmt_f(percent(count_matchable as f64, self.int().max_var as f64), 0)
        );
        let mut candidates: Vec<ClauseSize> = Vec::new();
        let mut potential: usize = 0;

        let nclauses = self.int().clauses.len();
        for ci in 0..nclauses {
            let c = self.int().clauses[ci];
            if c.garbage() {
                continue;
            }
            if c.redundant() {
                continue;
            }
            if c.size() == 2 {
                continue;
            }
            potential += 1;
            debug_assert!(self.int().analyzed.is_empty());
            let mut contains_matchable = false;
            let csize = c.size() as usize;
            for i in 0..csize {
                let lit = c.lit(i);
                let v = self.val(lit);
                if v < 0 {
                    continue;
                }
                if v > 0 {
                    log!(self.internal, c, "mark satisfied");
                    self.int().mark_garbage(c);
                    break;
                }
                if !contains_matchable {
                    let idx = lit.abs() as usize;
                    if matchable[idx] != 0 {
                        contains_matchable = true;
                    }
                }

                let repr = self.find_representative_and_compress_no_proofs(lit);
                debug_assert!(self.val(repr) == 0);
                if self.mk(repr) != 0 {
                    continue;
                }
                let not_repr = -repr;
                if self.mk(not_repr) != 0 {
                    log!(self.internal, c, "matches both {} and {}", lit, not_repr);
                    self.int().mark_garbage(c);
                    break;
                }
                self.set_mk(repr, 1);
                self.int().analyzed.push(repr);
            }

            let n = self.int().analyzed.len();
            for i in 0..n {
                let lit = self.int().analyzed[i];
                self.set_mk(lit, 0);
            }
            self.int().analyzed.clear();
            if c.garbage() {
                continue;
            }
            if !contains_matchable {
                log!(self.internal, "no matching variable");
                continue;
            }
            log!(self.internal, c, "candidate");
            candidates.push(ClauseSize::from_clause(c));
        }

        verbose!(
            self.internal,
            3,
            "[congruence-{}] considering {} matchable subsumption candidates out of {} {}%",
            self.int().stats.congruence.rounds,
            candidates.len(),
            potential,
            crate::format::fmt_f(percent(candidates.len() as f64, potential as f64), 0)
        );

        rsort(&mut candidates, |a: &ClauseSize| smaller_clause_size_rank(a));
        let mut tried: usize = 0;
        let mut subsumed: usize = 0;
        self.int().init_occs();
        for &c in candidates.iter() {
            debug_assert!(c.size != 2);
            if self.int().terminated_asynchronously(1) {
                break;
            }
            tried += 1;
            if self.find_subsuming_clause(c.clause) {
                subsumed += 1;
            }
        }
        verbose!(
            self.internal,
            3,
            "[congruence-{}] subsumed {} clauses out of {} tried {}% clauses",
            self.int().stats.congruence.rounds,
            subsumed,
            tried,
            crate::format::fmt_f(percent(subsumed as f64, tried as f64), 0)
        );
        stop!(self.int(), congruencematching);
    }

    /*----------------------------------------------------------------------*/
    // Candidate clause 'subsumed' is subsumed by 'subsuming'.  We need to
    // copy the function because 'congruence' is too early to include the
    // version from subsume

    pub fn subsume_clause(&mut self, subsuming: CRef, subsumed: CRef) {
        //  assert (!subsuming->redundant);
        // assert (!subsumed->redundant);
        self.int().stats.subsumed += 1;
        debug_assert!(subsuming.size() <= subsumed.size());
        log!(self.internal, subsumed, "subsumed");
        if subsumed.redundant() {
            self.int().stats.subred += 1;
        } else {
            self.int().stats.subirr += 1;
        }
        if subsumed.redundant() || !subsuming.redundant() {
            self.int().mark_garbage(subsumed);
            return;
        }
        log!(self.internal, "turning redundant subsuming clause into irredundant clause");
        subsuming.set_redundant(false);
        if let Some(proof) = self.int().proof.as_mut() {
            proof.strengthen(subsuming.id());
        }
        self.int().mark_garbage(subsumed);
        let stats = &mut self.int().stats;
        stats.current.irredundant += 1;
        stats.added.irredundant += 1;
        stats.irrlits += subsuming.size() as i64;
        debug_assert!(stats.current.redundant > 0);
        stats.current.redundant -= 1;
        debug_assert!(stats.added.redundant > 0);
        stats.added.redundant -= 1;
        // ... and keep 'stats.added.total'.
    }

    pub fn find_subsuming_clause(&mut self, subsumed: CRef) -> bool {
        debug_assert!(!subsumed.garbage());
        let mut subsuming = CRef::NULL;
        let ssize = subsumed.size() as usize;
        for i in 0..ssize {
            let lit = subsumed.lit(i);
            debug_assert!(self.val(lit) <= 0);
            let repr_lit = self.find_representative_already_compressed(lit);
            let repr_val = self.val(repr_lit);
            debug_assert!(repr_val <= 0);
            if repr_val < 0 {
                continue;
            }
            if self.mk(repr_lit) != 0 {
                continue;
            }
            debug_assert!(self.mk(-repr_lit) == 0);
            self.set_mk(repr_lit, 1);
        }
        let mut least_occuring_lit = 0;
        let mut count_least_occurring: usize = i32::MAX as usize;
        log!(self.internal, subsumed, "trying to forward subsume");

        'found_subsuming: for i in 0..ssize {
            let lit = subsumed.lit(i);
            let repr_lit = self.find_representative_already_compressed(lit);
            let count = self.int().occs(repr_lit).len();
            debug_assert!(count <= u32::MAX as usize);
            if count < count_least_occurring {
                count_least_occurring = count;
                least_occuring_lit = repr_lit;
            }
            for k in 0..count {
                let d = self.int().occs(repr_lit)[k];
                debug_assert!(!d.garbage());
                debug_assert!(subsumed != d);
                if !subsumed.redundant() && d.redundant() {
                    continue;
                }
                let mut all_marked = true;
                let dsize = d.size() as usize;
                for m in 0..dsize {
                    let other = d.lit(m);
                    let v = self.val(other);
                    if v < 0 {
                        continue;
                    }
                    debug_assert!(v == 0);
                    let repr_other = self.find_representative_already_compressed(other);
                    if self.mk(repr_other) == 0 {
                        all_marked = false;
                        break;
                    }
                    log!(self.internal, "subsuming due to {} -> {}", other, repr_other);
                }
                if !all_marked {
                    continue;
                }
                subsuming = d;
                break 'found_subsuming;
            }
        }
        if subsuming.is_null() {
            debug_assert!(least_occuring_lit != 0);
        }

        for i in 0..ssize {
            let lit = subsumed.lit(i);
            let repr_lit = self.find_representative_already_compressed(lit);
            let v = self.val(lit);
            if v == 0 {
                self.set_mk(repr_lit, 0);
            }
        }
        if !subsuming.is_null() {
            log!(self.internal, subsumed, "subsumed");
            log!(self.internal, subsuming, "subsuming");
            self.subsume_clause(subsuming, subsumed);
            self.int().stats.congruence.subsumed += 1;
            true
        } else {
            self.int().occs_mut(least_occuring_lit).push(subsumed);
            false
        }
    }

    /*----------------------------------------------------------------------*/

    pub fn produce_ite_merge_then_else_reasons(
        &mut self,
        g: *mut Gate,
        src: i32,
        dst: i32,
        reasons_implication: &mut Vec<i64>,
        reasons_back: &mut Vec<i64>,
    ) {
        debug_assert!(!gt(g).garbage);
        if !self.lrat() {
            return;
        }
        check_correct_ite_flags(g);
        // no merge is happening actually
        debug_assert!({
            let (r1, r2) = (gt(g).rhs[1], gt(g).rhs[2]);
            r1 == self.find_eager_representative(r1) || r2 == self.find_eager_representative(r2)
        });
        let lhs_repr = self.find_eager_representative(gt(g).lhs);
        if lhs_repr == gt(g).rhs[1] || self.find_eager_representative(gt(g).lhs) == gt(g).rhs[2] {
            return;
        }
        {
            let g = gt(g);
            if (g.rhs[1] == src && g.lhs == dst && g.rhs[2] == g.lhs)
                || (g.rhs[2] == src && g.lhs == dst && g.rhs[1] == g.lhs)
                || (g.rhs[1] == -src && g.lhs == -dst && g.rhs[2] == g.lhs)
                || (g.rhs[2] == -src && g.lhs == -dst && g.rhs[1] == g.lhs)
            {
                return;
            }
        }
        self.check_ite_lrat_reasons(g);
        debug_assert!(gt(g).arity() == 3);
        debug_assert!(src == gt(g).rhs[1] || src == gt(g).rhs[2]);
        debug_assert!(dst == gt(g).rhs[1] || dst == gt(g).rhs[2]);
        let flag = gt(g).degenerated_gate;
        debug_assert!(!ite_flags_no_then_clauses(flag)); // e = lhs: already merged
        debug_assert!(!ite_flags_no_else_clauses(flag)); // t = lhs: already merged
        let lhs = gt(g).lhs;
        self.produce_rewritten_clause_lrat_pairs(&mut gt(g).pos_lhs_ids, lhs, false);
        if ite_flags_neg_cond_lhs(flag) {
            log!(self.internal, "degenerated case with lhs = -cond");
            log!(self.internal, gt(g).pos_lhs_ids[1].clause, "1:");
            log!(self.internal, gt(g).pos_lhs_ids[2].clause, "2:");
            reasons_back.push(gt(g).pos_lhs_ids[1].clause.id());
            reasons_implication.push(gt(g).pos_lhs_ids[2].clause.id());
            return;
        }
        if ite_flags_cond_lhs(flag) {
            log!(self.internal, "degenerated case with lhs = cond");
            debug_assert!(!gt(g).pos_lhs_ids[0].clause.is_null());
            debug_assert!(!gt(g).pos_lhs_ids[3].clause.is_null());
            reasons_back.push(gt(g).pos_lhs_ids[3].clause.id());
            reasons_implication.push(gt(g).pos_lhs_ids[0].clause.id());
            return;
        }
        reasons_implication.push(gt(g).pos_lhs_ids[0].clause.id());
        reasons_implication.push(gt(g).pos_lhs_ids[2].clause.id());
        reasons_back.push(gt(g).pos_lhs_ids[1].clause.id());
        reasons_back.push(gt(g).pos_lhs_ids[3].clause.id());
    }

    pub fn rewrite_ite_gate_update_lrat_reasons(&mut self, g: *mut Gate, src: i32, dst: i32) {
        if !self.lrat() {
            return;
        }
        log!(self.internal, g, "updating lrat from");
        for litId in gt(g).pos_lhs_ids.iter_mut() {
            debug_assert!(!litId.clause.is_null() || gt(g).degenerated_gate != Special_Gate::NORMAL);
            if litId.current_lit == src {
                litId.current_lit = dst;
            }
            if litId.current_lit == -src {
                litId.current_lit = -dst;
            }
        }
        self.check_ite_lrat_reasons(g);
    }

    // Transforms an ITE gate to an AND gate
    //
    // In essence the transformation is simple for LRAT: two long clause need
    // to be resolved to get a binary and one long clause stays the long
    // ternary clause for the resulting gate.  There are two things to be
    // careful: we have to rewrite the LHS too, because if it appears on the
    // RHS too, it will not get rewritten and the proof will not work.
    pub fn rewrite_ite_gate_to_and(
        &mut self,
        g: *mut Gate,
        src: i32,
        dst: i32,
        idx1: usize,
        idx2: usize,
        cond_lit_to_learn_if_degenerated: i32,
    ) -> bool {
        let mut idx1 = idx1;
        let mut idx2 = idx2;
        debug_assert!(self.int().lrat_chain.is_empty());
        debug_assert!(!gt(g).garbage);
        log!(self.internal, g, "rewriting to proper AND gate, namely");
        if self.val(gt(g).lhs) > 0 {
            {
                let lit = gt(g).rhs[0];
                let v = self.val(lit);
                if v > 0 {
                } else if v == 0 {
                    if self.lrat() {
                        let c = gt(g).pos_lhs_ids[idx1].clause;
                        self.push_id_and_rewriting_lrat_unit_self(c, Rewrite::default(), true, Rewrite::default(), 0, 0);
                    }
                    self.learn_congruence_unit(cond_lit_to_learn_if_degenerated, false, false);
                } else {
                    if self.lrat() {
                        let c = gt(g).pos_lhs_ids[idx1].clause;
                        self.push_id_and_rewriting_lrat_unit_self(c, Rewrite::default(), true, Rewrite::default(), 0, 0);
                    }
                    self.push_lrat_unit(-lit);
                    self.int().learn_empty_clause();
                    return true;
                }
            }
            if !self.int().unsat {
                let lit = gt(g).rhs[1];
                let v = self.val(lit);
                let (r0, r1) = (gt(g).rhs[0], gt(g).rhs[1]);
                debug_assert!(dst == r0 || dst == r1 || -dst == r0 || -dst == r1);
                let other = if dst == r0 || dst == r1 { dst ^ r0 ^ r1 } else { (-dst) ^ r0 ^ r1 };
                if v > 0 {
                    // already set by propagation
                    return true;
                } else if v == 0 {
                    if self.lrat() {
                        let c = gt(g).pos_lhs_ids[idx2].clause;
                        self.push_id_and_rewriting_lrat_unit_self(c, Rewrite::default(), true, Rewrite::default(), 0, 0);
                    }
                    self.learn_congruence_unit(other, false, false);
                } else {
                    if self.lrat() {
                        self.push_lrat_unit(cond_lit_to_learn_if_degenerated);
                        let c = gt(g).pos_lhs_ids[idx2].clause;
                        self.push_id_and_rewriting_lrat_unit_self(c, Rewrite::default(), true, Rewrite::default(), 0, 0);
                    }
                    self.int().learn_empty_clause();
                    return true;
                }
            }
            return true;
        }
        if src == gt(g).lhs {
            gt(g).lhs = dst;
        } else if src == -gt(g).lhs {
            gt(g).lhs = -dst;
        }
        if !self.lrat() {
            return false;
        }
        log!(self.internal, g, "updating flags for");

        if gt(g).rhs[1] == -gt(g).lhs || gt(g).rhs[0] == -gt(g).lhs {
            gt(g).degenerated_gate = Special_Gate::DEGENERATED_AND;
        }

        if gt(g).degenerated_gate == Special_Gate::DEGENERATED_AND
            || gt(g).degenerated_gate == Special_Gate::DEGENERATED_AND_LHS_FALSE
        {
            log!(self.internal, "degenerated AND gate");
            debug_assert!(gt(g).rhs[1] == -gt(g).lhs || gt(g).rhs[0] == -gt(g).lhs);
            if gt(g).rhs[1] == -gt(g).lhs {
                if gt(g).rhs[0] == -gt(g).lhs {
                    // -2 := ITE 1 2 2: we need
                    // we need 2 3
                    let c1 = gt(g).pos_lhs_ids[2].clause;
                    let d1 = self.produce_rewritten_clause_lrat(c1, 0, true, false);
                    gt(g).pos_lhs_ids[2].clause = d1;
                    let c2 = gt(g).pos_lhs_ids[3].clause;
                    let d2 = self.produce_rewritten_clause_lrat(c2, 0, true, false);
                    gt(g).pos_lhs_ids[3].clause = d2;
                    debug_assert!(!d1.is_null());
                    debug_assert!(!d2.is_null());
                    self.lrat_chain.push(d1.id());
                    self.lrat_chain.push(d2.id());
                    // push_id_and_rewriting_lrat_unit (g->pos_lhs_ids[0].clause,
                    //                                  Rewrite (), lrat_chain);
                } else {
                    // -1 := ITE -4 1 -1 we need 3
                    // -2 := ITE 1 2 2 we need 2
                    log!(self.internal, "g->rhs[0] != -g->lhs");
                    let idx = if gt(g).lhs == gt(g).rhs[2] { 3 } else { 2 };
                    let c = gt(g).pos_lhs_ids[idx].clause;
                    self.push_id_and_rewriting_lrat_unit_self(c, Rewrite::default(), true, Rewrite::default(), 0, 0);
                }
                let lhs = gt(g).lhs;
                self.learn_congruence_unit(-lhs, false, false);
                return true;
            }
            if gt(g).rhs[0] == -gt(g).lhs {
                log!(self.internal, "g->rhs[0] == -g->lhs");
                let c = if gt(g).lhs > 0 { gt(g).pos_lhs_ids[1].clause } else { gt(g).pos_lhs_ids[0].clause };
                self.push_id_and_rewriting_lrat_unit_self(c, Rewrite::default(), true, Rewrite::default(), 0, 0);
                let lhs = gt(g).lhs;
                self.learn_congruence_unit(-lhs, false, false);
                return true;
            }
        }
        if gt(g).rhs[0] == gt(g).lhs || gt(g).rhs[1] == gt(g).lhs {
            gt(g).degenerated_gate = Special_Gate::DEGENERATED_AND;
        }

        debug_assert!(gt(g).arity() == 3);
        debug_assert!(gt(g).pos_lhs_ids.len() == 4);
        debug_assert!(idx1 < gt(g).pos_lhs_ids.len());
        debug_assert!(idx2 < gt(g).pos_lhs_ids.len());
        let lit = gt(g).pos_lhs_ids[idx2].current_lit;
        let other = gt(g).lhs;
        // TODO: remove argument
        let _ = src;
        let lhs = gt(g).lhs;
        self.produce_rewritten_clause_lrat_and_clean_positions(&mut gt(g).pos_lhs_ids, lhs, &mut idx1, &mut idx2, false);

        if idx1 == usize::MAX || idx2 == usize::MAX {
            // degenerated and gate
            return false;
        }

        debug_assert!(idx1 < gt(g).pos_lhs_ids.len());
        debug_assert!(idx2 < gt(g).pos_lhs_ids.len());
        let c = gt(g).pos_lhs_ids[idx1].clause;
        debug_assert!(c.size() == 2);
        let d = gt(g).pos_lhs_ids[idx2].clause;
        debug_assert!(c != d);
        debug_assert!(!c.is_null());
        debug_assert!(!d.is_null());
        gt(g).pos_lhs_ids.retain(|p| !(p.clause == d || p.clause.is_null()));
        debug_assert!(gt(g).pos_lhs_ids.len() == 2);
        debug_assert!(lit != 0);
        debug_assert!(other != 0);
        debug_assert!(lit != dst);
        debug_assert!(other != dst);
        debug_assert!(lit != other);
        self.lrat_chain.push(c.id());
        self.lrat_chain.push(d.id());
        let e = self.learn_binary_tmp_or_full_clause(lit, -other);
        debug_assert!(!e.is_null());

        let long_clause = gt(g).pos_lhs_ids.iter().position(|l| l.clause.size() == 3);
        debug_assert!(long_clause.is_some());
        let long_clause = long_clause.unwrap();
        log!(self.internal, gt(g).pos_lhs_ids[long_clause].clause, "new long clause");
        let lc = gt(g).pos_lhs_ids[long_clause];
        gt(g).neg_lhs_ids.set(lc);
        gt(g).pos_lhs_ids.remove(long_clause);

        debug_assert!(gt(g).pos_lhs_ids.len() == 1);

        let c0 = gt(g).pos_lhs_ids[0].clause;
        let _ = self.maybe_promote_tmp_binary_clause(c0);
        gt(g).pos_lhs_ids.push(LitClausePair::new(lit, e));
        #[cfg(debug_assertions)]
        {
            let n = gt(g).pos_lhs_ids.len();
            for i in 0..n {
                let litId = gt(g).pos_lhs_ids[i];
                let mut found = false;
                debug_assert!(!litId.clause.is_null());
                for k in 0..litId.clause.size() as usize {
                    let other = litId.clause.lit(k);
                    found = self.find_eager_representative(other) == litId.current_lit;
                    if found {
                        break;
                    }
                }
                debug_assert!(found);
            }
            for id in gt(g).pos_lhs_ids.clone() {
                log!(self.internal, id.clause, "clause after rewriting:");
                debug_assert!(id.clause.size() == 2);
            }
        }
        false
    }

    pub fn produce_ite_merge_rhs_cond(&mut self, g: *mut Gate, else_lit: i32, lhs: i32) {
        debug_assert!(self.unsimplified.is_empty());
        if self.lrat() {
            let gl = gt(g).lhs;
            self.produce_rewritten_clause_lrat_and_clean(&mut gt(g).pos_lhs_ids, gl, false, true);
            debug_assert!(gt(g).pos_lhs_ids.len() == 2);
            debug_assert!(self.lrat_chain.is_empty());
            self.lrat_chain.push(gt(g).pos_lhs_ids[0].clause.id());
            self.lrat_chain.push(gt(g).pos_lhs_ids[1].clause.id());
        } else if self.int().proof.is_some() {
            self.unsimplified.push(-else_lit);
            self.unsimplified.push(lhs);
            self.simplify_and_add_unsimplified_to_proof_chain(0);
            self.unsimplified.clear();
        }
    }

    /// Rewrites 'g->pos_lhs_ids[idx].clause' with 'produce_rewritten_clause_lrat
    /// (clause, g->lhs, false)'.
    fn rewrite_gate_clause_idx(&mut self, g: *mut Gate, idx: usize) -> CRef {
        let c = gt(g).pos_lhs_ids[idx].clause;
        let lhs = gt(g).lhs;
        let d = self.produce_rewritten_clause_lrat(c, lhs, false, false);
        gt(g).pos_lhs_ids[idx].clause = d;
        d
    }

    pub fn produce_ite_merge_lhs_then_else_reasons(
        &mut self,
        g: *mut Gate,
        reasons_implication: &mut Vec<i64>,
        reasons_back: &mut Vec<i64>,
        reasons_unit: &mut Vec<i64>,
        rewritting_then: bool,
        learn_units: &mut bool,
    ) {
        if self.int().proof.is_none() {
            return;
        }
        let idx1: usize = if rewritting_then { 0 } else { 2 };
        let idx2: usize = idx1 + 1;
        let other_idx1: usize = if rewritting_then { 2 } else { 0 };
        let other_idx2: usize = other_idx1 + 1;
        let cond_lit = gt(g).rhs[0];
        let lit_to_merge = gt(g).rhs[if rewritting_then { 2 } else { 1 }];
        let other_lit = gt(g).rhs[if rewritting_then { 1 } else { 2 }];
        let repr_cond_lit = self.find_eager_representative(gt(g).rhs[0]);
        let repr_lit_to_merge = self.find_eager_representative(lit_to_merge);
        let repr_other_lit = self.find_eager_representative(other_lit);
        let repr_lhs = self.find_eager_representative(gt(g).lhs);

        log!(self.internal, "cond: {}, merging {} and rewriting to {}", cond_lit, lit_to_merge, other_lit);
        if self.lrat() {
            debug_assert!(!self.lrat() || gt(g).pos_lhs_ids.len() == 4);

            if repr_lhs == -repr_other_lit {
                log!(
                    self.internal,
                    "special case: {}={}, checking if other: {} {}",
                    loglit!(self.internal, gt(g).lhs),
                    loglit!(self.internal, -lit_to_merge),
                    loglit!(self.internal, cond_lit),
                    loglit!(self.internal, other_lit)
                );
                // should have been rewritten before
                debug_assert!(repr_lit_to_merge != -repr_lhs);

                if rewritting_then && repr_cond_lit == repr_lhs {
                    log!(self.internal, "t=-lhs/c=lhs");
                    *learn_units = true;
                    // is a unit
                    self.unsimplified.push(-cond_lit);
                    let c = gt(g).pos_lhs_ids[0].clause;
                    self.push_id_and_rewriting_lrat_unit_self(c, Rewrite::default(), true, Rewrite::default(), 0, 0);
                    let id_unit = self.simplify_and_add_unsimplified_to_proof_chain(0);
                    self.unsimplified.clear();
                    *reasons_unit = vec![id_unit];
                    // don't bother finding out which one is used
                    reasons_implication.push(id_unit);
                    let d = self.rewrite_gate_clause_idx(g, 3);
                    debug_assert!(!d.is_null());
                    reasons_implication.push(d.id());
                    return;
                }
                if !rewritting_then && repr_cond_lit == repr_lhs {
                    log!(self.internal, "e=-lhs/c=lhs");
                    *learn_units = true;
                    // is a unit
                    self.unsimplified.push(cond_lit);
                    let c = gt(g).pos_lhs_ids[3].clause;
                    self.push_id_and_rewriting_lrat_unit_self(c, Rewrite::default(), true, Rewrite::default(), 0, 0);
                    let id_unit = self.simplify_and_add_unsimplified_to_proof_chain(0);
                    self.unsimplified.clear();
                    *reasons_unit = vec![id_unit];
                    // don't bother finding out which one is used
                    reasons_implication.push(id_unit);
                    let d = self.rewrite_gate_clause_idx(g, 0);
                    debug_assert!(!d.is_null());
                    reasons_implication.push(d.id());
                    return;
                }
                if !rewritting_then && repr_cond_lit == -repr_lhs {
                    log!(self.internal, "e=-lhs/c=-lhs");
                    *learn_units = true;
                    self.unsimplified.push(cond_lit);
                    // TODO: this function does not work to produce units for
                    // this case (see the C++ source for the example)
                    let c = gt(g).pos_lhs_ids[2].clause;
                    self.push_id_and_rewriting_lrat_unit_self(c, Rewrite::default(), true, Rewrite::default(), 0, 0);
                    let id_unit = self.simplify_and_add_unsimplified_to_proof_chain(0);
                    self.unsimplified.clear();
                    *reasons_unit = vec![id_unit];
                    let d = self.rewrite_gate_clause_idx(g, 1);
                    debug_assert!(!d.is_null());

                    // don't bother finding out which one is used
                    reasons_implication.push(id_unit);
                    reasons_implication.push(d.id());
                    return;
                }
                if rewritting_then && repr_cond_lit == -repr_lhs {
                    log!(self.internal, "t=-lhs/c=-lhs");
                    *learn_units = true;
                    self.unsimplified.push(-cond_lit);
                    let c = gt(g).pos_lhs_ids[1].clause;
                    self.push_id_and_rewriting_lrat_unit_self(c, Rewrite::default(), true, Rewrite::default(), 0, 0);
                    let id_unit = self.simplify_and_add_unsimplified_to_proof_chain(0);
                    self.unsimplified.clear();
                    *reasons_unit = vec![id_unit];
                    let d = self.rewrite_gate_clause_idx(g, 2);
                    debug_assert!(!d.is_null());

                    reasons_implication.push(id_unit);
                    reasons_implication.push(d.id());
                    return;
                }
                if rewritting_then && repr_lit_to_merge == repr_lhs {
                    log!(self.internal, "t=-lhs/e=lhs from rewriting then");
                    *learn_units = true;
                    let d1 = self.rewrite_gate_clause_idx(g, idx1);
                    let d2 = self.rewrite_gate_clause_idx(g, idx2);
                    debug_assert!(!d1.is_null());
                    debug_assert!(!d2.is_null());
                    self.lrat_chain.push(d1.id());
                    self.lrat_chain.push(d2.id());
                    self.unsimplified.push(-cond_lit);
                    let id_unit = self.simplify_and_add_unsimplified_to_proof_chain(0);
                    self.unsimplified.clear();
                    *reasons_unit = vec![id_unit];
                    return;
                }
                if !rewritting_then && repr_lit_to_merge == repr_lhs {
                    log!(self.internal, "t=-lhs/e=lhs from rewriting else");
                    *learn_units = true;
                    let d1 = self.rewrite_gate_clause_idx(g, idx1);
                    let d2 = self.rewrite_gate_clause_idx(g, idx2);
                    debug_assert!(!d1.is_null());
                    debug_assert!(!d2.is_null());
                    self.lrat_chain.push(d1.id());
                    self.lrat_chain.push(d2.id());
                    self.unsimplified.push(cond_lit);
                    let id_unit = self.simplify_and_add_unsimplified_to_proof_chain(0);
                    *reasons_unit = vec![id_unit];
                    self.unsimplified.clear();
                    return;
                }

                if other_lit == repr_lhs {
                    *learn_units = true;
                    // in the other direction we are merging a literal with
                    // itself
                    let d1 = self.rewrite_gate_clause_idx(g, idx1);
                    let d2 = self.rewrite_gate_clause_idx(g, idx2);
                    debug_assert!(!d1.is_null());
                    debug_assert!(!d2.is_null());
                    reasons_unit.push(d1.id());
                    reasons_unit.push(d2.id());
                    return;
                }
            }

            log!(self.internal, "normal path");
            let lhs = gt(g).lhs;
            self.produce_rewritten_clause_lrat_pairs(&mut gt(g).pos_lhs_ids, lhs, false);
            debug_assert!(gt(g).pos_lhs_ids.len() == 4);

            reasons_unit.push(gt(g).pos_lhs_ids[idx1].clause.id());
            reasons_unit.push(gt(g).pos_lhs_ids[idx2].clause.id());

            // already merged: only unit is important
            if !rewritting_then && repr_lhs == repr_lit_to_merge {
                return;
            }

            reasons_implication.push(gt(g).pos_lhs_ids[other_idx1].clause.id());
            reasons_implication.push(gt(g).pos_lhs_ids[idx1].clause.id());
            reasons_implication.push(gt(g).pos_lhs_ids[idx2].clause.id());

            reasons_back.push(gt(g).pos_lhs_ids[other_idx2].clause.id());
            reasons_back.push(gt(g).pos_lhs_ids[idx1].clause.id());
            reasons_back.push(gt(g).pos_lhs_ids[idx2].clause.id());
        } else {
            log!(self.internal, "learn extra clauses XXXXXXXXXXXXXXXXXXXXXXXXX");
            let lhs = gt(g).lhs;
            let cond = gt(g).rhs[0];
            if rewritting_then {
                self.unsimplified.push(-cond);
                self.unsimplified.push(lhs);
                self.simplify_and_add_unsimplified_to_proof_chain(0);
                self.unsimplified.push(-cond);
                self.unsimplified.push(-lhs);
                self.simplify_and_add_unsimplified_to_proof_chain(0);
            } else {
                self.unsimplified.push(cond);
                self.unsimplified.push(-lhs);
                self.simplify_and_add_unsimplified_to_proof_chain(0);
                self.unsimplified.push(cond);
                self.unsimplified.push(lhs);
                self.simplify_and_add_unsimplified_to_proof_chain(0);
            }
            self.unsimplified.clear();
        }
    }

    pub fn rewrite_ite_gate(&mut self, g: *mut Gate, dst: i32, src: i32) {
        debug_assert!(self.unsimplified.is_empty());
        if skip_ite_gate(g) {
            return;
        }
        if !gate_contains(g, src) {
            return;
        }
        log!(self.internal, g, "rewriting {} by {} in", src, dst);
        debug_assert!(!gt(g).shrunken);
        debug_assert!(gt(g).arity() == 3);
        debug_assert!(!self.lrat() || gt(g).pos_lhs_ids.len() == 4);
        let lhs = gt(g).lhs;
        let cond = gt(g).rhs[0];
        let then_lit = gt(g).rhs[1];
        let else_lit = gt(g).rhs[2];
        let not_lhs = -lhs;
        let not_dst = -dst;
        let not_cond = -cond;
        let not_then_lit = -then_lit;
        let not_else_lit = -else_lit;
        let mut new_tag = Gate_Type::And_Gate;

        let mut garbage = false;
        let mut shrink = true;
        let git: GatesIterator = if gt(g).indexed { self.table.find(g) } else { None };
        debug_assert!(!gt(g).indexed || git.is_some());
        debug_assert!(git.map_or(true, |it| self.table.get(it) == g));
        if self.val(cond) != 0 && self.val(then_lit) != 0 && self.val(else_lit) != 0 {
            // propagation has set all value anyway
            log!(self.internal, g, "all values are set");
            debug_assert!(self.val(gt(g).lhs) != 0);
            garbage = true;
        } else if self.val(gt(g).lhs) != 0 && self.val(cond) != 0 {
            log!(self.internal, g, "all values are set 2");
            debug_assert!(self.val(gt(g).lhs) != 0);
            garbage = true;
        }
        // this code is taken one-to-one from kissat
        else if src == cond {
            if dst == then_lit {
                // then_lit ? then_lit : else_lit
                // then_lit & then_lit | !then_lit & else_lit
                // then_lit | !then_lit & else_lit
                // then_lit | else_lit
                // !(!then_lit & !else_lit)
                gt(g).lhs = not_lhs;
                gt(g).rhs[0] = not_then_lit;
                gt(g).rhs[1] = not_else_lit;
                if then_lit == lhs || else_lit == lhs {
                    garbage = true;
                } else {
                    garbage = self.rewrite_ite_gate_to_and(g, src, dst, 1, 3, -dst);
                }
            } else if not_dst == then_lit {
                // !then_lit ? then_lit : else_lit
                // !then_lit & then_lit | then_lit & else_lit
                // then_lit & else_lit
                gt(g).rhs[0] = then_lit;
                gt(g).rhs[1] = else_lit;
                garbage = self.rewrite_ite_gate_to_and(g, src, dst, 0, 2, -dst);
            } else if dst == else_lit {
                // else_list ? then_lit : else_lit
                // else_list & then_lit | !else_list & else_lit
                // else_list & then_lit
                gt(g).rhs[0] = then_lit;
                gt(g).rhs[1] = else_lit;
                garbage = self.rewrite_ite_gate_to_and(g, src, dst, 2, 0, dst);
            } else if not_dst == else_lit {
                // !else_list ? then_lit : else_lit
                // !else_list & then_lit | else_lit & else_lit
                // !else_list & then_lit | else_lit
                // then_lit | else_lit
                // !(!then_lit & !else_lit)
                gt(g).lhs = not_lhs;
                gt(g).rhs[0] = not_then_lit;
                gt(g).rhs[1] = not_else_lit;
                if then_lit == lhs || else_lit == lhs {
                    garbage = true;
                } else {
                    garbage = self.rewrite_ite_gate_to_and(g, src, dst, 3, 1, dst);
                }
            } else {
                shrink = false;
                gt(g).rhs[0] = dst;
                self.rewrite_ite_gate_update_lrat_reasons(g, src, dst);
            }
        } else if src == then_lit {
            if not_dst == gt(g).lhs {
                // TODO not in kissat
                gt(g).rhs[1] = dst;
                let gl = gt(g).lhs;
                self.check_ite_implied(gl, cond, then_lit, else_lit);
                let mut reasons_implication: Vec<LRAT_ID> = Vec::new();
                let mut reasons_back: Vec<LRAT_ID> = Vec::new();
                let mut reasons_unit: Vec<LRAT_ID> = Vec::new();
                log!(self.internal, "{} = {} ?", gt(g).lhs, -gt(g).rhs[0]);
                let mut learn_units_instead_of_equivalence = false;
                self.produce_ite_merge_lhs_then_else_reasons(
                    g,
                    &mut reasons_implication,
                    &mut reasons_back,
                    &mut reasons_unit,
                    true,
                    &mut learn_units_instead_of_equivalence,
                );
                if learn_units_instead_of_equivalence {
                    // it is too hard to produce LRAT chains in this case
                    if self.lrat() {
                        self.lrat_chain = reasons_unit.clone();
                    }
                    self.learn_congruence_unit(-cond, true, false);
                    if -else_lit == lhs {
                        if self.lrat() {
                            self.lrat_chain = reasons_implication.clone();
                        }
                        self.learn_congruence_unit(if cond == -lhs { -else_lit } else { else_lit }, false, true);
                    } else {
                        self.fully_propagate();
                    }
                } else {
                    let gl = gt(g).lhs;
                    if self.merge_literals(gl, else_lit, &reasons_implication, &reasons_back) {
                        self.int().stats.congruence.unaries += 1;
                        self.int().stats.congruence.unary_ites += 1;
                    }
                    if !self.int().unsat {
                        if self.lrat() {
                            self.lrat_chain = reasons_unit.clone();
                        }
                        self.learn_congruence_unit(-cond, false, false);
                    }
                }
                self.delete_proof_chain();
                garbage = true;
            } else if dst == cond {
                // cond ? cond : else_lit
                // cond & cond | !cond & else_lit
                // cond | !cond & else_lit
                // cond | else_lit
                // !(!cond & !else_lit)
                gt(g).lhs = not_lhs;
                gt(g).rhs[0] = not_cond;
                gt(g).rhs[1] = not_else_lit;
                if else_lit == lhs || cond == lhs {
                    garbage = true;
                } else {
                    garbage = self.rewrite_ite_gate_to_and(g, src, dst, 1, 3, -cond);
                }
            } else if not_dst == cond {
                // cond ? !cond : else_lit
                // cond & !cond | !cond & else_lit
                // !cond & else_lit
                gt(g).rhs[0] = not_cond;
                gt(g).rhs[1] = else_lit;
                garbage = self.rewrite_ite_gate_to_and(g, src, dst, 0, 2, -cond);
            } else if dst == else_lit {
                // cond ? else_lit : else_lit
                // else_lit
                let mut reasons_implication: Vec<LRAT_ID> = Vec::new();
                let mut reasons_back: Vec<LRAT_ID> = Vec::new();
                self.produce_ite_merge_then_else_reasons(g, src, dst, &mut reasons_implication, &mut reasons_back);
                if self.merge_literals(lhs, else_lit, &reasons_implication, &reasons_back) {
                    self.int().stats.congruence.unaries += 1;
                    self.int().stats.congruence.unary_ites += 1;
                }
                self.delete_proof_chain();
                garbage = true;
            } else if not_dst == else_lit {
                // cond ? !else_lit : else_lit
                // cond & !else_lit | !cond & else_lit
                // cond ^ else_lit
                if gt(g).lhs == cond {
                    // not in Kissat
                    // TODO: can we trigger g->lhs == -cond?
                    self.produce_ite_merge_rhs_cond(g, else_lit, lhs);
                    self.learn_congruence_unit(-else_lit, false, false);
                    if !self.chain.is_empty() {
                        self.delete_proof_chain();
                    }
                    garbage = true;
                } else {
                    log!(
                        self.internal,
                        "changing to xor {} = {} ^ {}",
                        loglit!(self.internal, gt(g).lhs),
                        loglit!(self.internal, cond),
                        loglit!(self.internal, else_lit)
                    );
                    new_tag = Gate_Type::XOr_Gate;
                    debug_assert!(gt(g).rhs[0] == cond);
                    gt(g).rhs[1] = else_lit;
                    debug_assert!(!self.lrat() || !gt(g).pos_lhs_ids.is_empty());
                    {
                        #[cfg(feature = "logging")]
                        {
                            for litId in gt(g).pos_lhs_ids.clone() {
                                log!(self.internal, litId.clause, "{} ->", litId.current_lit);
                            }
                        }
                        let gl = gt(g).lhs;
                        self.produce_rewritten_clause_lrat_and_clean(&mut gt(g).pos_lhs_ids, gl, !true, true);
                        #[cfg(feature = "logging")]
                        {
                            for litId in gt(g).pos_lhs_ids.clone() {
                                log!(self.internal, litId.clause, "{} ->", litId.current_lit);
                            }
                        }
                    }
                }
            } else {
                shrink = false;
                gt(g).rhs[1] = dst;
                self.rewrite_ite_gate_update_lrat_reasons(g, src, dst);
            }
        } else {
            debug_assert!(src == else_lit);
            if not_dst == gt(g).lhs {
                // TODO not in kissat
                gt(g).rhs[2] = dst;
                let mut reasons_implication: Vec<LRAT_ID> = Vec::new();
                let mut reasons_back: Vec<LRAT_ID> = Vec::new();
                let mut reasons_unit: Vec<LRAT_ID> = Vec::new();
                let mut learn_units_instead_of_equivalence = false;
                self.produce_ite_merge_lhs_then_else_reasons(
                    g,
                    &mut reasons_implication,
                    &mut reasons_back,
                    &mut reasons_unit,
                    false,
                    &mut learn_units_instead_of_equivalence,
                );
                if learn_units_instead_of_equivalence {
                    // Too hard to produce LRAT
                    if self.lrat() {
                        self.lrat_chain = reasons_unit.clone();
                    }
                    self.learn_congruence_unit(cond, true, false);
                    if then_lit != lhs {
                        log!(self.internal, "special case, learning {}", if cond == -lhs { -then_lit } else { then_lit });
                        if self.lrat() {
                            self.lrat_chain = reasons_implication.clone();
                        }
                        self.learn_congruence_unit(if cond == -lhs { -then_lit } else { then_lit }, false, true);
                    } else {
                        self.fully_propagate();
                    }
                } else {
                    if self.merge_literals(lhs, then_lit, &reasons_implication, &reasons_back) {
                        self.int().stats.congruence.unaries += 1;
                        self.int().stats.congruence.unary_ites += 1;
                    }
                    if !self.int().unsat {
                        if self.lrat() {
                            self.lrat_chain = reasons_unit.clone();
                        }
                        self.learn_congruence_unit(cond, false, false);
                    }
                }
                self.delete_proof_chain();
                garbage = true;
            } else if dst == cond {
                // cond ? then_lit : cond
                // cond & then_lit | !cond & cond
                // cond & then_lit
                debug_assert!(gt(g).rhs[0] == cond);
                debug_assert!(gt(g).rhs[1] == then_lit);
                garbage = self.rewrite_ite_gate_to_and(g, src, dst, 2, 0, cond);
            } else if not_dst == cond {
                // cond ? then_lit : !cond
                // cond & then_lit | !cond & !cond
                // cond & then_lit | !cond
                // then_lit | !cond
                // !(!then_lit & cond)
                gt(g).lhs = not_lhs;
                debug_assert!(gt(g).rhs[0] == cond);
                gt(g).rhs[1] = not_then_lit;
                if then_lit == lhs || cond == lhs {
                    garbage = true;
                } else {
                    garbage = self.rewrite_ite_gate_to_and(g, src, dst, 3, 1, cond);
                }
            } else if dst == then_lit {
                // cond ? then_lit : then_lit
                // then_lit
                let mut reasons_implication: Vec<LRAT_ID> = Vec::new();
                let mut reasons_back: Vec<LRAT_ID> = Vec::new();
                self.produce_ite_merge_then_else_reasons(g, src, dst, &mut reasons_implication, &mut reasons_back);
                if self.merge_literals(lhs, then_lit, &reasons_implication, &reasons_back) {
                    self.int().stats.congruence.unaries += 1;
                    self.int().stats.congruence.unary_ites += 1;
                }
                garbage = true;
            } else if not_dst == then_lit {
                // cond ? then_lit : !then_lit
                // cond & then_lit | !cond & !then_lit
                // !(cond ^ then_lit)
                //
                // For the clause 11 = 11 ? 9 : 8, we have empty clauses. The
                // flag is only useful for debugging
                let allow_empty_lrat_clause = gt(g).degenerated_gate != Special_Gate::NORMAL;
                if lhs == cond {
                    if self.lrat() {
                        self.produce_rewritten_clause_lrat_and_clean(
                            &mut gt(g).pos_lhs_ids,
                            not_lhs,
                            false,
                            allow_empty_lrat_clause,
                        );
                        debug_assert!(gt(g).pos_lhs_ids.len() == 2);
                        self.lrat_chain.push(gt(g).pos_lhs_ids[0].clause.id());
                        self.lrat_chain.push(gt(g).pos_lhs_ids[1].clause.id());
                    }
                    self.learn_congruence_unit(then_lit, false, false);
                    garbage = true;
                } else if not_lhs == cond {
                    if self.lrat() {
                        self.produce_rewritten_clause_lrat_and_clean(
                            &mut gt(g).pos_lhs_ids,
                            not_lhs,
                            false,
                            allow_empty_lrat_clause,
                        );
                        debug_assert!(gt(g).pos_lhs_ids.len() == 2);
                        self.lrat_chain.push(gt(g).pos_lhs_ids[0].clause.id());
                        self.lrat_chain.push(gt(g).pos_lhs_ids[1].clause.id());
                    }
                    self.learn_congruence_unit(-then_lit, false, false);
                    garbage = true;
                } else if not_lhs == then_lit {
                    if self.lrat() {
                        self.produce_rewritten_clause_lrat_and_clean(
                            &mut gt(g).pos_lhs_ids,
                            not_lhs,
                            false,
                            allow_empty_lrat_clause,
                        );
                        debug_assert!(gt(g).pos_lhs_ids.len() == 2);
                        self.lrat_chain.push(gt(g).pos_lhs_ids[0].clause.id());
                        self.lrat_chain.push(gt(g).pos_lhs_ids[1].clause.id());
                    }
                    self.learn_congruence_unit(cond, false, false);
                    garbage = true;
                } else {
                    new_tag = Gate_Type::XOr_Gate;
                    gt(g).lhs = not_lhs;
                    debug_assert!(gt(g).rhs[0] == cond);
                    debug_assert!(gt(g).rhs[1] == then_lit);
                    debug_assert!(gt(g).rhs[0] != gt(g).lhs);
                    debug_assert!(gt(g).rhs[1] != gt(g).lhs);
                    self.produce_rewritten_clause_lrat_and_clean(&mut gt(g).pos_lhs_ids, not_lhs, false, false);
                }
            } else {
                shrink = false;
                gt(g).rhs[2] = dst;
                self.rewrite_ite_gate_update_lrat_reasons(g, src, dst);
            }
        }
        if !garbage && !self.int().unsat {
            debug_assert!(new_tag != Gate_Type::ITE_Gate || gt(g).lhs != -gt(g).rhs[1]);
            debug_assert!(new_tag != Gate_Type::ITE_Gate || gt(g).lhs != -gt(g).rhs[2]);
            if shrink {
                if new_tag == Gate_Type::XOr_Gate {
                    let mut negate_lhs = false;
                    if gt(g).rhs[0] < 0 {
                        gt(g).rhs[0] = -gt(g).rhs[0];
                        negate_lhs = !negate_lhs;
                    }
                    if gt(g).rhs[1] < 0 {
                        gt(g).rhs[1] = -gt(g).rhs[1];
                        negate_lhs = !negate_lhs;
                    }
                    if negate_lhs {
                        gt(g).lhs = -gt(g).lhs;
                    }
                }
                // unlike kissat, we need to do it after negating
                if self.int().vlit(gt(g).rhs[0]) > self.int().vlit(gt(g).rhs[1]) {
                    gt(g).rhs.swap(0, 1);
                    debug_assert!(new_tag != Gate_Type::ITE_Gate);
                }
                debug_assert!(self.int().vlit(gt(g).rhs[0]) < self.int().vlit(gt(g).rhs[1]));
                debug_assert!(!gt(g).shrunken);
                gt(g).shrunken = true;
                gt(g).rhs[2] = 0;
                gt(g).tag = new_tag;
                gt(g).rhs.resize(2, 0);
                debug_assert!(gt(g).rhs[0] != -gt(g).rhs[1]);
                if new_tag == Gate_Type::XOr_Gate {
                    if gt(g).rhs[0] == -gt(g).lhs || gt(g).rhs[1] == -gt(g).lhs {
                        log!(self.internal, g, "special XOR:");
                        let unit = gt(g).rhs[0] ^ -gt(g).lhs ^ gt(g).rhs[1];
                        self.produce_rewritten_clause_lrat_and_clean(&mut gt(g).pos_lhs_ids, not_lhs, false, false);
                        if self.lrat() {
                            debug_assert!(gt(g).pos_lhs_ids.len() == 2);
                            self.lrat_chain.push(gt(g).pos_lhs_ids[0].clause.id());
                            self.lrat_chain.push(gt(g).pos_lhs_ids[1].clause.id());
                        }
                        self.learn_congruence_unit(unit, false, false);
                        garbage = true;
                    } else if gt(g).rhs[0] == gt(g).lhs || gt(g).rhs[1] == gt(g).lhs {
                        log!(self.internal, g, "special XOR:");
                        let unit = gt(g).rhs[0] ^ gt(g).lhs ^ gt(g).rhs[1];
                        self.produce_rewritten_clause_lrat_and_clean(&mut gt(g).pos_lhs_ids, not_lhs, false, false);
                        if self.lrat() {
                            debug_assert!(gt(g).pos_lhs_ids.len() == 2);
                            self.lrat_chain.push(gt(g).pos_lhs_ids[0].clause.id());
                            self.lrat_chain.push(gt(g).pos_lhs_ids[1].clause.id());
                        }
                        self.learn_congruence_unit(-unit, false, false);
                        garbage = true;
                    } else {
                        let mut i: i32 = 0;
                        let mut negated = false;
                        let mut j: i32 = 0;
                        while j < 2 {
                            debug_assert!(i <= j);
                            let lit = gt(g).rhs[j as usize];
                            gt(g).rhs[i as usize] = lit;
                            let v = self.val(lit);
                            if v > 0 {
                                i -= 1;
                                negated = !negated;
                            } else if v < 0 {
                                i -= 1;
                            }
                            i += 1;
                            j += 1;
                        }
                        debug_assert!(i <= 2);
                        gt(g).rhs.resize(i as usize, 0);
                        if negated {
                            gt(g).lhs = -gt(g).lhs;
                        }
                        if i != 2 {
                            log!(self.internal, g, "removed units");
                        }
                        if i == 0 {
                            garbage = true;
                        } else if i == 1 {
                            #[cfg(feature = "logging")]
                            {
                                for litId in gt(g).pos_lhs_ids.clone() {
                                    log!(self.internal, litId.clause, "{} ->", litId.current_lit);
                                }
                            }
                            let gl = gt(g).lhs;
                            self.produce_rewritten_clause_lrat_and_clean(&mut gt(g).pos_lhs_ids, gl, true, false);
                            debug_assert!(
                                !self.lrat()
                                    || gt(g).pos_lhs_ids.len() == 2
                                    || (gt(g).arity() == 1 && {
                                        let (a, b) = (gt(g).lhs, gt(g).rhs[0]);
                                        self.find_representative(a) == self.find_representative(b)
                                    })
                            );
                            if gt(g).arity() == 1 {
                                // can happen when there are units in the gate
                                // that are not simplified yet
                                garbage = true;
                            } else {
                                let mut c1 = CRef::NULL;
                                let mut c2 = CRef::NULL;
                                if self.lrat() {
                                    debug_assert!(!gt(g).pos_lhs_ids[0].clause.is_null());
                                    let p0 = gt(g).pos_lhs_ids[0].clause;
                                    let rhs_as_src_first = p0.lit(0) == gt(g).lhs || p0.lit(1) == gt(g).lhs;
                                    c1 = if rhs_as_src_first { gt(g).pos_lhs_ids[0].clause } else { gt(g).pos_lhs_ids[1].clause };
                                    c2 = if rhs_as_src_first { gt(g).pos_lhs_ids[1].clause } else { gt(g).pos_lhs_ids[0].clause };
                                    c1 = self.maybe_promote_tmp_binary_clause(c1);
                                    c2 = self.maybe_promote_tmp_binary_clause(c2);
                                } else {
                                    let (gl, r0) = (gt(g).lhs, gt(g).rhs[0]);
                                    self.maybe_add_binary_clause(-gl, r0);
                                    self.maybe_add_binary_clause(gl, -r0);
                                }
                                let (gl, r0) = (gt(g).lhs, gt(g).rhs[0]);
                                self.merge_literals_equivalence(gl, r0, c1, c2);
                                garbage = true;
                            }
                        }
                    }
                    if !garbage {
                        debug_assert!(gt(g).rhs[0] != gt(g).lhs);
                        debug_assert!(gt(g).rhs[1] != gt(g).lhs);
                        debug_assert!(gt(g).rhs[0] != -gt(g).lhs);
                        debug_assert!(gt(g).rhs[1] != -gt(g).lhs);
                    }
                }

                if !garbage {
                    log!(self.internal, g, "rewritten");

                    if self.lrat() {
                        if new_tag == Gate_Type::XOr_Gate {
                            #[cfg(debug_assertions)]
                            {
                                for l in gt(g).pos_lhs_ids.iter() {
                                    debug_assert!(l.clause.size() as usize == 1 + gt(g).arity());
                                }
                            }
                        } else if new_tag == Gate_Type::And_Gate {
                            // we have to get rid of one clause, two become
                            // binaries, and becomes ternary
                            #[cfg(any(feature = "logging", debug_assertions))]
                            {
                                for id in gt(g).pos_lhs_ids.clone() {
                                    log!(self.internal, id.clause, "clause after rewriting:");
                                    debug_assert!(id.clause.size() == 2);
                                }
                            }
                            debug_assert!(gt(g).pos_lhs_ids.len() == 2 || gate_contains(g, gt(g).lhs));
                            debug_assert!(gt(g).neg_lhs_ids.is_set() || gate_contains(g, gt(g).lhs));
                            debug_assert!(gt(g).arity() == 2);
                        } else {
                            debug_assert!(false);
                            unreachable!();
                        }
                    }
                    let h;
                    if new_tag == Gate_Type::And_Gate {
                        self.check_and_gate_implied(g);
                        h = self.find_and_lits(&mut gt(g).rhs, std::ptr::null_mut());
                    } else {
                        debug_assert!(new_tag == Gate_Type::XOr_Gate);
                        self.check_xor_gate_implied(g);
                        h = self.find_xor_gate(g);
                    }
                    if !h.is_null() {
                        garbage = true;
                        if new_tag == Gate_Type::XOr_Gate {
                            let mut reasons_implication: Vec<LRAT_ID> = Vec::new();
                            let mut reasons_back: Vec<LRAT_ID> = Vec::new();
                            let clauses2 = gt(h).pos_lhs_ids.clone();
                            let (gl, hl) = (gt(g).lhs, gt(h).lhs);
                            self.add_xor_matching_proof_chain(
                                g,
                                gl,
                                &clauses2,
                                hl,
                                &mut reasons_implication,
                                &mut reasons_back,
                            );
                            let (gl, hl) = (gt(g).lhs, gt(h).lhs);
                            if self.merge_literals(gl, hl, &reasons_implication, &reasons_back) {
                                self.int().stats.congruence.xors += 1;
                            }
                        } else {
                            self.add_ite_turned_and_binary_clauses(g);
                            let mut reasons_implication: Vec<LRAT_ID> = Vec::new();
                            let mut reasons_back: Vec<LRAT_ID> = Vec::new();
                            if self.lrat() {
                                self.merge_and_gate_lrat_produce_lrat(g, h, &mut reasons_implication, &mut reasons_back, false);
                            }
                            let (gl, hl) = (gt(g).lhs, gt(h).lhs);
                            if self.merge_literals_gates(g, h, gl, hl, &reasons_implication, &reasons_back) {
                                self.int().stats.congruence.ands += 1;
                            }
                        }
                        self.delete_proof_chain();
                    } else {
                        garbage = false;
                        if gt(g).indexed {
                            self.remove_gate_at(git);
                        }
                        self.index_gate(g);
                        debug_assert!(gt(g).arity() == 2);
                        let n = gt(g).rhs.len();
                        for k in 0..n {
                            let lit = gt(g).rhs[k];
                            if lit != dst && lit != cond && lit != then_lit && lit != else_lit {
                                self.connect_goccs(g, lit);
                            }
                        }
                        if gt(g).tag == Gate_Type::And_Gate && !self.lrat() {
                            let n = gt(g).rhs.len();
                            for k in 0..n {
                                let lit = gt(g).rhs[k];
                                let gl = gt(g).lhs;
                                self.maybe_add_binary_clause(-gl, lit);
                            }
                        }
                    }
                }
            } else {
                log!(self.internal, g, "rewritten");
                if self.lrat() {
                    update_ite_flags(g);
                    check_correct_ite_flags(g);
                }
                {
                    let rhs = &gt(g).rhs;
                    debug_assert!(rhs[0] != rhs[1]);
                    debug_assert!(rhs[0] != rhs[2]);
                    debug_assert!(rhs[1] != rhs[2]);
                    debug_assert!(rhs[0] != -rhs[1]);
                    debug_assert!(rhs[0] != -rhs[2]);
                    debug_assert!(rhs[1] != -rhs[2]);
                }
                self.check_ite_gate_implied(g);
                self.check_ite_lrat_reasons(g);
                let mut negate_lhs = false;
                let h = self.find_ite_gate(g, &mut negate_lhs);
                debug_assert!(lhs == gt(g).lhs);
                debug_assert!(not_lhs == -gt(g).lhs);
                if negate_lhs {
                    gt(g).lhs = -lhs;
                }
                self.check_ite_lrat_reasons(g);
                if self.lrat() {
                    check_correct_ite_flags(g);
                }
                if !h.is_null() {
                    garbage = true;
                    self.check_ite_gate_implied(g);
                    self.check_ite_lrat_reasons(g);
                    self.check_ite_gate_implied(h);
                    self.check_ite_lrat_reasons(h);
                    let mut normalized_lhs = if negate_lhs { not_lhs } else { lhs };
                    let mut extra_reasons_lit: Vec<LRAT_ID> = Vec::new();
                    let mut extra_reasons_ulit: Vec<LRAT_ID> = Vec::new();
                    let hl = gt(h).lhs;
                    self.add_ite_matching_proof_chain(
                        g,
                        h,
                        normalized_lhs,
                        hl,
                        &mut extra_reasons_lit,
                        &mut extra_reasons_ulit,
                    );
                    // LHS can change for degenerated gates
                    if gt(g).lhs != normalized_lhs {
                        normalized_lhs = self.find_eager_representative(normalized_lhs);
                    }
                    let hl = gt(h).lhs;
                    if self.merge_literals_gates(g, h, normalized_lhs, hl, &extra_reasons_lit, &extra_reasons_ulit) {
                        self.int().stats.congruence.ites += 1;
                    }
                    self.delete_proof_chain();
                    debug_assert!(self.int().unsat || self.chain.is_empty());
                } else {
                    garbage = false;
                    if gt(g).indexed {
                        self.remove_gate_at(git);
                    }
                    log!(self.internal, g, "normalized");
                    self.index_gate(g);
                    debug_assert!(gt(g).arity() == 3);
                    let n = gt(g).rhs.len();
                    for k in 0..n {
                        let lit = gt(g).rhs[k];
                        if lit != dst && lit != cond && lit != then_lit && lit != else_lit {
                            self.connect_goccs(g, lit);
                        }
                    }
                }
            }
        }
        if garbage && !self.int().unsat {
            self.mark_garbage(g);
        }

        debug_assert!(self.chain.is_empty());
        self.int().stats.congruence.rewritten_ites += 1;
    }

    pub fn simplify_ite_gate_produce_unit_lrat(&mut self, g: *mut Gate, lit: i32, idx1: usize, idx2: usize) {
        if !self.lrat() {
            return;
        }
        if self.val(lit) > 0 {
            return;
        }
        debug_assert!(self.lrat());
        debug_assert!(!g.is_null());
        debug_assert!(idx1 < gt(g).pos_lhs_ids.len());
        debug_assert!(idx2 < gt(g).pos_lhs_ids.len());
        debug_assert!(gt(g).pos_lhs_ids.len() == 4);

        debug_assert!(idx1 != idx2);
        let mut c = gt(g).pos_lhs_ids[idx1].clause;
        let mut d = gt(g).pos_lhs_ids[idx2].clause;

        if gt(g).lhs == -gt(g).rhs[0] {
            log!(self.internal, "special case of LHS=-cond where only one clause in LRAT is needed is needed");
            let idx = if self.val(gt(g).rhs[1]) < 0 { idx2 } else { idx1 };
            let lhs = gt(g).lhs;
            c = self.produce_rewritten_clause_lrat(gt(g).pos_lhs_ids[idx].clause, lhs, false, false);
            debug_assert!(!c.is_null());
            // not possible to do this in a single lrat chain
            self.push_id_and_rewriting_lrat_unit_self(c, Rewrite::default(), true, Rewrite::default(), lhs, 0);
            debug_assert!(!d.is_null());
            return;
        }
        if gt(g).lhs == gt(g).rhs[0] {
            log!(self.internal, "special case of LHS=cond where only one clause in LRAT is needed is needed");
            let idx = if self.val(gt(g).rhs[1]) > 0 { idx2 } else { idx1 };
            let lhs = gt(g).lhs;
            c = self.produce_rewritten_clause_lrat(gt(g).pos_lhs_ids[idx].clause, lhs, false, false);
            debug_assert!(!c.is_null());
            // not possible to do this in a single lrat chain
            self.push_id_and_rewriting_lrat_unit_self(c, Rewrite::default(), true, Rewrite::default(), lhs, 0);
            debug_assert!(!d.is_null());
            return;
        }

        let lhs = gt(g).lhs;
        c = self.produce_rewritten_clause_lrat(c, lhs, true, false);
        if !c.is_null() {
            self.lrat_chain.push(c.id());
            d = self.produce_rewritten_clause_lrat(d, lhs, true, false);
            if !d.is_null() {
                self.lrat_chain.push(d.id());
            }
        } else {
            self.push_id_and_rewriting_lrat_unit_self(d, Rewrite::default(), true, Rewrite::default(), lhs, 0);
            debug_assert!(!d.is_null());
            self.lrat_chain.push(d.id());
        }
    }

    // TODO merge
    /// `remove_units` defaults to `true` in C++
    pub fn merge_and_gate_lrat_produce_lrat(
        &mut self,
        g: *mut Gate,
        h: *mut Gate,
        reasons_lrat_src: &mut Vec<i64>,
        reasons_lrat_usrc: &mut Vec<i64>,
        remove_units: bool,
    ) {
        debug_assert!(self.lrat());
        debug_assert!(gt(g).tag == Gate_Type::And_Gate);
        debug_assert!(gt(h).tag == Gate_Type::And_Gate);
        self.update_and_gate_build_lrat_chain(g, h, reasons_lrat_src, reasons_lrat_usrc, remove_units);
    }

    // odd copy of rewrite_ite_gate_lrat_and
    pub fn simplify_ite_gate_to_and(&mut self, g: *mut Gate, idx1: usize, idx2: usize, removed_lit: i32) -> bool {
        debug_assert!(self.int().lrat_chain.is_empty());
        debug_assert!(gt(g).arity() == 3);
        log!(
            self.internal,
            "transforming to gate[{}] {} = {} & {} with idx1={}, idx2={}",
            gt(g).id,
            loglit!(self.internal, gt(g).lhs),
            loglit!(self.internal, gt(g).rhs[0]),
            loglit!(self.internal, gt(g).rhs[1]),
            idx1,
            idx2
        );
        let orig_flag = gt(g).degenerated_gate;
        #[cfg(feature = "logging")]
        {
            for litId in gt(g).pos_lhs_ids.clone() {
                log!(self.internal, litId.clause, "{} ->", litId.current_lit);
            }
        }
        if gt(g).lhs == -gt(g).rhs[0] || gt(g).lhs == -gt(g).rhs[1] {
            if self.lrat() {
                let c = gt(g).pos_lhs_ids[idx1].clause;
                self.push_id_and_rewriting_lrat_unit_self(c, Rewrite::default(), true, Rewrite::default(), 0, 0);
                debug_assert!(!self.lrat_chain.is_empty());
            }
            let lhs = gt(g).lhs;
            self.learn_congruence_unit(-lhs, false, false);
            return true;
        }
        if !self.lrat() {
            return false;
        }

        if gt(g).rhs[1] == -gt(g).lhs || gt(g).rhs[0] == -gt(g).lhs {
            gt(g).degenerated_gate = Special_Gate::DEGENERATED_AND;
        } else if gt(g).rhs[0] == gt(g).lhs || gt(g).rhs[1] == gt(g).lhs {
            gt(g).degenerated_gate = Special_Gate::DEGENERATED_AND;
        } else {
            gt(g).degenerated_gate = Special_Gate::NORMAL;
        }

        if gt(g).lhs == -removed_lit && self.val(-removed_lit) != 0 {
            // 3 = 5 ? 1 : 3 where 3@0 = -1
            gt(g).degenerated_gate = Special_Gate::DEGENERATED_AND_LHS_FALSE;
            let mut new_idx1 = idx1;
            let mut new_idx2 = idx2;
            self.produce_rewritten_clause_lrat_and_clean_positions(
                &mut gt(g).pos_lhs_ids,
                0,
                &mut new_idx1,
                &mut new_idx2,
                true,
            );
            debug_assert!(gt(g).pos_lhs_ids.len() == 1);
            debug_assert!(gt(g).pos_lhs_ids[0].clause.size() == 2);
            return false;
        }
        debug_assert!(gt(g).pos_lhs_ids.len() == 4);
        debug_assert!(idx1 < gt(g).pos_lhs_ids.len());
        debug_assert!(idx2 < gt(g).pos_lhs_ids.len());
        let lit = gt(g).pos_lhs_ids[idx2].current_lit;
        let other = gt(g).lhs;
        let mut new_idx1 = idx1;
        let mut new_idx2 = idx2;
        let lhs = gt(g).lhs;
        self.produce_rewritten_clause_lrat_and_clean_positions(&mut gt(g).pos_lhs_ids, lhs, &mut new_idx1, &mut new_idx2, true);

        if gt(g).pos_lhs_ids.len() == 1 {
            log!(self.internal, g, "degenerated AND gate");
            debug_assert!(gt(g).degenerated_gate != Special_Gate::NORMAL);
            let replacement_lit = if gt(g).rhs[1] == gt(g).lhs { gt(g).rhs[0] } else { gt(g).rhs[1] };
            let n = gt(g).pos_lhs_ids.len();
            for i in 0..n {
                debug_assert!(!gt(g).pos_lhs_ids[i].clause.is_null());
                log!(self.internal, gt(g).pos_lhs_ids[i].clause, "{} ->", gt(g).pos_lhs_ids[i].current_lit);
                if gt(g).pos_lhs_ids[i].current_lit == removed_lit {
                    gt(g).pos_lhs_ids[i].current_lit = -replacement_lit;
                }
                if gt(g).pos_lhs_ids[i].current_lit == -removed_lit {
                    gt(g).pos_lhs_ids[i].current_lit = replacement_lit;
                }
                log!(self.internal, gt(g).pos_lhs_ids[i].clause, "{} ->", gt(g).pos_lhs_ids[i].current_lit);
                // TODO we need a replacement index
                debug_assert!(clause_contains(gt(g).pos_lhs_ids[i].clause, gt(g).pos_lhs_ids[i].current_lit));
                debug_assert!(gt(g).rhs.contains(&gt(g).pos_lhs_ids[i].current_lit));
            }
            return false;
        }
        log!(
            self.internal,
            "normal AND gate with clauses {} (was: {}) {} (was: {})",
            new_idx1 as isize,
            idx1,
            new_idx2 as isize,
            idx2
        );
        if (orig_flag == Special_Gate::NO_ELSE || orig_flag == Special_Gate::NO_THEN)
            && ({
                let (l, r0) = (gt(g).lhs, gt(g).rhs[0]);
                self.find_eager_representative(l) == self.find_eager_representative(r0)
            } || {
                let (l, r1) = (gt(g).lhs, gt(g).rhs[1]);
                self.find_eager_representative(l) == self.find_eager_representative(r1)
            })
        {
            gt(g).degenerated_gate = Special_Gate::DEGENERATED_AND;
            log!(self.internal, g, "marking as degenerated");
            debug_assert!({
                let l = self.find_eager_representative(gt(g).lhs);
                l == gt(g).rhs[0] || l == gt(g).rhs[1]
            });
            let d = gt(g).pos_lhs_ids[new_idx1].clause;
            // TODO there should be a better way than dereferencing the clause
            // even if it is cheap as we have just written the proof out
            debug_assert!(-gt(g).lhs == d.lit(0) || -gt(g).lhs == d.lit(1));
            let lit = d.lit(0) ^ d.lit(1) ^ -gt(g).lhs;
            log!(self.internal, "{} -> {}", gt(g).lhs, self.find_eager_representative(gt(g).lhs));
            log!(self.internal, "{} -> {}", d.lit(0), self.find_eager_representative(d.lit(0)));
            log!(self.internal, "{} -> {}", d.lit(1), self.find_eager_representative(d.lit(1)));
            log!(self.internal, d, "with reference {} at position {}", loglit!(self.internal, lit), new_idx1 as isize);
            debug_assert!(d.size() == 2);
            gt(g).pos_lhs_ids.clear();
            gt(g).pos_lhs_ids.push(LitClausePair::new(lit, d));
            gt(g).neg_lhs_ids.reset();
            // TODO should be before lrat test
            let l = self.find_eager_representative(gt(g).lhs);
            gt(g).lhs = l;
            return false;
        }
        debug_assert!(new_idx1 < gt(g).pos_lhs_ids.len());
        let c = gt(g).pos_lhs_ids[new_idx1].clause;
        debug_assert!(c.size() == 2);
        debug_assert!(!c.is_null());
        debug_assert!(new_idx2 < gt(g).pos_lhs_ids.len());
        debug_assert!(new_idx1 != new_idx2);
        let d = gt(g).pos_lhs_ids[new_idx2].clause;
        debug_assert!(c != d);
        debug_assert!(!d.is_null());
        gt(g).pos_lhs_ids.retain(|p| p.clause != d);
        debug_assert!(gt(g).pos_lhs_ids.len() == 2 || gt(g).degenerated_gate == Special_Gate::DEGENERATED_AND);
        debug_assert!(lit != 0);
        debug_assert!(other != 0);
        debug_assert!(lit != other);
        if !c.is_null() {
            self.lrat_chain.push(c.id());
        }
        self.lrat_chain.push(d.id());
        let e = self.add_tmp_binary_clause(lit, -other);

        let long_clause = gt(g).pos_lhs_ids.iter().position(|l| l.clause.size() == 3);
        debug_assert!(long_clause.is_some());
        let long_clause = long_clause.unwrap();
        log!(self.internal, gt(g).pos_lhs_ids[long_clause].clause, "new long clause");
        let lc = gt(g).pos_lhs_ids[long_clause];
        gt(g).neg_lhs_ids.set(lc);
        gt(g).pos_lhs_ids.remove(long_clause);
        debug_assert!(gt(g).pos_lhs_ids.len() == 1);
        gt(g).pos_lhs_ids.push(LitClausePair::new(lit, e));

        let first_lit = gt(g).rhs[0];
        let second_lit = gt(g).rhs[1];
        let n = gt(g).pos_lhs_ids.len();
        for i in 0..n {
            let litId = gt(g).pos_lhs_ids[i];
            debug_assert!(!litId.clause.is_null());
            log!(self.internal, litId.clause, "{} ->", loglit!(self.internal, litId.current_lit));
            if self.val(litId.current_lit) != 0 {
                debug_assert!(litId.clause.size() == 2);
                let mut replacement_lit = 0;
                for k in 0..2 {
                    if litId.clause.lit(k) == first_lit {
                        replacement_lit = first_lit;
                        break;
                    } else if litId.clause.lit(k) == second_lit {
                        replacement_lit = second_lit;
                        break;
                    }
                }
                debug_assert!(replacement_lit != 0);

                gt(g).pos_lhs_ids[i].current_lit = replacement_lit;
            } else if litId.current_lit == removed_lit {
                gt(g).pos_lhs_ids[i].current_lit = -gt(g).rhs[0];
            } else if litId.current_lit == -removed_lit {
                gt(g).pos_lhs_ids[i].current_lit = gt(g).rhs[0];
            }
            log!(self.internal, litId.clause, "{} ->", gt(g).pos_lhs_ids[i].current_lit);
            debug_assert!(gt(g).rhs.contains(&gt(g).pos_lhs_ids[i].current_lit));
            debug_assert!(clause_contains(litId.clause, gt(g).pos_lhs_ids[i].current_lit));
        }
        debug_assert!(gt(g).pos_lhs_ids.len() == 2 || gt(g).degenerated_gate != Special_Gate::NORMAL);
        false
    }

    pub fn merge_ite_gate_same_then_else_lrat(
        &mut self,
        clauses: &mut Vec<LitClausePair>,
        reasons_implication: &mut Vec<i64>,
        reasons_back: &mut Vec<i64>,
    ) {
        debug_assert!(clauses.len() == 4);
        self.produce_rewritten_clause_lrat_and_clean(clauses, 0, true, false);
        debug_assert!(clauses.len() == 4);
        let then_imp = clauses[0];
        let neg_then_imp = clauses[1];
        let else_imp = clauses[2];
        let neg_else_imp = clauses[3];
        reasons_implication.push(then_imp.clause.id());
        reasons_implication.push(else_imp.clause.id());
        reasons_back.push(neg_then_imp.clause.id());
        reasons_back.push(neg_else_imp.clause.id());
    }

    pub fn simplify_ite_gate_then_else_set(
        &mut self,
        g: *mut Gate,
        reasons_implication: &mut Vec<i64>,
        reasons_back: &mut Vec<i64>,
        idx1: usize,
        idx2: usize,
    ) {
        debug_assert!(idx1 < gt(g).pos_lhs_ids.len());
        debug_assert!(idx2 < gt(g).pos_lhs_ids.len());
        let c = gt(g).pos_lhs_ids[idx1].clause;
        let d = gt(g).pos_lhs_ids[idx2].clause;
        let lhs = gt(g).lhs;
        self.push_id_and_rewriting_lrat_unit(c, Rewrite::default(), reasons_back, true, Rewrite::default(), lhs, 0);
        self.push_id_and_rewriting_lrat_unit(d, Rewrite::default(), reasons_implication, true, Rewrite::default(), lhs, 0);
        log!(self.internal, &*reasons_back, "LRAT");
        log!(self.internal, &*reasons_implication, "LRAT");
    }

    pub fn simplify_ite_gate_condition_set(
        &mut self,
        g: *mut Gate,
        reasons_lrat: &mut Vec<i64>,
        reasons_back_lrat: &mut Vec<i64>,
        idx1: usize,
        idx2: usize,
    ) {
        debug_assert!(self.lrat());
        let c = gt(g).pos_lhs_ids[idx1].clause;
        let d = gt(g).pos_lhs_ids[idx2].clause;
        #[cfg(any(feature = "logging", debug_assertions))]
        {
            let cond = gt(g).rhs[0];
            debug_assert!(self.val(cond) != 0);
            log!(self.internal, "cond = {}", cond);
            let _ = cond;
        }
        #[cfg(feature = "logging")]
        {
            for litid in gt(g).pos_lhs_ids.clone() {
                log!(self.internal, litid.clause, "clause in gate:");
            }
        }
        let lhs = gt(g).lhs;
        if !c.is_null() {
            self.push_id_and_rewriting_lrat_unit(c, Rewrite::default(), reasons_lrat, true, Rewrite::default(), -lhs, 0);
        } else {
            debug_assert!(gt(g).degenerated_gate != Special_Gate::NORMAL);
        }

        if !d.is_null() {
            self.push_id_and_rewriting_lrat_unit(d, Rewrite::default(), reasons_back_lrat, true, Rewrite::default(), lhs, 0);
        } else {
            debug_assert!(gt(g).degenerated_gate != Special_Gate::NORMAL);
        }
    }

    pub fn simplify_ite_gate(&mut self, g: *mut Gate) {
        if skip_ite_gate(g) {
            return;
        }
        log!(self.internal, g, "simplifying");
        debug_assert!(gt(g).arity() == 3);
        let mut garbage = true;
        let lhs = gt(g).lhs;
        let cond = gt(g).rhs[0];
        let then_lit = gt(g).rhs[1];
        let else_lit = gt(g).rhs[2];
        let v_cond = self.val(cond);
        let v_else = self.val(else_lit);
        let v_then = self.val(then_lit);
        let mut reasons_lrat: Vec<LRAT_ID> = Vec::new();
        let mut reasons_back_lrat: Vec<LRAT_ID> = Vec::new();
        if v_cond != 0 && v_else != 0 && v_then != 0 {
            // propagation has set all value anyway
            log!(self.internal, g, "all values are set");
            debug_assert!(self.val(gt(g).lhs) != 0);
            garbage = true;
        } else if v_cond > 0 {
            if self.lrat() {
                self.simplify_ite_gate_condition_set(g, &mut reasons_lrat, &mut reasons_back_lrat, 0, 1);
            }
            if self.merge_literals(lhs, then_lit, &reasons_lrat, &reasons_back_lrat) {
                self.int().stats.congruence.unary_ites += 1;
                self.int().stats.congruence.unaries += 1;
            }
        } else if v_cond < 0 {
            if self.lrat() {
                self.simplify_ite_gate_condition_set(g, &mut reasons_lrat, &mut reasons_back_lrat, 2, 3);
            }
            if self.merge_literals(lhs, else_lit, &reasons_lrat, &reasons_back_lrat) {
                self.int().stats.congruence.unary_ites += 1;
                self.int().stats.congruence.unaries += 1;
            }
        } else {
            log!(self.internal, "then {}: {}; else {}: {}", then_lit, v_then, else_lit, v_else);
            let mut extra_reasons: Vec<LRAT_ID> = Vec::new();
            let mut extra_reasons_back: Vec<LRAT_ID> = Vec::new();
            debug_assert!(v_then != 0 || v_else != 0);
            if v_then > 0 && v_else > 0 {
                self.simplify_ite_gate_produce_unit_lrat(g, lhs, 1, 3);
                self.learn_congruence_unit(lhs, false, false);
            } else if v_then < 0 && v_else < 0 {
                self.simplify_ite_gate_produce_unit_lrat(g, -lhs, 0, 2);
                self.learn_congruence_unit(-lhs, false, false);
            } else if v_then > 0 && v_else < 0 {
                // if the gate is a = a ? true : false, there is nothing to do
                // and the lrat generation fails
                if self.lrat() && self.find_eager_representative(lhs) != self.find_eager_representative(cond) {
                    self.simplify_ite_gate_then_else_set(g, &mut extra_reasons, &mut extra_reasons_back, 1, 2);
                }
                if self.merge_literals(lhs, cond, &extra_reasons, &extra_reasons_back) {
                    self.int().stats.congruence.unary_ites += 1;
                    self.int().stats.congruence.unaries += 1;
                }
            } else if v_then < 0 && v_else > 0 {
                // if the gate is a = -a ? false : true, there is nothing to do
                // and the lrat generation fails
                if self.lrat() && self.find_eager_representative(lhs) != self.find_eager_representative(-cond) {
                    self.simplify_ite_gate_then_else_set(g, &mut extra_reasons, &mut extra_reasons_back, 0, 3);
                }
                if self.merge_literals(lhs, -cond, &extra_reasons_back, &extra_reasons) {
                    self.int().stats.congruence.unary_ites += 1;
                    self.int().stats.congruence.unaries += 1;
                }
            } else {
                debug_assert!((v_then != 0) as i32 + (v_else != 0) as i32 == 1);
                let git: GatesIterator = if gt(g).indexed { self.table.find(g) } else { None };
                debug_assert!(!gt(g).indexed || git.is_some());
                if v_then > 0 {
                    gt(g).lhs = -lhs;
                    gt(g).rhs[0] = -cond;
                    gt(g).rhs[1] = -else_lit;
                    self.simplify_ite_gate_to_and(g, 1, 3, then_lit);
                } else if v_then < 0 {
                    gt(g).rhs[0] = -cond;
                    gt(g).rhs[1] = else_lit;
                    self.simplify_ite_gate_to_and(g, 0, 2, -then_lit);
                } else if v_else > 0 {
                    gt(g).lhs = -lhs;
                    gt(g).rhs[0] = -then_lit;
                    gt(g).rhs[1] = cond;
                    self.simplify_ite_gate_to_and(g, 3, 1, else_lit);
                } else {
                    debug_assert!(v_else < 0);
                    gt(g).rhs[0] = then_lit;
                    gt(g).rhs[1] = cond;
                    self.simplify_ite_gate_to_and(g, 2, 0, -else_lit);
                }
                if self.int().unsat {
                    return;
                }
                if self.int().vlit(gt(g).rhs[0]) > self.int().vlit(gt(g).rhs[1]) {
                    gt(g).rhs.swap(0, 1);
                }
                gt(g).shrunken = true;
                gt(g).tag = Gate_Type::And_Gate;
                gt(g).rhs.resize(2, 0);
                debug_assert!({
                    let internal: &Internal = self.int();
                    is_sorted_by(&gt(g).rhs, |&a, &b| sort_literals_by_var_smaller(internal, a, b))
                });
                self.check_and_gate_implied(g);
                let h = self.find_and_lits(&mut gt(g).rhs, std::ptr::null_mut());
                if !h.is_null() {
                    debug_assert!(garbage);
                    let mut reasons_lrat: Vec<LRAT_ID> = Vec::new();
                    let mut reasons_lrat_back: Vec<LRAT_ID> = Vec::new();
                    if self.lrat() {
                        self.merge_and_gate_lrat_produce_lrat(g, h, &mut reasons_lrat, &mut reasons_lrat_back, true);
                    }
                    let (gl, hl) = (gt(g).lhs, gt(h).lhs);
                    if self.merge_literals_gates(g, h, gl, hl, &reasons_lrat, &reasons_lrat_back) {
                        self.int().stats.congruence.ites += 1;
                    }
                } else {
                    self.remove_gate_at(git);
                    self.index_gate(g);
                    garbage = false;
                    let n = gt(g).rhs.len();
                    for k in 0..n {
                        let lit = gt(g).rhs[k];
                        if lit != cond && lit != then_lit && lit != else_lit {
                            self.connect_goccs(g, lit);
                        }
                    }

                    if gt(g).rhs[0] == -gt(g).lhs || gt(g).rhs[1] == -gt(g).lhs {
                        // TODO Kissat does not do that, but it has also no
                        // checks to verify that it cannot happen...
                        self.simplify_and_gate(g);
                    }
                }
            }
        }
        if garbage && !self.int().unsat {
            self.mark_garbage(g);
        }
        self.int().stats.congruence.simplified += 1;
        self.int().stats.congruence.simplified_ites += 1;
    }

    pub fn add_ite_matching_proof_chain(
        &mut self,
        g: *mut Gate,
        h: *mut Gate,
        lhs1: i32,
        lhs2: i32,
        reasons1: &mut Vec<i64>,
        reasons2: &mut Vec<i64>,
    ) {
        if self.int().proof.is_none() {
            return;
        }
        self.check_ite_lrat_reasons(g);
        self.check_ite_lrat_reasons(h);
        debug_assert!(gt(g).lhs == lhs1);
        debug_assert!(gt(h).lhs == lhs2);
        let mut lhs1 = lhs1;
        let mut lhs2 = lhs2;
        if lhs1 == lhs2 {
            return;
        }
        log!(self.internal, g, "starting ITE matching proof chain");
        if gt(g).degenerated_gate != Special_Gate::NORMAL {
            let l = self.find_eager_representative(gt(g).lhs);
            gt(g).lhs = l;
            lhs1 = self.find_eager_representative(lhs1);
            log!(self.internal, g, "rewritten LHS of g");
        }
        log!(self.internal, h, "matching ITE proof chain with");
        if gt(h).degenerated_gate != Special_Gate::NORMAL {
            let l = self.find_eager_representative(gt(h).lhs);
            gt(h).lhs = l;
            lhs2 = self.find_eager_representative(lhs2);
            log!(self.internal, g, "rewritten LHS of h");
        }
        log!(self.internal, "producing ITE gates {} {}", lhs1, lhs2);
        debug_assert!(self.unsimplified.is_empty());
        debug_assert!(self.chain.is_empty());
        if self.lrat() {
            check_correct_ite_flags(g);
        }
        let flags_g = gt(g).degenerated_gate;
        let flags_h = gt(h).degenerated_gate;
        let cond = gt(g).rhs[0];
        let mut g_then_id: LRAT_ID = 0;
        let mut g_neg_then_id: LRAT_ID = 0;
        let mut g_neg_else_id: LRAT_ID = 0;
        let mut h_then_id: LRAT_ID = 0;
        let mut h_neg_then_id: LRAT_ID = 0;
        let mut h_else_id: LRAT_ID = 0;
        let mut g_else_id: LRAT_ID = 0;
        let mut h_neg_else_id: LRAT_ID = 0;
        let degenerated_g_then = ite_flags_no_then_clauses(flags_g);
        let degenerated_g_else = ite_flags_no_else_clauses(flags_g);
        let degenerated_h_then = ite_flags_no_then_clauses(flags_h);
        let degenerated_h_else = ite_flags_no_else_clauses(flags_h);

        let degenerated_g_cond = ite_flags_cond_lhs(flags_g);
        let degenerated_h_cond = ite_flags_cond_lhs(flags_h);
        debug_assert!(!(degenerated_g_cond && degenerated_h_cond));

        let degenerated_g_not_cond = ite_flags_neg_cond_lhs(flags_g);
        let degenerated_h_not_cond = ite_flags_neg_cond_lhs(flags_h);
        debug_assert!(!(degenerated_g_not_cond && degenerated_h_not_cond));

        if self.lrat() {
            // the code can produce tautologies in the case that:
            // a = (c ? a : e)
            // b = (c ? a : e)
            // (no clauses with (then) index a/-a)
            // but also for
            // a = (a ? t : e)
            // b = (a ? t : e)
            // (no clauses with (then) index -a and (else) index e)
            // and same for
            // a = (c ? t : a)
            // b = (c ? t : a)
            // (no clauses with (then) index a and (else) index -e)
            log!(self.internal, g, "get ids from");
            debug_assert!(gt(g).pos_lhs_ids.len() == 4);
            let mut ids = [0 as LRAT_ID; 8];
            for (k, &gate) in [g, h].iter().enumerate() {
                if k == 1 {
                    log!(self.internal, h, "now clauses from");
                    debug_assert!(gt(h).pos_lhs_ids.len() == 4);
                }
                for idx in 0..4 {
                    let c = gt(gate).pos_lhs_ids[idx].clause;
                    let d = if !c.is_null() {
                        let lhs = gt(gate).lhs;
                        self.produce_rewritten_clause_lrat(c, lhs, false, false)
                    } else {
                        CRef::NULL
                    };
                    gt(gate).pos_lhs_ids[idx].clause = d;
                    if !d.is_null() {
                        ids[4 * k + idx] = d.id();
                    }
                }
            }
            g_then_id = ids[0];
            g_neg_then_id = ids[1];
            g_else_id = ids[2];
            g_neg_else_id = ids[3];
            h_then_id = ids[4];
            h_neg_then_id = ids[5];
            h_else_id = ids[6];
            h_neg_else_id = ids[7];
        }

        if degenerated_g_cond {
            log!(self.internal, "special case: cond = lhs, g degenerated");
            self.unsimplified.push(-lhs1);
            self.unsimplified.push(lhs2);
            if self.lrat() {
                debug_assert!(g_then_id != 0);
                self.lrat_chain.push(g_then_id);
                if h_neg_then_id != 0 {
                    self.lrat_chain.push(h_neg_then_id);
                }
            }
            let id1 = self.simplify_and_add_unsimplified_to_proof_chain(0);

            self.unsimplified.clear();
            self.unsimplified.push(lhs1);
            self.unsimplified.push(-lhs2);
            if self.lrat() {
                self.lrat_chain.push(g_neg_else_id);
                if h_else_id != 0 {
                    self.lrat_chain.push(h_else_id);
                }
            }
            let id2 = self.simplify_and_add_unsimplified_to_proof_chain(0);

            debug_assert!(!self.lrat() || id1 != 0);
            debug_assert!(!self.lrat() || id2 != 0);
            reasons1.push(id1);
            reasons2.push(id2);
            self.unsimplified.clear();
            return;
        }

        if degenerated_h_cond {
            log!(self.internal, "special case: cond = lhs, h degenerated");
            self.unsimplified.push(lhs1); // potentially lhs1 == lhs2
            self.unsimplified.push(-lhs2);
            if self.lrat() {
                self.lrat_chain.push(h_then_id);
                if g_neg_then_id != 0 {
                    self.lrat_chain.push(g_neg_then_id);
                }
            }
            let id1 = self.simplify_and_add_unsimplified_to_proof_chain(0);

            self.unsimplified.clear();
            self.unsimplified.push(-lhs1);
            self.unsimplified.push(lhs2);
            if self.lrat() {
                self.lrat_chain.push(h_neg_else_id);
                if g_else_id != 0 {
                    self.lrat_chain.push(g_else_id);
                }
            }
            let id2 = self.simplify_and_add_unsimplified_to_proof_chain(0);

            debug_assert!(!self.lrat() || id1 != 0);
            debug_assert!(!self.lrat() || id2 != 0);
            reasons2.push(id1);
            reasons1.push(id2);
            self.unsimplified.clear();
            return;
        }

        if degenerated_g_not_cond {
            log!(self.internal, "special case: cond = -lhs, g degenerated");
            self.unsimplified.push(lhs1);
            self.unsimplified.push(-lhs2);
            if self.lrat() {
                debug_assert!(g_neg_then_id != 0);
                self.lrat_chain.push(g_neg_then_id);
                if h_then_id != 0 {
                    self.lrat_chain.push(h_then_id);
                }
            }
            let id1 = self.simplify_and_add_unsimplified_to_proof_chain(0);

            self.unsimplified.clear();
            self.unsimplified.push(-lhs1);
            self.unsimplified.push(lhs2);

            if self.lrat() {
                debug_assert!(g_else_id != 0);
                self.lrat_chain.push(g_else_id);
                if h_neg_else_id != 0 {
                    self.lrat_chain.push(h_neg_else_id);
                }
            }
            let id2 = self.simplify_and_add_unsimplified_to_proof_chain(0);
            debug_assert!(!self.lrat() || id1 != 0);
            debug_assert!(!self.lrat() || id2 != 0);
            reasons2.push(id1);
            reasons1.push(id2);
            self.unsimplified.clear();
            return;
        }

        if degenerated_h_not_cond {
            log!(self.internal, "special case: cond = -lhs, h degenerated");
            self.unsimplified.push(-lhs1);
            self.unsimplified.push(lhs2);
            if self.lrat() {
                debug_assert!(h_neg_then_id != 0);
                self.lrat_chain.push(h_neg_then_id);
                if g_then_id != 0 {
                    self.lrat_chain.push(g_then_id);
                }
            }
            let id1 = self.simplify_and_add_unsimplified_to_proof_chain(0);

            self.unsimplified.clear();
            self.unsimplified.push(lhs1);
            self.unsimplified.push(-lhs2);

            if self.lrat() {
                debug_assert!(h_else_id != 0);
                self.lrat_chain.push(h_else_id);
                if g_neg_else_id != 0 {
                    self.lrat_chain.push(g_neg_else_id);
                }
            }
            let id2 = self.simplify_and_add_unsimplified_to_proof_chain(0);
            debug_assert!(!self.lrat() || id1 != 0);
            debug_assert!(!self.lrat() || id2 != 0);
            reasons1.push(id1);
            reasons2.push(id2);
            self.unsimplified.clear();
            return;
        }

        log!(self.internal, "normal path");
        debug_assert!(!self.lrat() || degenerated_g_then || (g_then_id != 0 && g_neg_then_id != 0));
        debug_assert!(!self.lrat() || degenerated_g_else || (g_else_id != 0 && g_neg_else_id != 0));
        debug_assert!(!self.lrat() || degenerated_h_then || (h_then_id != 0 && h_neg_then_id != 0));
        debug_assert!(!self.lrat() || degenerated_h_else || (h_else_id != 0 && h_neg_else_id != 0));
        debug_assert!(!self.lrat() || g_then_id != 0 || h_neg_then_id != 0);
        debug_assert!(!self.lrat() || g_neg_then_id != 0 || h_then_id != 0);
        self.unsimplified.push(-lhs1);
        self.unsimplified.push(lhs2);
        self.unsimplified.push(-cond);
        let id1;
        if degenerated_g_then || degenerated_h_then {
            id1 = if degenerated_g_then { h_neg_then_id } else { g_then_id };
        } else {
            if self.lrat() {
                self.lrat_chain.push(g_then_id);
                self.lrat_chain.push(h_neg_then_id);
            }
            id1 = self.simplify_and_add_unsimplified_to_proof_chain(0);
        }
        self.unsimplified.pop();
        self.unsimplified.push(cond);

        let id2;
        if degenerated_g_else || degenerated_h_else {
            id2 = if degenerated_g_else { h_neg_else_id } else { g_else_id };
        } else {
            if self.lrat() {
                self.lrat_chain.push(h_neg_else_id);
                self.lrat_chain.push(g_else_id);
            }
            id2 = self.simplify_and_add_unsimplified_to_proof_chain(0);
        }
        self.unsimplified.pop();

        self.unsimplified.clear();
        self.unsimplified.push(lhs1);
        self.unsimplified.push(-lhs2);
        self.unsimplified.push(-cond);
        debug_assert!(self.lrat_chain.is_empty());

        let id3;
        if degenerated_g_then || degenerated_h_then {
            id3 = if degenerated_g_then { h_then_id } else { g_neg_then_id };
        } else {
            if self.lrat() {
                // lrat_chain.push_back (g_then_id);
                // lrat_chain.push_back (h_neg_then_id);
                self.lrat_chain.push(g_neg_then_id);
                self.lrat_chain.push(h_then_id);
            }
            id3 = self.simplify_and_add_unsimplified_to_proof_chain(0);
        }
        self.unsimplified.pop();
        self.unsimplified.push(cond);
        debug_assert!(self.lrat_chain.is_empty());

        let id4;
        if degenerated_g_else || degenerated_h_else {
            id4 = if degenerated_g_else { h_else_id } else { g_neg_else_id };
        } else {
            if self.lrat() {
                self.lrat_chain.push(g_neg_else_id);
                self.lrat_chain.push(h_else_id);
            }
            id4 = self.simplify_and_add_unsimplified_to_proof_chain(0);
        }
        self.unsimplified.pop();

        if self.lrat() {
            debug_assert!(!self.lrat() || (id1 != 0 && id2 != 0 && id3 != 0 && id4 != 0));
            reasons1.push(id1);
            reasons1.push(id2);
            reasons2.push(id3);
            reasons2.push(id4);
        }

        self.unsimplified.clear();

        log!(self.internal, "finished ITE matching proof chain");
    }

    pub fn new_ite_gate(
        &mut self,
        lhs: i32,
        cond: i32,
        then_lit: i32,
        else_lit: i32,
        clauses: Vec<LitClausePair>,
    ) -> *mut Gate {
        let mut lhs = lhs;
        let mut clauses = clauses;
        debug_assert!(self.chain.is_empty());
        if else_lit == -then_lit {
            if then_lit < 0 {
                log!(self.internal, "skipping ternary XOR {} := {} ^ {}", lhs, cond, -then_lit);
            } else {
                log!(self.internal, "skipping ternary XOR {} := {} ^ {}", -lhs, cond, then_lit);
            }
            return std::ptr::null_mut();
        }
        if else_lit == then_lit {
            log!(self.internal, "found trivial ITE gate {} := {} ? {} : {}", lhs, cond, then_lit, else_lit);
            let mut reasons_implication: Vec<LRAT_ID> = Vec::new();
            let mut reasons_back: Vec<LRAT_ID> = Vec::new();
            if self.lrat() {
                self.merge_ite_gate_same_then_else_lrat(&mut clauses, &mut reasons_implication, &mut reasons_back);
            }
            if self.merge_literals(lhs, then_lit, &reasons_implication, &reasons_back) {
                self.int().stats.congruence.trivial_ite += 1;
            }
            return std::ptr::null_mut();
        }

        self.rhs.clear();
        self.rhs.reserve(3);
        self.rhs.push(cond);
        self.rhs.push(then_lit);
        self.rhs.push(else_lit);
        log!(self.internal, "ITE gate {} = {} ? {} : {}", lhs, cond, then_lit, else_lit);

        let mut negate_lhs = false;
        let g = new_gate();
        gt(g).lhs = lhs;
        gt(g).tag = Gate_Type::ITE_Gate;
        gt(g).rhs = self.rhs.clone();
        gt(g).pos_lhs_ids = clauses;
        #[cfg(feature = "logging")]
        {
            gt(g).id = u64::MAX;
        }
        let h = self.find_ite_gate(g, &mut negate_lhs);
        if negate_lhs {
            lhs = -lhs;
        }
        gt(g).lhs = lhs;
        self.check_ite_gate_implied(g);
        self.check_ite_lrat_reasons(g); // due to merges done before during AND gate detection!

        if !h.is_null() {
            self.check_ite_gate_implied(h);
            let mut extra_reasons_lit: Vec<LRAT_ID> = Vec::new();
            let mut extra_reasons_ulit: Vec<LRAT_ID> = Vec::new();
            let hl = gt(h).lhs;
            self.add_ite_matching_proof_chain(h, g, hl, lhs, &mut extra_reasons_lit, &mut extra_reasons_ulit);
            let (hl, gl) = (gt(h).lhs, gt(g).lhs);
            if self.merge_literals_gates(h, g, hl, gl, &extra_reasons_lit, &extra_reasons_ulit) {
                self.int().stats.congruence.ites += 1;
                log!(self.internal, "found merged literals");
            }
            self.delete_proof_chain();
            delete_gate(g);
            return h;
        } else {
            // do not sort clauses here obviously!
            // sort (begin (g->rhs), end (g->rhs));
            gt(g).garbage = false;
            gt(g).indexed = true;
            gt(g).shrunken = false;
            self.table.insert(g);
            self.int().stats.congruence.gates += 1;
            #[cfg(feature = "logging")]
            {
                gt(g).id = self.fresh_id;
                self.fresh_id += 1;
            }
            log!(self.internal, g, "creating new");
            if self.lrat() {
                update_ite_flags(g);
            }
            self.check_ite_gate_implied(g);
            let n = gt(g).rhs.len();
            for k in 0..n {
                let lit = gt(g).rhs[k];
                self.connect_goccs(g, lit);
            }
        }
        self.check_ite_lrat_reasons(g);
        self.int().stats.congruence.ite_gates += 1;
        g
    }

    pub fn check_ite_implied(&mut self, lhs: i32, cond: i32, then_lit: i32, else_lit: i32) {
        if self.lrat() {
            return;
        }
        self.check_ternary(cond, -else_lit, lhs);
        self.check_ternary(cond, else_lit, -lhs);
        self.check_ternary(-cond, -then_lit, lhs);
        self.check_ternary(-cond, then_lit, -lhs);
    }

    pub fn check_contained_module_rewriting(&mut self, c: CRef, lit: i32, normalized: bool, except: i32) {
        #[cfg(debug_assertions)]
        {
            let mut except = except;
            if lit == except {
                // happens for degenerated cases
                except = 0;
            }
            let normalize_lit = if lit == except { except } else { self.find_eager_representative(lit) };
            debug_assert!(!normalized || lit == -except || normalize_lit == lit);
            let mut found = false;
            log!(self.internal, c, "looking for (normalized) {} in ", lit);
            for k in 0..c.size() as usize {
                let other = c.lit(k);
                let normalize_other = if other == except { except } else { self.find_eager_representative(other) };
                log!(self.internal, "{} -> {} ", other, normalize_other);
                debug_assert!(!normalized || other == -except || normalize_other == other);
                if normalize_other == normalize_lit {
                    found = true;
                    break;
                }
            }
            debug_assert!(found);
        }
        let _ = (c, lit, normalized, except);
    }

    pub fn check_ite_lrat_reasons(&mut self, g: *mut Gate) {
        #[cfg(debug_assertions)]
        {
            debug_assert!(gt(g).tag == Gate_Type::ITE_Gate);
            if !self.lrat() {
                return;
            }
            debug_assert!(gt(g).arity() == 3);
            debug_assert!(is_tautological_ite_gate(g) || gt(g).pos_lhs_ids.len() == 4);
            debug_assert!(!gt(g).neg_lhs_ids.is_set());
            debug_assert!(gt(g).pos_lhs_ids.len() == 4);
        }
        let _ = g;
    }

    pub fn check_ite_gate_implied(&mut self, g: *mut Gate) {
        debug_assert!(gt(g).tag == Gate_Type::ITE_Gate);
        if self.lrat() {
            return;
        }
        let (l, c, t, e) = (gt(g).lhs, gt(g).rhs[0], gt(g).rhs[1], gt(g).rhs[2]);
        self.check_ite_implied(l, c, t, e);
    }

    pub fn init_ite_gate_extraction(&mut self, candidates: &mut Vec<ClauseSize>) {
        let mut ternary: Vec<CRef> = Vec::new();
        let vsize = self.int().vsize;
        self.glargecounts.resize(2 * vsize, 0);
        let nclauses = self.int().clauses.len();
        'next_clause: for ci in 0..nclauses {
            let c = self.int().clauses[ci];
            if c.garbage() {
                continue;
            }
            if c.redundant() {
                continue;
            }
            if c.size() < 3 {
                continue;
            }
            let mut size: u32 = 0;

            debug_assert!(!c.garbage());
            let csize = c.size() as usize;
            for i in 0..csize {
                let lit = c.lit(i);
                let v = self.val(lit);
                if v < 0 {
                    continue;
                }
                if v > 0 {
                    log!(self.internal, c, "deleting as satisfied due to {}", lit);
                    self.int().mark_garbage(c);
                    continue 'next_clause;
                }
                if size == 3 {
                    continue 'next_clause;
                }
                size += 1;
            }
            if size < 3 {
                continue;
            }
            debug_assert!(size == 3);
            ternary.push(c);
            log!(self.internal, c, "counting original ITE gate base");
            for i in 0..csize {
                let lit = c.lit(i);
                if self.val(lit) == 0 {
                    *self.largecount(lit) += 1;
                }
            }
        }

        verbose!(
            self.internal,
            4,
            "counted {} ternary ITE gates({}% of {} irredundant clauses)",
            ternary.len(),
            crate::format::fmt_f(percent(ternary.len() as f64, self.int().stats.current.irredundant as f64), 0),
            self.int().stats.current.irredundant as u64
        );
        let mut connected: usize = 0;
        'next_ternary: for &c in ternary.iter() {
            debug_assert!(!c.garbage());
            debug_assert!(!c.redundant());
            if self.int().terminated_asynchronously(1) {
                break;
            }
            let mut positive: u32 = 0;
            let mut negative: u32 = 0;
            let mut twice: u32 = 0;
            let csize = c.size() as usize;
            for i in 0..csize {
                let lit = c.lit(i);
                if self.val(lit) != 0 {
                    continue;
                }
                let count_not_lit = *self.largecount(-lit) as i32;
                if count_not_lit == 0 {
                    continue 'next_ternary;
                }
                let count_lit = *self.largecount(lit) as u32;
                debug_assert!(count_lit != 0);
                if count_lit > 1 && count_not_lit > 1 {
                    twice += 1;
                }
                if lit < 0 {
                    negative += 1;
                } else {
                    positive += 1;
                }
            }
            if twice < 2 {
                continue 'next_ternary;
            }
            debug_assert!(c.size() != 2);
            connected += 1;
            for i in 0..csize {
                let lit = c.lit(i);
                self.int().occs_mut(lit).push(c);
            }
            if positive != 0 && negative != 0 {
                candidates.push(ClauseSize::from_clause(c));
            }
        }

        ternary.clear();

        verbose!(
            self.internal,
            4,
            "connected {} large clauses {}%",
            candidates.len(),
            crate::format::fmt_f(percent(candidates.len() as f64, self.int().stats.current.irredundant as f64), 0)
        );

        let size_candidates = candidates.len();
        verbose!(
            self.internal,
            4,
            "{} candidates ITE base clauses ({}% of {} connected)",
            size_candidates,
            crate::format::fmt_f(percent(size_candidates as f64, connected as f64), 0),
            connected
        );
    }

    pub fn reset_ite_gate_extraction(&mut self) {
        self.condbin[0].clear();
        self.condbin[1].clear();
        self.condeq[0].clear();
        self.condeq[1].clear();
        self.glargecounts.clear();
        self.int().clear_occs();
    }

    pub fn copy_conditional_equivalences(&mut self, lit: i32, condbin: &mut lit_implications) {
        debug_assert!(condbin.is_empty());
        let n = self.int().occs(lit).len();
        for k in 0..n {
            let c = self.int().occs(lit)[k];
            debug_assert!(c.size() != 2);
            let mut first = 0;
            let mut second = 0;
            let csize = c.size() as usize;
            for i in 0..csize {
                let other = c.lit(i);
                if self.val(other) != 0 {
                    continue;
                }
                if other == lit {
                    continue;
                }
                if first == 0 {
                    first = other;
                } else {
                    debug_assert!(second == 0);
                    second = other;
                    // all other literals are true, so we can stop here
                    // otherwise, one clause does not have length 3 (ignoring
                    // unit)
                    #[cfg(not(debug_assertions))]
                    break;
                }
            }
            debug_assert!(first != 0);
            debug_assert!(second != 0);
            let mut p = lit_implication::new(first, second, c);

            if self.int().vlit(first) < self.int().vlit(second) {
                debug_assert!(p.first == first);
                debug_assert!(p.second == second);
            } else {
                debug_assert!(self.int().vlit(second) < self.int().vlit(first));
                p.swap();
                debug_assert!(p.first == second);
                debug_assert!(p.second == first);
            }
            log!(self.internal, c, "literal {} condition binary clause {} {}", lit, first, second);
            condbin.push(p);
        }
    }

    /// The C++ iterator range `[begin, end)` is passed as the slice
    /// `implications`; the result is an index into it
    /// (`implications.len ()` == `end`).
    pub fn find_lit_implication_second_literal(&mut self, lit: i32, implications: &[lit_implication]) -> usize {
        let internal: &Internal = self.int();
        let key = internal.vlit(lit);
        let found = implications.partition_point(|a| internal.vlit(a.second) < key);
        #[cfg(debug_assertions)]
        let found2 = found < implications.len() && !(key < internal.vlit(implications[found].second));

        if found < implications.len() && implications[found].second == lit {
            #[cfg(debug_assertions)]
            debug_assert!(found2 == (found < implications.len()));
            return found;
        }
        implications.len()
    }

    /// The C++ iterator ranges `[pos_begin, pos_end)` and
    /// `[neg_begin, neg_end)` are passed as slices.
    pub fn search_condeq(
        &mut self,
        lit: i32,
        pos_lit: i32,
        pos: &[lit_implication],
        neg_lit: i32,
        neg: &[lit_implication],
        condeq: &mut lit_equivalences,
    ) {
        debug_assert!(neg_lit == -pos_lit);
        debug_assert!(!pos.is_empty());
        debug_assert!(!neg.is_empty());
        debug_assert!(pos[0].first == pos_lit);
        debug_assert!(neg[0].first == neg_lit);
        for p in pos.iter() {
            let other = p.second;
            let not_other = -other;
            let other_clause = self.find_lit_implication_second_literal(not_other, neg);
            debug_assert!(clause_contains(p.clause, lit));
            if other_clause != neg.len() {
                let oc = neg[other_clause];
                debug_assert!(clause_contains(oc.clause, neg_lit));
                debug_assert!(clause_contains(p.clause, other));
                let mut equivalence = lit_equivalence::new(neg_lit, oc.clause, other, p.clause);
                if pos_lit > 0 {
                    equivalence.negate_both();
                }
                if self.lrat() {
                    equivalence.check_invariant();
                }
                log!(
                    self.internal,
                    "found conditional {} equivalence {} = {}",
                    lit,
                    equivalence.first,
                    equivalence.second
                );
                debug_assert!(equivalence.first > 0);
                debug_assert!(self.int().vlit(equivalence.first) < self.int().vlit(equivalence.second));
                self.check_ternary(lit, neg_lit, -other);
                self.check_ternary(lit, -neg_lit, other);
                condeq.push(equivalence);
                if equivalence.second < 0 {
                    let mut tmp = equivalence.swap();
                    let inverse_equivalence = tmp.negate_both();
                    condeq.push(inverse_equivalence);
                    if self.lrat() {
                        inverse_equivalence.check_invariant();
                    }
                } else {
                    let inverse_equivalence = equivalence.swap();
                    condeq.push(inverse_equivalence);
                    if self.lrat() {
                        inverse_equivalence.check_invariant();
                    }
                }
            }
        }
        let _ = lit;
    }

    pub fn extract_condeq_pairs(&mut self, lit: i32, condbin: &mut lit_implications, condeq: &mut lit_equivalences) {
        let end = condbin.len();
        let mut pos_begin = 0usize;
        let mut next_lit;

        log!(self.internal, "searching for first positive literal for lit {}", lit);
        loop {
            if pos_begin == end {
                return;
            }
            next_lit = condbin[pos_begin].first;
            log!(self.internal, "checking {}", next_lit);
            if next_lit > 0 {
                break;
            }
            pos_begin += 1;
        }

        loop {
            debug_assert!(pos_begin != end);
            debug_assert!(next_lit == condbin[pos_begin].first);
            debug_assert!(next_lit > 0);
            let pos_lit = next_lit;
            let mut pos_end = pos_begin + 1;
            log!(self.internal, "searching for first other literal after finding lit {}", next_lit);
            loop {
                if pos_end == end {
                    return;
                }
                next_lit = condbin[pos_end].first;
                if next_lit != pos_lit {
                    break;
                }
                pos_end += 1;
            }
            debug_assert!(pos_end != end);
            debug_assert!(next_lit == condbin[pos_end].first);
            let neg_lit = -pos_lit;
            if next_lit != neg_lit {
                if next_lit < 0 {
                    pos_begin = pos_end + 1;
                    log!(self.internal, "next_lit {} < 0", next_lit);
                    loop {
                        if pos_begin == end {
                            return;
                        }
                        next_lit = condbin[pos_begin].first;
                        if next_lit > 0 {
                            break;
                        }
                        pos_begin += 1;
                    }
                } else {
                    pos_begin = pos_end;
                }
                continue;
            }
            let neg_begin = pos_end;
            let mut neg_end = neg_begin + 1;
            while neg_end != end {
                next_lit = condbin[neg_end].first;
                if next_lit != neg_lit {
                    break;
                }
                neg_end += 1;
            }
            #[cfg(feature = "logging")]
            {
                for p in pos_begin..pos_end {
                    log!(
                        self.internal,
                        "conditional {} binary clause {} {} with positive {}",
                        lit,
                        condbin[p].first,
                        condbin[p].second,
                        pos_lit
                    );
                }
                for p in neg_begin..neg_end {
                    log!(
                        self.internal,
                        "conditional {} binary clause {} {} with negative {}",
                        lit,
                        condbin[p].first,
                        condbin[p].second,
                        neg_lit
                    );
                }
            }
            let pos_size = pos_end - pos_begin;
            let neg_size = neg_end - neg_begin;
            debug_assert!(pos_end <= neg_begin || neg_end <= pos_begin);
            if pos_size <= neg_size {
                log!(
                    self.internal,
                    "searching negation of {} conditional binary clauses with positive {} in {} conditional binary clauses with {}",
                    pos_size,
                    loglit!(self.internal, pos_lit),
                    neg_size,
                    loglit!(self.internal, neg_lit)
                );
                self.search_condeq(
                    lit,
                    pos_lit,
                    &condbin[pos_begin..pos_end],
                    neg_lit,
                    &condbin[neg_begin..neg_end],
                    condeq,
                );
            } else {
                log!(
                    self.internal,
                    "searching negation of {} conditional binary clauses with negative {} in {} conditional binary clauses with {}",
                    neg_size,
                    neg_lit,
                    pos_size,
                    pos_lit
                );
                self.search_condeq(
                    lit,
                    neg_lit,
                    &condbin[neg_begin..neg_end],
                    pos_lit,
                    &condbin[pos_begin..pos_end],
                    condeq,
                );
            }
            if neg_end == end {
                return;
            }
            debug_assert!(next_lit == condbin[neg_end].first);
            if next_lit < 0 {
                pos_begin = neg_end + 1;
                loop {
                    if pos_begin == end {
                        return;
                    }
                    next_lit = condbin[pos_begin].first;
                    if next_lit > 0 {
                        break;
                    }
                    pos_begin += 1;
                }
            } else {
                pos_begin = neg_end;
            }
        }
    }

    pub fn find_conditional_equivalences(&mut self, lit: i32, condbin: &mut lit_implications, condeq: &mut lit_equivalences) {
        debug_assert!(condbin.is_empty());
        debug_assert!(condeq.is_empty());
        debug_assert!(self.int().occs(lit).len() > 1);
        self.copy_conditional_equivalences(lit, condbin);
        {
            let internal: &Internal = self.int();
            msort(
                internal.opts.radixsortlim as usize,
                condbin,
                |a| litpair_rank(internal, a),
                |a, b| litpair_rank(internal, a) < litpair_rank(internal, b),
            );
        }

        self.extract_condeq_pairs(lit, condbin, condeq);
        {
            let internal: &Internal = self.int();
            msort(
                internal.opts.radixsortlim as usize,
                condeq,
                |a| litequivalence_rank(internal, a),
                |a, b| litequivalence_rank(internal, a) < litequivalence_rank(internal, b),
            );
        }

        #[cfg(feature = "logging")]
        {
            for pair in condeq.iter() {
                log!(self.internal, "sorted conditional {} equivalence {} = {}", lit, pair.first, pair.second);
            }
            log!(self.internal, "found {} conditional {} equivalences", condeq.len(), lit);
        }
    }

    pub fn merge_condeq(&mut self, cond: i32, condeq: &mut lit_equivalences, not_condeq: &mut lit_equivalences) {
        log!(self.internal, "merging cond for literal {}", cond);
        let mut q = 0usize;
        let end_not_condeq = not_condeq.len();
        for pi in 0..condeq.len() {
            let p = condeq[pi];
            let lhs = p.first;
            let then_lit = p.second;
            #[cfg(debug_assertions)]
            {
                for q2 in 0..q {
                    debug_assert!(not_condeq[q2].first < lhs);
                }
                if self.lrat() {
                    p.check_invariant();
                }
            }
            debug_assert!(lhs > 0);
            while q != end_not_condeq && not_condeq[q].first < lhs {
                q += 1;
            }
            let mut q2 = q;
            while q2 != end_not_condeq && not_condeq[q2].first == lhs {
                log!(self.internal, "looking when {} at p= {} {}", cond, p.first, p.second);
                log!(self.internal, "looking when {} at {} {}", -cond, not_condeq[q].first, not_condeq[q].second);
                let not_cond_pair = not_condeq[q2];
                q2 += 1;
                let else_lit = not_cond_pair.second;
                let mut clauses: Vec<LitClausePair> = Vec::new();
                if self.lrat() {
                    // The then/else literal is the second of the pair, hence
                    // the swap of the reasons
                    debug_assert!(!p.first_clause.is_null() && !p.second_clause.is_null());
                    debug_assert!(!not_cond_pair.first_clause.is_null() && !not_cond_pair.second_clause.is_null());
                    log!(self.internal, p.second_clause, "pairing {}", then_lit);
                    log!(self.internal, p.first_clause, "pairing {}", -then_lit);
                    log!(self.internal, not_cond_pair.second_clause, "pairing {}", else_lit);
                    log!(self.internal, not_cond_pair.first_clause, "pairing {}", -else_lit);
                    clauses.push(LitClausePair::new(then_lit, p.second_clause));
                    clauses.push(LitClausePair::new(-then_lit, p.first_clause));
                    clauses.push(LitClausePair::new(else_lit, not_cond_pair.second_clause));
                    clauses.push(LitClausePair::new(-else_lit, not_cond_pair.first_clause));
                    not_cond_pair.check_invariant();
                }
                self.new_ite_gate(lhs, cond, then_lit, else_lit, clauses);
                if self.int().unsat {
                    return;
                }
            }
        }
    }

    pub fn extract_ite_gates_of_literal(&mut self, lit: i32) {
        log!(self.internal, "search for ITE for literal {} ", lit);
        // The callees never access the members 'condbin' and 'condeq'
        // directly, so we can move them out while working on them.
        let mut condbin0 = std::mem::take(&mut self.condbin[0]);
        let mut condbin1 = std::mem::take(&mut self.condbin[1]);
        let mut condeq0 = std::mem::take(&mut self.condeq[0]);
        let mut condeq1 = std::mem::take(&mut self.condeq[1]);
        self.find_conditional_equivalences(lit, &mut condbin0, &mut condeq0);
        if !condeq0.is_empty() {
            self.find_conditional_equivalences(-lit, &mut condbin1, &mut condeq1);
            if !condeq1.is_empty() {
                if lit < 0 {
                    self.merge_condeq(-lit, &mut condeq0, &mut condeq1);
                } else {
                    self.merge_condeq(lit, &mut condeq1, &mut condeq0);
                }
            }
        }

        condbin0.clear();
        condbin1.clear();
        condeq0.clear();
        condeq1.clear();
        self.condbin[0] = condbin0;
        self.condbin[1] = condbin1;
        self.condeq[0] = condeq0;
        self.condeq[1] = condeq1;
    }

    pub fn extract_ite_gates_of_variable(&mut self, idx: i32) {
        let lit = idx;
        let not_lit = -idx;

        let size_lit_watches = self.int().occs(lit).len();
        let size_not_lit_watches = self.int().occs(not_lit).len();
        if size_lit_watches <= size_not_lit_watches {
            if size_lit_watches > 1 {
                self.extract_ite_gates_of_literal(lit);
            }
        } else if size_not_lit_watches > 1 {
            self.extract_ite_gates_of_literal(not_lit);
        }
    }

    pub fn extract_ite_gates(&mut self) {
        debug_assert!(!self.full_watching);
        if self.int().opts.congruenceite == 0 {
            return;
        }
        if self.int().terminated_asynchronously(1) {
            return;
        }
        start!(self.int(), extractites);
        let mut candidates: Vec<ClauseSize> = Vec::new();
        let gates_before = self.int().stats.congruence.ite_gates;
        self.init_ite_gate_extraction(&mut candidates);

        for idx in self.int().vars() {
            if self.int().flags(idx).active() {
                self.extract_ite_gates_of_variable(idx);
                if self.int().unsat || self.int().terminated_asynchronously(1) {
                    break;
                }
            }
        }
        // Kissat has an alternative version MERGE_CONDITIONAL_EQUIVALENCES
        verbose!(
            self.internal,
            2,
            "[congruence-{}] found {} ITE clauses",
            self.int().stats.congruence.rounds,
            self.int().stats.congruence.ite_gates - gates_before
        );
        self.reset_ite_gate_extraction();
        stop!(self.int(), extractites);
    }

    /*----------------------------------------------------------------------*/

    pub fn extract_gates(&mut self) {
        start!(self.int(), extract);
        self.extract_and_gates();
        debug_assert!(self.int().unsat || self.lrat_chain.is_empty());
        debug_assert!(self.int().unsat || self.chain.is_empty());
        if self.int().unsat || self.int().terminated_asynchronously(1) {
            stop!(self.int(), extract);
            return;
        }

        if self.lrat() {
            // save some memory
            self.mu2_ids.clear();
            shrink_vector(&mut self.mu2_ids);
            self.mu4_ids.clear();
            shrink_vector(&mut self.mu4_ids);
        } else {
            debug_assert!(self.mu2_ids.is_empty());
            debug_assert!(self.mu4_ids.is_empty());
        }
        self.extract_xor_gates();
        debug_assert!(self.int().unsat || self.lrat_chain.is_empty());
        debug_assert!(self.int().unsat || self.chain.is_empty());

        if self.int().unsat || self.int().terminated_asynchronously(1) {
            stop!(self.int(), extract);
            return;
        }
        self.extract_ite_gates();
        stop!(self.int(), extract);
    }
}

/*------------------------------------------------------------------------*/
// top level function to extract gate

impl Internal {
    /// `remove_units_before_run` defaults to `false` in C++
    pub fn extract_gates(&mut self, remove_units_before_run: bool) -> bool {
        if self.terminated_asynchronously(1) {
            return false;
        }
        if self.unsat {
            return false;
        }
        if self.opts.congruence == 0 {
            return false;
        }
        if self.level != 0 {
            self.backtrack(0);
        }
        if !self.propagate() {
            self.learn_empty_clause();
            return false;
        }
        if self.congruence_delay.bumpreasons.delay() {
            log!(self, "delaying congruence {} more times", self.congruence_delay.bumpreasons.limit);
            return false;
        }

        // congruencebinary is already doing it (and more actually)
        if self.opts.congruencebinaries == 0 {
            if remove_units_before_run {
                self.clear_watches();
                self.mark_satisfied_clauses_as_garbage(); // breaks watch lists
                self.connect_watches(false);
            }
            let dedup = self.opts.deduplicate;
            self.opts.deduplicate = 1;
            self.mark_duplicated_binary_clauses_as_garbage();
            self.opts.deduplicate = dedup;
        } else if remove_units_before_run {
            // to remove false literals from clauses
            // It makes the technique stronger as long clauses
            // can become binary / ternary

            // In the SC2024 there are benchmarks where 16% of variables are
            // units at the beginning, so we remove units during
            // preprocessing. Later GC and other techniques are doing it
            // anyway, so we try to avoid going over all clauses once more.
            self.mark_satisfied_clauses_as_garbage(); // breaks watch lists but we
                                                      // unwatch anyway afterwards
            self.report(b'.', 0);
        }
        self.stats.congruence.rounds += 1;
        self.clear_watches();
        //  connect_binary_watches ();
        start_simplifier!(self, congruence, CONGRUENCE);
        let mut closure = Closure::new(self as *mut Internal);

        closure.init_closure();
        debug_assert!(self.unsat || closure.chain.is_empty());
        debug_assert!(self.unsat || self.lrat_chain.is_empty());
        closure.extract_binaries();
        // the binary stuff is covered by other techniques
        let old_merged = self.stats.congruence.congruent;
        debug_assert!(self.unsat || closure.chain.is_empty());
        debug_assert!(self.unsat || self.lrat_chain.is_empty());
        closure.extract_gates();
        debug_assert!(self.unsat || closure.chain.is_empty());
        debug_assert!(self.unsat || self.lrat_chain.is_empty());
        let mut reconnect = true;
        if !self.terminated_asynchronously(1) {
            closure.reset_extraction(); // reconnect watches
            reconnect = false; // fresh watches
        }

        if !self.unsat && !self.terminated_asynchronously(1) {
            closure.find_units();
            debug_assert!(self.unsat || closure.chain.is_empty());
            debug_assert!(self.unsat || self.lrat_chain.is_empty());
            if !self.unsat && !self.terminated_asynchronously(1) {
                closure.find_equivalences();
                debug_assert!(self.unsat || closure.chain.is_empty());
                debug_assert!(self.unsat || self.lrat_chain.is_empty());

                if !self.unsat && !self.terminated_asynchronously(1) {
                    let propagated = closure.propagate_units_and_equivalences() as i32;
                    debug_assert!(self.unsat || closure.chain.is_empty());
                    if !self.unsat && propagated != 0 && !self.terminated_asynchronously(1) {
                        closure.forward_subsume_matching_clauses();
                    }
                }
            }
            reconnect = true; // possibly stale watches
        }
        closure.reset_closure();
        if reconnect {
            self.clear_watches();
            self.connect_watches(false);
        }
        if !self.unsat {
            self.propagated = 0;
            self.propagated2 = 0;
        }
        debug_assert!(closure.new_unwatched_binary_clauses.is_empty() || self.terminated_asynchronously(1));
        drop(closure);
        self.reset_occs();
        self.reset_noccs();
        debug_assert!(!self.occurring());
        debug_assert!(self.lrat_chain.is_empty());
        let new_merged = self.stats.congruence.congruent;

        phase!(self, "congruence-phase", self.stats.congruence.rounds, "merged {} literals", new_merged - old_merged);
        if !self.terminated_asynchronously(1) && !self.unsat && !self.propagate() {
            self.learn_empty_clause();
        }

        stop_simplifier!(self, congruence, CONGRUENCE);
        let quiet = (self.opts.reportall == 0 && (self.stats.congruence.congruent - old_merged) == 0) as i32;
        self.report(b'c', quiet);
        #[cfg(debug_assertions)]
        {
            let mut watched: usize = 0;
            for v in self.vars() {
                let mut sgn = -1;
                while sgn <= 1 {
                    let lit = v * sgn;
                    let n = self.watches(lit).len();
                    for i in 0..n {
                        let w = self.watches(lit)[i];
                        debug_assert!(!w.binary() || !w.clause.garbage());
                        if w.clause.garbage() {
                            continue;
                        }
                        watched += 1;
                        log!(self, w.clause, "watched");
                    }
                    sgn += 2;
                }
            }
            log!(self, "and now the clauses:");
            let mut nb_clauses: usize = 0;
            for i in 0..self.clauses.len() {
                let c = self.clauses[i];
                if c.garbage() {
                    continue;
                }
                log!(self, c, "watched");
                nb_clauses += 1;
            }
            debug_assert!(watched == nb_clauses * 2);
        }
        debug_assert!(!self.occurring());

        if new_merged == old_merged {
            self.congruence_delay.bumpreasons.bump_delay();
        } else {
            self.congruence_delay.bumpreasons.reduce_delay();
        }

        new_merged != old_merged
    }
}

/*------------------------------------------------------------------------*/

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn next_prime_matches_brute_force() {
        fn brute(n: usize) -> usize {
            if n == 0 {
                return 0;
            }
            let mut m = std::cmp::max(n, 2);
            loop {
                if (2..m).take_while(|d| d * d <= m).all(|d| m % d != 0) {
                    return m;
                }
                m += 1;
            }
        }
        for n in 0..5000usize {
            assert_eq!(ht_next_prime(n), brute(n), "n = {}", n);
        }
        assert_eq!(ht_next_hash_pow2(129), 256);
        assert_eq!(ht_next_hash_pow2(128), 128);
    }

    fn hash_of(mode: u32, k: u64) -> usize {
        (match mode {
            0 => k,
            1 => k % 13,
            2 => k.wrapping_mul(0x9E3779B97F4A7C15) ^ (k >> 3),
            _ => (k.wrapping_mul(2654435761)) & 0xffffff,
        }) as usize
    }

    struct Xs(u64);
    impl Xs {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0
        }
    }

    /// Generates a random operation script (see
    /// 'scripts/congruence_hashtable_driver.cpp').
    fn gen_script(seed: u64, len: usize) -> Vec<String> {
        let mut r = Xs(seed | 1);
        let mut ops = Vec::new();
        let bcs = [128usize, 0, 1, 2, 3, 10, 16, 97, 100, 7];
        let range = [40u64, 300, 5000];
        let mut keyrange = 300;
        for step in 0..len {
            if step % 400 == 0 {
                let bc = bcs[(r.next() % bcs.len() as u64) as usize];
                let mode = r.next() % 4;
                keyrange = range[(r.next() % 3) as usize];
                ops.push(format!("N {} {}", bc, mode));
            }
            let x = r.next() % 100;
            let op = if x < 45 {
                format!("I {}", r.next() % keyrange)
            } else if x < 60 {
                format!("E {}", r.next() % keyrange)
            } else if x < 70 {
                format!("P {}", r.next() % 64)
            } else if x < 80 {
                format!("F {}", r.next() % keyrange)
            } else if x < 82 {
                "C".to_string()
            } else if x < 85 {
                format!("R {}", r.next() % 600)
            } else if x < 88 {
                format!("V {}", r.next() % 600)
            } else if x < 90 {
                format!("W {}", 2 + r.next() % 5)
            } else {
                "D".to_string()
            };
            ops.push(op);
        }
        ops.push("D".to_string());
        ops
    }

    /// Runs the script on 'LibcxxHashSet' and produces the same trace as
    /// the C++ driver.
    fn run_script(ops: &[String]) -> String {
        let mut out = String::new();
        let mut s: Option<(LibcxxHashSet<u64>, u32)> = None;
        for op in ops {
            let parts: Vec<&str> = op.split_whitespace().collect();
            match parts[0] {
                "N" => {
                    let bc: usize = parts[1].parse().unwrap();
                    let mode: u32 = parts[2].parse().unwrap();
                    let set = LibcxxHashSet::new(bc, 0u64);
                    out += &format!("N {}\n", set.bucket_count());
                    s = Some((set, mode));
                }
                _ => {
                    let (set, mode) = s.as_mut().unwrap();
                    let mode = *mode;
                    match parts[0] {
                        "I" => {
                            let k: u64 = parts[1].parse().unwrap();
                            let ins = set.insert(hash_of(mode, k), k, |x| x == k).1;
                            out += &format!("I {} {}\n", k, ins as i32);
                        }
                        "E" => {
                            let k: u64 = parts[1].parse().unwrap();
                            let it = set.find(hash_of(mode, k), |x| x == k);
                            if let Some(n) = it {
                                set.erase(n);
                            }
                            out += &format!("E {} {}\n", k, it.is_some() as i32);
                        }
                        "P" => {
                            let i: usize = parts[1].parse().unwrap();
                            let mut next: i64 = -1;
                            if i < set.len() {
                                let mut it = set.begin().unwrap();
                                for _ in 0..i {
                                    it = set.next(it).unwrap();
                                }
                                if let Some(nx) = set.erase(it) {
                                    next = set.get(nx) as i64;
                                }
                            }
                            out += &format!("P {} {}\n", i, next);
                        }
                        "F" => {
                            let k: u64 = parts[1].parse().unwrap();
                            let found = set.find(hash_of(mode, k), |x| x == k).is_some();
                            out += &format!("F {} {}\n", k, found as i32);
                        }
                        "C" => {
                            set.clear();
                            out += "C\n";
                        }
                        "R" => {
                            let n: usize = parts[1].parse().unwrap();
                            set.rehash(n);
                            out += &format!("R {} {}\n", n, set.bucket_count());
                        }
                        "V" => {
                            let n: usize = parts[1].parse().unwrap();
                            set.reserve(n);
                            out += &format!("V {} {}\n", n, set.bucket_count());
                        }
                        "W" => {
                            let m: u64 = parts[1].parse().unwrap();
                            let mut erased = 0;
                            let mut it = set.begin();
                            while let Some(n) = it {
                                if set.get(n) % m == 0 {
                                    it = set.erase(n);
                                    erased += 1;
                                } else {
                                    it = set.next(n);
                                }
                            }
                            out += &format!("W {} {}\n", m, erased);
                        }
                        "D" => {
                            out += &format!("D {} {}:", set.bucket_count(), set.len());
                            for k in set.elements() {
                                out += &format!(" {}", k);
                            }
                            out += "\n";
                        }
                        _ => unreachable!(),
                    }
                }
            }
        }
        out
    }

    /// Differential test against libc++ 21 'std::unordered_set'.  Requires
    /// the compiled driver 'scripts/congruence_hashtable_driver.cpp' whose
    /// path is given in 'CADICAL_HT_DRIVER' (skipped otherwise).
    #[test]
    fn libcxx_hash_set_differential() {
        let driver = match std::env::var("CADICAL_HT_DRIVER") {
            Ok(d) => d,
            Err(_) => {
                eprintln!("CADICAL_HT_DRIVER not set, skipping libc++ differential test");
                return;
            }
        };
        for seed in 1..=40u64 {
            let ops = gen_script(seed * 0x1234567, 6000);
            let expected = run_script(&ops);
            let mut child = std::process::Command::new(&driver)
                .stdin(std::process::Stdio::piped())
                .stdout(std::process::Stdio::piped())
                .spawn()
                .expect("cannot run driver");
            {
                use std::io::Write;
                let stdin = child.stdin.as_mut().unwrap();
                stdin.write_all(ops.join("\n").as_bytes()).unwrap();
                stdin.write_all(b"\n").unwrap();
            }
            let output = child.wait_with_output().unwrap();
            let actual = String::from_utf8(output.stdout).unwrap();
            if actual != expected {
                let a: Vec<&str> = actual.lines().collect();
                let e: Vec<&str> = expected.lines().collect();
                for i in 0..std::cmp::max(a.len(), e.len()) {
                    if a.get(i) != e.get(i) {
                        panic!(
                            "seed {} line {}: C++ '{}' vs Rust '{}'",
                            seed,
                            i,
                            a.get(i).unwrap_or(&""),
                            e.get(i).unwrap_or(&"")
                        );
                    }
                }
            }
        }
    }
}

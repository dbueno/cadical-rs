//! Port of `extend.cpp`.

#[allow(unused_imports)]
use crate::prelude::*;

impl External {
    pub fn push_zero_on_extension_stack(&mut self) {
        self.extension.push(0);
        log!(self, "pushing 0 on extension stack");
    }

    pub fn push_id_on_extension_stack(&mut self, id: i64) {
        // (C++: 'static_cast<int> (id << 32)', which is always zero.)
        let higher_bits: u32 = (id.wrapping_shl(32) as i32) as u32;
        let lower_bits: u32 = (id & ((1i64 << 32) - 1)) as u32;
        self.extension.push(higher_bits as i32);
        self.extension.push(lower_bits as i32);
        log!(self, "pushing id {} = {} + {}", id as u64, higher_bits as i32, lower_bits as i32);
    }

    pub fn push_clause_literal_on_extension_stack(&mut self, ilit: i32) {
        debug_assert!(ilit != 0);
        let internal = self.internal_unbound();
        let elit = internal.externalize(ilit);
        let eidx = elit.abs();
        let is_extension_var = self.ervars[eidx as usize];
        if is_extension_var {
            internal.flags_mut(ilit).factored_but_on_reconstruction_stack = true;
            log!(self, "marking lit {} as tainted", loglit!(self, ilit));
        }

        debug_assert!(elit != 0);
        self.extension.push(elit);
        log!(self, "pushing clause literal {} on extension stack (internal {})", elit, ilit);
    }

    pub fn push_witness_literal_on_extension_stack(&mut self, ilit: i32) {
        debug_assert!(ilit != 0);
        let elit = self.internal().externalize(ilit);
        debug_assert!(elit != 0);
        self.extension.push(elit);
        log!(self, "pushing witness literal {} on extension stack (internal {})", elit, ilit);
        if self.marked(&self.witness, elit) {
            return;
        }
        log!(self, "marking witness {}", elit);
        let mut witness = std::mem::take(&mut self.witness);
        self.mark(&mut witness, elit);
        self.witness = witness;
    }

    /// The extension stack allows to reconstruct a satisfying assignment
    /// for the original formula after removing eliminated clauses.  This
    /// was pioneered by Niklas Soerensson in MiniSAT and for instance is
    /// described in our inprocessing paper, published at IJCAR'12.  This
    /// first function adds a clause to this stack.  First the blocking or
    /// eliminated literal is added, and then the rest of the clause.
    pub fn push_clause_on_extension_stack(&mut self, c: CRef) {
        let internal = self.internal_unbound();
        internal.stats.weakened += 1;
        internal.stats.weakenedlen += c.size() as i64;
        self.push_zero_on_extension_stack();
        self.push_id_on_extension_stack(c.id());
        self.push_zero_on_extension_stack();
        for i in 0..c.size() as usize {
            let lit = c.lit(i);
            self.push_clause_literal_on_extension_stack(lit);
        }
    }

    /// C++ overload `External::push_clause_on_extension_stack` (renamed).
    pub fn push_clause_on_extension_stack_with_witness(&mut self, c: CRef, pivot: i32) {
        self.push_zero_on_extension_stack();
        self.push_witness_literal_on_extension_stack(pivot);
        self.push_clause_on_extension_stack(c);
    }

    pub fn push_binary_clause_on_extension_stack(&mut self, id: i64, pivot: i32, other: i32) {
        let internal = self.internal_unbound();
        internal.stats.weakened += 1;
        internal.stats.weakenedlen += 2;
        self.push_zero_on_extension_stack();
        self.push_witness_literal_on_extension_stack(pivot);
        self.push_zero_on_extension_stack();
        self.push_id_on_extension_stack(id);
        self.push_zero_on_extension_stack();
        self.push_clause_literal_on_extension_stack(pivot);
        self.push_clause_literal_on_extension_stack(other);
    }

    /*----------------------------------------------------------------------*/

    pub fn push_external_clause_and_witness_on_extension_stack(&mut self, c: &[i32], w: &[i32], id: i64) {
        debug_assert!(id != 0);
        self.extension.push(0);
        for &elit in w.iter() {
            debug_assert!(elit != i32::MIN);
            self.init(elit.abs(), false);
            self.extension.push(elit);
            let mut witness = std::mem::take(&mut self.witness);
            self.mark(&mut witness, elit);
            self.witness = witness;
        }
        self.extension.push(0);
        let higher_bits: u32 = (id.wrapping_shl(32) as i32) as u32;
        let lower_bits: u32 = (id & ((1i64 << 32) - 1)) as u32;
        self.extension.push(higher_bits as i32);
        self.extension.push(lower_bits as i32);
        self.extension.push(0);
        for &elit in c.iter() {
            debug_assert!(elit != i32::MIN);
            self.init(elit.abs(), false);
            self.extension.push(elit);
        }
    }

    /*----------------------------------------------------------------------*/

    /// This is the actual extension process. It goes backward over the
    /// clauses on the extension stack and flips the assignment of one of
    /// the blocking literals in the conditional autarky stored before the
    /// clause.  In the original algorithm for witness construction for
    /// variable elimination and blocked clause removal the conditional
    /// autarky consists of a single literal from the removed clause, while
    /// in general the autarky witness can contain an arbitrary set of
    /// literals.  We are using the more general witness reconstruction here
    /// which for instance would also work for super-blocked or set-blocked
    /// clauses.
    pub fn extend(&mut self) {
        debug_assert!(!self.extended);
        let internal = self.internal_unbound();
        start!(internal, extend);
        internal.stats.extensions += 1;

        phase!(
            self,
            "extend",
            internal.stats.extensions,
            "mapping internal {} assignments to {} assignments",
            internal.max_var,
            self.max_var
        );

        let mut updated: i64 = 0;
        let mut i: u32 = 1;
        while i <= self.max_var as u32 {
            let ilit = self.e2i[i as usize];
            if ilit == 0 {
                i += 1;
                continue;
            }
            if i as usize >= self.vals.len() {
                self.vals.resize(i as usize + 1, false);
            }
            self.vals[i as usize] = internal.val(ilit) > 0;
            updated += 1;
            i += 1;
        }
        phase!(self, "extend", internal.stats.extensions, "updated {} external assignments", updated);
        phase!(
            self,
            "extend",
            internal.stats.extensions,
            "extending through extension stack of size {}",
            self.extension.len()
        );
        let _ = updated;
        let begin = 0usize;
        let mut i = self.extension.len();
        let mut flipped: i64 = 0;
        while i != begin {
            let mut satisfied = false;
            let mut lit;
            debug_assert!(i != begin);
            loop {
                i -= 1;
                lit = self.extension[i];
                if lit == 0 {
                    break;
                }
                if satisfied {
                    continue;
                }
                if self.ival(lit) == lit {
                    satisfied = true;
                }
                debug_assert!(i != begin);
            }
            debug_assert!(i != begin);
            log!(self, "id={}", ((self.extension[i] as i64) << 32) + self.extension[i - 1] as i64);
            debug_assert!(self.extension[i] != 0 || self.extension[i - 1] != 0);
            i -= 1;
            debug_assert!(i != begin);
            i -= 1;
            debug_assert!(i != begin);
            debug_assert!(self.extension[i] == 0);
            i -= 1;
            debug_assert!(i != begin);
            if satisfied {
                loop {
                    i -= 1;
                    if self.extension[i] == 0 {
                        break;
                    }
                    debug_assert!(i != begin);
                }
            } else {
                loop {
                    i -= 1;
                    lit = self.extension[i];
                    if lit == 0 {
                        break;
                    }
                    let tmp = self.ival(lit); // not 'signed char'!!!
                    if tmp != lit {
                        log!(self, "flipping blocking literal {}", lit);
                        debug_assert!(lit != 0);
                        debug_assert!(lit != i32::MIN);
                        let idx = lit.unsigned_abs() as usize;
                        if idx >= self.vals.len() {
                            self.vals.resize(idx + 1, false);
                        }
                        self.vals[idx] = !self.vals[idx];
                        internal.stats.extended += 1;
                        flipped += 1;
                    }
                    debug_assert!(i != begin);
                }
            }
        }
        phase!(
            self,
            "extend",
            internal.stats.extensions,
            "flipped {} literals during extension",
            flipped
        );
        let _ = flipped;
        self.extended = true;
        log!(self, "extended");
        stop!(internal, extend);
    }

    /*----------------------------------------------------------------------*/

    pub fn traverse_witnesses_backward(&mut self, it: &mut dyn WitnessIterator) -> bool {
        if self.internal().unsat {
            return true;
        }
        let mut clause: Vec<i32> = Vec::new();
        let mut witness: Vec<i32> = Vec::new();
        let begin = 0usize;
        let mut i = self.extension.len();
        while i != begin {
            let mut lit;
            loop {
                i -= 1;
                lit = self.extension[i];
                if lit == 0 {
                    break;
                }
                clause.push(lit);
            }
            debug_assert!(lit == 0);
            i -= 1;
            let id: i64 = ((self.extension[i - 1] as i64) << 32) + self.extension[i] as i64;
            debug_assert!(id != 0);
            i -= 2;
            debug_assert!(self.extension[i] == 0);
            debug_assert!(i != begin);
            loop {
                i -= 1;
                lit = self.extension[i];
                if lit == 0 {
                    break;
                }
                witness.push(lit);
            }
            clause.reverse();
            witness.reverse();
            log!(self, &clause, "traversing clause");
            if !it.witness(&clause, &witness, id) {
                return false;
            }
            clause.clear();
            witness.clear();
        }
        true
    }

    pub fn traverse_witnesses_forward(&mut self, it: &mut dyn WitnessIterator) -> bool {
        if self.internal().unsat {
            return true;
        }
        let mut clause: Vec<i32> = Vec::new();
        let mut witness: Vec<i32> = Vec::new();
        let end = self.extension.len();
        let mut i = 0usize;
        if i != end {
            let mut lit = self.extension[i];
            i += 1;
            loop {
                debug_assert!(lit == 0);
                loop {
                    lit = self.extension[i];
                    i += 1;
                    if lit == 0 {
                        break;
                    }
                    witness.push(lit);
                }
                debug_assert!(lit == 0);
                debug_assert!(i != end);
                debug_assert!(self.extension[i] == 0);
                let id: i64 = ((self.extension[i] as i64) << 32) + self.extension[i + 1] as i64;
                debug_assert!(id > 0);
                i += 3;
                debug_assert!(self.extension[i] != 0);
                debug_assert!(i != end);
                while i != end {
                    lit = self.extension[i];
                    i += 1;
                    if lit == 0 {
                        break;
                    }
                    clause.push(lit);
                }
                if !it.witness(&clause, &witness, id) {
                    return false;
                }
                clause.clear();
                witness.clear();
                if i == end {
                    break;
                }
            }
        }
        true
    }

    /*----------------------------------------------------------------------*/

    pub fn conclude_sat(&mut self) {
        if self.internal().proof.is_none() || self.concluded {
            return;
        }
        self.concluded = true;
        if !self.extended {
            self.extend();
        }
        let mut model: Vec<i32> = Vec::new();
        for idx in 1..=self.max_var {
            if self.ervars[idx as usize] {
                continue;
            }
            let lit = self.ival(idx);
            model.push(lit);
        }
        self.internal().proof.as_mut().unwrap().conclude_sat(&model);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct Collect(Vec<(Vec<i32>, Vec<i32>, i64)>);
    impl WitnessIterator for Collect {
        fn witness(&mut self, clause: &[i32], witness: &[i32], id: i64) -> bool {
            self.0.push((clause.to_vec(), witness.to_vec(), id));
            true
        }
    }

    #[test]
    fn extension_stack_extend_and_traverse() {
        let mut internal = Internal::new();
        let ip: *mut Internal = &mut *internal;
        let mut external = External::new(ip);
        external.init(4, false);
        assert_eq!(internal.max_var, 4);
        assert_eq!(external.e2i, vec![0, 1, 2, 3, 4]);
        assert_eq!(internal.i2e, vec![0, 1, 2, 3, 4]);
        external.push_external_clause_and_witness_on_extension_stack(&[-1, 2], &[-1], 7);
        external.push_external_clause_and_witness_on_extension_stack(&[3, 4], &[3], 8);
        assert_eq!(external.extension, vec![0, -1, 0, 0, 7, 0, -1, 2, 0, 3, 0, 0, 8, 0, 3, 4]);
        // Same layout via the internal clause pushing functions.
        external.push_zero_on_extension_stack();
        external.push_witness_literal_on_extension_stack(2);
        external.push_zero_on_extension_stack();
        external.push_id_on_extension_stack((5i64 << 32) + 9);
        external.push_zero_on_extension_stack();
        external.push_clause_literal_on_extension_stack(2);
        external.push_clause_literal_on_extension_stack(-4);
        assert_eq!(&external.extension[16..], &[0, 2, 0, 0, 9, 0, 2, -4]);
        assert!(external.marked(&external.witness, 2));
        assert!(external.marked(&external.witness, 3));
        assert!(external.marked(&external.witness, -1));
        assert!(!external.marked(&external.witness, 1));

        // All internal variables unassigned, thus all false.
        external.extend();
        assert!(external.extended);
        // (2 -4) satisfied by -4, (3 4) flips 3, (-1 2) satisfied by -1.
        assert_eq!(external.vals, vec![false, false, false, true, false]);
        assert_eq!(internal.stats.extended, 1);

        let mut fwd = Collect(Vec::new());
        assert!(external.traverse_witnesses_forward(&mut fwd));
        assert_eq!(
            fwd.0,
            vec![
                (vec![-1, 2], vec![-1], 7),
                (vec![3, 4], vec![3], 8),
                (vec![2, -4], vec![2], 9),
            ]
        );
        let mut bwd = Collect(Vec::new());
        assert!(external.traverse_witnesses_backward(&mut bwd));
        let mut rev = fwd.0.clone();
        rev.reverse();
        assert_eq!(bwd.0, rev);
        drop(internal);
        drop(external);
    }
}

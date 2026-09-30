//! Port of `deduplicate.cpp`.
//!
//! Equivalent literal substitution in 'decompose' and shrinking in
//! 'subsume' or 'vivify' might produce duplicated binary clauses.  They can
//! not be found in 'subsume' nor 'vivify' since we explicitly do not
//! consider binary clauses as candidates to be shrunken or subsumed.  They
//! are detected here by a simple scan of watch lists and then marked as
//! garbage.  This is actually also quite fast.
//!
//! Further it might also be possible that two binary clauses can be
//! resolved to produce a unit (we call it 'hyper unary resolution').  For
//! example resolving the binary clauses '1 -2' and '1 2' produces the unit
//! '1'.  This could be found by probing in 'probe' unless '-1' also occurs
//! in a binary clause (add the clause '-1 2' to those two clauses) in which
//! case '1' as well as '2' both occur positively as well as negatively and
//! none of them nor their negation is considered as probe

#[allow(unused_imports)]
use crate::prelude::*;

use crate::util::erase_vector;

impl Internal {
    pub fn mark_duplicated_binary_clauses_as_garbage(&mut self) {
        if self.opts.deduplicate == 0 {
            return;
        }
        if self.unsat {
            return;
        }
        if self.terminated_asynchronously(1) {
            return;
        }

        start_simplifier!(self, deduplicate, DEDUP);
        self.stats.deduplications += 1;

        debug_assert!(self.level == 0);
        debug_assert!(self.watching());

        let mut stack: Vec<i32> = Vec::new(); // To save marked literals and unmark them later.

        let mut subsumed: i64 = 0;
        let mut units: i64 = 0;

        for idx in self.vars() {
            if self.unsat {
                break;
            }
            if !self.active(idx) {
                continue;
            }
            let mut unit = 0;

            let mut sign = -1;
            while unit == 0 && sign <= 1 {
                let lit = sign * idx; // Consider all literals.

                debug_assert!(stack.is_empty());
                let wi = self.vlit(lit) as usize;

                // We are removing references to garbage clause. Thus no
                // 'auto'.

                let end = self.wtab[wi].len();
                let mut j = 0usize;
                let mut i = 0usize;

                while unit == 0 && i != end {
                    let w = self.wtab[wi][i];
                    self.wtab[wi][j] = w;
                    j += 1;
                    if !w.binary() {
                        i += 1;
                        continue;
                    }
                    let other = w.blit;
                    let tmp = self.marked(other);
                    let mut c = w.clause;

                    if tmp > 0 {
                        // Found duplicated binary clause.

                        if c.garbage() {
                            j -= 1;
                            i += 1;
                            continue;
                        }
                        log!(self, c, "found duplicated");

                        // The previous identical clause 'd' might be
                        // redundant and if the second clause 'c' is not (so
                        // irredundant), then we have to keep 'c' instead of
                        // 'd', thus we search for it and replace it.

                        if !c.redundant() {
                            let mut k = 0usize;
                            loop {
                                debug_assert!(k != i);
                                let wk = self.wtab[wi][k];
                                if !wk.binary() {
                                    k += 1;
                                    continue;
                                }
                                if wk.blit != other {
                                    k += 1;
                                    continue;
                                }
                                let d = wk.clause;
                                if d.garbage() {
                                    k += 1;
                                    continue;
                                }
                                c = d;
                                break;
                            }
                            self.wtab[wi][k] = w;
                        }

                        log!(self, c, "mark garbage duplicated");
                        self.stats.subsumed += 1;
                        self.stats.deduplicated += 1;
                        subsumed += 1;
                        self.mark_garbage(c);
                        j -= 1;
                    } else if tmp < 0 {
                        // Hyper unary resolution.

                        log!(
                            self,
                            "found {} {} and {} {} which produces unit {}",
                            lit,
                            -other,
                            lit,
                            other,
                            lit
                        );
                        unit = lit;
                        if self.lrat {
                            // taken from fradical
                            debug_assert!(self.lrat_chain.is_empty());
                            self.lrat_chain.push(c.id());
                            // We've forgotten where the other binary clause
                            // is, so go find it again
                            let mut k = 0usize;
                            loop {
                                debug_assert!(k != i);
                                let wk = self.wtab[wi][k];
                                if !wk.binary() {
                                    k += 1;
                                    continue;
                                }
                                if wk.blit != -other {
                                    k += 1;
                                    continue;
                                }
                                self.lrat_chain.push(wk.clause.id());
                                break;
                            }
                        }
                        j = 0; // Flush 'ws'.
                        units += 1;
                    } else {
                        if c.garbage() {
                            j -= 1;
                            i += 1;
                            continue;
                        }
                        self.mark(other);
                        stack.push(other);
                    }
                    i += 1;
                }

                if j == 0 {
                    erase_vector(&mut self.wtab[wi]);
                } else if j != end {
                    self.wtab[wi].truncate(j); // Shrink watchers.
                }

                for &other in stack.iter() {
                    self.unmark(other);
                }

                stack.clear();

                sign += 2;
            }

            // Propagation potentially messes up the watches and thus we can
            // not propagate the unit immediately after finding it.  Instead
            // we break out of both loops and assign and propagate the unit
            // here.

            if unit != 0 {
                self.stats.failed += 1;
                self.stats.hyperunary += 1;
                self.assign_unit(unit);
                // lrat_chain.clear ();   done in search_assign

                if !self.propagate() {
                    log!(self, "empty clause after propagating unit");
                    self.learn_empty_clause();
                }
            }
        }
        stop_simplifier!(self, deduplicate, DEDUP);

        let quiet = self.opts.reportall == 0 && (subsumed + units) == 0;
        self.report(b'2', quiet as i32);
    }

    /*------------------------------------------------------------------------*/

    // We discovered in a bug report
    // (https://github.com/arminbiere/cadical/issues/147) that some problems
    // contains clauses several times. This was handled properly before (as a
    // side effect of vivifyflush), but the proper ticks scheduling limitation
    // makes this impossible since 2.2. Therefore, we have implemented this
    // detection as a proper inprocessing technique that is off by default
    // and run only once during preprocess quickly. As we do not want to
    // assume anything on the input clauses, we also remove the true/false
    // literals.
    //
    // In essence, the code is simply taken from vivifyflush (without all the
    // rest of the code around obviously).
    //
    pub fn deduplicate_all_clauses(&mut self) {
        debug_assert!(self.level == 0);
        self.clear_watches();

        self.mark_satisfied_clauses_as_garbage();
        self.garbage_collection();

        // in order to do the inprocessing inplace, we remove the deleted
        // clauses, put the binary deleted clauses first. Then we work on the
        // non-deleted clauses by sorting them and sorting the clause w.r.t
        // each other.
        //
        let start = 0usize;
        let mid = partition(&mut self.clauses, |c: &CRef| !c.garbage());
        for i in start..mid {
            let c = self.clauses[i];
            crate::sort::std_sort_default_arith(c.lits_mut());
        }
        debug_assert!(self.clauses[start..mid].iter().all(|c| !c.garbage()));
        debug_assert!(self.clauses[mid..].iter().all(|c| c.garbage()));

        self.clauses[start..mid].sort_by(|a, b| {
            if deduplicate_flush_smaller(*a, *b) {
                std::cmp::Ordering::Less
            } else if deduplicate_flush_smaller(*b, *a) {
                std::cmp::Ordering::Greater
            } else {
                std::cmp::Ordering::Equal
            }
        });
        let mut j = start;
        let mut i = j;

        let mut prev = CRef::NULL;
        let mut subsumed: i64 = 0;
        while i != mid {
            let c = self.clauses[i];
            self.clauses[j] = c;
            j += 1;
            i += 1;
            if prev.is_null() || c.size() < prev.size() {
                prev = c;
                continue;
            }
            let eop = prev.size() as usize;
            let mut k = 0usize;
            while k != eop {
                if prev.lit(k) != c.lit(k) {
                    break;
                }
                k += 1;
            }
            if k == eop {
                log!(self, c, "found subsumed");
                log!(self, prev, "subsuming");
                debug_assert!(!c.garbage());
                debug_assert!(!prev.garbage());
                debug_assert!(c.redundant() || !prev.redundant());
                self.mark_garbage(c);
                self.delete_clause(c);
                subsumed += 1;
                j -= 1;
            } else {
                prev = c;
            }
        }

        while i != self.clauses.len() {
            let c = self.clauses[i];
            debug_assert!(c.garbage());
            self.delete_clause(c);
            i += 1;
        }

        self.clauses.truncate(j);

        self.stats.deduplicatedinitrounds += 1;
        phase!(
            self,
            "deduplicate-all",
            self.stats.deduplicatedinitrounds,
            "flushed {} subsumed clauses out of {}",
            subsumed,
            self.clauses.len() - start
        );
        self.stats.subsumed += subsumed;
        self.stats.deduplicatedinit += subsumed;
        self.check_clause_stats();
        self.connect_watches(false);
        let quiet = self.opts.reportall == 0 && subsumed == 0;
        self.report(b'd', quiet as i32);
    }
}

/// `std::partition` as implemented in libc++ (bidirectional version, used
/// for vector iterators), so that the order of both parts (the garbage part
/// is deleted in this order) is identical to C++.  Returns the start of the
/// second part.
fn partition<T>(v: &mut [T], mut pred: impl FnMut(&T) -> bool) -> usize {
    let mut first = 0usize;
    let mut last = v.len();
    loop {
        loop {
            if first == last {
                return first;
            }
            if !pred(&v[first]) {
                break;
            }
            first += 1;
        }
        loop {
            last -= 1;
            if first == last {
                return first;
            }
            if pred(&v[last]) {
                break;
            }
        }
        v.swap(first, last);
        first += 1;
    }
}

/// See the comment for vivifyflush (`deduplicate_flush_smaller`).
fn deduplicate_flush_smaller(a: CRef, b: CRef) -> bool {
    let eoa = a.size() as usize;
    let eob = b.size() as usize;
    let mut i = 0usize;
    let mut j = 0usize;
    while i != eoa && j != eob {
        let x = a.lit(i);
        let y = b.lit(j);
        if x != y {
            return x < y;
        }
        i += 1;
        j += 1;
    }
    (j == eob && i != eoa)
        || (j == eob && i == eoa && !a.redundant() && b.redundant())
        || (j == eob && i == eoa && (a.redundant() == b.redundant()) && b.id() < a.id())
}

#[cfg(test)]
mod tests {
    use super::partition;

    /// Prints the result of 'partition' on pseudo random inputs, to be
    /// compared with the output of libc++ 'std::partition' (see the report
    /// of package P4, 'scripts' are not part of the crate).
    #[test]
    fn partition_matches_libcxx_dump() {
        let mut state: u64 = 12345;
        let mut next = || {
            state = state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            (state >> 33) as u32
        };
        let mut out = String::new();
        for _ in 0..300 {
            let n = (next() % 40) as usize;
            let mut v: Vec<u32> = (0..n).map(|_| next() % 10).collect();
            let mid = partition(&mut v, |x| x % 3 != 0);
            out += &format!("{} {:?}\n", mid, v);
        }
        if let Ok(path) = std::env::var("P4_PARTITION_DUMP") {
            std::fs::write(path, out).unwrap();
        }
    }
}

//! Port of `gates.cpp`.

#[allow(unused_imports)]
use crate::prelude::*;

/*------------------------------------------------------------------------*/

// As in our original SATeLite published at SAT'05 we are trying to find
// gates in order to restrict the number of resolutions that need to be
// tried.  If there is such a gate, we only need to consider resolvents
// among gate and one non-gate clauses.  Resolvents between definitions will
// be tautological anyhow and resolvents among non-gates can actually be
// shown to be redundant too.

impl Internal {
    /*--------------------------------------------------------------------*/

    // The next function returns a non-zero if the clause 'c', which is
    // assumed to contain the literal 'first', after removing falsified
    // literals is a binary clause.  Then the actual second literal is
    // returned.

    pub fn second_literal_in_binary_clause(&mut self, eliminator: &mut Eliminator, c: CRef, first: i32) -> i32 {
        debug_assert!(!c.garbage());
        let mut second = 0;
        for &lit in c.lits() {
            if lit == first {
                continue;
            }
            let tmp = self.val(lit);
            if tmp < 0 {
                continue;
            }
            if tmp > 0 {
                self.mark_garbage(c);
                self.elim_update_removed_clause(eliminator, c, 0);
                return 0;
            }
            if second != 0 {
                second = i32::MIN;
                break;
            }
            second = lit;
        }
        if second == 0 {
            return 0;
        }
        if second == i32::MIN {
            return 0;
        }
        debug_assert!(self.active(second));
        #[cfg(feature = "logging")]
        {
            if c.size() == 2 {
                log!(self, c, "found binary");
            } else {
                log!(self, c, "found actual binary {} {}", first, second);
            }
        }
        second
    }

    /*--------------------------------------------------------------------*/

    // need a copy from above that does not care about garbage

    pub fn second_literal_in_binary_clause_lrat(&mut self, c: CRef, first: i32) -> i32 {
        if c.garbage() {
            return 0;
        }
        let mut second = 0;
        for &lit in c.lits() {
            if lit == first {
                continue;
            }
            let tmp = self.val(lit);
            if tmp < 0 {
                continue;
            }
            if tmp > 0 {
                return 0;
            }
            if tmp == 0 {
                if second != 0 {
                    second = i32::MIN;
                    break;
                }
                second = lit;
            }
        }
        if second == 0 {
            return 0;
        }
        if second == i32::MIN {
            return 0;
        }
        second
    }

    // I needed to find the second clause for hyper unary resolution to
    // build LRAT this is not efficient but I could not find a better way
    // then just finding the corresponding clause in all possible clauses
    //
    pub fn find_binary_clause(&mut self, first: i32, second: i32) -> CRef {
        let mut best = first;
        let mut other = second;
        if self.occs(first).len() > self.occs(second).len() {
            best = second;
            other = first;
        }
        let n = self.occs(best).len();
        for k in 0..n {
            let c = self.occs(best)[k];
            if self.second_literal_in_binary_clause_lrat(c, best) == other {
                return c;
            }
        }
        CRef::NULL
    }

    /// Push the unit ids of the falsified literals of `c` (except `a` and
    /// `b`) on the LRAT chain (shared code of the hyper unary resolution
    /// cases below, written out twice in C++).
    fn gates_push_unit_ids(&mut self, c: CRef, a: i32, b: i32) {
        for &lit in c.lits() {
            if lit == a || lit == b {
                continue;
            }
            debug_assert!(self.val(lit) < 0);
            if self.flags(lit).seen {
                continue;
            }
            self.analyzed.push(lit);
            self.flags_mut(lit).seen = true;
            let id = self.unit_id(-lit);
            self.lrat_chain.push(id);
            // LOG ("gates added id %" PRId64, id);
        }
    }

    /*--------------------------------------------------------------------*/

    // Mark all other literals in binary clauses with 'first'.  During this
    // marking we might also detect hyper unary resolvents producing a unit.
    // If such a unit is found we propagate it and return immediately.

    pub fn mark_binary_literals(&mut self, eliminator: &mut Eliminator, first: i32) {
        if self.unsat {
            return;
        }
        if self.val(first) != 0 {
            return;
        }
        if !eliminator.gates.is_empty() {
            return;
        }

        debug_assert!(self.marked(first) == 0);
        debug_assert!(eliminator.marked.is_empty());

        let n = self.occs(first).len();
        for k in 0..n {
            let c = self.occs(first)[k];
            if c.garbage() {
                continue;
            }
            let second = self.second_literal_in_binary_clause(eliminator, c, first);
            if second == 0 {
                continue;
            }
            let tmp = self.marked(second);
            if tmp < 0 {
                // had a bug where units could occur multiple times here
                // solved with flags
                log!(self, "found binary resolved unit {}", first);
                if self.lrat {
                    let d = self.find_binary_clause(first, -second);
                    debug_assert!(!d.is_null());
                    self.gates_push_unit_ids(d, first, -second);
                    self.gates_push_unit_ids(c, first, second);
                    self.lrat_chain.push(c.id());
                    self.lrat_chain.push(d.id());
                    // LOG ("gates added id %" PRId64, c->id);
                    // LOG ("gates added id %" PRId64, d->id);
                    self.clear_analyzed_literals();
                }
                self.assign_unit(first);
                self.elim_propagate(eliminator, first);
                return;
            }
            if tmp > 0 {
                log!(self, c, "duplicated actual binary clause");
                self.elim_update_removed_clause(eliminator, c, 0);
                self.mark_garbage(c);
                continue;
            }
            eliminator.marked.push(second);
            self.mark(second);
            log!(self, "marked second literal {} in binary clause {} {}", second, first, second);
        }
    }

    // Unmark all literals saved on the 'marked' stack.

    pub fn unmark_binary_literals(&mut self, eliminator: &mut Eliminator) {
        log!(self, "unmarking {} literals", eliminator.marked.len());
        for &lit in eliminator.marked.iter() {
            self.unmark(lit);
        }
        eliminator.marked.clear();
    }

    /*--------------------------------------------------------------------*/

    // Find equivalence for 'pivot'.  Requires that all other literals in
    // binary clauses with 'pivot' are marked (through
    // 'mark_binary_literals');

    pub fn find_equivalence(&mut self, eliminator: &mut Eliminator, pivot: i32) {
        if self.opts.elimequivs == 0 {
            return;
        }

        debug_assert!(self.opts.elimsubst != 0);

        if self.unsat {
            return;
        }
        if self.val(pivot) != 0 {
            return;
        }
        if !eliminator.gates.is_empty() {
            return;
        }

        self.mark_binary_literals(eliminator, pivot);
        'done: {
            if self.unsat || self.val(pivot) != 0 {
                break 'done;
            }

            let n = self.occs(-pivot).len();
            for k in 0..n {
                let c = self.occs(-pivot)[k];

                if c.garbage() {
                    continue;
                }

                let second = self.second_literal_in_binary_clause(eliminator, c, -pivot);
                if second == 0 {
                    continue;
                }
                let tmp = self.marked(second);
                if tmp > 0 {
                    log!(self, "found binary resolved unit {}", second);
                    // did not find a bug where units could occur multiple
                    // times here still solved potential issues with flags
                    if self.lrat {
                        let d = self.find_binary_clause(pivot, second);
                        debug_assert!(!d.is_null());
                        self.gates_push_unit_ids(d, pivot, second);
                        self.gates_push_unit_ids(c, -pivot, second);
                        self.lrat_chain.push(c.id());
                        self.lrat_chain.push(d.id());
                        self.clear_analyzed_literals();
                        // LOG ("gates added id %" PRId64, c->id);
                        // LOG ("gates added id %" PRId64, d->id);
                    }
                    self.assign_unit(second);
                    self.elim_propagate(eliminator, second);
                    if self.val(pivot) != 0 {
                        break;
                    }
                    if self.unsat {
                        break;
                    }
                }
                if tmp >= 0 {
                    continue;
                }

                log!(self, "found equivalence {} = {}", pivot, -second);
                self.stats.elimequivs += 1;
                self.stats.elimgates += 1;

                log!(self, c, "first gate clause");
                debug_assert!(!c.gate());
                c.set_gate(true);
                eliminator.gates.push(c);

                let mut d = CRef::NULL;
                let m = self.occs(pivot).len();
                for l in 0..m {
                    let e = self.occs(pivot)[l];
                    if e.garbage() {
                        continue;
                    }
                    let other = self.second_literal_in_binary_clause(eliminator, e, pivot);
                    if other == -second {
                        d = e;
                        break;
                    }
                }
                debug_assert!(!d.is_null());

                log!(self, d, "second gate clause");
                debug_assert!(!d.gate());
                d.set_gate(true);
                eliminator.gates.push(d);
                eliminator.gatetype = GateType::EQUI;

                break;
            }
        }
        // DONE:
        self.unmark_binary_literals(eliminator);
    }

    /*--------------------------------------------------------------------*/

    // Find and gates for 'pivot' with a long clause, in which the pivot
    // occurs positively.  Requires that all other literals in binary
    // clauses with 'pivot' are marked (through 'mark_binary_literals');

    pub fn find_and_gate(&mut self, eliminator: &mut Eliminator, pivot: i32) {
        if self.opts.elimands == 0 {
            return;
        }

        debug_assert!(self.opts.elimsubst != 0);

        if self.unsat {
            return;
        }
        if self.val(pivot) != 0 {
            return;
        }
        if !eliminator.gates.is_empty() {
            return;
        }

        self.mark_binary_literals(eliminator, pivot);
        'done: {
            if self.unsat || self.val(pivot) != 0 {
                break 'done;
            }

            let n = self.occs(-pivot).len();
            for k in 0..n {
                let c = self.occs(-pivot)[k];

                if c.garbage() {
                    continue;
                }
                if c.size() < 3 {
                    continue;
                }

                let mut all_literals_marked = true;
                let mut arity: u32 = 0;
                let mut satisfied = 0;

                for &lit in c.lits() {
                    if lit == -pivot {
                        continue;
                    }
                    debug_assert!(lit != pivot);
                    let mut tmp = self.val(lit);
                    if tmp < 0 {
                        continue;
                    }
                    if tmp > 0 {
                        satisfied = lit;
                        break;
                    }
                    tmp = self.marked(lit);
                    if tmp < 0 {
                        arity += 1;
                        continue;
                    }
                    all_literals_marked = false;
                    break;
                }

                if !all_literals_marked {
                    continue;
                }

                if satisfied != 0 {
                    log!(self, c, "satisfied by {} candidate base clause", satisfied);
                    self.mark_garbage(c);
                    continue;
                }

                #[cfg(feature = "logging")]
                if self.opts.log != 0 {
                    use crate::logging::Logger;
                    use crate::message::{c_stdout, fflush, fputc, fputs};
                    use crate::terminal::tout;
                    Logger::print_log_prefix(self);
                    tout().magenta(false);
                    cprintf!("found arity {} AND gate {} = ", arity, -pivot);
                    let mut first = true;
                    for &lit in c.lits() {
                        if lit == -pivot {
                            continue;
                        }
                        debug_assert!(lit != pivot);
                        if !first {
                            fputs(" & ", c_stdout());
                        }
                        cprintf!("{}", -lit);
                        first = false;
                    }
                    fputc(b'\n' as i32, c_stdout());
                    tout().normal();
                    fflush(c_stdout());
                }
                self.stats.elimands += 1;
                self.stats.elimgates += 1;
                eliminator.gatetype = GateType::AND;

                let _ = arity;
                debug_assert!(!c.gate());
                c.set_gate(true);
                eliminator.gates.push(c);
                for &lit in c.lits() {
                    if lit == -pivot {
                        continue;
                    }
                    debug_assert!(lit != pivot);
                    let tmp = self.val(lit);
                    if tmp < 0 {
                        continue;
                    }
                    debug_assert!(tmp == 0);
                    debug_assert!(self.marked(lit) < 0);
                    let idx = self.vidx(lit) as usize;
                    self.marks[idx] *= 2;
                }

                let mut count: u32 = 0;
                let m = self.occs(pivot).len();
                for l in 0..m {
                    let d = self.occs(pivot)[l];
                    if d.garbage() {
                        continue;
                    }
                    let other = self.second_literal_in_binary_clause(eliminator, d, pivot);
                    if other == 0 {
                        continue;
                    }
                    let tmp = self.marked(other) as i32;
                    if tmp != 2 {
                        continue;
                    }
                    log!(self, d, "AND gate binary side clause");
                    debug_assert!(!d.gate());
                    d.set_gate(true);
                    eliminator.gates.push(d);
                    count += 1;
                }
                debug_assert!(count >= arity);
                let _ = count;

                break;
            }
        }
        // DONE:
        self.unmark_binary_literals(eliminator);
    }

    /*--------------------------------------------------------------------*/

    // Find and extract ternary clauses.

    pub fn get_ternary_clause(&mut self, d: CRef, a: &mut i32, b: &mut i32, c: &mut i32) -> bool {
        if d.garbage() {
            return false;
        }
        if d.size() < 3 {
            return false;
        }
        let mut found = 0;
        *a = 0;
        *b = 0;
        *c = 0;
        for &lit in d.lits() {
            if self.val(lit) != 0 {
                continue;
            }
            found += 1;
            if found == 1 {
                *a = lit;
            } else if found == 2 {
                *b = lit;
            } else if found == 3 {
                *c = lit;
            } else {
                return false;
            }
        }
        found == 3
    }

    // This function checks whether 'd' exists as ternary clause.

    pub fn match_ternary_clause(&mut self, d: CRef, a: i32, b: i32, c: i32) -> bool {
        if d.garbage() {
            return false;
        }
        let mut found = 0;
        for &lit in d.lits() {
            if self.val(lit) != 0 {
                continue;
            }
            if a != lit && b != lit && c != lit {
                return false;
            }
            found += 1;
        }
        found == 3
    }

    pub fn find_ternary_clause(&mut self, a: i32, b: i32, c: i32) -> CRef {
        let mut a = a;
        let mut b = b;
        let mut c = c;
        if self.occs(b).len() > self.occs(c).len() {
            std::mem::swap(&mut b, &mut c);
        }
        if self.occs(a).len() > self.occs(b).len() {
            std::mem::swap(&mut a, &mut b);
        }
        let n = self.occs(a).len();
        for k in 0..n {
            let d = self.occs(a)[k];
            if self.match_ternary_clause(d, a, b, c) {
                return d;
            }
        }
        CRef::NULL
    }

    /*--------------------------------------------------------------------*/

    // Find if-then-else gate.

    pub fn find_if_then_else(&mut self, eliminator: &mut Eliminator, pivot: i32) {
        if self.opts.elimites == 0 {
            return;
        }

        debug_assert!(self.opts.elimsubst != 0);

        if self.unsat {
            return;
        }
        if self.val(pivot) != 0 {
            return;
        }
        if !eliminator.gates.is_empty() {
            return;
        }

        let end = self.occs(pivot).len();
        for i in 0..end {
            let di = self.occs(pivot)[i];
            let (mut ai, mut bi, mut ci) = (0, 0, 0);
            if !self.get_ternary_clause(di, &mut ai, &mut bi, &mut ci) {
                continue;
            }
            if bi == pivot {
                std::mem::swap(&mut ai, &mut bi);
            }
            if ci == pivot {
                std::mem::swap(&mut ai, &mut ci);
            }
            debug_assert!(ai == pivot);
            for j in (i + 1)..end {
                let dj = self.occs(pivot)[j];
                let (mut aj, mut bj, mut cj) = (0, 0, 0);
                if !self.get_ternary_clause(dj, &mut aj, &mut bj, &mut cj) {
                    continue;
                }
                if bj == pivot {
                    std::mem::swap(&mut aj, &mut bj);
                }
                if cj == pivot {
                    std::mem::swap(&mut aj, &mut cj);
                }
                debug_assert!(aj == pivot);
                if bi.abs() == cj.abs() {
                    std::mem::swap(&mut bj, &mut cj);
                }
                if ci.abs() == cj.abs() {
                    continue;
                }
                if bi != -bj {
                    continue;
                }
                let d1 = self.find_ternary_clause(-pivot, bi, -ci);
                if d1.is_null() {
                    continue;
                }
                let d2 = self.find_ternary_clause(-pivot, bj, -cj);
                if d2.is_null() {
                    continue;
                }
                log!(self, di, "1st if-then-else");
                log!(self, dj, "2nd if-then-else");
                log!(self, d1, "3rd if-then-else");
                log!(self, d2, "4th if-then-else");
                log!(self, "found ITE gate {} == ({} ? {} : {})", pivot, -bi, -ci, -cj);
                debug_assert!(!di.gate());
                debug_assert!(!dj.gate());
                debug_assert!(!d1.gate());
                debug_assert!(!d2.gate());
                di.set_gate(true);
                dj.set_gate(true);
                d1.set_gate(true);
                d2.set_gate(true);
                eliminator.gates.push(di);
                eliminator.gates.push(dj);
                eliminator.gates.push(d1);
                eliminator.gates.push(d2);
                self.stats.elimgates += 1;
                self.stats.elimites += 1;
                eliminator.gatetype = GateType::ITE;
                return;
            }
        }
    }

    /*--------------------------------------------------------------------*/

    // Find and extract clause.

    pub fn get_clause(&mut self, c: CRef, l: &mut Vec<i32>) -> bool {
        if c.garbage() {
            return false;
        }
        l.clear();
        for &lit in c.lits() {
            if self.val(lit) < 0 {
                continue;
            }
            if self.val(lit) > 0 {
                l.clear();
                return false;
            }
            l.push(lit);
        }
        true
    }

    // Check whether 'c' contains only the literals in 'l'.

    pub fn is_clause(&mut self, c: CRef, lits: &[i32]) -> bool {
        if c.garbage() {
            return false;
        }
        let size = lits.len() as i32;
        if c.size() < size {
            return false;
        }
        let mut found = 0;
        for &lit in c.lits() {
            if self.val(lit) < 0 {
                continue;
            }
            if self.val(lit) > 0 {
                return false;
            }
            if !lits.contains(&lit) {
                return false;
            }
            found += 1;
            if found > size {
                return false;
            }
        }
        found == size
    }

    pub fn find_clause(&mut self, lits: &[i32]) -> CRef {
        let mut best = 0;
        let mut len: usize = 0;
        for &lit in lits {
            let l = self.occs(lit).len();
            if best != 0 && l >= len {
                continue;
            }
            len = l;
            best = lit;
        }
        let n = self.occs(best).len();
        for k in 0..n {
            let c = self.occs(best)[k];
            if self.is_clause(c, lits) {
                return c;
            }
        }
        CRef::NULL
    }

    pub fn find_xor_gate(&mut self, eliminator: &mut Eliminator, pivot: i32) {
        if self.opts.elimxors == 0 {
            return;
        }

        debug_assert!(self.opts.elimsubst != 0);

        if self.unsat {
            return;
        }
        if self.val(pivot) != 0 {
            return;
        }
        if !eliminator.gates.is_empty() {
            return;
        }

        let mut lits: Vec<i32> = Vec::new();

        let n = self.occs(pivot).len();
        for k in 0..n {
            let d = self.occs(pivot)[k];

            if !self.get_clause(d, &mut lits) {
                continue;
            }

            let size = lits.len() as i32; // clause size
            let arity = size - 1; // arity of XOR

            if size < 3 {
                continue;
            }
            if arity > self.opts.elimxorlim {
                continue;
            }

            debug_assert!(eliminator.gates.is_empty());

            let mut needed: u32 = (1u32 << arity) - 1; // additional clauses
            let mut signs: u32 = 0; // literals to negate

            loop {
                let prev = signs;
                loop {
                    signs = signs.wrapping_add(1);
                    if !parity(signs) {
                        break;
                    }
                }
                for j in 0..size as usize {
                    let bit = 1u32 << j;
                    let lit = lits[j];
                    if (prev & bit) != (signs & bit) {
                        lits[j] = -lit;
                    }
                }
                let e = self.find_clause(&lits);
                if e.is_null() {
                    break;
                }
                eliminator.gates.push(e);
                needed -= 1;
                if needed == 0 {
                    break;
                }
            }

            if needed != 0 {
                eliminator.gates.clear();
                continue;
            }

            eliminator.gates.push(d);
            debug_assert!(eliminator.gates.len() == (1usize << arity));

            #[cfg(feature = "logging")]
            if self.opts.log != 0 {
                use crate::logging::Logger;
                use crate::message::{c_stdout, fflush, fputc, fputs};
                use crate::terminal::tout;
                Logger::print_log_prefix(self);
                tout().magenta(false);
                cprintf!("found arity {} XOR gate {} = ", arity as u32, -pivot);
                let mut first = true;
                for &lit in d.lits() {
                    if lit == pivot {
                        continue;
                    }
                    debug_assert!(lit != -pivot);
                    if !first {
                        fputs(" ^ ", c_stdout());
                    }
                    cprintf!("{}", lit);
                    first = false;
                }
                fputc(b'\n' as i32, c_stdout());
                tout().normal();
                fflush(c_stdout());
            }
            self.stats.elimgates += 1;
            self.stats.elimxors += 1;
            let end = eliminator.gates.len();
            let mut j = 0;
            for i in 0..end {
                let e = eliminator.gates[i];
                if e.gate() {
                    continue;
                }
                e.set_gate(true);
                log!(self, e, "contributing");
                eliminator.gates[j] = e;
                j += 1;
            }
            eliminator.gates.truncate(j);
            eliminator.gatetype = GateType::XOR;
            break;
        }
    }

    /*--------------------------------------------------------------------*/

    // Find a gate for 'pivot'.  If such a gate is found, the gate clauses
    // are marked and pushed on the stack of gates.  Further hyper unary
    // resolution might detect units, which are propagated.  This might
    // assign the pivot or even produce the empty clause.

    pub fn find_gate_clauses(&mut self, eliminator: &mut Eliminator, pivot: i32) {
        if self.opts.elimsubst == 0 {
            return;
        }

        if self.unsat {
            return;
        }
        if self.val(pivot) != 0 {
            return;
        }

        debug_assert!(eliminator.gates.is_empty());

        self.find_equivalence(eliminator, pivot);
        self.find_and_gate(eliminator, pivot);
        self.find_and_gate(eliminator, -pivot);
        self.find_if_then_else(eliminator, pivot);
        self.find_xor_gate(eliminator, pivot);
        self.find_definition(eliminator, pivot);
    }

    pub fn unmark_gate_clauses(&mut self, eliminator: &mut Eliminator) {
        log!(self, "unmarking {} gate clauses", eliminator.gates.len());
        for &c in eliminator.gates.iter() {
            debug_assert!(c.gate());
            c.set_gate(false);
        }
        eliminator.gates.clear();
        eliminator.definition_unit = 0;
    }
}

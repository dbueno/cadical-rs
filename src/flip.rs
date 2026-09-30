//! Port of `flip.cpp`.

#[allow(unused_imports)]
use crate::prelude::*;

impl Internal {
    pub fn flip(&mut self, lit: i32) -> bool {
        let mut lit = lit;

        // Do not try to flip inactive literals except for unused variables.

        if !self.active(lit) && !self.flags(lit).unused() {
            return false;
        }

        /*
        if (flags (lit).unused ()) {
          assert (lit <= max_var);
          mark_active (lit);
          set_val (lit, 1);
          return true;
        }
        */

        // TODO: Unused case is not handled yet.
        // if (flags (lit).unused ()) return false;

        // Need to reestablish proper watching invariants as if there are no
        // blocking literals as flipping in principle does not work with
        // them.

        if self.propergated < self.trail.len() {
            self.propergate();
        }

        log!(self, "trying to flip {}", lit);

        let idx = self.vidx(lit);
        let original_value = self.val(idx);
        debug_assert!(original_value != 0);
        lit = if original_value < 0 { -idx } else { idx };
        debug_assert!(self.val(lit) > 0);

        // Here we go over all the clauses in which 'lit' is watched by
        // 'lit' and check whether assigning 'lit' to false would break
        // watching invariants or even make the clause false.  We also try
        // to find replacement watches in case this fixes the watching
        // invariant.  This code is very similar to propagation of a literal
        // in 'Internal::propagate'.

        let mut res = true;

        let widx = self.vlit(lit) as usize;
        let eow = self.wtab[widx].len();

        // We first go over binary watches/clauses first as this is cheaper
        // and has higher chance of failure and we can not use blocking
        // literals.

        for i in 0..eow {
            let w = self.wtab[widx][i];
            if !w.binary() {
                continue;
            }
            let b = self.val(w.blit);
            if b > 0 {
                continue;
            }
            debug_assert!(b < 0);
            res = false;
            break;
        }

        if res {
            let mut i = 0;
            let mut j = 0;

            while i != eow {
                let w = self.wtab[widx][i];
                self.wtab[widx][j] = w;
                i += 1;
                j += 1;

                if w.binary() {
                    continue;
                }

                let c = w.clause;
                if c.garbage() {
                    j -= 1;
                    continue;
                }

                let other = c.lit(0) ^ c.lit(1) ^ lit;
                let u = self.val(other);
                if u > 0 {
                    continue;
                }

                let size = c.size() as usize;
                let middle = c.pos() as usize;
                let end = size;
                let mut k = middle;

                let mut r = 0;
                let mut v: i8 = -1;
                while k != end {
                    r = c.lit(k);
                    v = self.val(r);
                    if v >= 0 {
                        break;
                    }
                    k += 1;
                }
                if v < 0 {
                    k = 2;
                    debug_assert!(c.pos() <= size as i32);
                    while k != middle {
                        r = c.lit(k);
                        v = self.val(r);
                        if v >= 0 {
                            break;
                        }
                        k += 1;
                    }
                }

                if v < 0 {
                    res = false;
                    break;
                }

                debug_assert!(v > 0);
                debug_assert!(2 <= k && k <= size);
                c.set_pos(k as i32);
                c.set_lit(0, other);
                c.set_lit(1, r);
                c.set_lit(k, lit);
                self.watch_literal(r, lit, c);
                j -= 1;
            }

            if j != i {
                while i != eow {
                    let w = self.wtab[widx][i];
                    self.wtab[widx][j] = w;
                    j += 1;
                    i += 1;
                }

                self.wtab[widx].truncate(j);
            }
        }
        #[cfg(feature = "logging")]
        {
            if res {
                log!(self, "literal {} can be flipped", lit);
            } else {
                log!(self, "literal {} can not be flipped", lit);
            }
        }

        if res {
            let idx = self.vidx(lit);
            let original_value = self.val(idx);
            debug_assert!(original_value != 0);
            lit = if original_value < 0 { -idx } else { idx };
            debug_assert!(self.val(lit) > 0);

            log!(self, "flipping value of {} = 1 to {} = -1", lit, lit);

            self.set_val(idx, -original_value);
            debug_assert!(self.val(-lit) > 0);
            debug_assert!(self.val(lit) < 0);

            let v = *self.var(idx);
            debug_assert!(self.trail[v.trail as usize] == lit);
            self.trail[v.trail as usize] = -lit;
            if self.opts.ilb != 0 {
                if self.changed_val == 0 {
                    self.changed_val = lit;
                } else {
                    debug_assert!(self.val(self.changed_val) != 0);
                    if v.level < self.var(self.changed_val).level {
                        self.changed_val = lit;
                    }
                }
            }
        } else {
            log!(self, "flipping value of {} failed", lit);
        }

        res
    }

    pub fn flippable(&mut self, lit: i32) -> bool {
        let mut lit = lit;

        // Can not check inactive literals except for unused variables.

        if !self.active(lit) && !self.flags(lit).unused() {
            return false;
        }

        /*
        if (flags (lit).unused ()) {
          assert (lit <= max_var);
          mark_active (lit);
          return true;
        }
        */
        // TODO: Unused case is not handled yet
        // if (flags (lit).unused ()) return false;

        // Need to reestablish proper watching invariants as if there are no
        // blocking literals as flipping in principle does not work with
        // them.

        if self.propergated < self.trail.len() {
            self.propergate();
        }

        log!(self, "checking whether {} is flippable", lit);

        let idx = self.vidx(lit);
        let original_value = self.val(idx);
        debug_assert!(original_value != 0);
        lit = if original_value < 0 { -idx } else { idx };
        debug_assert!(self.val(lit) > 0);

        // Here we go over all the clauses in which 'lit' is watched by
        // 'lit' and check whether assigning 'lit' to false would break
        // watching invariants or even make the clause false.  In contrast
        // to 'flip' we do not try to find replacement literals but do use
        // blocking literals'.  Therefore we also do not split the traversal
        // code into two parts.

        let mut res = true;

        let widx = self.vlit(lit) as usize;
        let eow = self.wtab[widx].len();
        for i in 0..eow {
            let w = self.wtab[widx][i];
            let b = self.val(w.blit);
            if b > 0 {
                continue;
            }
            debug_assert!(b < 0);

            if w.binary() {
                res = false;
                break;
            }

            let c = w.clause;
            if c.garbage() {
                continue;
            }

            let other = c.lit(0) ^ c.lit(1) ^ lit;
            let u = self.val(other);
            if u > 0 {
                self.wtab[widx][i].blit = other;
                continue;
            }

            let size = c.size() as usize;
            let middle = c.pos() as usize;
            let end = size;
            let mut k = middle;

            let mut r = 0;
            let mut v: i8 = -1;
            while k != end {
                r = c.lit(k);
                v = self.val(r);
                if v >= 0 {
                    break;
                }
                k += 1;
            }
            if v < 0 {
                k = 2;
                debug_assert!(c.pos() <= size as i32);
                while k != middle {
                    r = c.lit(k);
                    v = self.val(r);
                    if v >= 0 {
                        break;
                    }
                    k += 1;
                }
            }

            if v < 0 {
                res = false;
                break;
            }

            debug_assert!(v > 0);
            debug_assert!(2 <= k);
            debug_assert!(k <= size);
            c.set_pos(k as i32);
            self.wtab[widx][i].blit = r;
        }

        #[cfg(feature = "logging")]
        {
            if res {
                log!(self, "literal {} can be flipped", lit);
            } else {
                log!(self, "literal {} can not be flipped", lit);
            }
        }

        res
    }
}

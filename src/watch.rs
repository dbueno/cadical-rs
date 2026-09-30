//! Port of `watch.hpp` and `watch.cpp`.
//!
//! Watch lists for CDCL search.  The blocking literal is a must and thus
//! combining that with a 64 bit pointer gives a 16 byte structure anyhow,
//! which means the additional 4 bytes for the size come for free.

use crate::clause::CRef;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct Watch {
    pub clause: CRef,
    pub blit: i32,
    pub size: i32,
}

const _: () = assert!(std::mem::size_of::<Watch>() == 16);

impl Default for Watch {
    /// C++ leaves the default constructed watch uninitialized.
    fn default() -> Self {
        Watch { clause: CRef::NULL, blit: 0, size: 0 }
    }
}

impl Watch {
    /// `Watch (int b, Clause *c)`.
    #[inline(always)]
    pub fn new(blit: i32, c: CRef) -> Watch {
        Watch { clause: c, blit, size: c.size() }
    }
    /// `Watch (bool, int b, Clause *c)` for binary clauses.
    #[inline(always)]
    pub fn new_binary(blit: i32, c: CRef) -> Watch {
        debug_assert!(c.size() == 2);
        Watch { clause: c, blit, size: 2 }
    }
    #[inline(always)]
    pub fn binary(&self) -> bool {
        self.size == 2
    }
}

/// Watches of one literal.
pub type Watches = Vec<Watch>;

/// Remove the (unique) watch of `clause` from `ws`, keeping the order.
#[inline]
pub fn remove_watch(ws: &mut Watches, clause: CRef) {
    let end = ws.len();
    let mut i = 0;
    for j in 0..end {
        let w = ws[j];
        ws[i] = w;
        i += 1;
        if w.clause == clause {
            i -= 1;
        }
    }
    debug_assert!(i + 1 == end);
    ws.truncate(i);
}

/// Search for the clause and update the size marked in the watch lists.
#[inline]
pub fn update_watch_size(ws: &mut Watches, blit: i32, conflict: CRef) {
    let mut found = false;
    let size = conflict.size();
    for w in ws.iter_mut() {
        if w.clause == conflict {
            w.size = size;
            w.blit = blit;
            found = true;
        }
        debug_assert!(w.clause.garbage() || w.size == 2 || w.clause.size() != 2);
    }
    debug_assert!(found);
    let _ = found;
}

/*------------------------------------------------------------------------*/

// Port of 'watch.cpp'.

use crate::internal::Internal;
use crate::util::erase_vector;

impl Internal {
    pub fn init_watches(&mut self) {
        debug_assert!(self.wtab.is_empty());
        if self.wtab.len() < 2 * self.vsize {
            self.wtab.resize(2 * self.vsize, Watches::new());
        }
        log!(self, "initialized watcher tables");
    }

    pub fn clear_watches(&mut self) {
        for lit in self.lits() {
            self.watches_mut(lit).clear();
        }
    }

    pub fn reset_watches(&mut self) {
        debug_assert!(!self.wtab.is_empty());
        erase_vector(&mut self.wtab);
        log!(self, "reset watcher tables");
    }

    /// This can be quite costly since lots of memory is accessed in a
    /// rather random fashion, and thus we optionally profile it.
    ///
    /// `irredundant_only` defaults to `false` in C++.
    pub fn connect_watches(&mut self, irredundant_only: bool) {
        start!(self, connect);
        debug_assert!(self.watching());

        log!(
            self,
            "watching all {}clauses",
            if irredundant_only { "irredundant " } else { "" }
        );

        // First connect binary clauses.
        //
        for i in 0..self.clauses.len() {
            let c = self.clauses[i];
            if irredundant_only && c.redundant() {
                continue;
            }
            if c.garbage() || c.size() > 2 {
                continue;
            }
            self.watch_clause(c);
        }

        // Then connect non-binary clauses.
        //
        for i in 0..self.clauses.len() {
            let c = self.clauses[i];
            if irredundant_only && c.redundant() {
                continue;
            }
            if c.garbage() || c.size() == 2 {
                continue;
            }
            self.watch_clause(c);
            if self.level == 0 {
                let lit0 = c.lit(0);
                let lit1 = c.lit(1);
                let tmp0 = self.val(lit0);
                let tmp1 = self.val(lit1);
                if tmp0 > 0 {
                    continue;
                }
                if tmp1 > 0 {
                    continue;
                }
                if tmp0 < 0 {
                    let pos0 = self.var(lit0).trail as usize;
                    if pos0 < self.propagated {
                        self.propagated = pos0;
                        log!(self, "literal {} resets propagated to {}", lit0, pos0);
                    }
                }
                if tmp1 < 0 {
                    let pos1 = self.var(lit1).trail as usize;
                    if pos1 < self.propagated {
                        self.propagated = pos1;
                        log!(self, "literal {} resets propagated to {}", lit1, pos1);
                    }
                }
            }
        }

        stop!(self, connect);
    }

    /// This can be quite costly since lots of memory is accessed in a
    /// rather random fashion, and thus we optionally profile it.
    pub fn connect_binary_watches(&mut self) {
        start!(self, connect);
        debug_assert!(self.watching());

        log!(self, "watching binary clauses");

        // First connect binary clauses.
        //
        for i in 0..self.clauses.len() {
            let c = self.clauses[i];
            if c.garbage() || c.size() > 2 {
                continue;
            }
            self.watch_clause(c);
        }

        stop!(self, connect);
    }

    pub fn sort_watches(&mut self) {
        debug_assert!(self.watching());
        log!(self, "sorting watches");
        let mut saved: Watches = Vec::new();
        for lit in self.lits() {
            let ws = self.watches_mut(lit);
            let end = ws.len();
            let mut j = 0usize;
            debug_assert!(saved.is_empty());
            for i in 0..end {
                let w = ws[i];
                if w.binary() {
                    ws[j] = w;
                    j += 1;
                } else {
                    saved.push(w);
                }
            }
            ws[j..j + saved.len()].copy_from_slice(&saved);
            saved.clear();
        }
    }
}

//! Port of `queue.hpp` and `queue.cpp`: the variable move to front (VMTF)
//! decision queue.

use crate::internal::Internal;
use crate::random::Random;

/// Links for double linked decision queue (initialized explicitly in
/// `init_queue`).
#[derive(Clone, Copy, Debug, Default)]
pub struct Link {
    /// Variable indices.
    pub prev: i32,
    pub next: i32,
}

pub type Links = Vec<Link>;

/// Variable move to front (VMTF) decision queue ordered by 'bumped'.  See
/// our SAT'15 paper for an explanation on how this works.
#[derive(Clone, Copy, Debug, Default)]
pub struct Queue {
    /// Anchors (head/tail) for doubly linked list.
    pub first: i32,
    pub last: i32,
    /// All variables after this one are assigned.
    pub unassigned: i32,
    /// See 'Internal.update_queue_unassigned'.
    pub bumped: i64,
}

impl Queue {
    #[inline]
    pub fn dequeue(&mut self, links: &mut Links, idx: i32) {
        let l = links[idx as usize];
        if l.prev != 0 {
            links[l.prev as usize].next = l.next;
        } else {
            self.first = l.next;
        }
        if l.next != 0 {
            links[l.next as usize].prev = l.prev;
        } else {
            self.last = l.prev;
        }
    }

    #[inline]
    pub fn enqueue(&mut self, links: &mut Links, idx: i32) {
        links[idx as usize].prev = self.last;
        if self.last != 0 {
            links[self.last as usize].next = idx;
        } else {
            self.first = idx;
        }
        self.last = idx;
        links[idx as usize].next = 0;
    }

    #[inline]
    pub fn bury(&mut self, links: &mut Links, idx: i32) {
        links[idx as usize].next = self.first;
        if self.first != 0 {
            links[self.first as usize].prev = idx;
        } else {
            self.last = idx;
        }
        self.first = idx;
        links[idx as usize].prev = 0;
    }
}

/*------------------------------------------------------------------------*/

// Port of 'queue.cpp'.

impl Internal {
    /// Slightly different than 'bump_variable' since the variable is not
    /// enqueued at all.
    #[inline]
    pub fn init_enqueue(&mut self, idx: i32) {
        let uidx = idx as usize;
        if self.opts.reverse != 0 {
            self.links[uidx].prev = 0;
            if self.queue.first != 0 {
                let first = self.queue.first as usize;
                debug_assert!(self.links[first].prev == 0);
                self.links[first].prev = idx;
                self.btab[uidx] = self.btab[first] - 1;
            } else {
                debug_assert!(self.queue.last == 0);
                self.queue.last = idx;
                self.btab[uidx] = 0;
            }
            debug_assert!(self.btab[uidx] <= self.stats.bumped);
            self.links[uidx].next = self.queue.first;
            self.queue.first = idx;
            if self.queue.unassigned == 0 {
                let last = self.queue.last;
                self.update_queue_unassigned(last);
            }
        } else {
            self.links[uidx].next = 0;
            if self.queue.last != 0 {
                let last = self.queue.last as usize;
                debug_assert!(self.links[last].next == 0);
                self.links[last].next = idx;
            } else {
                debug_assert!(self.queue.first == 0);
                self.queue.first = idx;
            }
            self.stats.bumped += 1;
            self.btab[uidx] = self.stats.bumped;
            self.links[uidx].prev = self.queue.last;
            self.queue.last = idx;
            let last = self.queue.last;
            self.update_queue_unassigned(last);
        }
    }

    /// Initialize VMTF queue from current 'old_max_var + 1' to
    /// 'new_max_var'.  This incorporates an initial variable order.  We
    /// currently simply assume that variables with smaller index are more
    /// important.  This is the same as in MiniSAT (implicitly) and also
    /// matches the 'scores' initialization.
    pub fn init_queue(&mut self, old_max_var: i32, new_max_var: i32) {
        log!(self, "initializing VMTF queue from {} to {}", old_max_var + 1, new_max_var);
        debug_assert!(old_max_var < new_max_var);
        // New variables can be created that can invoke enlarge anytime (eg
        // via calls during ipasir-up call-backs), thus assuming (!level) is
        // not correct
        for idx in old_max_var..new_max_var {
            self.init_enqueue(idx + 1);
        }
    }

    /// Shuffle the VMTF queue.
    pub fn shuffle_queue(&mut self) {
        if self.opts.shuffle == 0 {
            return;
        }
        if self.opts.shufflequeue == 0 {
            return;
        }
        self.stats.shuffled += 1;
        log!(self, "shuffling queue");
        let mut shuffle: Vec<i32> = Vec::new();
        if self.opts.shufflerandom != 0 {
            let mut idx = self.max_var;
            while idx != 0 {
                shuffle.push(idx);
                idx -= 1;
            }
            let mut random = Random::new(self.opts.seed as u64); // global seed
            random += self.stats.shuffled as u64; // different every time
            let max_var = self.max_var;
            let mut i = 0;
            while i <= max_var - 2 {
                let j = random.pick_int(i, max_var - 1);
                shuffle.swap(i as usize, j as usize);
                i += 1;
            }
        } else {
            let mut idx = self.queue.last;
            while idx != 0 {
                shuffle.push(idx);
                idx = self.links[idx as usize].prev;
            }
        }
        self.queue.first = 0;
        self.queue.last = 0;
        for &idx in &shuffle {
            self.queue.enqueue(&mut self.links, idx);
        }
        let mut bumped = self.queue.bumped;
        let mut idx = self.queue.last;
        while idx != 0 {
            self.btab[idx as usize] = bumped;
            bumped -= 1;
            idx = self.links[idx as usize].prev;
        }
        self.queue.unassigned = self.queue.last;
    }
}

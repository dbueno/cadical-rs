//! Port of `heap.hpp`: a binary heap priority queue with updates for
//! unsigned integers (the maximum w.r.t. `less` is at the front).

use crate::util::{erase_vector, shrink_vector};

/// `UINT_MAX` marks 'not contained'.
pub const INVALID_HEAP_POSITION: u32 = u32::MAX;

/// The comparator of a heap (C++ template parameter `C` with
/// `bool operator() (unsigned, unsigned)`).
pub trait HeapLess {
    fn less(&self, a: u32, b: u32) -> bool;
}

/// `template <class C> class heap`.
#[derive(Clone, Debug)]
pub struct Heap<C: HeapLess> {
    /// Actual binary heap.
    array: Vec<u32>,
    /// Positions of elements in array.
    pos: Vec<u32>,
    /// Less-than for elements.
    pub less: C,
}

impl<C: HeapLess> Heap<C> {
    pub fn new(c: C) -> Self {
        Heap { array: Vec::new(), pos: Vec::new(), less: c }
    }

    // Map an element to its position entry in the 'pos' map.
    #[inline]
    fn index(&mut self, e: u32) -> &mut u32 {
        if e as usize >= self.pos.len() {
            self.pos.resize(1 + e as usize, INVALID_HEAP_POSITION);
        }
        let res = &mut self.pos[e as usize];
        debug_assert!(*res == INVALID_HEAP_POSITION || (*res as usize) < self.array.len());
        res
    }

    #[inline]
    fn has_parent(&mut self, e: u32) -> bool {
        *self.index(e) > 0
    }
    #[inline]
    fn has_left(&mut self, e: u32) -> bool {
        2 * (*self.index(e) as usize) + 1 < self.size()
    }
    #[inline]
    fn has_right(&mut self, e: u32) -> bool {
        2 * (*self.index(e) as usize) + 2 < self.size()
    }
    #[inline]
    fn parent(&mut self, e: u32) -> u32 {
        debug_assert!(self.has_parent(e));
        let i = *self.index(e);
        self.array[((i - 1) / 2) as usize]
    }
    #[inline]
    fn left(&mut self, e: u32) -> u32 {
        debug_assert!(self.has_left(e));
        let i = *self.index(e);
        self.array[(2 * i + 1) as usize]
    }
    #[inline]
    fn right(&mut self, e: u32) -> u32 {
        debug_assert!(self.has_right(e));
        let i = *self.index(e);
        self.array[(2 * i + 2) as usize]
    }

    // Exchange elements 'a' and 'b' in 'array' and fix their positions.
    #[inline]
    fn exchange(&mut self, a: u32, b: u32) {
        let i = *self.index(a);
        let j = *self.index(b);
        self.array.swap(i as usize, j as usize);
        self.pos[a as usize] = j;
        self.pos[b as usize] = i;
    }

    // Bubble up an element as far as necessary.
    #[inline]
    fn up(&mut self, e: u32) {
        loop {
            if !self.has_parent(e) {
                break;
            }
            let p = self.parent(e);
            if !self.less.less(p, e) {
                break;
            }
            self.exchange(p, e);
        }
    }

    // Bubble down an element as far as necessary.
    #[inline]
    fn down(&mut self, e: u32) {
        while self.has_left(e) {
            let mut c = self.left(e);
            if self.has_right(e) {
                let r = self.right(e);
                if self.less.less(c, r) {
                    c = r;
                }
            }
            if !self.less.less(e, c) {
                break;
            }
            self.exchange(e, c);
        }
    }

    // Very expensive checker for the main 'heap' invariant (disabled as in
    // the C++ code).
    #[inline]
    fn check(&self) {}

    /// Number of elements in the heap.
    #[inline]
    pub fn size(&self) -> usize {
        self.array.len()
    }
    /// Check if no more elements are in the heap.
    #[inline]
    pub fn empty(&self) -> bool {
        self.array.is_empty()
    }
    /// Check whether `e` is already in the heap.
    #[inline]
    pub fn contains(&self, e: u32) -> bool {
        if e as usize >= self.pos.len() {
            return false;
        }
        self.pos[e as usize] != INVALID_HEAP_POSITION
    }
    /// Add a new (not contained) element `e` to the heap.
    pub fn push_back(&mut self, e: u32) {
        debug_assert!(!self.contains(e));
        let i = self.array.len();
        debug_assert!(i < INVALID_HEAP_POSITION as usize);
        self.array.push(e);
        *self.index(e) = i as u32;
        self.up(e);
        self.down(e);
        self.check();
    }
    /// Returns the maximum element in the heap.
    #[inline]
    pub fn front(&self) -> u32 {
        debug_assert!(!self.empty());
        self.array[0]
    }
    /// Removes the maximum element in the heap.
    pub fn pop_front(&mut self) -> u32 {
        debug_assert!(!self.empty());
        let res = self.array[0];
        let last = *self.array.last().unwrap();
        if self.size() > 1 {
            self.exchange(res, last);
        }
        *self.index(res) = INVALID_HEAP_POSITION;
        self.array.pop();
        if self.size() > 1 {
            self.down(last);
        }
        self.check();
        res
    }
    /// Notify the heap, that evaluation of `less` has changed for `e`.
    pub fn update(&mut self, e: u32) {
        debug_assert!(self.contains(e));
        self.up(e);
        self.down(e);
        self.check();
    }
    pub fn clear(&mut self) {
        self.array.clear();
        self.pos.clear();
    }
    pub fn erase(&mut self) {
        erase_vector(&mut self.array);
        erase_vector(&mut self.pos);
    }
    pub fn shrink(&mut self) {
        shrink_vector(&mut self.array);
        shrink_vector(&mut self.pos);
    }
    /// Iteration over the heap array (`begin ()` / `end ()`).
    #[inline]
    pub fn iter(&self) -> std::slice::Iter<'_, u32> {
        self.array.iter()
    }
    /// The underlying heap array.
    #[inline]
    pub fn as_slice(&self) -> &[u32] {
        &self.array
    }
}

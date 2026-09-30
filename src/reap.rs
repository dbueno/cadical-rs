//! Port of `reap.hpp` and `reap.cpp`: radix heap for 'shrink'.

#[derive(Clone, Debug)]
pub struct Reap {
    num_elements: usize,
    last_deleted: u32,
    min_bucket: u32,
    max_bucket: u32,
    buckets: [Vec<u32>; 33],
}

impl Default for Reap {
    fn default() -> Self {
        Reap::new()
    }
}

#[inline]
fn leading_zeroes_of_unsigned(x: u32) -> u32 {
    if x != 0 {
        x.leading_zeros()
    } else {
        32
    }
}

impl Reap {
    pub fn new() -> Reap {
        Reap {
            num_elements: 0,
            last_deleted: 0,
            min_bucket: 32,
            max_bucket: 0,
            buckets: std::array::from_fn(|_| Vec::new()),
        }
    }

    pub fn init(&mut self) {
        // Faithful to C++ 'bucket = {0}' which assigns a vector holding a
        // single zero element (not an empty vector).
        for bucket in self.buckets.iter_mut() {
            *bucket = vec![0];
        }
        debug_assert!(self.num_elements == 0);
        debug_assert!(self.last_deleted == 0);
        self.min_bucket = 32;
        debug_assert!(self.max_bucket == 0);
    }

    pub fn release(&mut self) {
        self.num_elements = 0;
        self.last_deleted = 0;
        self.min_bucket = 32;
        self.max_bucket = 0;
    }

    #[inline]
    pub fn empty(&self) -> bool {
        self.num_elements == 0
    }
    #[inline]
    pub fn size(&self) -> usize {
        self.num_elements
    }

    pub fn push(&mut self, e: u32) {
        debug_assert!(self.last_deleted <= e);
        let diff = e ^ self.last_deleted;
        let bucket = 32 - leading_zeroes_of_unsigned(diff);
        self.buckets[bucket as usize].push(e);
        if self.min_bucket > bucket {
            self.min_bucket = bucket;
        }
        if self.max_bucket < bucket {
            self.max_bucket = bucket;
        }
        debug_assert!(self.num_elements != u32::MAX as usize);
        self.num_elements += 1;
    }

    pub fn pop(&mut self) -> u32 {
        debug_assert!(self.num_elements > 0);
        let mut i = self.min_bucket;
        loop {
            debug_assert!(i < 33);
            debug_assert!(i <= self.max_bucket);
            if self.buckets[i as usize].is_empty() {
                i += 1;
                self.min_bucket = i;
                continue;
            }
            let res: u32;
            if i != 0 {
                let mut r = u32::MAX;
                let mut q = 0usize;
                let s = std::mem::take(&mut self.buckets[i as usize]);
                debug_assert!(!s.is_empty());
                for (p, &tmp) in s.iter().enumerate() {
                    if tmp >= r {
                        continue;
                    }
                    r = tmp;
                    q = p;
                }
                for (p, &other) in s.iter().enumerate() {
                    if p == q {
                        continue;
                    }
                    let diff = other ^ r;
                    let j = 32 - leading_zeroes_of_unsigned(diff);
                    debug_assert!(j < i);
                    self.buckets[j as usize].push(other);
                    if self.min_bucket > j {
                        self.min_bucket = j;
                    }
                }
                // 's.clear ()' keeps the capacity in C++.
                let mut s = s;
                s.clear();
                self.buckets[i as usize] = s;
                if i != 0 && self.max_bucket == i {
                    #[cfg(debug_assertions)]
                    for j in (i + 1)..33 {
                        debug_assert!(self.buckets[j as usize].is_empty());
                    }
                    if self.buckets[i as usize].is_empty() {
                        self.max_bucket = i - 1;
                    }
                }
                res = r;
            } else {
                res = self.last_deleted;
                debug_assert!(!self.buckets[0].is_empty());
                debug_assert!(self.buckets[0][0] == res);
                self.buckets[0].pop();
            }
            if self.min_bucket == i {
                #[cfg(debug_assertions)]
                for j in 0..i {
                    debug_assert!(self.buckets[j as usize].is_empty());
                }
                if self.buckets[i as usize].is_empty() {
                    self.min_bucket = std::cmp::min((i + 1) as i32, 32) as u32;
                }
            }
            self.num_elements -= 1;
            debug_assert!(self.last_deleted <= res);
            self.last_deleted = res;
            return res;
        }
    }

    pub fn clear(&mut self) {
        debug_assert!(self.max_bucket <= 32);
        for i in 0..33 {
            self.buckets[i].clear();
        }
        self.num_elements = 0;
        self.last_deleted = 0;
        self.min_bucket = 32;
        self.max_bucket = 0;
    }
}

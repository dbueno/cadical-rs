//! Bit-exact port of LLVM libc++ 21 (21.1.6) `std::sort`, `std::nth_element`
//! and `std::partial_sort` (comparator-taking overloads).
//!
//! The goal is that for any comparator -- in particular comparators which are
//! a strict weak ordering but *not* a total order on the elements (ties
//! between distinguishable elements) -- the resulting permutation is exactly
//! the one the C++ reference produces, and the comparator is invoked the same
//! number of times with the same arguments in the same order.
//!
//! Sources ported (libc++ 21.1.6 headers, `include/c++/v1/__algorithm/`):
//! `sort.h` (`__introsort`, `__sort3/4/5`, `__insertion_sort*`,
//! `__partition_with_equals_on_{left,right}`, `__bitset_partition`),
//! `nth_element.h`, `partial_sort.h`, `make_heap.h`, `sift_down.h`,
//! `pop_heap.h`, `push_heap.h` (`__sift_up`), `sort_heap.h`, `min_element.h`.
//!
//! Dispatch in libc++ (`__sort_dispatch`):
//! * custom comparator (any class type / lambda / function pointer), or a
//!   non-arithmetic value type: `__introsort<..., _UseBitSetPartition=false>`
//!   with the branchy `__sort3/4/5`.  => [`std_sort`].
//! * arithmetic value type with `std::less` / `std::less<>` / `__less<>` /
//!   `ranges::less` (i.e. `std::sort(b, e)` on ints etc.): calls the
//!   out-of-line `std::__sort<__less<T>&, T*>` in the libc++ dylib, which runs
//!   `__introsort<..., _UseBitSetPartition=true>` with the branchless
//!   `__sort3/4/5`.  => [`std_sort_default_arith`].
//! * arithmetic value type with `std::greater`: same branchless + bitset
//!   algorithm, instantiated inline.  => [`std_sort_branchless`] with `>`.
//!
//! Elements are required to be `Copy`: libc++ moves elements into temporaries
//! (pivot, insertion-sort hole, heap hole), which for `Copy` types is a plain
//! copy.  All indexing is bounds-checked, so a comparator that is not a strict
//! weak ordering (for which libc++ has UB / reads out of bounds) makes this
//! code panic instead of misbehaving.  No `unsafe` is used.

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// `std::sort(first, last, comp)` with a custom comparator (the path taken by
/// every CaDiCaL call site that passes a comparator object).
pub fn std_sort<T: Copy, F: FnMut(&T, &T) -> bool>(v: &mut [T], mut less: F) {
    sort_dispatch::<T, F, false>(v, &mut less);
}

/// `std::sort(first, last)` (default `std::less`) on an arithmetic value type
/// (`int`, `unsigned`, `double`, ...): branchless small sorts + bitset
/// partition, as in the libc++ dylib's `std::__sort<__less<T>&, T*>`.
///
/// For integer types the result is uniquely determined anyway (equal ints are
/// indistinguishable); the port matters only for observability of e.g.
/// `-0.0` vs `+0.0`.
pub fn std_sort_default_arith<T: PartialOrd + Copy>(v: &mut [T]) {
    let mut less = |a: &T, b: &T| a < b;
    sort_dispatch::<T, _, true>(v, &mut less);
}

/// `std::sort` on an arithmetic value type with a comparator that libc++
/// recognises as `std::less`/`std::greater` (so `__use_branchless_sort` is
/// true).  Only use this to model `std::greater<T>()` / `std::less<T>()` on
/// arithmetic `T`; for any other comparator use [`std_sort`].
pub fn std_sort_branchless<T: Copy, F: FnMut(&T, &T) -> bool>(v: &mut [T], mut less: F) {
    sort_dispatch::<T, F, true>(v, &mut less);
}

/// `std::nth_element(first, first + nth, last, comp)` with a custom comparator.
/// `nth >= v.len()` is a no-op (as `nth == last` is in libc++).
pub fn std_nth_element<T: Copy, F: FnMut(&T, &T) -> bool>(v: &mut [T], nth: usize, mut less: F) {
    if nth >= v.len() {
        return;
    }
    let last = v.len();
    nth_element(v, 0, nth, last, &mut less);
}

/// `std::partial_sort(first, first + mid, last, comp)` with a custom comparator.
pub fn std_partial_sort<T: Copy, F: FnMut(&T, &T) -> bool>(v: &mut [T], mid: usize, mut less: F) {
    assert!(mid <= v.len(), "std_partial_sort: mid out of range");
    if mid == 0 {
        return;
    }
    let last = v.len();
    partial_sort_impl(v, 0, mid, last, &mut less);
}

// ---------------------------------------------------------------------------
// sort.h
// ---------------------------------------------------------------------------

fn sort_dispatch<T: Copy, F: FnMut(&T, &T) -> bool, const B: bool>(v: &mut [T], c: &mut F) {
    let n = v.len();
    if n == 0 {
        return;
    }
    // 2 * __bit_log2(len)
    let depth = 2 * (usize::BITS - 1 - n.leading_zeros()) as usize;
    introsort::<T, F, B>(v, 0, n, c, depth, true);
}

/// `__cond_swap`: ensures c(*x, *y) (swaps unless c(*x,*y)).
#[inline(always)]
fn cond_swap<T: Copy, F: FnMut(&T, &T) -> bool>(v: &mut [T], x: usize, y: usize, c: &mut F) -> bool {
    let r = c(&v[x], &v[y]);
    let tmp = if r { v[x] } else { v[y] };
    v[y] = if r { v[y] } else { v[x] };
    v[x] = tmp;
    !r
}

/// `__partially_sorted_swap`
#[inline(always)]
fn partially_sorted_swap<T: Copy, F: FnMut(&T, &T) -> bool>(
    v: &mut [T],
    x: usize,
    y: usize,
    z: usize,
    c: &mut F,
) -> bool {
    let r1 = c(&v[z], &v[x]);
    let tmp = if r1 { v[z] } else { v[x] };
    v[z] = if r1 { v[x] } else { v[z] };
    let r2 = c(&tmp, &v[y]);
    v[x] = if r2 { v[x] } else { v[y] };
    v[y] = if r2 { v[y] } else { tmp };
    !r1 || !r2
}

#[inline(always)]
fn sort3<T: Copy, F: FnMut(&T, &T) -> bool, const B: bool>(
    v: &mut [T],
    x: usize,
    y: usize,
    z: usize,
    c: &mut F,
) -> bool {
    if B {
        let s1 = cond_swap(v, y, z, c);
        let s2 = partially_sorted_swap(v, x, y, z, c);
        return s1 || s2;
    }
    if !c(&v[y], &v[x]) {
        if !c(&v[z], &v[y]) {
            return false;
        }
        v.swap(y, z);
        if c(&v[y], &v[x]) {
            v.swap(x, y);
        }
        return true;
    }
    if c(&v[z], &v[y]) {
        v.swap(x, z);
        return true;
    }
    v.swap(x, y);
    if c(&v[z], &v[y]) {
        v.swap(y, z);
    }
    true
}

#[inline(always)]
fn sort4<T: Copy, F: FnMut(&T, &T) -> bool, const B: bool>(
    v: &mut [T],
    x1: usize,
    x2: usize,
    x3: usize,
    x4: usize,
    c: &mut F,
) {
    if B {
        cond_swap(v, x1, x3, c);
        cond_swap(v, x2, x4, c);
        cond_swap(v, x1, x2, c);
        cond_swap(v, x3, x4, c);
        cond_swap(v, x2, x3, c);
        return;
    }
    sort3::<T, F, B>(v, x1, x2, x3, c);
    if c(&v[x4], &v[x3]) {
        v.swap(x3, x4);
        if c(&v[x3], &v[x2]) {
            v.swap(x2, x3);
            if c(&v[x2], &v[x1]) {
                v.swap(x1, x2);
            }
        }
    }
}

#[inline(always)]
fn sort5<T: Copy, F: FnMut(&T, &T) -> bool, const B: bool>(
    v: &mut [T],
    x1: usize,
    x2: usize,
    x3: usize,
    x4: usize,
    x5: usize,
    c: &mut F,
) {
    if B {
        cond_swap(v, x1, x2, c);
        cond_swap(v, x4, x5, c);
        partially_sorted_swap(v, x3, x4, x5, c);
        cond_swap(v, x2, x5, c);
        partially_sorted_swap(v, x1, x3, x4, c);
        partially_sorted_swap(v, x2, x3, x4, c);
        return;
    }
    sort4::<T, F, B>(v, x1, x2, x3, x4, c);
    if c(&v[x5], &v[x4]) {
        v.swap(x4, x5);
        if c(&v[x4], &v[x3]) {
            v.swap(x3, x4);
            if c(&v[x3], &v[x2]) {
                v.swap(x2, x3);
                if c(&v[x2], &v[x1]) {
                    v.swap(x1, x2);
                }
            }
        }
    }
}

/// `__selection_sort` (assumes size > 0), with `__min_element`.
fn selection_sort<T: Copy, F: FnMut(&T, &T) -> bool>(v: &mut [T], mut first: usize, last: usize, c: &mut F) {
    let lm1 = last - 1;
    while first != lm1 {
        // __min_element(first, last)
        let mut m = first;
        let mut i = first;
        loop {
            i += 1;
            if i == last {
                break;
            }
            if c(&v[i], &v[m]) {
                m = i;
            }
        }
        if m != first {
            v.swap(first, m);
        }
        first += 1;
    }
}

/// `__insertion_sort` (guarded).
fn insertion_sort<T: Copy, F: FnMut(&T, &T) -> bool>(v: &mut [T], first: usize, last: usize, c: &mut F) {
    if first == last {
        return;
    }
    let mut i = first + 1;
    while i != last {
        let mut j = i - 1;
        if c(&v[i], &v[j]) {
            let t = v[i];
            let mut k = j;
            j = i;
            loop {
                v[j] = v[k];
                j = k;
                if j == first {
                    break;
                }
                k -= 1;
                if !c(&t, &v[k]) {
                    break;
                }
            }
            v[j] = t;
        }
        i += 1;
    }
}

/// `__insertion_sort_unguarded`: requires `first >= 1` and that v[first-1] is
/// not greater than any element of [first, last).
fn insertion_sort_unguarded<T: Copy, F: FnMut(&T, &T) -> bool>(
    v: &mut [T],
    first: usize,
    last: usize,
    c: &mut F,
) {
    if first == last {
        return;
    }
    let mut i = first + 1;
    while i != last {
        let mut j = i - 1;
        if c(&v[i], &v[j]) {
            let t = v[i];
            let mut k = j;
            j = i;
            loop {
                v[j] = v[k];
                j = k;
                k -= 1; // may reach first-1 (the guard); panics on underflow below 0
                if !c(&t, &v[k]) {
                    break;
                }
            }
            v[j] = t;
        }
        i += 1;
    }
}

/// `__insertion_sort_incomplete`
fn insertion_sort_incomplete<T: Copy, F: FnMut(&T, &T) -> bool, const B: bool>(
    v: &mut [T],
    first: usize,
    last: usize,
    c: &mut F,
) -> bool {
    match last - first {
        0 | 1 => return true,
        2 => {
            if c(&v[last - 1], &v[first]) {
                v.swap(first, last - 1);
            }
            return true;
        }
        3 => {
            sort3::<T, F, B>(v, first, first + 1, last - 1, c);
            return true;
        }
        4 => {
            sort4::<T, F, B>(v, first, first + 1, first + 2, last - 1, c);
            return true;
        }
        5 => {
            sort5::<T, F, B>(v, first, first + 1, first + 2, first + 3, last - 1, c);
            return true;
        }
        _ => {}
    }
    let mut j = first + 2;
    sort3::<T, F, B>(v, first, first + 1, j, c);
    const LIMIT: u32 = 8;
    let mut count: u32 = 0;
    let mut i = j + 1;
    while i != last {
        if c(&v[i], &v[j]) {
            let t = v[i];
            let mut k = j;
            j = i;
            loop {
                v[j] = v[k];
                j = k;
                if j == first {
                    break;
                }
                k -= 1;
                if !c(&t, &v[k]) {
                    break;
                }
            }
            v[j] = t;
            count += 1;
            if count == LIMIT {
                return i + 1 == last;
            }
        }
        j = i;
        i += 1;
    }
    true
}

// ----- bitset partition (only for B == true) -------------------------------

const BLOCK: isize = 64;

#[inline(always)]
fn swap_bitmap_pos<T: Copy>(v: &mut [T], first: isize, last: isize, lb: &mut u64, rb: &mut u64) {
    while *lb != 0 && *rb != 0 {
        let tzl = lb.trailing_zeros() as isize;
        *lb &= *lb - 1;
        let tzr = rb.trailing_zeros() as isize;
        *rb &= *rb - 1;
        v.swap((first + tzl) as usize, (last - tzr) as usize);
    }
}

#[inline(always)]
fn populate_left_bitset<T: Copy, F: FnMut(&T, &T) -> bool>(
    v: &[T],
    first: isize,
    c: &mut F,
    pivot: &T,
    lb: &mut u64,
) {
    let mut it = first;
    for j in 0..BLOCK {
        let r = !c(&v[it as usize], pivot);
        *lb |= (r as u64) << j;
        it += 1;
    }
}

#[inline(always)]
fn populate_right_bitset<T: Copy, F: FnMut(&T, &T) -> bool>(
    v: &[T],
    lm1: isize,
    c: &mut F,
    pivot: &T,
    rb: &mut u64,
) {
    let mut it = lm1;
    for j in 0..BLOCK {
        let r = c(&v[it as usize], pivot);
        *rb |= (r as u64) << j;
        it -= 1;
    }
}

fn bitset_partition_partial_blocks<T: Copy, F: FnMut(&T, &T) -> bool>(
    v: &mut [T],
    first: &mut isize,
    lm1: &mut isize,
    c: &mut F,
    pivot: &T,
    lb: &mut u64,
    rb: &mut u64,
) {
    let remaining = *lm1 - *first + 1;
    let (l_size, r_size);
    if *lb == 0 && *rb == 0 {
        l_size = remaining / 2; // C++ truncating division; Rust `/` matches
        r_size = remaining - l_size;
    } else if *lb == 0 {
        l_size = remaining - BLOCK;
        r_size = BLOCK;
    } else {
        l_size = BLOCK;
        r_size = remaining - BLOCK;
    }
    if *lb == 0 {
        let mut it = *first;
        let mut j = 0;
        while j < l_size {
            let r = !c(&v[it as usize], pivot);
            *lb |= (r as u64) << j;
            it += 1;
            j += 1;
        }
    }
    if *rb == 0 {
        let mut it = *lm1;
        let mut j = 0;
        while j < r_size {
            let r = c(&v[it as usize], pivot);
            *rb |= (r as u64) << j;
            it -= 1;
            j += 1;
        }
    }
    swap_bitmap_pos(v, *first, *lm1, lb, rb);
    *first += if *lb == 0 { l_size } else { 0 };
    *lm1 -= if *rb == 0 { r_size } else { 0 };
}

fn swap_bitmap_pos_within<T: Copy>(v: &mut [T], first: &mut isize, lm1: &mut isize, lb: &mut u64, rb: &mut u64) {
    if *lb != 0 {
        while *lb != 0 {
            let tz = BLOCK - 1 - lb.leading_zeros() as isize;
            *lb &= (1u64 << tz) - 1;
            let it = *first + tz;
            if it != *lm1 {
                v.swap(it as usize, *lm1 as usize);
            }
            *lm1 -= 1;
        }
        *first = *lm1 + 1;
    } else if *rb != 0 {
        while *rb != 0 {
            let tz = BLOCK - 1 - rb.leading_zeros() as isize;
            *rb &= (1u64 << tz) - 1;
            let it = *lm1 - tz;
            if it != *first {
                v.swap(it as usize, *first as usize);
            }
            *first += 1;
        }
    }
}

/// `__bitset_partition`: returns (pivot position, already partitioned).
fn bitset_partition<T: Copy, F: FnMut(&T, &T) -> bool>(
    v: &mut [T],
    first_u: usize,
    last_u: usize,
    c: &mut F,
) -> (usize, bool) {
    let begin = first_u as isize;
    let mut first = first_u as isize;
    let mut last = last_u as isize;
    let pivot = v[first_u];
    if c(&pivot, &v[(last - 1) as usize]) {
        loop {
            first += 1;
            if c(&pivot, &v[first as usize]) {
                break;
            }
        }
    } else {
        loop {
            first += 1;
            if !(first < last && !c(&pivot, &v[first as usize])) {
                break;
            }
        }
    }
    if first < last {
        loop {
            last -= 1;
            if !c(&pivot, &v[last as usize]) {
                break;
            }
        }
    }
    let already = first >= last;
    if !already {
        v.swap(first as usize, last as usize);
        first += 1;
    }
    let mut lm1 = last - 1;
    let mut lb: u64 = 0;
    let mut rb: u64 = 0;
    while lm1 - first >= 2 * BLOCK - 1 {
        if lb == 0 {
            populate_left_bitset(v, first, c, &pivot, &mut lb);
        }
        if rb == 0 {
            populate_right_bitset(v, lm1, c, &pivot, &mut rb);
        }
        swap_bitmap_pos(v, first, lm1, &mut lb, &mut rb);
        first += if lb == 0 { BLOCK } else { 0 };
        lm1 -= if rb == 0 { BLOCK } else { 0 };
    }
    bitset_partition_partial_blocks(v, &mut first, &mut lm1, c, &pivot, &mut lb, &mut rb);
    swap_bitmap_pos_within(v, &mut first, &mut lm1, &mut lb, &mut rb);
    let pivot_pos = first - 1;
    if begin != pivot_pos {
        v[begin as usize] = v[pivot_pos as usize];
    }
    v[pivot_pos as usize] = pivot;
    (pivot_pos as usize, already)
}

/// `__partition_with_equals_on_right`: returns (pivot position, already partitioned).
fn partition_with_equals_on_right<T: Copy, F: FnMut(&T, &T) -> bool>(
    v: &mut [T],
    begin: usize,
    mut last: usize,
    c: &mut F,
) -> (usize, bool) {
    let mut first = begin;
    let pivot = v[first];
    loop {
        first += 1;
        if !c(&v[first], &pivot) {
            break;
        }
    }
    if begin == first - 1 {
        while first < last {
            last -= 1;
            if c(&v[last], &pivot) {
                break;
            }
        }
    } else {
        loop {
            last -= 1;
            if c(&v[last], &pivot) {
                break;
            }
        }
    }
    let already = first >= last;
    while first < last {
        v.swap(first, last);
        loop {
            first += 1;
            if !c(&v[first], &pivot) {
                break;
            }
        }
        loop {
            last -= 1;
            if c(&v[last], &pivot) {
                break;
            }
        }
    }
    let pivot_pos = first - 1;
    if begin != pivot_pos {
        v[begin] = v[pivot_pos];
    }
    v[pivot_pos] = pivot;
    (pivot_pos, already)
}

/// `__partition_with_equals_on_left`: returns the new `first` (pivot pos + 1).
fn partition_with_equals_on_left<T: Copy, F: FnMut(&T, &T) -> bool>(
    v: &mut [T],
    begin: usize,
    mut last: usize,
    c: &mut F,
) -> usize {
    let mut first = begin;
    let pivot = v[first];
    if c(&pivot, &v[last - 1]) {
        loop {
            first += 1;
            if c(&pivot, &v[first]) {
                break;
            }
        }
    } else {
        loop {
            first += 1;
            if !(first < last && !c(&pivot, &v[first])) {
                break;
            }
        }
    }
    if first < last {
        loop {
            last -= 1;
            if !c(&pivot, &v[last]) {
                break;
            }
        }
    }
    while first < last {
        v.swap(first, last);
        loop {
            first += 1;
            if c(&pivot, &v[first]) {
                break;
            }
        }
        loop {
            last -= 1;
            if !c(&pivot, &v[last]) {
                break;
            }
        }
    }
    let pivot_pos = first - 1;
    if begin != pivot_pos {
        v[begin] = v[pivot_pos];
    }
    v[pivot_pos] = pivot;
    first
}

/// `__introsort`
fn introsort<T: Copy, F: FnMut(&T, &T) -> bool, const B: bool>(
    v: &mut [T],
    mut first: usize,
    mut last: usize,
    c: &mut F,
    mut depth: usize,
    mut leftmost: bool,
) {
    const LIMIT: usize = 24;
    const NINTHER_THRESHOLD: usize = 128;
    loop {
        let len = last - first;
        match len {
            0 | 1 => return,
            2 => {
                if c(&v[last - 1], &v[first]) {
                    v.swap(first, last - 1);
                }
                return;
            }
            3 => {
                sort3::<T, F, B>(v, first, first + 1, last - 1, c);
                return;
            }
            4 => {
                sort4::<T, F, B>(v, first, first + 1, first + 2, last - 1, c);
                return;
            }
            5 => {
                sort5::<T, F, B>(v, first, first + 1, first + 2, first + 3, last - 1, c);
                return;
            }
            _ => {}
        }
        if len < LIMIT {
            if leftmost {
                insertion_sort(v, first, last, c);
            } else {
                insertion_sort_unguarded(v, first, last, c);
            }
            return;
        }
        if depth == 0 {
            // __partial_sort(first, last, last): heapsort
            partial_sort_impl(v, first, last, last, c);
            return;
        }
        depth -= 1;
        {
            let half = len / 2;
            if len > NINTHER_THRESHOLD {
                sort3::<T, F, B>(v, first, first + half, last - 1, c);
                sort3::<T, F, B>(v, first + 1, first + (half - 1), last - 2, c);
                sort3::<T, F, B>(v, first + 2, first + (half + 1), last - 3, c);
                sort3::<T, F, B>(v, first + (half - 1), first + half, first + (half + 1), c);
                v.swap(first, first + half);
            } else {
                sort3::<T, F, B>(v, first + half, first, last - 1, c);
            }
        }
        if !leftmost && !c(&v[first - 1], &v[first]) {
            first = partition_with_equals_on_left(v, first, last, c);
            continue;
        }
        let (mut i, already) = if B {
            bitset_partition(v, first, last, c)
        } else {
            partition_with_equals_on_right(v, first, last, c)
        };
        if already {
            let fs = insertion_sort_incomplete::<T, F, B>(v, first, i, c);
            if insertion_sort_incomplete::<T, F, B>(v, i + 1, last, c) {
                if fs {
                    return;
                }
                last = i;
                continue;
            } else if fs {
                i += 1;
                first = i;
                continue;
            }
        }
        introsort::<T, F, B>(v, first, i, c, depth, leftmost);
        leftmost = false;
        i += 1;
        first = i;
    }
}

// ---------------------------------------------------------------------------
// Heap operations (make_heap.h, sift_down.h, pop_heap.h, push_heap.h,
// sort_heap.h, partial_sort.h).  All indices are relative to `base`.
// ---------------------------------------------------------------------------

/// `__sift_down(first, comp, len, start)`
fn sift_down<T: Copy, F: FnMut(&T, &T) -> bool>(v: &mut [T], base: usize, c: &mut F, len: usize, start: usize) {
    let mut start = start; // relative
    let mut child = start;
    if len < 2 || (len - 2) / 2 < child {
        return;
    }
    child = 2 * child + 1;
    if child + 1 < len && c(&v[base + child], &v[base + child + 1]) {
        child += 1;
    }
    if c(&v[base + child], &v[base + start]) {
        return;
    }
    let top = v[base + start];
    loop {
        v[base + start] = v[base + child];
        start = child;
        if (len - 2) / 2 < child {
            break;
        }
        child = 2 * child + 1;
        if child + 1 < len && c(&v[base + child], &v[base + child + 1]) {
            child += 1;
        }
        if c(&v[base + child], &top) {
            break;
        }
    }
    v[base + start] = top;
}

/// `__floyd_sift_down(first, comp, len)`: returns hole position (relative).
fn floyd_sift_down<T: Copy, F: FnMut(&T, &T) -> bool>(v: &mut [T], base: usize, c: &mut F, len: usize) -> usize {
    let mut hole = 0usize;
    let mut child = 0usize;
    loop {
        child = 2 * child + 1; // == child_i
        if child + 1 < len && c(&v[base + child], &v[base + child + 1]) {
            child += 1;
        }
        v[base + hole] = v[base + child];
        hole = child;
        if child > (len - 2) / 2 {
            return hole;
        }
    }
}

/// `__sift_up(first, last, comp, len)` with `last`/`len` relative to `base`.
fn sift_up<T: Copy, F: FnMut(&T, &T) -> bool>(v: &mut [T], base: usize, last: usize, c: &mut F, len: usize) {
    if len > 1 {
        let mut len = (len - 2) / 2;
        let mut ptr = len;
        let mut last = last - 1;
        if c(&v[base + ptr], &v[base + last]) {
            let t = v[base + last];
            loop {
                v[base + last] = v[base + ptr];
                last = ptr;
                if len == 0 {
                    break;
                }
                len = (len - 1) / 2;
                ptr = len;
                if !c(&v[base + ptr], &t) {
                    break;
                }
            }
            v[base + last] = t;
        }
    }
}

/// `__pop_heap(first, last, comp, len)` (last relative to base).
fn pop_heap<T: Copy, F: FnMut(&T, &T) -> bool>(v: &mut [T], base: usize, last: usize, c: &mut F, len: usize) {
    if len > 1 {
        let top = v[base];
        let mut hole = floyd_sift_down(v, base, c, len);
        let last = last - 1;
        if hole == last {
            v[base + hole] = top;
        } else {
            v[base + hole] = v[base + last];
            hole += 1;
            v[base + last] = top;
            sift_up(v, base, hole, c, hole);
        }
    }
}

/// `__make_heap(first, first + n)`
fn make_heap<T: Copy, F: FnMut(&T, &T) -> bool>(v: &mut [T], base: usize, n: usize, c: &mut F) {
    if n > 1 {
        let mut start = (n - 2) / 2;
        loop {
            sift_down(v, base, c, n, start);
            if start == 0 {
                break;
            }
            start -= 1;
        }
    }
}

/// `__sort_heap(first, first + n)`
fn sort_heap<T: Copy, F: FnMut(&T, &T) -> bool>(v: &mut [T], base: usize, n: usize, c: &mut F) {
    let mut last = n;
    let mut n = n;
    while n > 1 {
        pop_heap(v, base, last, c, n);
        last -= 1;
        n -= 1;
    }
}

/// `__partial_sort_impl(first, middle, last)` (absolute indices).
fn partial_sort_impl<T: Copy, F: FnMut(&T, &T) -> bool>(
    v: &mut [T],
    first: usize,
    middle: usize,
    last: usize,
    c: &mut F,
) {
    if first == middle {
        return;
    }
    let len = middle - first;
    make_heap(v, first, len, c);
    for i in middle..last {
        if c(&v[i], &v[first]) {
            v.swap(i, first);
            sift_down(v, first, c, len, 0);
        }
    }
    sort_heap(v, first, len, c);
}

// ---------------------------------------------------------------------------
// nth_element.h (non-branchless __sort3, as for custom comparators)
// ---------------------------------------------------------------------------

fn nth_element<T: Copy, F: FnMut(&T, &T) -> bool>(
    v: &mut [T],
    mut first: usize,
    nth: usize,
    mut last: usize,
    c: &mut F,
) {
    const LIMIT: usize = 7;
    'outer: loop {
        if nth == last {
            return;
        }
        let len = last - first;
        match len {
            0 | 1 => return,
            2 => {
                if c(&v[last - 1], &v[first]) {
                    v.swap(first, last - 1);
                }
                return;
            }
            3 => {
                sort3::<T, F, false>(v, first, first + 1, last - 1, c);
                return;
            }
            _ => {}
        }
        if len <= LIMIT {
            selection_sort(v, first, last, c);
            return;
        }
        let mut m = first + len / 2;
        let lm1 = last - 1;
        let mut n_swaps: u32 = sort3::<T, F, false>(v, first, m, lm1, c) as u32;
        let mut i = first;
        let mut j = lm1;
        if !c(&v[i], &v[m]) {
            // __nth_element_find_guard(i, j, m)
            let found = loop {
                j -= 1;
                if i == j {
                    break false;
                }
                if c(&v[j], &v[m]) {
                    break true;
                }
            };
            if found {
                v.swap(i, j);
                n_swaps += 1;
            } else {
                i += 1;
                j = last;
                j -= 1;
                if !c(&v[first], &v[j]) {
                    loop {
                        if i == j {
                            return;
                        } else if c(&v[first], &v[i]) {
                            v.swap(i, j);
                            n_swaps += 1;
                            i += 1;
                            break;
                        }
                        i += 1;
                    }
                }
                if i == j {
                    return;
                }
                loop {
                    while !c(&v[first], &v[i]) {
                        i += 1;
                    }
                    loop {
                        j -= 1;
                        if !c(&v[first], &v[j]) {
                            break;
                        }
                    }
                    if i >= j {
                        break;
                    }
                    v.swap(i, j);
                    n_swaps += 1;
                    i += 1;
                }
                let _ = n_swaps;
                if nth < i {
                    return;
                }
                first = i;
                continue 'outer;
            }
        }
        i += 1;
        if i < j {
            loop {
                while c(&v[i], &v[m]) {
                    i += 1;
                }
                loop {
                    j -= 1;
                    if c(&v[j], &v[m]) {
                        break;
                    }
                }
                if i >= j {
                    break;
                }
                v.swap(i, j);
                n_swaps += 1;
                if m == i {
                    m = j;
                }
                i += 1;
            }
        }
        if i != m && c(&v[m], &v[i]) {
            v.swap(i, m);
            n_swaps += 1;
        }
        if nth == i {
            return;
        }
        if n_swaps == 0 {
            if nth < i {
                j = first;
                m = first;
                loop {
                    j += 1;
                    if j == i {
                        return;
                    }
                    if c(&v[j], &v[m]) {
                        break;
                    }
                    m = j;
                }
            } else {
                j = i;
                m = i;
                loop {
                    j += 1;
                    if j == last {
                        return;
                    }
                    if c(&v[j], &v[m]) {
                        break;
                    }
                    m = j;
                }
            }
        }
        if nth < i {
            last = i;
        } else {
            i += 1;
            first = i;
        }
    }
}

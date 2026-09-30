//! Port of `radix.hpp`: generic (stable) radix sort `rsort` and the
//! `MSORT` hybrid (`msort`).  Faithful to the C++ code, including which
//! bucket counters are reset between passes.

/// Unsigned rank types usable with [`rsort`] (`Rank::Type` in C++).
pub trait RadixRank: Copy {
    /// `sizeof (R)`.
    const BYTES: usize;
    fn to_u64(self) -> u64;
}

impl RadixRank for u8 {
    const BYTES: usize = 1;
    #[inline(always)]
    fn to_u64(self) -> u64 {
        self as u64
    }
}
impl RadixRank for u16 {
    const BYTES: usize = 2;
    #[inline(always)]
    fn to_u64(self) -> u64 {
        self as u64
    }
}
impl RadixRank for u32 {
    const BYTES: usize = 4;
    #[inline(always)]
    fn to_u64(self) -> u64 {
        self as u64
    }
}
impl RadixRank for u64 {
    const BYTES: usize = 8;
    #[inline(always)]
    fn to_u64(self) -> u64 {
        self
    }
}
impl RadixRank for usize {
    const BYTES: usize = 8;
    #[inline(always)]
    fn to_u64(self) -> u64 {
        self as u64
    }
}

/// `pointer_rank`: rank clauses by their address.
#[inline(always)]
pub fn pointer_rank(c: &crate::clause::CRef) -> usize {
    c.addr()
}

/// Radix sort `v` by `rank` (stable, byte-wise).
pub fn rsort<T: Copy, R: RadixRank, F: FnMut(&T) -> R>(v: &mut [T], mut rank: F) {
    let n = v.len();
    if n <= 1 {
        return;
    }

    const L: usize = 8; // Radix 8, thus byte-wise.
    const W: usize = 1 << L; // So many buckets.
    let mask: u64 = (W - 1) as u64; // Fast mod 'w'.

    // Arithmetic in the rank type 'R' is emulated in 'u64' truncated to
    // 'width_mask'.
    let width_bits = 8 * R::BYTES;
    let width_mask: u64 = if width_bits >= 64 { u64::MAX } else { (1u64 << width_bits) - 1 };

    let mut count = [0usize; W]; // Put buckets on the stack.

    // 'c' is either the input ('a') or the temporary vector ('b').
    let mut c_is_a = true;
    let mut initialized = false;
    let mut tmp: Vec<T> = Vec::new();

    let mut upper: u64 = 0;
    let mut lower: u64 = !upper & width_mask;
    let mut shifted: u64 = mask;
    let mut bounded = false;

    let mut masked_lower: u64 = 0;
    let mut masked_upper: u64 = mask;

    let mut i = 0usize;
    while i < width_bits {
        if !(bounded && (lower & shifted) == (upper & shifted)) {
            for j in masked_lower..=masked_upper {
                count[j as usize] = 0;
            }

            let mut sorted = true;
            let mut last: u64 = 0;

            {
                let src: &[T] = if c_is_a { &*v } else { &tmp };
                for p in src.iter() {
                    let r = rank(p).to_u64();
                    if !bounded {
                        lower &= r;
                        upper |= r;
                    }
                    let s = r >> i;
                    let m = s & mask;
                    if sorted && last > m {
                        sorted = false;
                    } else {
                        last = m;
                    }
                    count[m as usize] += 1;
                }
            }

            masked_lower = (lower >> i) & mask;
            masked_upper = (upper >> i) & mask;

            let mut skip = false;
            if !bounded {
                bounded = true;
                if (lower & shifted) == (upper & shifted) {
                    skip = true;
                }
            }

            if !skip && !sorted {
                let mut pos = 0usize;
                let mut j = masked_lower;
                while j <= masked_upper {
                    let delta = count[j as usize];
                    count[j as usize] = pos;
                    pos += delta;
                    j += 1;
                }

                if !initialized {
                    debug_assert!(c_is_a);
                    tmp.resize(n, v[0]);
                    initialized = true;
                }

                if c_is_a {
                    for k in 0..n {
                        let r = rank(&v[k]).to_u64();
                        let s = r >> i;
                        let m = (s & mask) as usize;
                        tmp[count[m]] = v[k];
                        count[m] += 1;
                    }
                } else {
                    for k in 0..n {
                        let r = rank(&tmp[k]).to_u64();
                        let s = r >> i;
                        let m = (s & mask) as usize;
                        v[count[m]] = tmp[k];
                        count[m] += 1;
                    }
                }
                c_is_a = !c_is_a;
            }
        }
        i += L;
        shifted = (shifted << L) & width_mask;
    }

    if !c_is_a {
        v.copy_from_slice(&tmp[..n]);
    }

    #[cfg(debug_assertions)]
    for k in 0..n - 1 {
        debug_assert!(rank(&v[k]).to_u64() <= rank(&v[k + 1]).to_u64());
    }
}

/// `MSORT (LIMIT, FIRST, LAST, RANK, LESS)`: use `std::sort` (the libc++
/// port in [`crate::sort::std_sort`]) up to `limit` elements and radix sort
/// above.
#[inline]
pub fn msort<T: Copy, R: RadixRank, FR: FnMut(&T) -> R, FL: FnMut(&T, &T) -> bool>(
    limit: usize,
    v: &mut [T],
    rank: FR,
    less: FL,
) {
    let n = v.len();
    if n <= limit {
        crate::sort::std_sort(v, less);
    } else {
        rsort(v, rank);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn rsort_sorts_stably() {
        let mut v: Vec<(u32, u32)> = (0..1000u32).map(|i| ((i * 7919) % 257, i)).collect();
        rsort(&mut v, |p: &(u32, u32)| p.0);
        for w in v.windows(2) {
            assert!(w[0].0 < w[1].0 || (w[0].0 == w[1].0 && w[0].1 < w[1].1));
        }
        let mut u: Vec<u64> = vec![5, 1 << 40, 3, 1 << 20, 0, 7];
        rsort(&mut u, |x: &u64| *x);
        assert_eq!(u, vec![0, 3, 5, 7, 1 << 20, 1 << 40]);
    }
}

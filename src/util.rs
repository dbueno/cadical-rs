//! Port of `util.hpp` and `util.cpp`: common simple utility functions
//! independent from `Internal`.
//!
//! The C++ `DeferDeleteArray` / `DeferDeletePtr` helpers (bad_alloc
//! safety) are not needed in Rust and are not ported.

/*------------------------------------------------------------------------*/

#[inline]
pub fn relative(a: f64, b: f64) -> f64 {
    if b != 0.0 {
        a / b
    } else {
        0.0
    }
}

#[inline]
pub fn percent(a: f64, b: f64) -> f64 {
    relative(100.0 * a, b)
}

#[inline]
pub fn sign(lit: i32) -> i32 {
    (lit > 0) as i32 - (lit < 0) as i32
}

#[inline]
pub fn bign(lit: i32) -> u32 {
    1 + (lit < 0) as u32
}

/*------------------------------------------------------------------------*/

pub fn has_suffix(str: &str, suffix: &str) -> bool {
    let k = str.len();
    let l = suffix.len();
    k > l && &str.as_bytes()[k - l..] == suffix.as_bytes()
}

pub fn has_prefix(str: &str, prefix: &str) -> bool {
    // C++ compares byte by byte until the end of 'prefix' (the terminating
    // zero of 'str' never matches a non-zero prefix character).
    let s = str.as_bytes();
    for (i, &q) in prefix.as_bytes().iter().enumerate() {
        if i >= s.len() || s[i] != q {
            return false;
        }
    }
    true
}

/*------------------------------------------------------------------------*/

/// Parse integer string in the form of
///
/// ```text
///   true
///   false
///   [-]<mantissa>[e<exponent>]
/// ```
///
/// and in the latter case `<val>` has to be within `[-INT_MAX,INT_MAX]`.
/// Returns `true` if parsing is successful and then also sets `val`.
pub fn parse_int_str(val_str: &str, val: &mut i32) -> bool {
    if val_str == "true" {
        *val = 1;
    } else if val_str == "false" {
        *val = 0;
    } else {
        // Emulate the C pointer walk including the terminating zero.
        let bytes = val_str.as_bytes();
        let at = |i: usize| -> i32 {
            if i < bytes.len() {
                bytes[i] as i32
            } else {
                0
            }
        };
        let isdigit = |c: i32| (b'0' as i32..=b'9' as i32).contains(&c);
        let mut p = 0usize;
        let sign: i32 = if at(p) == b'-' as i32 {
            p += 1;
            -1
        } else {
            1
        };
        let mut ch = at(p);
        p += 1;
        if !isdigit(ch) {
            return false;
        }
        let bound: i64 = -(i32::MIN as i64);
        let mut mantissa: i64 = (ch - b'0' as i32) as i64;
        loop {
            ch = at(p);
            p += 1;
            if !isdigit(ch) {
                break;
            }
            if bound / 10 < mantissa {
                mantissa = bound;
            } else {
                mantissa *= 10;
            }
            let digit = (ch - b'0' as i32) as i64;
            if bound - digit < mantissa {
                mantissa = bound;
            } else {
                mantissa += digit;
            }
        }
        let mut exponent = 0;
        if ch == b'e' as i32 {
            loop {
                ch = at(p);
                p += 1;
                if !isdigit(ch) {
                    break;
                }
                exponent = if exponent != 0 { 10 } else { ch - b'0' as i32 };
            }
            if ch != 0 {
                return false;
            }
        } else if ch != 0 {
            return false;
        }
        debug_assert!(exponent <= 10);
        let mut val64 = mantissa;
        for _ in 0..exponent {
            val64 = val64.saturating_mul(10);
        }
        if sign < 0 {
            val64 = -val64;
            if val64 < i32::MIN as i64 {
                val64 = i32::MIN as i64;
            }
        } else if val64 > i32::MAX as i64 {
            val64 = i32::MAX as i64;
        }
        debug_assert!(i32::MIN as i64 <= val64);
        debug_assert!(val64 <= i32::MAX as i64);
        *val = val64 as i32;
    }
    true
}

/*------------------------------------------------------------------------*/

#[inline]
pub fn is_power_of_two(n: u32) -> bool {
    n != 0 && (n & (n - 1)) == 0
}

#[inline]
pub fn contained(c: i64, l: i64, u: i64) -> bool {
    l <= c && c <= u
}

#[inline]
pub fn aligned(n: usize, alignment: usize) -> bool {
    debug_assert!(alignment.is_power_of_two());
    let mask = alignment - 1;
    (n & mask) == 0
}

#[inline]
pub fn align(n: usize, alignment: usize) -> usize {
    let mut res = n;
    debug_assert!(alignment.is_power_of_two());
    let mask = alignment - 1;
    if res & mask != 0 {
        res = (res | mask) + 1;
    }
    debug_assert!(aligned(res, alignment));
    res
}

/*------------------------------------------------------------------------*/

#[inline]
pub fn parity(a: u32) -> bool {
    let mut tmp = a;
    tmp ^= tmp >> 16;
    tmp ^= tmp >> 8;
    tmp ^= tmp >> 4;
    tmp ^= tmp >> 2;
    tmp ^= tmp >> 1;
    (tmp & 1) != 0
}

/*------------------------------------------------------------------------*/

/// Clear a vector and release its memory ('Effective STL' swap trick).
#[inline]
pub fn erase_vector<T>(v: &mut Vec<T>) {
    if v.capacity() != 0 {
        *v = Vec::new();
    }
}

/// Shrink the capacity of a vector to its size.
#[inline]
pub fn shrink_vector<T>(v: &mut Vec<T>) {
    if v.capacity() > v.len() {
        v.shrink_to_fit();
    }
}

#[inline]
pub fn enlarge_init<T: Clone>(v: &mut Vec<T>, n: usize, i: T) {
    if v.len() < n {
        v.resize(n, i);
    }
}

#[inline]
pub fn enlarge_only<T: Clone + Default>(v: &mut Vec<T>, n: usize) {
    if v.len() < n {
        v.resize(n, T::default());
    }
}

#[inline]
pub fn enlarge_zero<T: Clone + Default>(v: &mut Vec<T>, n: usize) {
    enlarge_only(v, n)
}

/// Double the capacity until it fits (keeps amortized complexity).
pub fn reserve_at_least<T>(v: &mut Vec<T>, n: usize) {
    if n < v.capacity() {
        return;
    }
    let mut new_size = v.len();
    if new_size == 0 {
        new_size = n;
    }
    while new_size < n {
        new_size *= 2;
    }
    if new_size > v.len() {
        v.reserve_exact(new_size - v.len());
    }
}

/// `memset (base, 0, sizeof (T) * n)`.
#[inline]
pub fn clear_n<T: Default>(base: &mut [T]) {
    for x in base {
        *x = T::default();
    }
}

/*------------------------------------------------------------------------*/

/// These are options both to 'cadical' and 'mobical'.
pub fn is_color_option(arg: &str) -> bool {
    matches!(
        arg,
        "--color"
            | "--colors"
            | "--colour"
            | "--colours"
            | "--color=1"
            | "--colors=1"
            | "--colour=1"
            | "--colours=1"
            | "--color=true"
            | "--colors=true"
            | "--colour=true"
            | "--colours=true"
    )
}

pub fn is_no_color_option(arg: &str) -> bool {
    matches!(
        arg,
        "--no-color"
            | "--no-colors"
            | "--no-colour"
            | "--no-colours"
            | "--color=0"
            | "--colors=0"
            | "--colour=0"
            | "--colours=0"
            | "--color=false"
            | "--colors=false"
            | "--colour=false"
            | "--colours=false"
    )
}

/*------------------------------------------------------------------------*/

const PRIMES: [u64; 9] = [
    1111111111111111111,
    2222222222222222249,
    3333333333333333347,
    4444444444444444537,
    5555555555555555621,
    6666666666666666677,
    7777777777777777793,
    8888888888888888923,
    9999999999999999961,
];

pub fn hash_string(str: &str) -> u64 {
    let size = PRIMES.len();
    let mut res: u64 = 0;
    let mut i = 0;
    for &ch in str.as_bytes() {
        if ch == 0 {
            break;
        }
        res = res.wrapping_add(ch as u64);
        res = res.wrapping_mul(PRIMES[i]);
        i += 1;
        if i == size {
            i = 0;
        }
    }
    res
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn parse_int() {
        let mut v = 0;
        assert!(parse_int_str("1e3", &mut v) && v == 1000);
        assert!(parse_int_str("-12", &mut v) && v == -12);
        assert!(parse_int_str("true", &mut v) && v == 1);
        assert!(!parse_int_str("x", &mut v));
        assert!(parse_int_str("99999999999", &mut v) && v == i32::MAX);
        assert!(parse_int_str("2e9", &mut v) && v == 2000000000);
    }
}

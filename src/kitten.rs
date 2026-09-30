//! Port of `kitten.h` and `kitten.c` (the small embedded SAT solver used
//! for definition mining and SAT sweeping), including the Kissat random
//! number helpers of `random.h` and the `stack.h` macros (as `Vec`).
//!
//! The C interface is kept (free functions taking `&mut Kitten`).  C call
//! backs taking a `void *state` are Rust closures here (the state is
//! captured by the closure).  `kitten_set_terminator` keeps the C style
//! (`*mut c_void` state and a function pointer) since the terminator is
//! stored inside the solver.
//!
//! Porting notes:
//!
//! * The clause arena `klauses` is a `Vec<u32>` with exactly the C layout
//!   (`aux`, `size`, `flags`, literals, then antecedents for learned
//!   clauses if antecedents are tracked), and clauses are referenced by
//!   their offset in it.
//! * The per variable / per literal arrays (`vars`, `links`, `marks`,
//!   `values`, `failed`, `phases`, `watches`) always have the C capacity
//!   (`size / 2` resp. `size` entries), and resizing copies only the
//!   active prefix like the C `RESIZE1` / `RESIZE2` macros, since
//!   `kitten_randomize_phases` and `kitten_flip_phases` work on the whole
//!   capacity.
//! * `stack.h` stacks are `Vec<u32>`; `SET_END_OF_STACK` is `truncate`.
//! * `CHECK_KITTEN` is the constant `CHECK_KITTEN` below.

#![allow(clippy::needless_range_loop)]

use crate::message::{c_stderr, c_stdout, fflush, fputc, fputs};

/// Terminator call back (`int (*terminator) (void *)`).
pub type KittenTerminator = fn(*mut libc::c_void) -> i32;

/*------------------------------------------------------------------------*/
// random.h

/// `generator` of `random.h`.
pub type Generator = u64;

/// `kissat_next_random64`.
#[inline]
pub fn kissat_next_random64(rng: &mut Generator) -> u64 {
    *rng = rng.wrapping_mul(6364136223846793005u64);
    *rng = rng.wrapping_add(1442695040888963407u64);
    *rng
}

/// `kissat_next_random32`.
#[inline]
pub fn kissat_next_random32(rng: &mut Generator) -> u32 {
    (kissat_next_random64(rng) >> 32) as u32
}

/// `kissat_pick_random` (picks from `[l, r)`).
#[inline]
pub fn kissat_pick_random(rng: &mut Generator, l: u32, r: u32) -> u32 {
    debug_assert!(l <= r);
    if l == r {
        return l;
    }
    let delta = r - l;
    let tmp = kissat_next_random32(rng);
    let fraction = tmp as f64 / 4294967296.0;
    debug_assert!(0.0 <= fraction);
    debug_assert!(fraction < 1.0);
    let scaled = (delta as f64 * fraction) as u32;
    debug_assert!(scaled < delta);
    let res = l + scaled;
    debug_assert!(l <= res);
    debug_assert!(res < r);
    res
}

/// `kissat_pick_bool`.
#[inline]
pub fn kissat_pick_bool(rng: &mut Generator) -> bool {
    kissat_pick_random(rng, 0, 2) != 0
}

/// `kissat_pick_double`.
#[inline]
pub fn kissat_pick_double(rng: &mut Generator) -> f64 {
    kissat_next_random32(rng) as f64 / 4294967296.0
}

/*------------------------------------------------------------------------*/
// kitten.c

type Value = i8;

const INVALID: u32 = u32::MAX;
#[allow(dead_code)]
const MAX_VARS: u32 = (1u32 << 31) - 1;

const CORE_FLAG: u32 = 1;
const LEARNED_FLAG: u32 = 2;

/// Enables the (expensive) queue consistency checks (`CHECK_KITTEN`).
const CHECK_KITTEN: bool = false;

/// Offsets of the header fields of a `klause` in the arena.
const AUX: usize = 0;
const SIZE: usize = 1;
const FLAGS: usize = 2;
const LITS: usize = 3;

/// `struct kar`.
#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
struct Kar {
    level: u32,
    reason: u32,
}

/// `struct kink`.
#[derive(Clone, Copy, Default, Debug)]
struct Kink {
    next: u32,
    prev: u32,
    stamp: u64,
}

/// `struct statistics`.
#[derive(Clone, Copy, Default, Debug)]
pub struct KittenStatistics {
    pub learned: u64,
    pub original: u64,
    pub kitten_flip: u64,
    pub kitten_flipped: u64,
    pub kitten_sat: u64,
    pub kitten_solved: u64,
    pub kitten_conflicts: u64,
    pub kitten_decisions: u64,
    pub kitten_propagations: u64,
    pub kitten_ticks: u64,
    pub kitten_unknown: u64,
    pub kitten_unsat: u64,
}

/// `struct kimits`.
#[derive(Clone, Copy, Default, Debug)]
struct Kimits {
    ticks: u64,
}

/// Anonymous `queue` struct.
#[derive(Clone, Copy, Default, Debug)]
struct KQueue {
    first: u32,
    last: u32,
    stamp: u64,
    search: u32,
}

/// `struct kitten` (opaque in `kitten.h`).
pub struct Kitten {
    // First zero initialized field in 'clear_kitten' is 'status'.
    status: i32,

    #[cfg(feature = "logging")]
    logging: bool,
    antecedents: bool,
    learned: bool,

    level: u32,
    propagated: u32,
    unassigned: u32,
    inconsistent: u32,
    failing: u32,

    generator: u64,

    lits: usize,
    evars: usize,

    end_original_ref: usize,

    queue: KQueue,

    // The 'size' field below is the first not zero reinitialized field
    // by 'memset' in 'clear_kitten'.
    size: usize,
    esize: usize,

    vars: Vec<Kar>,
    links: Vec<Kink>,
    marks: Vec<Value>,
    values: Vec<Value>,
    failed: Vec<bool>,
    phases: Vec<u8>,
    import: Vec<u32>,
    watches: Vec<Vec<u32>>,

    analyzed: Vec<u32>,
    assumptions: Vec<u32>,
    core: Vec<u32>,
    #[allow(dead_code)]
    rcore: Vec<u32>,
    eclause: Vec<u32>,
    export: Vec<u32>,
    klause: Vec<u32>,
    klauses: Vec<u32>,
    resolved: Vec<u32>,
    trail: Vec<u32>,
    units: Vec<u32>,
    prime: [Vec<u32>; 2],

    limits: Kimits,
    terminator: Option<KittenTerminator>,
    terminator_data: *mut libc::c_void,
    clause: Vec<u32>,
    initialized: u64,
    statistics: KittenStatistics,
}

/*------------------------------------------------------------------------*/

fn die(args: std::fmt::Arguments<'_>) -> ! {
    fputs("kitten: error: ", c_stderr());
    crate::message::cfprint(c_stderr(), args);
    fputc(b'\n' as i32, c_stderr());
    std::process::exit(1);
}

fn invalid_api_usage(fun: &str, args: std::fmt::Arguments<'_>) -> ! {
    crate::cfprintf!(c_stderr(), "kitten: fatal error: invalid API usage in '{}': ", fun);
    crate::message::cfprint(c_stderr(), args);
    fputc(b'\n' as i32, c_stderr());
    fflush(c_stderr());
    // SAFETY: 'abort' never returns.
    unsafe { libc::abort() }
}

macro_rules! invalid_api_usage {
    ($fun:expr, $($arg:tt)*) => {
        invalid_api_usage($fun, format_args!($($arg)*))
    };
}

/// `REQUIRE_STATUS (EXPECTED)` (`REQUIRE_INITIALIZED` is implied by the
/// reference argument).
macro_rules! require_status {
    ($kitten:expr, $fun:expr, $expected:expr) => {
        if $kitten.status != ($expected) {
            invalid_api_usage!(
                $fun,
                "invalid status '{}' (expected '{}')",
                status_to_string($kitten.status),
                status_to_string($expected)
            );
        }
    };
}

/*------------------------------------------------------------------------*/
// Logging.

#[cfg(feature = "logging")]
macro_rules! klog {
    ($kitten:expr, $($arg:tt)*) => {
        if $kitten.logging {
            log_basic(&*$kitten, format_args!($($arg)*));
        }
    };
}

#[cfg(not(feature = "logging"))]
macro_rules! klog {
    ($kitten:expr, $($arg:tt)*) => {};
}

#[cfg(feature = "logging")]
macro_rules! rog {
    ($kitten:expr, $ref:expr, $($arg:tt)*) => {
        if $kitten.logging {
            log_reference(&*$kitten, $ref, format_args!($($arg)*));
        }
    };
}

#[cfg(not(feature = "logging"))]
macro_rules! rog {
    ($kitten:expr, $ref:expr, $($arg:tt)*) => {};
}

#[cfg(feature = "logging")]
macro_rules! loglits {
    ($kitten:expr, $lits:expr, $($arg:tt)*) => {
        if $kitten.logging {
            log_literals(&*$kitten, $lits, format_args!($($arg)*));
        }
    };
}

#[cfg(not(feature = "logging"))]
macro_rules! loglits {
    ($kitten:expr, $lits:expr, $($arg:tt)*) => {};
}

#[cfg(feature = "logging")]
fn log_basic(kitten: &Kitten, args: std::fmt::Arguments<'_>) {
    debug_assert!(kitten.logging);
    crate::cprintf!("c KITTEN {} ", kitten.level);
    crate::message::cprint(args);
    fputc(b'\n' as i32, c_stdout());
    fflush(c_stdout());
}

#[cfg(feature = "logging")]
fn log_reference(kitten: &Kitten, r: u32, args: std::fmt::Arguments<'_>) {
    let c = r as usize;
    debug_assert!(c < kitten.klauses.len());
    debug_assert!(kitten.logging);
    crate::cprintf!("c KITTEN {} ", kitten.level);
    crate::message::cprint(args);
    let aux = kitten.klauses[c + AUX];
    if is_learned_klause(kitten, r) {
        fputs(" learned", c_stdout());
        if aux != 0 {
            crate::cprintf!("[{}]", aux);
        }
    } else {
        fputs(" original", c_stdout());
        if aux != INVALID {
            crate::cprintf!("[{}]", aux);
        }
    }
    let size = kitten.klauses[c + SIZE];
    crate::cprintf!(" size {} clause[{}]", size, r);
    // 'kitten_shrink_to_clausal_core' in C logs clauses at their
    // destination before moving them there, thus reading stale data
    // (and out of bounds, which is undefined behaviour in C).  We only
    // avoid panicking in that case (otherwise identical output).
    for i in 0..size as usize {
        let Some(&lit) = kitten.klauses.get(c + LITS + i) else {
            break;
        };
        crate::cprintf!(" {}", lit);
        let value = kitten.values.get(lit as usize).copied().unwrap_or(0);
        if value != 0 {
            crate::cprintf!("@{}={}", kitten.vars[(lit / 2) as usize].level, value as i32);
        }
    }
    fputc(b'\n' as i32, c_stdout());
    fflush(c_stdout());
}

#[cfg(feature = "logging")]
fn log_literals(kitten: &Kitten, lits: &[u32], args: std::fmt::Arguments<'_>) {
    debug_assert!(kitten.logging);
    crate::cprintf!("c KITTEN {} ", kitten.level);
    crate::message::cprint(args);
    for &lit in lits {
        crate::cprintf!(" {}", lit);
        let value = kitten.values[lit as usize];
        if value != 0 {
            crate::cprintf!("@{}={}", kitten.vars[(lit / 2) as usize].level, value as i32);
        }
    }
    fputc(b'\n' as i32, c_stdout());
    fflush(c_stdout());
}

/*------------------------------------------------------------------------*/
// Clause arena helpers.

#[inline]
fn klause_size(kitten: &Kitten, r: u32) -> u32 {
    kitten.klauses[r as usize + SIZE]
}

#[inline]
fn klause_aux(kitten: &Kitten, r: u32) -> u32 {
    kitten.klauses[r as usize + AUX]
}

#[inline]
fn klause_lit(kitten: &Kitten, r: u32, i: usize) -> u32 {
    kitten.klauses[r as usize + LITS + i]
}

#[inline]
fn is_core_klause(kitten: &Kitten, r: u32) -> bool {
    kitten.klauses[r as usize + FLAGS] & CORE_FLAG != 0
}

#[inline]
fn is_learned_klause(kitten: &Kitten, r: u32) -> bool {
    kitten.klauses[r as usize + FLAGS] & LEARNED_FLAG != 0
}

#[inline]
fn set_core_klause(kitten: &mut Kitten, r: u32) {
    kitten.klauses[r as usize + FLAGS] |= CORE_FLAG;
}

#[inline]
fn unset_core_klause(kitten: &mut Kitten, r: u32) {
    kitten.klauses[r as usize + FLAGS] &= !CORE_FLAG;
}

/// `dereference_klause` only checks the reference (the arena is indexed
/// directly).
#[inline]
fn check_reference(kitten: &Kitten, r: u32) {
    debug_assert!((r as usize) < kitten.klauses.len());
    let _ = (kitten, r);
}

/// Start of the antecedents of a learned clause (`antecedents (c)`).
#[inline]
fn antecedents(kitten: &Kitten, r: u32) -> usize {
    debug_assert!(is_learned_klause(kitten, r));
    r as usize + LITS + klause_size(kitten, r) as usize
}

/// `begin_klauses`.
#[inline]
fn begin_klauses(_kitten: &Kitten) -> usize {
    0
}

/// `end_original_klauses`.
#[inline]
fn end_original_klauses(kitten: &Kitten) -> usize {
    kitten.end_original_ref
}

/// `end_klauses`.
#[inline]
fn end_klauses(kitten: &Kitten) -> usize {
    kitten.klauses.len()
}

/// `next_klause`.
#[inline]
fn next_klause(kitten: &Kitten, c: usize) -> usize {
    debug_assert!(begin_klauses(kitten) <= c);
    debug_assert!(c < end_klauses(kitten));
    let r = c as u32;
    let mut res = c + LITS + klause_size(kitten, r) as usize;
    if kitten.antecedents && is_learned_klause(kitten, r) {
        res += klause_aux(kitten, r) as usize;
    }
    res
}

/*------------------------------------------------------------------------*/

fn check_queue(kitten: &Kitten) {
    if !CHECK_KITTEN {
        return;
    }
    let vars = (kitten.lits / 2) as u32;
    let mut found = 0u32;
    let mut prev = INVALID;
    let links = &kitten.links;
    let mut stamp = 0u64;
    let mut idx = kitten.queue.first;
    while idx != INVALID {
        let link = &links[idx as usize];
        assert_eq!(link.prev, prev);
        assert!(found == 0 || stamp < link.stamp);
        assert!(link.stamp < kitten.queue.stamp);
        stamp = link.stamp;
        let next = link.next;
        prev = idx;
        found += 1;
        idx = next;
    }
    assert_eq!(found, vars);
    let mut next = INVALID;
    found = 0;
    let mut idx = kitten.queue.last;
    while idx != INVALID {
        let link = &links[idx as usize];
        assert_eq!(link.next, next);
        let prev = link.prev;
        next = idx;
        found += 1;
        idx = prev;
    }
    assert_eq!(found, vars);
    let values = &kitten.values;
    let mut first = true;
    let mut idx = kitten.queue.search;
    while idx != INVALID {
        let link = &links[idx as usize];
        let next = link.next;
        let lit = 2 * idx;
        assert!(first || values[lit as usize] != 0);
        first = false;
        idx = next;
    }
}

fn update_search(kitten: &mut Kitten, idx: u32) {
    if kitten.queue.search == idx {
        return;
    }
    kitten.queue.search = idx;
    klog!(kitten, "search updated to {} stamped {}", idx, kitten.links[idx as usize].stamp);
}

fn enqueue(kitten: &mut Kitten, idx: u32) {
    klog!(kitten, "enqueue {}", idx);
    let last = kitten.queue.last;
    if last == INVALID {
        kitten.queue.first = idx;
    } else {
        kitten.links[last as usize].next = idx;
    }
    let stamp = kitten.queue.stamp;
    kitten.queue.stamp += 1;
    let l = &mut kitten.links[idx as usize];
    l.prev = last;
    l.next = INVALID;
    kitten.queue.last = idx;
    l.stamp = stamp;
    klog!(kitten, "stamp {}", kitten.links[idx as usize].stamp);
}

fn dequeue(kitten: &mut Kitten, idx: u32) {
    klog!(kitten, "dequeue {}", idx);
    let l = kitten.links[idx as usize];
    let prev = l.prev;
    let next = l.next;
    if prev == INVALID {
        kitten.queue.first = next;
    } else {
        kitten.links[prev as usize].next = next;
    }
    if next == INVALID {
        kitten.queue.last = prev;
    } else {
        kitten.links[next as usize].prev = prev;
    }
}

fn init_queue(kitten: &mut Kitten, old_vars: usize, new_vars: usize) {
    for idx in old_vars..new_vars {
        debug_assert!(kitten.values[2 * idx] == 0);
        debug_assert!(kitten.unassigned < u32::MAX);
        kitten.unassigned += 1;
        enqueue(kitten, idx as u32);
    }
    klog!(kitten, "initialized decision queue from {} to {}", old_vars, new_vars);
    let last = kitten.queue.last;
    update_search(kitten, last);
    check_queue(kitten);
}

fn initialize_kitten(kitten: &mut Kitten) {
    kitten.queue.first = INVALID;
    kitten.queue.last = INVALID;
    kitten.inconsistent = INVALID;
    kitten.failing = INVALID;
    kitten.queue.search = INVALID;
    kitten.terminator = None;
    kitten.terminator_data = std::ptr::null_mut();
    kitten.limits.ticks = u64::MAX;
    kitten.generator = kitten.initialized;
    kitten.initialized += 1;
}

fn clear_kitten(kitten: &mut Kitten) {
    // 'memset' of all fields from 'status' up to (excluding) 'size'.
    kitten.status = 0;
    #[cfg(feature = "logging")]
    {
        kitten.logging = false;
    }
    kitten.antecedents = false;
    kitten.learned = false;
    kitten.level = 0;
    kitten.propagated = 0;
    kitten.unassigned = 0;
    kitten.inconsistent = 0;
    kitten.failing = 0;
    kitten.generator = 0;
    kitten.lits = 0;
    kitten.evars = 0;
    kitten.end_original_ref = 0;
    kitten.queue = KQueue::default();
    kitten.statistics = KittenStatistics::default();
    initialize_kitten(kitten);
}

/// `RESIZE1` / `RESIZE2`: allocate `new_len` zeroed entries and copy the
/// first `copy` entries of the old array.
fn resize_array<T: Default + Clone>(v: &mut Vec<T>, new_len: usize, copy: usize) {
    let mut new_vec = vec![T::default(); new_len];
    let copy = copy.min(v.len());
    new_vec[..copy].clone_from_slice(&v[..copy]);
    *v = new_vec;
}

fn resize_watches(v: &mut Vec<Vec<u32>>, new_len: usize, copy: usize) {
    let mut new_vec: Vec<Vec<u32>> = Vec::with_capacity(new_len);
    let copy = copy.min(v.len());
    for w in v.drain(..copy) {
        new_vec.push(w);
    }
    new_vec.resize_with(new_len, Vec::new);
    *v = new_vec;
}

fn enlarge_internal(kitten: &mut Kitten, lit: usize) {
    let new_lits = (lit | 1) + 1;
    let old_lits = kitten.lits;
    debug_assert!(old_lits <= lit);
    debug_assert!(old_lits < new_lits);
    debug_assert!((lit ^ 1) < new_lits);
    debug_assert!(lit < new_lits);
    let old_size = kitten.size;
    let new_vars = (new_lits / 2) as u32;
    let old_vars = (old_lits / 2) as u32;
    if old_size < new_lits {
        let mut new_size = if old_size != 0 { 2 * old_size } else { 2 };
        while new_size <= lit {
            new_size *= 2;
        }
        klog!(
            kitten,
            "internal literals resized to {} from {} (requested {})",
            new_size,
            old_size,
            new_lits
        );

        let ov = old_vars as usize;
        resize_array(&mut kitten.marks, new_size / 2, ov);
        resize_array(&mut kitten.phases, new_size / 2, ov);
        resize_array(&mut kitten.values, new_size, old_lits);
        resize_array(&mut kitten.failed, new_size, old_lits);
        resize_array(&mut kitten.vars, new_size / 2, ov);
        resize_array(&mut kitten.links, new_size / 2, ov);
        resize_watches(&mut kitten.watches, new_size, old_lits);

        kitten.size = new_size;
    }
    kitten.lits = new_lits;
    init_queue(kitten, old_vars as usize, new_vars as usize);
    klog!(kitten, "internal literals activated until {} literals", new_lits);
}

fn status_to_string(status: i32) -> &'static str {
    match status {
        10 => "formula satisfied",
        11 => "formula satisfied and prime implicant computed",
        20 => "formula inconsistent",
        21 => "formula inconsistent and core computed",
        _ => {
            debug_assert!(status == 0);
            "formula unsolved"
        }
    }
}

#[allow(unused_macros)]
macro_rules! update_status {
    ($kitten:expr, $status:expr) => {{
        let new_status: i32 = $status;
        if $kitten.status != new_status {
            klog!(
                $kitten,
                "updating status from '{}' to '{}'",
                status_to_string($kitten.status),
                status_to_string(new_status)
            );
        } else {
            klog!($kitten, "keeping status at '{}'", status_to_string(new_status));
        }
        $kitten.status = new_status;
    }};
}

pub fn kitten_init() -> Box<Kitten> {
    let mut kitten = Box::new(Kitten {
        status: 0,
        #[cfg(feature = "logging")]
        logging: false,
        antecedents: false,
        learned: false,
        level: 0,
        propagated: 0,
        unassigned: 0,
        inconsistent: 0,
        failing: 0,
        generator: 0,
        lits: 0,
        evars: 0,
        end_original_ref: 0,
        queue: KQueue::default(),
        size: 0,
        esize: 0,
        vars: Vec::new(),
        links: Vec::new(),
        marks: Vec::new(),
        values: Vec::new(),
        failed: Vec::new(),
        phases: Vec::new(),
        import: Vec::new(),
        watches: Vec::new(),
        analyzed: Vec::new(),
        assumptions: Vec::new(),
        core: Vec::new(),
        rcore: Vec::new(),
        eclause: Vec::new(),
        export: Vec::new(),
        klause: Vec::new(),
        klauses: Vec::new(),
        resolved: Vec::new(),
        trail: Vec::new(),
        units: Vec::new(),
        prime: [Vec::new(), Vec::new()],
        limits: Kimits::default(),
        terminator: None,
        terminator_data: std::ptr::null_mut(),
        clause: Vec::new(),
        initialized: 0,
        statistics: KittenStatistics::default(),
    });
    initialize_kitten(&mut kitten);
    kitten
}

#[cfg(feature = "logging")]
pub fn kitten_set_logging(kitten: &mut Kitten) {
    kitten.logging = true;
}

pub fn kitten_track_antecedents(kitten: &mut Kitten) {
    require_status!(kitten, "kitten_track_antecedents", 0);

    if kitten.learned {
        invalid_api_usage!("kitten_track_antecedents", "can not start tracking antecedents after learning");
    }

    klog!(kitten, "enabling antecedents tracking");
    kitten.antecedents = true;
}

pub fn kitten_randomize_phases(kitten: &mut Kitten) {
    klog!(kitten, "randomizing phases");

    let vars = (kitten.size / 2) as u32;

    let mut random = kissat_next_random64(&mut kitten.generator);

    let mut i = 0u32;
    let rest = vars & !63u32;

    let phases = &mut kitten.phases;
    while i != rest {
        // 'uint64_t *p = (uint64_t *) (phases + i)' on a little endian
        // machine: byte 'k' of 'p[j]' is bit '8 * k + j' of 'random'.
        for j in 0..8u32 {
            let word = (random >> j) & 0x0101010101010101u64;
            for k in 0..8u32 {
                phases[(i + 8 * j + k) as usize] = ((word >> (8 * k)) & 0xff) as u8;
            }
        }
        random = kissat_next_random64(&mut kitten.generator);
        i += 64;
    }

    let mut shift = 0u32;
    while i != vars {
        phases[i as usize] = ((random >> shift) & 1) as u8;
        i += 1;
        shift += 1;
    }
}

pub fn kitten_flip_phases(kitten: &mut Kitten) {
    klog!(kitten, "flipping phases");

    let vars = kitten.size / 2;
    for i in 0..vars {
        kitten.phases[i] ^= 1;
    }
}

pub fn kitten_no_ticks_limit(kitten: &mut Kitten) {
    klog!(kitten, "forcing no ticks limit");
    kitten.limits.ticks = u64::MAX;
}

pub fn kitten_current_ticks(kitten: &mut Kitten) -> u64 {
    kitten.statistics.kitten_ticks
}

pub fn kitten_set_ticks_limit(kitten: &mut Kitten, delta: u64) {
    let current = kitten.statistics.kitten_ticks;
    let limit;
    if u64::MAX - delta <= current {
        klog!(kitten, "forcing unlimited ticks limit");
        limit = u64::MAX;
    } else {
        limit = current + delta;
        klog!(kitten, "new limit of {} ticks after {}", limit, delta);
    }

    kitten.limits.ticks = limit;
}

pub fn kitten_no_terminator(kitten: &mut Kitten) {
    klog!(kitten, "removing terminator");
    kitten.terminator = None;
    kitten.terminator_data = std::ptr::null_mut();
}

pub fn kitten_set_terminator(kitten: &mut Kitten, data: *mut libc::c_void, terminator: KittenTerminator) {
    klog!(kitten, "setting terminator");
    kitten.terminator = Some(terminator);
    kitten.terminator_data = data;
}

#[inline]
fn terminated(kitten: &Kitten) -> bool {
    match kitten.terminator {
        Some(t) => t(kitten.terminator_data) != 0,
        None => false,
    }
}

fn shuffle_unsigned_array(generator: &mut Generator, a: &mut [u32]) {
    let size = a.len();
    for i in 0..size {
        let j = kissat_pick_random(generator, 0, i as u32) as usize;
        if j == i {
            continue;
        }
        let first = a[i];
        let second = a[j];
        a[i] = second;
        a[j] = first;
    }
}

fn shuffle_katches(kitten: &mut Kitten) {
    klog!(kitten, "shuffling watch lists");
    for lit in 0..kitten.lits {
        shuffle_unsigned_array(&mut kitten.generator, &mut kitten.watches[lit]);
    }
}

fn shuffle_queue(kitten: &mut Kitten) {
    klog!(kitten, "shuffling variable decision order");

    let vars = (kitten.lits / 2) as u32;
    for _ in 0..vars {
        let idx = kissat_pick_random(&mut kitten.generator, 0, vars);
        dequeue(kitten, idx);
        enqueue(kitten, idx);
    }
    let last = kitten.queue.last;
    update_search(kitten, last);
}

fn shuffle_units(kitten: &mut Kitten) {
    klog!(kitten, "shuffling units");
    shuffle_unsigned_array(&mut kitten.generator, &mut kitten.units);
}

pub fn kitten_shuffle_clauses(kitten: &mut Kitten) {
    require_status!(kitten, "kitten_shuffle_clauses", 0);
    shuffle_queue(kitten);
    shuffle_katches(kitten);
    shuffle_units(kitten);
}

#[inline]
fn watch_klause(kitten: &mut Kitten, lit: u32, r: u32) {
    rog!(kitten, r, "watching {} in", lit);
    debug_assert!((lit as usize) < kitten.lits);
    kitten.watches[lit as usize].push(r);
}

#[inline]
fn connect_new_klause(kitten: &mut Kitten, r: u32) {
    rog!(kitten, r, "new");

    check_reference(kitten, r);
    let size = klause_size(kitten, r);

    if size == 0 {
        if kitten.inconsistent == INVALID {
            rog!(kitten, r, "registering inconsistent empty");
            kitten.inconsistent = r;
        } else {
            rog!(kitten, r, "ignoring inconsistent empty");
        }
    } else if size == 1 {
        rog!(kitten, r, "watching unit");
        kitten.units.push(r);
    } else {
        let l0 = klause_lit(kitten, r, 0);
        let l1 = klause_lit(kitten, r, 1);
        watch_klause(kitten, l0, r);
        watch_klause(kitten, l1, r);
    }
}

fn new_reference(kitten: &mut Kitten) -> u32 {
    let r = kitten.klauses.len();
    if r >= INVALID as usize {
        die(format_args!("maximum number of literals exhausted"));
    }
    let res = r as u32;
    debug_assert!(res != INVALID);
    debug_assert!(kitten.statistics.kitten_ticks < u64::MAX);
    kitten.statistics.kitten_ticks += 1;
    res
}

fn new_original_klause(kitten: &mut Kitten, id: u32) {
    let res = new_reference(kitten);
    let size = kitten.klause.len() as u32;
    kitten.klauses.push(id);
    kitten.klauses.push(size);
    kitten.klauses.push(0);
    let Kitten { klauses, klause, .. } = &mut *kitten;
    klauses.extend_from_slice(klause);
    connect_new_klause(kitten, res);
    kitten.end_original_ref = kitten.klauses.len();
    kitten.statistics.original += 1;
}

fn enlarge_external(kitten: &mut Kitten, eidx: usize) {
    let old_size = kitten.esize;
    let old_evars = kitten.evars as u32;
    debug_assert!(old_evars as usize <= eidx);
    let new_evars = (eidx + 1) as u32;
    if old_size <= eidx {
        let mut new_size = if old_size != 0 { 2 * old_size } else { 1 };
        while new_size <= eidx {
            new_size *= 2;
        }
        klog!(
            kitten,
            "external resizing to {} variables from {} (requested {})",
            new_size,
            old_size,
            new_evars
        );
        resize_array(&mut kitten.import, new_size, old_evars as usize);
        kitten.esize = new_size;
    }
    kitten.evars = new_evars as usize;
    klog!(kitten, "external variables enlarged to {}", new_evars);
}

fn import_literal(kitten: &mut Kitten, elit: u32) -> u32 {
    let eidx = elit / 2;
    if eidx as usize >= kitten.evars {
        enlarge_external(kitten, eidx as usize);
    }

    let mut iidx = kitten.import[eidx as usize];
    if iidx == 0 {
        iidx = kitten.export.len() as u32;
        kitten.export.push(eidx);
        kitten.import[eidx as usize] = iidx + 1;
    } else {
        iidx -= 1;
    }
    let ilit = 2 * iidx + (elit & 1);
    klog!(kitten, "imported external literal {} as internal literal {}", elit, ilit);
    if ilit as usize >= kitten.lits {
        enlarge_internal(kitten, ilit as usize);
    }
    ilit
}

#[inline]
fn export_literal(kitten: &Kitten, ilit: u32) -> u32 {
    let iidx = ilit / 2;
    debug_assert!((iidx as usize) < kitten.export.len());
    let eidx = kitten.export[iidx as usize];
    2 * eidx + (ilit & 1)
}

fn new_learned_klause(kitten: &mut Kitten) -> u32 {
    let res = new_reference(kitten);
    let size = kitten.klause.len();
    debug_assert!(size <= u32::MAX as usize);
    let aux = if kitten.antecedents { kitten.resolved.len() } else { 0 };
    debug_assert!(aux <= u32::MAX as usize);
    kitten.klauses.push(aux as u32);
    kitten.klauses.push(size as u32);
    kitten.klauses.push(LEARNED_FLAG);
    {
        let Kitten { klauses, klause, resolved, .. } = &mut *kitten;
        klauses.extend_from_slice(klause);
        if aux != 0 {
            klauses.extend_from_slice(resolved);
        }
    }
    connect_new_klause(kitten, res);
    kitten.learned = true;
    kitten.statistics.learned += 1;
    res
}

pub fn kitten_clear(kitten: &mut Kitten) {
    klog!(kitten, "clear kitten of size {}", kitten.size);

    debug_assert!(kitten.analyzed.is_empty());
    debug_assert!(kitten.eclause.is_empty());
    debug_assert!(kitten.resolved.is_empty());

    kitten.assumptions.clear();
    kitten.core.clear();
    kitten.klause.clear();
    kitten.klauses.clear();
    kitten.trail.clear();
    kitten.units.clear();
    kitten.clause.clear();
    kitten.prime[0].clear();
    kitten.prime[1].clear();

    for kit in 0..kitten.lits {
        kitten.watches[kit].clear();
    }

    while let Some(eidx) = kitten.export.pop() {
        kitten.import[eidx as usize] = 0;
    }

    let lits = kitten.size;
    let vars = lits / 2;

    #[cfg(debug_assertions)]
    for i in 0..vars {
        debug_assert!(kitten.marks[i] == 0);
    }

    for p in kitten.phases[..vars].iter_mut() {
        *p = 0;
    }
    for v in kitten.values[..lits].iter_mut() {
        *v = 0;
    }
    for f in kitten.failed[..lits].iter_mut() {
        *f = false;
    }
    // 'memset (kitten->vars, 0, vars)' only clears the first 'vars'
    // *bytes* of the 'kar' array (as in C).
    if !kitten.vars.is_empty() {
        debug_assert!(vars <= kitten.vars.len() * std::mem::size_of::<Kar>());
        // SAFETY: 'Kar' is 'repr(C)' plain old data of two 'u32' and the
        // array has 'vars' entries of 8 bytes, thus at least 'vars' bytes.
        unsafe {
            std::ptr::write_bytes(kitten.vars.as_mut_ptr() as *mut u8, 0, vars);
        }
    }

    clear_kitten(kitten);
}

pub fn kitten_release(kitten: Box<Kitten>) {
    drop(kitten);
}

#[inline]
fn move_to_front(kitten: &mut Kitten, idx: u32) {
    if idx == kitten.queue.last {
        return;
    }
    klog!(kitten, "move to front variable {}", idx);
    dequeue(kitten, idx);
    enqueue(kitten, idx);
    debug_assert!(kitten.values[2 * idx as usize] != 0);
}

#[inline]
fn assign(kitten: &mut Kitten, lit: u32, mut reason: u32) {
    #[cfg(feature = "logging")]
    {
        if reason == INVALID {
            klog!(kitten, "assign {} as decision", lit);
        } else {
            rog!(kitten, reason, "assign {} reason", lit);
        }
    }
    let not_lit = lit ^ 1;
    debug_assert!(kitten.values[lit as usize] == 0);
    debug_assert!(kitten.values[not_lit as usize] == 0);
    kitten.values[lit as usize] = 1;
    kitten.values[not_lit as usize] = -1;
    let idx = (lit / 2) as usize;
    let sign = lit & 1;
    kitten.phases[idx] = sign as u8;
    kitten.trail.push(lit);
    let level = kitten.level;
    kitten.vars[idx].level = level;
    if level == 0 {
        debug_assert!(reason != INVALID);
        check_reference(kitten, reason);
        let size = klause_size(kitten, reason);
        if size > 1 {
            if kitten.antecedents {
                kitten.resolved.push(reason);
                for i in 0..size as usize {
                    let other = klause_lit(kitten, reason, i);
                    if other != lit {
                        let other_idx = (other / 2) as usize;
                        let other_ref = kitten.vars[other_idx].reason;
                        debug_assert!(other_ref != INVALID);
                        kitten.resolved.push(other_ref);
                    }
                }
            }
            kitten.klause.push(lit);
            reason = new_learned_klause(kitten);
            kitten.resolved.clear();
            kitten.klause.clear();
        }
    }
    kitten.vars[idx].reason = reason;
    debug_assert!(kitten.unassigned != 0);
    kitten.unassigned -= 1;
}

#[inline]
fn propagate_literal(kitten: &mut Kitten, lit: u32) -> u32 {
    klog!(kitten, "propagating {}", lit);
    debug_assert!(kitten.values[lit as usize] > 0);
    let not_lit = lit ^ 1;
    let nl = not_lit as usize;
    let mut conflict = INVALID;
    let end_watches = kitten.watches[nl].len();
    let mut q = 0usize;
    let mut p = 0usize;
    let mut ticks: u64 = (((end_watches * std::mem::size_of::<u32>()) >> 7) + 1) as u64;
    while p != end_watches {
        let r = kitten.watches[nl][p];
        kitten.watches[nl][q] = r;
        p += 1;
        q += 1;
        check_reference(kitten, r);
        let size = klause_size(kitten, r) as usize;
        debug_assert!(size > 1);
        let lits = r as usize + LITS;
        let other = kitten.klauses[lits] ^ kitten.klauses[lits + 1] ^ not_lit;
        let other_value = kitten.values[other as usize];
        ticks += 1;
        if other_value > 0 {
            continue;
        }
        let mut replacement_value: Value = -1;
        let mut replacement = INVALID;
        let end_lits = lits + size;
        let mut rp = lits + 2;
        while rp != end_lits {
            replacement = kitten.klauses[rp];
            replacement_value = kitten.values[replacement as usize];
            if replacement_value >= 0 {
                break;
            }
            rp += 1;
        }
        if replacement_value >= 0 {
            debug_assert!(replacement != INVALID);
            rog!(kitten, r, "unwatching {} in", not_lit);
            kitten.klauses[lits] = other;
            kitten.klauses[lits + 1] = replacement;
            kitten.klauses[rp] = not_lit;
            watch_klause(kitten, replacement, r);
            q -= 1;
        } else if other_value < 0 {
            rog!(kitten, r, "conflict");
            debug_assert!(kitten.statistics.kitten_conflicts < u64::MAX);
            kitten.statistics.kitten_conflicts += 1;
            conflict = r;
            break;
        } else {
            debug_assert!(other_value == 0);
            assign(kitten, other, r);
        }
    }
    {
        let watches = &mut kitten.watches[nl];
        while p != end_watches {
            watches[q] = watches[p];
            q += 1;
            p += 1;
        }
        watches.truncate(q);
    }
    debug_assert!(kitten.statistics.kitten_ticks <= u64::MAX - ticks);
    kitten.statistics.kitten_ticks += ticks;
    conflict
}

#[inline]
fn propagate(kitten: &mut Kitten) -> u32 {
    debug_assert!(kitten.inconsistent == INVALID);
    let mut propagated: u32 = 0;
    let mut conflict = INVALID;
    while conflict == INVALID && (kitten.propagated as usize) < kitten.trail.len() {
        if terminated(kitten) {
            break;
        }
        let lit = kitten.trail[kitten.propagated as usize];
        conflict = propagate_literal(kitten, lit);
        kitten.propagated += 1;
        propagated += 1;
    }
    debug_assert!(kitten.statistics.kitten_propagations <= u64::MAX - propagated as u64);
    kitten.statistics.kitten_propagations += propagated as u64;
    conflict
}

fn bump(kitten: &mut Kitten) {
    for i in 0..kitten.analyzed.len() {
        let idx = kitten.analyzed[i];
        kitten.marks[idx as usize] = 0;
        move_to_front(kitten, idx);
    }
    check_queue(kitten);
}

#[inline]
fn unassign(kitten: &mut Kitten, lit: u32) {
    let not_lit = lit ^ 1;
    debug_assert!(kitten.values[lit as usize] != 0);
    debug_assert!(kitten.values[not_lit as usize] != 0);
    let idx = lit / 2;
    #[cfg(feature = "logging")]
    {
        kitten.level = kitten.vars[idx as usize].level;
        klog!(kitten, "unassign {}", lit);
    }
    kitten.values[lit as usize] = 0;
    kitten.values[not_lit as usize] = 0;
    debug_assert!((kitten.unassigned as usize) < kitten.lits / 2);
    kitten.unassigned += 1;
    let stamp = kitten.links[idx as usize].stamp;
    if stamp > kitten.links[kitten.queue.search as usize].stamp {
        update_search(kitten, idx);
    }
}

fn backtrack(kitten: &mut Kitten, jump: u32) {
    check_queue(kitten);
    debug_assert!(jump < kitten.level);
    klog!(
        kitten,
        "back{} to level {}",
        if kitten.level == jump + 1 { "tracking" } else { "jumping" },
        jump
    );
    while let Some(&lit) = kitten.trail.last() {
        let idx = (lit / 2) as usize;
        let level = kitten.vars[idx].level;
        if level == jump {
            break;
        }
        kitten.trail.pop();
        unassign(kitten, lit);
    }
    kitten.propagated = kitten.trail.len() as u32;
    kitten.level = jump;
    check_queue(kitten);
}

fn completely_backtrack_to_root_level(kitten: &mut Kitten) {
    check_queue(kitten);
    klog!(kitten, "completely backtracking to level 0");
    for i in 0..kitten.trail.len() {
        let lit = kitten.trail[i];
        debug_assert!(kitten.vars[(lit / 2) as usize].level != 0);
        unassign(kitten, lit);
    }
    kitten.trail.clear();
    for i in 0..kitten.units.len() {
        let r = kitten.units[i];
        check_reference(kitten, r);
        debug_assert!(klause_size(kitten, r) == 1);
        let unit = klause_lit(kitten, r, 0);
        let value = kitten.values[unit as usize];
        if value <= 0 {
            continue;
        }
        unassign(kitten, unit);
    }
    kitten.propagated = 0;
    kitten.level = 0;
    check_queue(kitten);
}

fn analyze(kitten: &mut Kitten, conflict: u32) {
    debug_assert!(kitten.level != 0);
    debug_assert!(kitten.inconsistent == INVALID);
    debug_assert!(kitten.analyzed.is_empty());
    debug_assert!(kitten.resolved.is_empty());
    debug_assert!(kitten.klause.is_empty());
    kitten.klause.push(INVALID);
    let mut reason = conflict;
    let level = kitten.level;
    let mut p = kitten.trail.len();
    let mut open: u32 = 0;
    let mut jump: u32 = 0;
    let mut size: u32 = 1;
    let mut uip: u32;
    loop {
        debug_assert!(reason != INVALID);
        check_reference(kitten, reason);
        rog!(kitten, reason, "analyzing");
        kitten.resolved.push(reason);
        let csize = klause_size(kitten, reason) as usize;
        for i in 0..csize {
            let mut lit = klause_lit(kitten, reason, i);
            let idx = (lit / 2) as usize;
            if kitten.marks[idx] != 0 {
                continue;
            }
            debug_assert!(kitten.values[lit as usize] < 0);
            klog!(kitten, "analyzed {}", lit);
            kitten.marks[idx] = 1;
            kitten.analyzed.push(idx as u32);
            let tmp = kitten.vars[idx].level;
            if tmp < level {
                if tmp > jump {
                    jump = tmp;
                    if size > 1 {
                        let other = kitten.klause[1];
                        kitten.klause[1] = lit;
                        lit = other;
                    }
                }
                kitten.klause.push(lit);
                size += 1;
            } else {
                open += 1;
            }
        }
        let mut idx;
        loop {
            debug_assert!(0 < p);
            p -= 1;
            uip = kitten.trail[p];
            idx = (uip / 2) as usize;
            if kitten.marks[idx] != 0 {
                break;
            }
        }
        debug_assert!(open != 0);
        open -= 1;
        if open == 0 {
            break;
        }
        reason = kitten.vars[idx].reason;
    }
    let not_uip = uip ^ 1;
    klog!(kitten, "first UIP {} jump level {} size {}", not_uip, jump, size);
    kitten.klause[0] = not_uip;
    bump(kitten);
    kitten.analyzed.clear();
    let learned_ref = new_learned_klause(kitten);
    kitten.resolved.clear();
    kitten.klause.clear();
    backtrack(kitten, jump);
    assign(kitten, not_uip, learned_ref);
}

fn failing(kitten: &mut Kitten) {
    debug_assert!(kitten.inconsistent == INVALID);
    debug_assert!(!kitten.assumptions.is_empty());
    debug_assert!(kitten.analyzed.is_empty());
    debug_assert!(kitten.resolved.is_empty());
    debug_assert!(kitten.klause.is_empty());
    klog!(kitten, "analyzing failing assumptions");
    let mut failed_clashing = INVALID;
    let mut first_failed = INVALID;
    let mut failed_unit = INVALID;
    for i in 0..kitten.assumptions.len() {
        let lit = kitten.assumptions[i];
        if kitten.values[lit as usize] >= 0 {
            continue;
        }
        if first_failed == INVALID {
            first_failed = lit;
        }
        let failed_idx = (lit / 2) as usize;
        let failed_var = kitten.vars[failed_idx];
        if failed_var.level == 0 {
            failed_unit = lit;
            break;
        }
        if failed_clashing == INVALID && failed_var.reason == INVALID {
            failed_clashing = lit;
        }
    }
    let failed = if failed_unit != INVALID {
        failed_unit
    } else if failed_clashing != INVALID {
        failed_clashing
    } else {
        first_failed
    };
    debug_assert!(failed != INVALID);
    let failed_idx = (failed / 2) as usize;
    let failed_reason = kitten.vars[failed_idx].reason;
    klog!(kitten, "first failed assumption {}", failed);
    kitten.failed[failed as usize] = true;

    if failed_unit != INVALID {
        debug_assert!(klause_size(kitten, failed_reason) == 1);
        klog!(kitten, "root-level falsified assumption {}", failed);
        kitten.failing = failed_reason;
        rog!(kitten, kitten.failing, "failing reason");
        return;
    }

    let not_failed = failed ^ 1;
    if failed_clashing != INVALID {
        klog!(kitten, "clashing with negated assumption {}", not_failed);
        kitten.failed[not_failed as usize] = true;
        debug_assert!(kitten.failing == INVALID);
        return;
    }

    debug_assert!(kitten.marks[failed_idx] == 0);
    kitten.marks[failed_idx] = 1;
    kitten.analyzed.push(failed_idx as u32);
    kitten.klause.push(not_failed);

    let mut work: Vec<u32> = Vec::new();

    loglits!(kitten, &kitten.trail, "trail");

    debug_assert!(!kitten.trail.is_empty());
    let mut p = kitten.trail.len();
    let mut open: u32 = 1;
    loop {
        if open == 0 {
            break;
        }
        open -= 1;
        let mut idx;
        loop {
            debug_assert!(0 < p);
            p -= 1;
            let uip = kitten.trail[p];
            idx = (uip / 2) as usize;
            if kitten.marks[idx] != 0 {
                break;
            }
        }

        let reason = kitten.vars[idx].reason;
        if reason == INVALID {
            let mut lit = 2 * idx as u32;
            if kitten.values[lit as usize] < 0 {
                lit ^= 1;
            }
            klog!(kitten, "failed assumption {}", lit);
            debug_assert!(!kitten.failed[lit as usize]);
            kitten.failed[lit as usize] = true;
            let not_lit = lit ^ 1;
            kitten.klause.push(not_lit);
        } else {
            rog!(kitten, reason, "analyzing");
            kitten.resolved.push(reason);
            check_reference(kitten, reason);
            let csize = klause_size(kitten, reason) as usize;
            for i in 0..csize {
                let other = klause_lit(kitten, reason, i);
                let other_idx = (other / 2) as usize;
                if kitten.marks[other_idx] != 0 {
                    continue;
                }
                debug_assert!(other_idx != idx);
                kitten.marks[other_idx] = 1;
                debug_assert!(kitten.values[other as usize] != 0);
                if kitten.vars[other_idx].level != 0 {
                    open += 1;
                } else {
                    work.push(other_idx as u32);
                }
                kitten.analyzed.push(other_idx as u32);

                klog!(kitten, "analyzing final literal {}", other ^ 1);
            }
        }
    }
    for next in 0..work.len() {
        let idx = work[next] as usize;
        let reason = kitten.vars[idx].reason;
        if reason == INVALID {
            let mut lit = 2 * idx as u32;
            if kitten.values[lit as usize] < 0 {
                lit ^= 1;
            }
            klog!(kitten, "failed assumption {}", lit);
            debug_assert!(!kitten.failed[lit as usize]);
            kitten.failed[lit as usize] = true;
            let not_lit = lit ^ 1;
            kitten.klause.push(not_lit);
        } else {
            rog!(kitten, reason, "analyzing unit");
            kitten.resolved.push(reason);
        }
    }

    for i in 0..kitten.analyzed.len() {
        let idx = kitten.analyzed[i] as usize;
        debug_assert!(kitten.marks[idx] != 0);
        kitten.marks[idx] = 0;
    }
    kitten.analyzed.clear();

    drop(work);

    let resolved = kitten.resolved.len();
    debug_assert!(resolved != 0);

    if resolved == 1 {
        kitten.failing = kitten.resolved[0];
        rog!(kitten, kitten.failing, "reusing as core");
    } else {
        kitten.failing = new_learned_klause(kitten);
        rog!(kitten, kitten.failing, "new core");
    }

    kitten.resolved.clear();
    kitten.klause.clear();
}

fn flush_trail(kitten: &mut Kitten) {
    klog!(kitten, "flushing {} root-level literals from trail", kitten.trail.len());
    debug_assert!(kitten.level == 0);
    kitten.propagated = 0;
    kitten.trail.clear();
}

fn decide(kitten: &mut Kitten) -> i32 {
    if kitten.level == 0 && !kitten.trail.is_empty() {
        flush_trail(kitten);
    }

    let mut decision = INVALID;
    let assumptions = kitten.assumptions.len();
    while (kitten.level as usize) < assumptions {
        let assumption = kitten.assumptions[kitten.level as usize];
        let value = kitten.values[assumption as usize];
        if value < 0 {
            klog!(kitten, "found failing assumption {}", assumption);
            failing(kitten);
            return 20;
        } else if value > 0 {
            kitten.level += 1;
            klog!(
                kitten,
                "pseudo decision level {} for already satisfied assumption {}",
                kitten.level,
                assumption
            );
        } else {
            decision = assumption;
            klog!(kitten, "using assumption {} as decision", decision);
            break;
        }
    }

    if kitten.unassigned == 0 {
        return 10;
    }

    if kitten.statistics.kitten_ticks >= kitten.limits.ticks {
        klog!(
            kitten,
            "ticks limit {} hit after {} ticks",
            kitten.limits.ticks,
            kitten.statistics.kitten_ticks
        );
        return -1;
    }

    if terminated(kitten) {
        klog!(kitten, "terminator requested termination");
        return -1;
    }

    if decision == INVALID {
        let mut idx = kitten.queue.search;
        loop {
            debug_assert!(idx != INVALID);
            if kitten.values[2 * idx as usize] == 0 {
                break;
            }
            idx = kitten.links[idx as usize].prev;
        }
        update_search(kitten, idx);
        let phase = kitten.phases[idx as usize] as u32;
        decision = 2 * idx + phase;
        klog!(kitten, "decision {} variable {} phase {}", decision, idx, phase);
    }
    debug_assert!(kitten.statistics.kitten_decisions < u64::MAX);
    kitten.statistics.kitten_decisions += 1;
    kitten.level += 1;
    assign(kitten, decision, INVALID);
    0
}

fn inconsistent(kitten: &mut Kitten, mut r: u32) {
    debug_assert!(r != INVALID);
    debug_assert!(kitten.inconsistent == INVALID);

    if !kitten.antecedents {
        kitten.inconsistent = r;
        rog!(kitten, r, "registering inconsistent virtually empty");
        return;
    }

    debug_assert!(kitten.analyzed.is_empty());
    debug_assert!(kitten.resolved.is_empty());

    let mut next = 0usize;

    loop {
        debug_assert!(r != INVALID);
        check_reference(kitten, r);
        rog!(kitten, r, "analyzing inconsistent");
        kitten.resolved.push(r);
        let csize = klause_size(kitten, r) as usize;
        for i in 0..csize {
            let lit = klause_lit(kitten, r, i);
            let idx = (lit / 2) as usize;
            debug_assert!(kitten.vars[idx].level == 0);
            if kitten.marks[idx] != 0 {
                continue;
            }
            debug_assert!(kitten.values[lit as usize] < 0);
            klog!(kitten, "analyzed {}", lit);
            kitten.marks[idx] = 1;
            kitten.analyzed.push(idx as u32);
        }
        if next == kitten.analyzed.len() {
            break;
        }
        let idx = kitten.analyzed[next] as usize;
        next += 1;
        debug_assert!(kitten.vars[idx].level == 0);
        r = kitten.vars[idx].reason;
    }
    debug_assert!(kitten.klause.is_empty());
    r = new_learned_klause(kitten);
    rog!(kitten, r, "registering final inconsistent empty");
    kitten.inconsistent = r;

    for i in 0..kitten.analyzed.len() {
        let idx = kitten.analyzed[i] as usize;
        kitten.marks[idx] = 0;
    }

    kitten.analyzed.clear();
    kitten.resolved.clear();
}

fn propagate_units(kitten: &mut Kitten) -> i32 {
    if kitten.inconsistent != INVALID {
        return 20;
    }

    if kitten.units.is_empty() {
        klog!(kitten, "no root level unit clauses");
        return 0;
    }

    klog!(kitten, "propagating {} root level unit clauses", kitten.units.len());

    let mut next = 0usize;
    while next < kitten.units.len() {
        let r = kitten.units[next];
        next += 1;
        debug_assert!(r != INVALID);
        check_reference(kitten, r);
        debug_assert!(klause_size(kitten, r) == 1);
        rog!(kitten, r, "propagating unit");
        let unit = klause_lit(kitten, r, 0);
        let value = kitten.values[unit as usize];
        if value > 0 {
            continue;
        }
        if value < 0 {
            inconsistent(kitten, r);
            return 20;
        }
        assign(kitten, unit, r);
    }
    let conflict = propagate(kitten);
    if conflict == INVALID {
        return 0;
    }
    inconsistent(kitten, conflict);
    20
}

/*------------------------------------------------------------------------*/

fn reset_core(kitten: &mut Kitten) {
    klog!(kitten, "resetting core clauses");
    let mut reset: usize = 0;
    let mut c = begin_klauses(kitten);
    let end = end_klauses(kitten);
    while c != end {
        if is_core_klause(kitten, c as u32) {
            unset_core_klause(kitten, c as u32);
            reset += 1;
        }
        c = next_klause(kitten, c);
    }
    klog!(kitten, "reset {} core clauses", reset);
    let _ = reset;
    kitten.core.clear();
}

fn reset_assumptions(kitten: &mut Kitten) {
    klog!(kitten, "reset {} assumptions", kitten.assumptions.len());
    while let Some(assumption) = kitten.assumptions.pop() {
        kitten.failed[assumption as usize] = false;
    }
    #[cfg(debug_assertions)]
    for i in 0..kitten.size {
        debug_assert!(!kitten.failed[i]);
    }
    kitten.assumptions.clear();
    if kitten.failing != INVALID {
        rog!(kitten, kitten.failing, "reset failed assumption reason");
        kitten.failing = INVALID;
    }
}

fn reset_incremental(kitten: &mut Kitten) {
    completely_backtrack_to_root_level(kitten);
    if !kitten.assumptions.is_empty() {
        reset_assumptions(kitten);
    } else {
        debug_assert!(kitten.failing == INVALID);
    }
    if kitten.status == 21 {
        reset_core(kitten);
    }
    update_status!(kitten, 0);
}

/*------------------------------------------------------------------------*/

fn flip_literal(kitten: &mut Kitten, mut lit: u32) -> bool {
    debug_assert!(kitten.statistics.kitten_flip < u64::MAX);
    kitten.statistics.kitten_flip += 1;
    if kitten.values[lit as usize] < 0 {
        lit ^= 1;
    }
    klog!(kitten, "trying to flip value of satisfied literal {}", lit);
    debug_assert!(kitten.values[lit as usize] > 0);
    let wl = lit as usize;
    let end_watches = kitten.watches[wl].len();
    let mut q = 0usize;
    let mut p = 0usize;
    let mut ticks: u64 = (((end_watches * std::mem::size_of::<u32>()) >> 7) + 1) as u64;
    let mut res = true;
    while p != end_watches {
        let r = kitten.watches[wl][p];
        kitten.watches[wl][q] = r;
        p += 1;
        q += 1;
        check_reference(kitten, r);
        let size = klause_size(kitten, r) as usize;
        let lits = r as usize + LITS;
        let other = kitten.klauses[lits] ^ kitten.klauses[lits + 1] ^ lit;
        let other_value = kitten.values[other as usize];
        ticks += 1;
        if other_value > 0 {
            continue;
        }
        let mut replacement_value: Value = -1;
        let mut replacement = INVALID;
        let end_lits = lits + size;
        let mut rp = lits + 2;
        while rp != end_lits {
            replacement = kitten.klauses[rp];
            debug_assert!(replacement != lit);
            replacement_value = kitten.values[replacement as usize];
            debug_assert!(replacement_value != 0);
            if replacement_value > 0 {
                break;
            }
            rp += 1;
        }
        if replacement_value > 0 {
            debug_assert!(replacement != INVALID);
            rog!(kitten, r, "unwatching {} in", lit);
            kitten.klauses[lits] = other;
            kitten.klauses[lits + 1] = replacement;
            kitten.klauses[rp] = lit;
            watch_klause(kitten, replacement, r);
            q -= 1;
        } else {
            debug_assert!(replacement_value < 0);
            rog!(kitten, r, "single satisfied");
            res = false;
            break;
        }
    }
    {
        let watches = &mut kitten.watches[wl];
        while p != end_watches {
            watches[q] = watches[p];
            q += 1;
            p += 1;
        }
        watches.truncate(q);
    }
    debug_assert!(kitten.statistics.kitten_ticks <= u64::MAX - ticks);
    kitten.statistics.kitten_ticks += ticks;
    if res {
        klog!(kitten, "flipping value of {}", lit);
        kitten.values[lit as usize] = -1;
        let not_lit = lit ^ 1;
        kitten.values[not_lit as usize] = 1;
        debug_assert!(kitten.statistics.kitten_flipped < u64::MAX);
        kitten.statistics.kitten_flipped += 1;
    } else {
        klog!(kitten, "failed to flip value of {}", lit);
    }
    res
}

/*------------------------------------------------------------------------*/

// this cadical specific clause addition avoids copying clauses multiple
// times just to convert literals to unsigned representation.
//
#[inline]
fn int2u(lit: i32) -> u32 {
    debug_assert!(lit != 0);
    let idx = lit.abs() - 1;
    (lit < 0) as u32 + 2u32 * (idx as u32)
}

pub fn kitten_assume(kitten: &mut Kitten, elit: u32) {
    if kitten.status != 0 {
        reset_incremental(kitten);
    }
    let ilit = import_literal(kitten, elit);
    klog!(kitten, "registering assumption {}", ilit);
    kitten.assumptions.push(ilit);
}

pub fn kitten_assume_signed(kitten: &mut Kitten, lit: i32) {
    let kelit = int2u(lit);
    kitten_assume(kitten, kelit);
}

/// Common part of the clause addition functions: imports the literals
/// produced by `elits` (already filtered) into `klause` checking for
/// duplicated variables.
#[inline]
fn import_klause_literal(kitten: &mut Kitten, fun: &str, elit: u32) {
    let ilit = import_literal(kitten, elit);
    debug_assert!((ilit as usize) < kitten.lits);
    let iidx = (ilit / 2) as usize;
    if kitten.marks[iidx] != 0 {
        invalid_api_usage!(fun, "variable '{}' of literal '{}' occurs twice", elit / 2, elit);
    }
    kitten.marks[iidx] = 1;
    kitten.klause.push(ilit);
}

#[inline]
fn unmark_klause(kitten: &mut Kitten) {
    for i in 0..kitten.klause.len() {
        let lit = kitten.klause[i];
        kitten.marks[(lit / 2) as usize] = 0;
    }
}

pub fn kitten_clause_with_id_and_exception(kitten: &mut Kitten, id: u32, lits: &[u32], except: u32) {
    if kitten.status != 0 {
        reset_incremental(kitten);
    }
    debug_assert!(kitten.klause.is_empty());
    for &elit in lits {
        if elit == except {
            continue;
        }
        import_klause_literal(kitten, "kitten_clause_with_id_and_exception", elit);
    }
    unmark_klause(kitten);
    new_original_klause(kitten, id);
    kitten.klause.clear();
}

pub fn citten_clause_with_id_and_exception(kitten: &mut Kitten, id: u32, lits: &[i32], except: u32) {
    if kitten.status != 0 {
        reset_incremental(kitten);
    }
    debug_assert!(kitten.klause.is_empty());
    for &l in lits {
        let elit = int2u(l); // this is the conversion
        if elit == except {
            continue;
        }
        import_klause_literal(kitten, "citten_clause_with_id_and_exception", elit);
    }
    unmark_klause(kitten);
    new_original_klause(kitten, id);
    kitten.klause.clear();
}

pub fn citten_clause_with_id_and_equivalence(kitten: &mut Kitten, id: u32, lits: &[i32], lit: u32, other: u32) {
    if kitten.status != 0 {
        reset_incremental(kitten);
    }
    debug_assert!(kitten.klause.is_empty());
    let mut sat = false;
    for &l in lits {
        let elit = int2u(l); // this is the conversion
        if elit == (lit ^ 1u32) || elit == (other ^ 1u32) {
            continue;
        }
        if elit == lit || elit == other {
            sat = true;
            break;
        }
        import_klause_literal(kitten, "citten_clause_with_id_and_equivalence", elit);
    }
    unmark_klause(kitten);
    if !sat {
        new_original_klause(kitten, id);
    }
    kitten.klause.clear();
}

/// `kitten_clause (kitten *, size_t size, unsigned *)`.
pub fn kitten_clause(kitten: &mut Kitten, lits: &[u32]) {
    kitten_clause_with_id_and_exception(kitten, INVALID, lits, INVALID);
}

/// `citten_clause_with_id (kitten *, unsigned id, size_t size, int *)`.
pub fn citten_clause_with_id(kitten: &mut Kitten, id: u32, lits: &[i32]) {
    citten_clause_with_id_and_exception(kitten, id, lits, INVALID);
}

pub fn kitten_unit(kitten: &mut Kitten, lit: u32) {
    kitten_clause(kitten, &[lit]);
}

pub fn kitten_binary(kitten: &mut Kitten, a: u32, b: u32) {
    let clause = [a, b];
    kitten_clause(kitten, &clause);
}

pub fn kitten_solve(kitten: &mut Kitten) -> i32 {
    if kitten.status != 0 {
        reset_incremental(kitten);
    } else {
        completely_backtrack_to_root_level(kitten);
    }

    klog!(kitten, "starting solving under {} assumptions", kitten.assumptions.len());

    debug_assert!(kitten.statistics.kitten_solved < u64::MAX);
    kitten.statistics.kitten_solved += 1;

    let mut res = propagate_units(kitten);
    while res == 0 {
        let conflict = propagate(kitten);
        if terminated(kitten) {
            klog!(kitten, "terminator requested termination");
            res = -1;
            break;
        }
        if conflict != INVALID {
            if kitten.level != 0 {
                analyze(kitten, conflict);
            } else {
                inconsistent(kitten, conflict);
                res = 20;
            }
        } else {
            res = decide(kitten);
        }
    }

    if res < 0 {
        res = 0;
    }

    if res == 0 && !kitten.assumptions.is_empty() {
        reset_assumptions(kitten);
    }

    update_status!(kitten, res);

    if res == 10 {
        kitten.statistics.kitten_sat += 1;
    } else if res == 20 {
        kitten.statistics.kitten_unsat += 1;
    } else {
        kitten.statistics.kitten_unknown += 1;
    }

    klog!(kitten, "finished solving with result {}", res);

    res
}

pub fn kitten_status(kitten: &mut Kitten) -> i32 {
    kitten.status
}

/// `kitten_compute_clausal_core (kitten *, uint64_t *learned)` (`learned`
/// may be null).
pub fn kitten_compute_clausal_core(kitten: &mut Kitten, learned_ptr: Option<&mut u64>) -> u32 {
    require_status!(kitten, "kitten_compute_clausal_core", 20);

    if !kitten.antecedents {
        invalid_api_usage!("kitten_compute_clausal_core", "antecedents not tracked");
    }

    klog!(kitten, "computing clausal core");

    debug_assert!(kitten.resolved.is_empty());

    let mut original: u32 = 0;
    let mut learned: u64 = 0;

    let mut reason_ref = kitten.inconsistent;

    let mut done = false;
    if reason_ref == INVALID {
        debug_assert!(!kitten.assumptions.is_empty());
        reason_ref = kitten.failing;
        if reason_ref == INVALID {
            klog!(kitten, "assumptions mutually inconsistent");
            done = true;
        }
    }

    if !done {
        kitten.resolved.push(reason_ref);
        debug_assert!(kitten.core.is_empty());

        while let Some(c_ref) = kitten.resolved.pop() {
            if c_ref == INVALID {
                let d_ref = kitten.resolved.pop().unwrap();
                rog!(kitten, d_ref, "core[{}]", kitten.core.len());
                kitten.core.push(d_ref);
                check_reference(kitten, d_ref);
                debug_assert!(!is_core_klause(kitten, d_ref));
                set_core_klause(kitten, d_ref);
                if is_learned_klause(kitten, d_ref) {
                    learned += 1;
                } else {
                    original += 1;
                }
            } else {
                check_reference(kitten, c_ref);
                if is_core_klause(kitten, c_ref) {
                    continue;
                }
                kitten.resolved.push(c_ref);
                kitten.resolved.push(INVALID);
                rog!(kitten, c_ref, "analyzing antecedent core");
                if !is_learned_klause(kitten, c_ref) {
                    continue;
                }
                let begin = antecedents(kitten, c_ref);
                let aux = klause_aux(kitten, c_ref) as usize;
                for i in begin..begin + aux {
                    let d_ref = kitten.klauses[i];
                    if !is_core_klause(kitten, d_ref) {
                        kitten.resolved.push(d_ref);
                    }
                }
            }
        }
    }

    // DONE:

    if let Some(ptr) = learned_ptr {
        *ptr = learned;
    }

    klog!(kitten, "clausal core of {} original clauses", original);
    klog!(kitten, "clausal core of {} learned clauses", learned);
    kitten.statistics.original = original as u64;
    kitten.statistics.learned = 0;
    update_status!(kitten, 21);

    original
}

/// `traverse (state, id)`.
pub fn kitten_traverse_core_ids(kitten: &mut Kitten, traverse: &mut dyn FnMut(u32)) {
    require_status!(kitten, "kitten_traverse_core_ids", 21);

    klog!(kitten, "traversing core of original clauses");

    let mut traversed: u32 = 0;

    let mut c = begin_klauses(kitten);
    let end = end_original_klauses(kitten);
    while c != end {
        let r = c as u32;
        // only happens for 'true' incremental calls, i.e. if add happens
        // after solve
        if !is_learned_klause(kitten, r) && is_core_klause(kitten, r) {
            rog!(kitten, r, "traversing");
            traverse(klause_aux(kitten, r));
            traversed += 1;
        }
        c = next_klause(kitten, c);
    }

    klog!(kitten, "traversed {} original core clauses", traversed);
    let _ = traversed;

    debug_assert!(kitten.status == 21);
}

/// Exports the literals of core clause `c_ref` into `eclause`.
fn export_klause(kitten: &mut Kitten, c_ref: u32) {
    debug_assert!(kitten.eclause.is_empty());
    let size = klause_size(kitten, c_ref) as usize;
    for i in 0..size {
        let ilit = klause_lit(kitten, c_ref, i);
        let elit = export_literal(kitten, ilit);
        kitten.eclause.push(elit);
    }
}

/// `traverse (state, learned, size, literals)`.
pub fn kitten_traverse_core_clauses(kitten: &mut Kitten, traverse: &mut dyn FnMut(bool, &[u32])) {
    require_status!(kitten, "kitten_traverse_core_clauses", 21);

    klog!(kitten, "traversing clausal core");

    let mut traversed: u32 = 0;

    for i in 0..kitten.core.len() {
        let c_ref = kitten.core[i];
        check_reference(kitten, c_ref);
        debug_assert!(is_core_klause(kitten, c_ref));
        let learned = is_learned_klause(kitten, c_ref);
        export_klause(kitten, c_ref);
        rog!(kitten, c_ref, "traversing");
        traverse(learned, &kitten.eclause);
        kitten.eclause.clear();
        traversed += 1;
    }

    klog!(kitten, "traversed {} core clauses", traversed);
    let _ = traversed;

    debug_assert!(kitten.status == 21);
}

/// `traverse (state, id, learned, size, literals)`.
pub fn kitten_traverse_core_clauses_with_id(kitten: &mut Kitten, traverse: &mut dyn FnMut(u32, bool, &[u32])) {
    require_status!(kitten, "kitten_traverse_core_clauses_with_id", 21);

    klog!(kitten, "traversing clausal core");

    let mut traversed: u32 = 0;

    for i in 0..kitten.core.len() {
        let c_ref = kitten.core[i];
        check_reference(kitten, c_ref);
        debug_assert!(is_core_klause(kitten, c_ref));
        let learned = is_learned_klause(kitten, c_ref);
        export_klause(kitten, c_ref);
        rog!(kitten, c_ref, "traversing");
        let ctag = if learned { 0 } else { klause_aux(kitten, c_ref) };
        traverse(ctag, learned, &kitten.eclause);
        kitten.eclause.clear();
        traversed += 1;
    }

    klog!(kitten, "traversed {} core clauses", traversed);
    let _ = traversed;

    debug_assert!(kitten.status == 21);
}

/// `trace (state, cid, ctag, learned, size, literals, chain_size, chain)`:
/// the closure is called as `trace (cid, ctag, learned, literals, chain)`
/// exactly in the argument order of the call in `kitten.c`, where `cid` is
/// the clause reference in the kitten arena, `ctag` the user id of an
/// original clause (`0` for learned clauses), `literals` the exported
/// literals and `chain` the references of the antecedents (learned only).
pub fn kitten_trace_core(kitten: &mut Kitten, trace: &mut dyn FnMut(u32, u32, bool, &[u32], &[u32])) {
    require_status!(kitten, "kitten_trace_core", 21);

    klog!(kitten, "tracing clausal core");

    let mut traced: u32 = 0;

    for i in 0..kitten.core.len() {
        let c_ref = kitten.core[i];
        check_reference(kitten, c_ref);
        debug_assert!(is_core_klause(kitten, c_ref));
        let learned = is_learned_klause(kitten, c_ref);
        export_klause(kitten, c_ref);

        debug_assert!(kitten.resolved.is_empty());
        if learned {
            let begin = antecedents(kitten, c_ref);
            let aux = klause_aux(kitten, c_ref) as usize;
            for j in begin..begin + aux {
                let r = kitten.klauses[j];
                kitten.resolved.push(r);
            }
        }

        let cid = c_ref;
        let ctag = if learned { 0 } else { klause_aux(kitten, c_ref) };
        rog!(kitten, cid, "tracing");
        trace(cid, ctag, learned, &kitten.eclause, &kitten.resolved);
        kitten.eclause.clear();
        kitten.resolved.clear();
        traced += 1;
    }

    klog!(kitten, "traced {} core clauses", traced);
    let _ = traced;

    debug_assert!(kitten.status == 21);
}

pub fn kitten_shrink_to_clausal_core(kitten: &mut Kitten) {
    require_status!(kitten, "kitten_shrink_to_clausal_core", 21);

    klog!(kitten, "shrinking formula to core of original clauses");

    kitten.trail.clear();

    kitten.unassigned = (kitten.lits / 2) as u32;
    kitten.propagated = 0;
    kitten.level = 0;

    let last = kitten.queue.last;
    update_search(kitten, last);

    let lits = kitten.lits;
    for v in kitten.values[..lits].iter_mut() {
        *v = 0;
    }

    for lit in 0..lits {
        kitten.watches[lit].clear();
    }

    debug_assert!(kitten.inconsistent != INVALID);
    let inc = kitten.inconsistent;
    check_reference(kitten, inc);
    if is_learned_klause(kitten, inc) || klause_size(kitten, inc) != 0 {
        rog!(kitten, inc, "resetting inconsistent");
        kitten.inconsistent = INVALID;
    } else {
        rog!(kitten, inc, "keeping inconsistent");
    }

    kitten.units.clear();

    let begin = begin_klauses(kitten);
    let mut q = begin;
    let end = end_original_klauses(kitten);
    #[cfg(feature = "logging")]
    let mut original: u32 = 0;
    let mut c = begin;
    while c != end {
        let next = next_klause(kitten, c);
        let r = c as u32;
        // assert (!is_learned_klause (c)); not necessarily true
        if is_learned_klause(kitten, r) || !is_core_klause(kitten, r) {
            c = next;
            continue;
        }
        unset_core_klause(kitten, r);
        let dst = (q - begin) as u32;
        let size = klause_size(kitten, r);
        if size == 0 {
            if kitten.inconsistent != INVALID {
                kitten.inconsistent = dst;
            }
        } else if size == 1 {
            kitten.units.push(dst);
            rog!(kitten, dst, "keeping");
        } else {
            let l0 = klause_lit(kitten, r, 0);
            let l1 = klause_lit(kitten, r, 1);
            watch_klause(kitten, l0, dst);
            watch_klause(kitten, l1, dst);
        }
        if c == q {
            q = next;
        } else {
            kitten.klauses.copy_within(c..next, q);
            q += next - c;
        }
        #[cfg(feature = "logging")]
        {
            original += 1;
        }
        c = next;
    }
    debug_assert!(q <= kitten.klauses.len());
    kitten.klauses.truncate(q);
    kitten.end_original_ref = kitten.klauses.len();
    klog!(kitten, "end of original clauses at {}", kitten.end_original_ref);
    klog!(kitten, "{} original clauses left", original);

    kitten.core.clear();

    update_status!(kitten, 0);
}

/// Converts second argument.
pub fn kitten_signed_value(kitten: &mut Kitten, selit: i32) -> i8 {
    require_status!(kitten, "kitten_signed_value", 10);
    let elit = int2u(selit);
    let eidx = elit / 2;
    if eidx as usize >= kitten.evars {
        return 0;
    }
    let iidx = kitten.import[eidx as usize];
    if iidx == 0 {
        return 0;
    }
    let ilit = 2 * (iidx - 1) + (elit & 1);
    kitten.values[ilit as usize]
}

pub fn kitten_value(kitten: &mut Kitten, elit: u32) -> i8 {
    require_status!(kitten, "kitten_value", 10);
    let eidx = elit / 2;
    if eidx as usize >= kitten.evars {
        return 0;
    }
    let iidx = kitten.import[eidx as usize];
    if iidx == 0 {
        return 0;
    }
    let ilit = 2 * (iidx - 1) + (elit & 1);
    kitten.values[ilit as usize]
}

pub fn kitten_fixed(kitten: &mut Kitten, elit: u32) -> i8 {
    let eidx = elit / 2;
    if eidx as usize >= kitten.evars {
        return 0;
    }
    let mut iidx = kitten.import[eidx as usize];
    if iidx == 0 {
        return 0;
    }
    iidx -= 1;
    let ilit = 2 * iidx + (elit & 1);
    let res = kitten.values[ilit as usize];
    if res == 0 {
        return 0;
    }
    if kitten.vars[iidx as usize].level != 0 {
        return 0;
    }
    res
}

/// Converts second argument.
pub fn kitten_fixed_signed(kitten: &mut Kitten, lit: i32) -> i8 {
    let kelit = int2u(lit);
    kitten_fixed(kitten, kelit)
}

pub fn kitten_flip_literal(kitten: &mut Kitten, elit: u32) -> bool {
    require_status!(kitten, "kitten_flip_literal", 10);
    let eidx = elit / 2;
    if eidx as usize >= kitten.evars {
        return false;
    }
    let iidx = kitten.import[eidx as usize];
    if iidx == 0 {
        return false;
    }
    let ilit = 2 * (iidx - 1) + (elit & 1);
    if kitten_fixed(kitten, elit) != 0 {
        return false;
    }
    flip_literal(kitten, ilit)
}

pub fn kitten_flip_signed_literal(kitten: &mut Kitten, lit: i32) -> bool {
    require_status!(kitten, "kitten_flip_signed_literal", 10);
    let kelit = int2u(lit);
    kitten_flip_literal(kitten, kelit)
}

pub fn kitten_failed(kitten: &mut Kitten, elit: u32) -> bool {
    require_status!(kitten, "kitten_failed", 20);
    let eidx = elit / 2;
    if eidx as usize >= kitten.evars {
        return false;
    }
    let iidx = kitten.import[eidx as usize];
    if iidx == 0 {
        return false;
    }
    let ilit = 2 * (iidx - 1) + (elit & 1);
    kitten.failed[ilit as usize]
}

// checks both watches for clauses with only one literal positively
// assigned. if such a clause is found, return false. Otherwise fix watch
// invariant and return true
fn prime_propagate(kitten: &mut Kitten, idx: u32, ignoring: bool, ignore: &mut dyn FnMut(u32) -> bool) -> bool {
    let mut lit = 2 * idx;
    let mut conflict = INVALID;
    for i in 0..2u32 {
        if conflict != INVALID {
            break;
        }
        lit ^= i;
        let not_lit = lit ^ 1;
        let wl = not_lit as usize;
        let end_watches = kitten.watches[wl].len();
        let mut q = 0usize;
        let mut p = 0usize;
        let mut ticks: u64 = (((end_watches * std::mem::size_of::<u32>()) >> 7) + 1) as u64;
        while p != end_watches {
            let r = kitten.watches[wl][p];
            kitten.watches[wl][q] = r;
            p += 1;
            q += 1;
            check_reference(kitten, r);
            if is_learned_klause(kitten, r) || ignore(klause_aux(kitten, r)) == ignoring {
                continue;
            }
            let size = klause_size(kitten, r) as usize;
            debug_assert!(size > 1);
            let lits = r as usize + LITS;
            let other = kitten.klauses[lits] ^ kitten.klauses[lits + 1] ^ not_lit;
            let other_value = kitten.values[other as usize];
            ticks += 1;
            if other_value > 0 {
                continue;
            }
            let mut replacement_value: Value = -1;
            let mut replacement = INVALID;
            let end_lits = lits + size;
            let mut rp = lits + 2;
            while rp != end_lits {
                replacement = kitten.klauses[rp];
                replacement_value = kitten.values[replacement as usize];
                if replacement_value > 0 {
                    break;
                }
                rp += 1;
            }
            if replacement_value > 0 {
                debug_assert!(replacement != INVALID);
                rog!(kitten, r, "unwatching {} in", not_lit);
                kitten.klauses[lits] = other;
                kitten.klauses[lits + 1] = replacement;
                kitten.klauses[rp] = not_lit;
                watch_klause(kitten, replacement, r);
                q -= 1;
            } else {
                rog!(kitten, r, "idx {} forced prime by", idx);
                conflict = r;
                break;
            }
        }
        {
            let watches = &mut kitten.watches[wl];
            while p != end_watches {
                watches[q] = watches[p];
                q += 1;
                p += 1;
            }
            watches.truncate(q);
        }
        debug_assert!(kitten.statistics.kitten_ticks <= u64::MAX - ticks);
        kitten.statistics.kitten_ticks += ticks;
    }
    conflict == INVALID
}

/// `add_implicant (state, side, size, literals)`.
pub fn kitten_add_prime_implicant(kitten: &mut Kitten, side: i32, add_implicant: &mut dyn FnMut(i32, &[u32])) {
    require_status!(kitten, "kitten_add_prime_implicant", 11);
    // might be possible in some edge cases
    let s = (side != 0) as usize;
    let o = (side == 0) as usize;
    debug_assert!(!kitten.prime[s].is_empty() || !kitten.prime[o].is_empty());
    kitten.prime[o].clear();

    for i in 0..kitten.prime[s].len() {
        let lit = kitten.prime[s][i];
        let not_lit = lit ^ 1;
        let elit = export_literal(kitten, not_lit);
        kitten.prime[o].push(elit);
    }

    // adds a clause which will reset kitten status and backtrack
    add_implicant(side, &kitten.prime[o]);
    kitten.prime[s].clear();
    kitten.prime[o].clear();
}

/// `ignore (state, lit)`.
///
/// Computes two prime implicants, only considering clauses based on
/// ignore return -1 if no prime implicant has been computed, otherwise
/// returns index of shorter implicant.
/// TODO does not work if flip has been called beforehand
pub fn kitten_compute_prime_implicant(kitten: &mut Kitten, ignore: &mut dyn FnMut(u32) -> bool) -> i32 {
    require_status!(kitten, "kitten_compute_prime_implicant", 10);

    let mut unassigned: Vec<u32> = Vec::new();
    let mut limit_hit = false;
    debug_assert!(kitten.prime[0].is_empty() && kitten.prime[1].is_empty());
    for i in 0..2usize {
        let ignoring = i != 0;
        for t in 0..kitten.trail.len() {
            let lit = kitten.trail[t];
            if kitten.statistics.kitten_ticks >= kitten.limits.ticks {
                klog!(
                    kitten,
                    "ticks limit {} hit after {} ticks",
                    kitten.limits.ticks,
                    kitten.statistics.kitten_ticks
                );
                limit_hit = true;
                break;
            }
            debug_assert!(kitten.values[lit as usize] > 0);
            let idx = lit / 2;
            let r = kitten.vars[idx as usize].reason;
            debug_assert!(kitten.vars[idx as usize].level != 0);
            if r != INVALID {
                check_reference(kitten, r);
            }
            if r == INVALID || is_learned_klause(kitten, r) || ignore(klause_aux(kitten, r)) == ignoring {
                klog!(kitten, "non-prime candidate var {}", idx);
                if prime_propagate(kitten, idx, ignoring, ignore) {
                    kitten.values[lit as usize] = 0;
                    kitten.values[(lit ^ 1) as usize] = 0;
                    unassigned.push(lit);
                } else {
                    debug_assert!(kitten.values[lit as usize] > 0);
                }
            }
        }
        // push on prime implicant stack.
        for lit in 0..kitten.lits {
            if kitten.values[lit] > 0 {
                kitten.prime[i].push(lit as u32);
            }
        }
        // reassign all literals on
        for &lit in unassigned.iter() {
            debug_assert!(kitten.values[lit as usize] == 0);
            kitten.values[lit as usize] = 1;
            kitten.values[(lit ^ 1) as usize] = -1;
        }
        unassigned.clear();
    }
    drop(unassigned);

    if limit_hit {
        kitten.prime[0].clear();
        kitten.prime[1].clear();
        return -1;
    }
    // the only case when one of the prime implicants is allowed to be empty
    // is if ignore returns always true or always false.
    debug_assert!(!kitten.prime[0].is_empty() || !kitten.prime[1].is_empty());
    update_status!(kitten, 11);

    (kitten.prime[0].len() > kitten.prime[1].len()) as i32
}

fn prime_propagate_blit(kitten: &mut Kitten, idx: u32, blit: u32) -> bool {
    let mut lit = 2 * idx;
    let mut conflict = INVALID;
    klog!(kitten, "prime propagating idx {} for blit {}", idx, blit);
    for i in 0..2u32 {
        if conflict != INVALID {
            break;
        }
        lit ^= i;
        if lit == blit {
            continue;
        }
        let not_lit = lit ^ 1;
        let wl = not_lit as usize;
        let end_watches = kitten.watches[wl].len();
        let mut q = 0usize;
        let mut p = 0usize;
        let mut ticks: u64 = (((end_watches * std::mem::size_of::<u32>()) >> 7) + 1) as u64;
        while p != end_watches {
            let r = kitten.watches[wl][p];
            kitten.watches[wl][q] = r;
            p += 1;
            q += 1;
            check_reference(kitten, r);
            if is_learned_klause(kitten, r) {
                continue;
            }
            rog!(kitten, r, "checking with blit {}", blit);
            let size = klause_size(kitten, r) as usize;
            debug_assert!(size > 1);
            let lits = r as usize + LITS;
            let other = kitten.klauses[lits] ^ kitten.klauses[lits + 1] ^ not_lit;
            let other_value = kitten.values[other as usize];
            ticks += 1;
            let mut use_ = other == blit || not_lit == blit;
            if other_value > 0 {
                continue;
            }
            let mut replacement_value: Value = -1;
            let mut replacement = INVALID;
            let end_lits = lits + size;
            let mut rp = lits + 2;
            while rp != end_lits {
                replacement = kitten.klauses[rp];
                replacement_value = kitten.values[replacement as usize];
                use_ = use_ || replacement == blit;
                if replacement_value > 0 {
                    break;
                }
                rp += 1;
            }
            if replacement_value > 0 {
                debug_assert!(replacement != INVALID);
                rog!(kitten, r, "unwatching {} in", not_lit);
                kitten.klauses[lits] = other;
                kitten.klauses[lits + 1] = replacement;
                kitten.klauses[rp] = not_lit;
                watch_klause(kitten, replacement, r);
                q -= 1;
            } else if !use_ {
                continue;
            } else {
                rog!(kitten, r, "idx {} forced prime by", idx);
                conflict = r;
                break;
            }
        }
        {
            let watches = &mut kitten.watches[wl];
            while p != end_watches {
                watches[q] = watches[p];
                q += 1;
                p += 1;
            }
            watches.truncate(q);
        }
        debug_assert!(kitten.statistics.kitten_ticks <= u64::MAX - ticks);
        kitten.statistics.kitten_ticks += ticks;
    }
    conflict == INVALID
}

fn compute_prime_implicant_for(kitten: &mut Kitten, blit: u32) -> i32 {
    let mut unassigned: Vec<u32> = Vec::new();
    let mut limit_hit = false;
    debug_assert!(kitten.prime[0].is_empty() && kitten.prime[1].is_empty());
    for i in 0..2usize {
        let block = blit ^ i as u32;
        let ignoring = i;
        if prime_propagate_blit(kitten, block / 2, block) {
            let tmp = kitten.values[blit as usize];
            debug_assert!(tmp != 0);
            kitten.values[blit as usize] = 0;
            kitten.values[(blit ^ 1) as usize] = 0;
            unassigned.push(if tmp > 0 { blit } else { blit ^ 1 });
            kitten.prime[ignoring].push(block); // will be negated!
        } else {
            debug_assert!(false);
        }
        for t in 0..kitten.trail.len() {
            let lit = kitten.trail[t];
            if kitten.statistics.kitten_ticks >= kitten.limits.ticks {
                klog!(
                    kitten,
                    "ticks limit {} hit after {} ticks",
                    kitten.limits.ticks,
                    kitten.statistics.kitten_ticks
                );
                limit_hit = true;
                break;
            }
            if kitten.values[lit as usize] == 0 {
                continue;
            }
            debug_assert!(kitten.values[lit as usize] != 0); // not true when flipping is involved
            let idx = lit / 2;
            debug_assert!(kitten.vars[idx as usize].level != 0);
            klog!(kitten, "non-prime candidate var {}", idx);
            if prime_propagate_blit(kitten, idx, block) {
                let tmp = kitten.values[lit as usize];
                debug_assert!(tmp != 0);
                kitten.values[lit as usize] = 0;
                kitten.values[(lit ^ 1) as usize] = 0;
                unassigned.push(if tmp > 0 { lit } else { lit ^ 1 });
            }
        }
        // push on prime implicant stack.
        for lit in 0..kitten.lits {
            if kitten.values[lit] > 0 {
                kitten.prime[i].push(lit as u32);
            }
        }
        // reassign all literals on
        for &lit in unassigned.iter() {
            debug_assert!(kitten.values[lit as usize] == 0);
            kitten.values[lit as usize] = 1;
            kitten.values[(lit ^ 1) as usize] = -1;
        }
        unassigned.clear();
    }
    drop(unassigned);

    if limit_hit {
        kitten.prime[0].clear();
        kitten.prime[1].clear();
        return -1;
    }
    // the only case when one of the prime implicants is allowed to be empty
    // is if ignore returns always true or always false.
    debug_assert!(!kitten.prime[0].is_empty() || !kitten.prime[1].is_empty());
    loglits!(kitten, &kitten.prime[0], "first implicant {}", blit);
    loglits!(kitten, &kitten.prime[1], "second implicant {}", blit ^ 1);
    update_status!(kitten, 11);

    (kitten.prime[0].len() > kitten.prime[1].len()) as i32
}

pub fn kitten_flip_and_implicant_for_signed_literal(kitten: &mut Kitten, elit: i32) -> i32 {
    require_status!(kitten, "kitten_flip_and_implicant_for_signed_literal", 10);
    let kelit = int2u(elit);
    if !kitten_flip_literal(kitten, kelit) {
        return -2;
    }
    let eidx = kelit / 2;
    let iidx = kitten.import[eidx as usize];
    debug_assert!(iidx != 0);
    let ilit = 2 * (iidx - 1) + (kelit & 1);
    compute_prime_implicant_for(kitten, ilit)
}

/*------------------------------------------------------------------------*/
// Testing support (Rust addition, not part of the C API).

/// Dumps the complete observable internal state of the solver in the
/// same format as the `dump_state` function of the C differential test
/// driver (`scripts/kitten/kitten_driver.c`).  Used for differential
/// testing only.
#[doc(hidden)]
pub fn kitten_dump_state(kitten: &Kitten) -> String {
    use std::fmt::Write;
    let mut s = String::new();
    let st = &kitten.statistics;
    let _ = write!(
        s,
        "state status={} level={} propagated={} unassigned={} inconsistent={} failing={} generator={} lits={} evars={} end_original_ref={} size={} esize={} antecedents={} learned={}",
        kitten.status,
        kitten.level,
        kitten.propagated,
        kitten.unassigned,
        kitten.inconsistent,
        kitten.failing,
        kitten.generator,
        kitten.lits,
        kitten.evars,
        kitten.end_original_ref,
        kitten.size,
        kitten.esize,
        kitten.antecedents as i32,
        kitten.learned as i32
    );
    let _ = write!(
        s,
        "\nqueue first={} last={} stamp={} search={}",
        kitten.queue.first, kitten.queue.last, kitten.queue.stamp, kitten.queue.search
    );
    let _ = write!(
        s,
        "\nstats learned={} original={} flip={} flipped={} sat={} solved={} conflicts={} decisions={} propagations={} ticks={} unknown={} unsat={} limit={}",
        st.learned,
        st.original,
        st.kitten_flip,
        st.kitten_flipped,
        st.kitten_sat,
        st.kitten_solved,
        st.kitten_conflicts,
        st.kitten_decisions,
        st.kitten_propagations,
        st.kitten_ticks,
        st.kitten_unknown,
        st.kitten_unsat,
        kitten.limits.ticks
    );
    let dump = |s: &mut String, name: &str, v: &[u32]| {
        let _ = write!(s, "\n{}", name);
        for x in v {
            let _ = write!(s, " {}", x);
        }
    };
    dump(&mut s, "klauses", &kitten.klauses);
    dump(&mut s, "trail", &kitten.trail);
    dump(&mut s, "units", &kitten.units);
    dump(&mut s, "assumptions", &kitten.assumptions);
    dump(&mut s, "core", &kitten.core);
    dump(&mut s, "export", &kitten.export);
    dump(&mut s, "prime0", &kitten.prime[0]);
    dump(&mut s, "prime1", &kitten.prime[1]);
    let _ = write!(s, "\nphases");
    for x in &kitten.phases[..kitten.size / 2] {
        let _ = write!(s, " {}", x);
    }
    let _ = write!(s, "\nvalues");
    for x in &kitten.values[..kitten.lits] {
        let _ = write!(s, " {}", x);
    }
    let _ = write!(s, "\nfailed");
    for x in &kitten.failed[..kitten.lits] {
        let _ = write!(s, " {}", *x as i32);
    }
    let _ = write!(s, "\nlinks");
    for x in &kitten.links[..kitten.lits / 2] {
        let _ = write!(s, " {}:{}:{}", x.prev, x.next, x.stamp);
    }
    let _ = write!(s, "\nvars");
    for (i, x) in kitten.vars[..kitten.lits / 2].iter().enumerate() {
        // Only assigned variables have meaningful levels and reasons.
        if kitten.values[2 * i] != 0 {
            let _ = write!(s, " {}:{}", x.level, x.reason);
        } else {
            let _ = write!(s, " -");
        }
    }
    for lit in 0..kitten.lits {
        let _ = write!(s, "\nwatches[{}]", lit);
        for x in &kitten.watches[lit] {
            let _ = write!(s, " {}", x);
        }
    }
    s.push('\n');
    s
}

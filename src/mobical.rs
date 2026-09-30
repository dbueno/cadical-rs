//! Port of `mobical.cpp`: the model based tester for the CaDiCaL SAT
//! solver library.
//!
//! The C++ code is a single translation unit with a global `Mobical`
//! object.  Here the global object is a heap allocated `Mobical` reached
//! through a raw pointer (`m ()`), and the member functions of `Mobical`
//! which run while other (Trace) code needs the global object are free
//! functions (associated functions without `self`) to avoid keeping a
//! `&mut Mobical` alive across such calls.
//!
//! The class hierarchy of API calls (`Call` and its sub-classes) is mapped
//! to one `Call` struct with a `Kind` tag (the dynamic class), keeping the
//! `type` bit mask as in C++.  All quirks of the C++ code are kept (for
//! instance `FlippableCall::copy` returning a `FlipCall`, `CubingCall`
//! solving with depth `arg == 0`, the trace reader reusing the previous
//! `lit` for `cubing` without argument, etc.), since traces and random
//! trace generation have to be identical to the C++ version.
//!
//! Output streams: `std::cerr` (with its sticky `setfill`/`left`/`right`
//! state), `std::cout` and `std::ofstream` are emulated by `OStream`
//! which writes to C `FILE` streams (like `std::cerr` synchronized with
//! C stdio does).
//!
//! Not ported: the optional `MOBICAL_MEMORY` build mode (malloc hooks for
//! memory fuzzing; not enabled in the default C++ build, where
//! `--bad-alloc` and `--leak-alloc` die with an error message as here)
//! and catching `std::bad_alloc` (Rust aborts on allocation failure).

use std::collections::{BTreeMap, BTreeSet};
use std::ptr;

use crate::config::Config;
use crate::file::File;
use crate::message::{c_stderr, c_stdout, fflush, fputc, fputs};
use crate::options::Options;
use crate::random::Random;
use crate::resources::absolute_real_time;
use crate::signal::{Handler, Signal};
use crate::solver::{ExternalPropagator, FixedAssignmentListener, Solver};
use crate::solver::{INCONCLUSIVE, SATISFIED, UNSATISFIED};
use crate::terminal::{terr, tout, Terminal};
use crate::util::{has_prefix, is_color_option, is_no_color_option, parse_int_str, percent};
use crate::version::{affiliations, authors, copyright, version};

/*------------------------------------------------------------------------*/

// clang-format off

const USAGE: &str =
"usage: mobical [ <option> ... ] [ <mode> ]\n\
\n\
where '<option>' can be one of the following:\n\
\n\
\x20 --help    | -h    print this command line option summary and exit\n\
\x20 --version         print CaDiCaL's three character version and exit\n\
\x20 --build           print build configuration\n\
\n\
\x20 -v | --verbose    increase verbosity\n\
\x20 -q | --quiet      be quiet (only print failing and reduced traces)\n\
\n\
\x20 --colors          force colors for both '<stdout>' and '<stderr>'\n\
\x20 --no-colors       disable colors if '<stderr>' is connected to terminal\n\
\x20 --no-terminal     assume '<stderr>' is not connected to terminal\n\
\x20 --no-seeds        do not print seeds in random mode\n\
\n\
\x20 -<n>              specify the number of solving phases explicitly\n\
\x20 --time <seconds>  set time limit per trace (none=0, default=%d)\n\
\x20 --space <MB>      set space limit (none=0, default=%d)\n\
\x20 --bad-alloc       generate failing memory allocations, monitor for crashes\n\
\x20 --leak-alloc      generate failing memory allocations, monitor for leaks\n\
\n\
\x20 --do-not-ignore-resource-limits consider out-of-time or memory as error\n\
\n\
\x20 --tiny            generate tiny formulas only\n\
\x20 --small           generate small formulas only\n\
\x20 --medium          generate medium sized formulas only\n\
\x20 --big             generate big formulas only\n\
\n\
Then '<mode>' is one of these\n\
\n\
\x20 <seed>            generate and execute trace for given 64-bit seed\n\
\x20 <seed>  <output>  generate trace, shrink and write it to file\n\
\x20 <input> <output>  read trace, shrink and write it to output file\n\
\x20 <input>           read and replay the specified input trace\n\
\n\
In order to let the test execute '<r>' runs (starting from '<seed>') use:\n\
\n\
\x20 -L[ ]<r>          execute '<r>' runs\n\
\n\
The output trace is not shrunken if it is not failing.  However, before\n\
it is written it is executed, unless '--do-not-execute' is specified:\n\
\n\
\x20 --do-not-execute  just write to '<output>' without execution\n\
\n\
In order to check memory issues or collect coverage you can force\n\
execution within the main process, which however also means that the\n\
model based tester aborts as soon a test fails\n\
\n\
\x20 --do-not-fork     execute all tests in main process directly\n\
\n\
In order to replay a trace which violates an API contract use\n\
\n\
\x20 --do-not-enforce-contracts\n\
\n\
To read from '<stdin>' use '-' as '<input>' and also '-' instead of\n\
'<output>' to write to '<stdout>'.\n\
\n\
As the library is compiled with logging support ('-DLOGGING')\n\
one can force to add the 'set log 1' call to the trace with\n\
\n\
\x20 --log | -l        force low-level logging for detailed debugging\n\
\n\
Implicitly add 'dump' and 'stats' calls to traces:\n\
\n\
\x20 --dump  | -d      force dumping the CNF before every 'solve'\n\
\x20 --stats | -s      force printing statistics after every 'solve'\n\
\n\
Implicitly add 'configure plain' after setting options:\n\
\n\
\x20 --plain | -p\n\
\n\
Otherwise if no '<mode>' is specified the default is to generate random\n\
traces internally until the execution of a trace fails, which means it\n\
produces a non-zero exit code.  Then the trace is rerun and shrunken\n\
through delta-debugging to produce a smaller trace.  The shrunken failing\n\
trace is written as 'red-<seed>.trace' to the current working directory.\n\
\n\
The following options disable certain parts of the shrinking algorithm:\n\
\n\
\x20 --do-not-shrink[-at-all]\n\
\x20 --do-not-add-options[-before-shrinking]\n\
\x20 --do-not-shrink-phases\n\
\x20 --do-not-shrink-clauses\n\
\x20 --do-not-shrink-literals\n\
\x20 --do-not-shrink-basic[-calls]\n\
\x20 --do-not-disable[-options]\n\
\x20 --do-not-reduce[[-option]-values]\n\
\x20 --do-not-shrink-variables\n\
\x20 --do-not-shrink-options\n\
\n\
The standard mode of using the model based tester is to start it in\n\
random testing mode without '<input>', '<seed>' nor '<output>' option.\n\
If a failing trace is found it will be shrunken and the resulting\n\
trace written to the current working directory.  Then the model based\n\
tester can be interrupted and then called again with the produced\n\
failing trace as single argument.\n\
\n\
This second invocation will execute the trace within the same process\n\
and thus can directly be investigated with a symbolic debugger such\n\
as 'gdb' or maybe first checked for memory issues with 'valgrind'\n\
or recompilation with memory checking '-fsanitize=address'.\n";

// clang-format on

/*------------------------------------------------------------------------*/

const DEFAULT_TIME_LIMIT: i64 = 10;
const DEFAULT_SPACE_LIMIT: i64 = 1024;

/*------------------------------------------------------------------------*/

// Emulation of the C++ output streams ('std::cerr', 'std::cout' and
// 'std::ofstream') including the sticky 'setfill', 'left' and 'right'
// manipulators and the non-sticky 'setw'.

pub(crate) struct OStream {
    /// 1 = C 'stdout', 2 = C 'stderr', 0 = 'own'.
    target: i32,
    own: *mut libc::FILE,
    fill: u8,
    left: bool,
    width: usize,
}

impl OStream {
    const fn new(target: i32) -> OStream {
        OStream { target, own: ptr::null_mut(), fill: b' ', left: false, width: 0 }
    }

    fn file(&self) -> *mut libc::FILE {
        match self.target {
            1 => c_stdout(),
            2 => c_stderr(),
            _ => self.own,
        }
    }

    /// Formatted output of a string (applies and resets 'setw').
    fn s(&mut self, str: &str) -> &mut Self {
        let width = self.width;
        self.width = 0;
        let len = str.len();
        let file = self.file();
        if len < width {
            let pad: String = std::iter::repeat(self.fill as char).take(width - len).collect();
            if self.left {
                fputs(str, file);
                fputs(&pad, file);
            } else {
                fputs(&pad, file);
                fputs(str, file);
            }
        } else {
            fputs(str, file);
        }
        self
    }

    /// Formatted output of anything else (numbers).
    fn d<T: std::fmt::Display>(&mut self, x: T) -> &mut Self {
        let str = x.to_string();
        self.s(&str)
    }

    fn c(&mut self, ch: char) -> &mut Self {
        let mut buf = [0u8; 4];
        let str = ch.encode_utf8(&mut buf);
        self.s(str)
    }

    fn setw(&mut self, w: i64) -> &mut Self {
        self.width = if w < 0 { 0 } else { w as usize };
        self
    }

    fn setfill(&mut self, ch: char) -> &mut Self {
        self.fill = ch as u8;
        self
    }

    fn left(&mut self) -> &mut Self {
        self.left = true;
        self
    }

    fn right(&mut self) -> &mut Self {
        self.left = false;
        self
    }

    fn flush(&mut self) -> &mut Self {
        fflush(self.file());
        self
    }

    fn endl(&mut self) -> &mut Self {
        fputc(b'\n' as i32, self.file());
        self.flush()
    }
}

static mut CERR: OStream = OStream::new(2);
static mut COUT: OStream = OStream::new(1);

/// `std::cerr`.
#[allow(clippy::mut_from_ref)]
fn cerr() -> &'static mut OStream {
    // SAFETY: single threaded (signal handlers do not use it).
    unsafe { &mut *ptr::addr_of_mut!(CERR) }
}

/// `std::cout`.
fn cout() -> &'static mut OStream {
    // SAFETY: single threaded.
    unsafe { &mut *ptr::addr_of_mut!(COUT) }
}

/*------------------------------------------------------------------------*/

// Options to generate traces.

type Size = i32; // enum Size
const NOSIZE: Size = 0;
const TINY: Size = 5;
const SMALL: Size = 10;
const MEDIUM: Size = 30;
const BIG: Size = 50;

struct Force {
    size: Size,
    phases: i32,
}

impl Default for Force {
    fn default() -> Force {
        Force { size: NOSIZE, phases: -1 }
    }
}

// Options to shrink traces.

#[derive(Default)]
struct DoNotShrink {
    atall: bool,    // do not shrink anything              's'
    phases: bool,   // shrink complete incremental solving 'p'
    clauses: bool,  // shrink full clauses                 'c'
    lemmas: bool,   // shrink external lemmas              'u'
    literals: bool, // shrink literals which shrinks       'l'
    basic: bool,    // shrink other basic calls            'b'
    options: bool,  // shrink option calls                 'o'
}

#[derive(Default)]
struct DoNot {
    add: bool, // add all options before shrinking    'a'
    shrink: DoNotShrink,
    disable: bool, // try to eagerly disable all options  'd'
    map: bool,     // do not map variable indices         'm'
    reduce: bool,  // reduce option values                'r'
    execute: bool, // do not execute trace
    fork: bool,    // do not fork sub-process
    enforce: bool, // do not enforce contracts on read trace
    seeds: bool,
    ignore_resource_limits: bool,
}

/*------------------------------------------------------------------------*/

#[repr(C)]
struct Shared {
    solved: i64,
    incremental: i64,
    unsat: i64,
    sat: i64,
    memout: i64,
    timeout: i64,
    oom: i64,
}

#[derive(Default)]
pub(crate) struct ExtendMap {
    map: Vec<i32>,
}

/*------------------------------------------------------------------------*/

// Helper to print very verbose log during debugging ('MLOG' and 'MLOGC'
// write to 'std::cout'; 'std::endl' flushes, which is the 'true' flag).

macro_rules! mlog {
    ($self:expr, $endl:expr, $($arg:tt)*) => {
        #[cfg(feature = "logging")]
        {
            if $self.logging {
                cprintf!("[mock-propagator] ");
                cprintf!($($arg)*);
                if $endl {
                    fflush(c_stdout());
                }
            }
        }
    };
}

macro_rules! mlogc {
    ($self:expr, $endl:expr, $($arg:tt)*) => {
        #[cfg(feature = "logging")]
        {
            if $self.logging {
                cprintf!($($arg)*);
                if $endl {
                    fflush(c_stdout());
                }
            }
        }
    };
}

struct ExternalLemma {
    id: usize,
    add_count: usize,
    size: usize,
    next: usize,

    mapped: bool,
    forgettable: bool,
    tainting: bool,
    propagation_reason: bool,

    literals: Vec<i32>,
}

impl ExternalLemma {
    fn next_lit(&mut self) -> i32 {
        if self.next < self.size {
            let res = self.literals[self.next];
            self.next += 1;
            res
        } else {
            self.next = 0;
            0
        }
    }
}

pub(crate) struct MockPropagator {
    s: *mut Solver,
    extendmap: *mut ExtendMap,

    // MockPropagator parameters
    lemma_per_cb: usize,
    logging: bool,

    // The list of all external lemmas (including reason clauses)
    external_lemmas: Vec<Box<ExternalLemma>>,

    // The reasons of present external propagations
    reason_map: BTreeMap<i32, i32>,
    // The external propagations that are currently unassigned
    unassigned_reasons: BTreeSet<i32>,

    // Next lemma to add
    add_lemma_idx: usize,

    // Forced lemme addition (falsified lemma in model)
    must_add_clause: bool,
    must_add_idx: usize,
    // Next decision to make
    decision_loc: usize,
    forced_bt: usize,

    // Observed variables and their current assignments
    observed_variables: BTreeSet<i32>,
    new_observed_variables: Vec<i32>,
    observed_trail: Vec<Vec<i32>>,

    // Helpers
    added_lemma_count: usize,
    nof_clauses: usize,
    clause: Vec<i32>,
    new_ovars: bool,

    // It is public, so it can be shared easily between different propagators
    pub observed_fixed: Vec<i32>,
}

impl MockPropagator {
    #[allow(clippy::mut_from_ref)]
    fn solver(&self) -> &mut Solver {
        // SAFETY: the solver outlives the connected mock propagator (it is
        // deleted before the propagator in 'ResetCall'), and as in C++ the
        // propagator calls back into the solver during solving.
        unsafe { &mut *self.s }
    }

    #[allow(clippy::mut_from_ref)]
    fn emap(&self) -> &mut ExtendMap {
        // SAFETY: points to the 'extendmap' of the executed trace.
        unsafe { &mut *self.extendmap }
    }

    fn add_new_lemma(&mut self, forgettable: bool) -> usize {
        debug_assert!(self.clause.len() <= i32::MAX as usize);
        debug_assert!(self.external_lemmas.len() <= i32::MAX as usize);

        let size = self.clause.len();
        let mut lemma = Box::new(ExternalLemma {
            id: 0,
            add_count: 0,
            size: 0,
            next: 0,
            mapped: false,
            forgettable: false,
            tainting: false,
            propagation_reason: false,
            literals: Vec::with_capacity(size),
        });

        lemma.id = self.external_lemmas.len();
        lemma.add_count = 0;
        lemma.size = size;
        lemma.next = 0;
        lemma.forgettable = forgettable;
        lemma.tainting = true;
        lemma.propagation_reason = false;

        for &lit in &self.clause {
            lemma.literals.push(lit);
        }

        let id = lemma.id;
        self.external_lemmas.push(lemma);

        id
    }

    fn extend_map(&mut self, arg: i32) {
        let max_var_fn = |s: &MockPropagator| s.solver().vars();
        let map = &mut self.emap().map;
        if map.is_empty() {
            map.push(0); // 0 is always mapped to 0
        }
        if arg == 0 {
            return;
        }
        let abs_arg = arg.unsigned_abs();
        if (abs_arg as usize) < map.len() {
            return; // arg is already mapped
        }
        let diff = (abs_arg as i32).wrapping_sub(map.len() as i32).wrapping_add(1);
        let max_var = max_var_fn(self);
        let map = &mut self.emap().map;
        let want = (max_var as i64 + diff as i64) as usize;
        if want > map.capacity() {
            map.reserve(want - map.len());
        }
        for i in 1..=diff {
            map.push(max_var + i);
        }
    }

    fn map_arg(&mut self, arg: i32) -> i32 {
        let abs_arg = arg.wrapping_abs();
        let sign = if arg > 0 { 1 } else { -1 };
        let map_size = self.emap().map.len() as i32;
        if abs_arg < map_size {
            return self.emap().map[abs_arg as usize] * sign;
        }
        let max_var = self.solver().vars();
        let diff = abs_arg - map_size + 1;
        sign * (max_var + diff)
    }

    pub(crate) fn new(solver: *mut Solver, map: *mut ExtendMap, with_logging: bool) -> MockPropagator {
        let mut res = MockPropagator {
            s: ptr::null_mut(),
            extendmap: ptr::null_mut(),
            lemma_per_cb: 2,
            logging: false,
            external_lemmas: Vec::new(),
            reason_map: BTreeMap::new(),
            unassigned_reasons: BTreeSet::new(),
            add_lemma_idx: 0,
            must_add_clause: false,
            must_add_idx: 0,
            decision_loc: 0,
            forced_bt: 0,
            observed_variables: BTreeSet::new(),
            new_observed_variables: Vec::new(),
            observed_trail: Vec::new(),
            added_lemma_count: 0,
            nof_clauses: 0,
            clause: Vec::new(),
            new_ovars: false,
            observed_fixed: Vec::new(),
        };
        res.observed_trail.push(Vec::new());
        res.s = solver;
        res.extendmap = map;
        res.logging = res.logging || with_logging;
        res
    }

    /*-----------------functions for mobical -----------------------------*/

    pub(crate) fn push_lemma_lit(&mut self, lit: i32) {
        if lit != 0 {
            self.clause.push(lit);
        } else {
            self.nof_clauses += 1;

            mlog!(self, false, "push lemma to position {}: ", self.external_lemmas.len());
            #[cfg(feature = "logging")]
            for l in &self.clause {
                mlogc!(self, false, "{} ", l);
            }
            mlogc!(self, true, "0\n");

            self.add_new_lemma(true);
            self.clause.clear();
        }
    }

    pub(crate) fn add_observed_lit(&mut self, lit: i32) {
        // Zero lit indicates that the new observed variables start here
        if lit == 0 {
            debug_assert!(!self.new_ovars);
            self.new_ovars = true;
            return;
        }

        if !self.new_ovars {
            let abs_lit = lit.wrapping_abs();
            let mapped = self.map_arg(abs_lit);
            if !self.solver().is_witness(mapped) {
                // does not extend map
                self.extend_map(abs_lit); // now we have to extend map
                let mapped = self.map_arg(abs_lit);
                self.solver().add_observed_var(mapped); // might be different
                let mapped = self.map_arg(abs_lit);
                self.observed_variables.insert(mapped);
            }
        } else {
            self.new_observed_variables.push(lit.wrapping_abs());
        }
    }

    fn add_new_observed_var(&mut self) -> i32 {
        let mut i = 0;
        while i < self.new_observed_variables.len() {
            let lit = self.new_observed_variables[i];
            let mapped = self.map_arg(lit);
            if self.solver().is_witness(mapped) {
                i += 1;
                continue;
            }
            self.new_observed_variables.remove(i);

            self.extend_map(lit);
            let mapped = self.map_arg(lit);
            self.solver().add_observed_var(mapped);
            let mapped = self.map_arg(lit);
            self.observed_variables.insert(mapped);

            return self.map_arg(lit);
        }
        0
    }

    pub(crate) fn remove_new_observed_var(&mut self) -> i32 {
        // TODO: check out red-02744449867227930989.trace
        0
    }

    fn is_observed_now(&self, lit: i32) -> bool {
        self.observed_variables.contains(&lit.wrapping_abs())
    }

    fn compare_trails(&mut self) -> bool {
        #[cfg(debug_assertions)]
        {
            let mut etrail: BTreeSet<i32> = BTreeSet::new(); // Trail of the solver
            let mut otrail: BTreeSet<i32> = BTreeSet::new(); // Observed trail

            let mut idx: usize = 0;

            // 1. Collect merged/eliminated variables in case there are:
            let mut eq_class: Vec<i32> = Vec::new();
            // can be an expensive call, avoid if possible
            let is_merger = self.solver().internal().get_merged_literals(&mut eq_class);
            if is_merger {
                for &elit in &eq_class {
                    if self.is_observed_now(elit) {
                        etrail.insert(elit);
                    }
                }
                idx += 1; // trail[0] is processed already
            }

            // 2. Collect all other variables from trail
            while idx < self.solver().internal().trail.len() {
                let ilit = self.solver().internal().trail[idx];
                let elit = self.solver().internal().externalize(ilit);
                if self.is_observed_now(elit) {
                    etrail.insert(elit);
                }
                idx += 1;
            }

            for level in &self.observed_trail {
                for &elit in level {
                    if self.is_observed_now(elit) {
                        // There can be duplicate assignments due to fixed variables
                        // so assert (otrail_inserted == otrail.size()) will not work.
                        debug_assert!(!otrail.contains(&elit) || self.observed_fixed.contains(&elit));

                        otrail.insert(elit);
                    }
                }
            }
            #[cfg(feature = "logging")]
            if etrail.len() != otrail.len() {
                mlog!(self, false, "etrail: ");
                for lit in &etrail {
                    mlogc!(self, false, "{} ", lit);
                }
                mlogc!(self, true, "\n");
                mlog!(self, false, "otrail: ");
                for lit in &otrail {
                    mlogc!(self, false, "{} ", lit);
                }
                mlogc!(self, true, "\n");
            }
            debug_assert!(etrail.len() == otrail.len());

            debug_assert!(etrail == otrail);
        }
        true
    }
    /*-----------------functions for mobical ends ------------------------*/

    /*------------------ FixedAssignmentListener functions
     * ---------------------*/
    fn notify_fixed_assignment_impl(&mut self, lit: i32) {
        mlog!(
            self,
            true,
            "notify_fixed_assignment: {} (current level: {}, current fixed count: {})\n",
            lit,
            self.observed_trail.len().wrapping_sub(1),
            self.observed_fixed.len()
        );

        debug_assert!(!self.observed_fixed.contains(&lit));
        self.observed_fixed.push(lit);
    }

    pub(crate) fn add_prev_fixed(&mut self, fixed_assignments: &[i32]) {
        for &lit in fixed_assignments {
            self.notify_fixed_assignment_impl(lit);
        }
    }

    pub(crate) fn collect_prev_fixed(&mut self) {
        #[cfg(debug_assertions)]
        {
            mlog!(self, false, "collecting previously fixed assignments for the new FixedAssignmentListener: ");

            let mut fixed_lits: Vec<i32> = Vec::new();
            self.solver().internal().get_all_fixed_literals(&mut fixed_lits);
            mlogc!(self, true, "found: {} fixed literals\n", fixed_lits.len());
            self.add_prev_fixed(&fixed_lits);
            fixed_lits.clear();
        }
    }

    /* ---------------- FixedAssignmentListener functions end
     * ------------------*/

    /* -------------------- ExternalPropagator functions -----------------*/

    fn cb_check_found_model_impl(&mut self, model: &[i32]) -> bool {
        mlog!(self, false, "cb_check_found_model ({}) returns: ", model.len());

        // Model reconstruction can change the assignments of certain variables,
        // but the internal trail of the solver and the propagator should be
        // still in synchron.
        debug_assert!(self.compare_trails());

        for li in 0..self.external_lemmas.len() {
            let mut satisfied = false;

            {
                let lemma = &self.external_lemmas[li];
                for k in 0..lemma.size {
                    let lit = lemma.literals[k];
                    if lit == 0 {
                        continue; // eoc
                    }

                    if model.contains(&lit) {
                        satisfied = true;
                        break;
                    } else {
                        // if not satisfied, it must be falsified.
                        debug_assert!(model.contains(&-lit));
                    }
                }
            }

            if !satisfied {
                let (id, forgettable, add_count, size) = {
                    let lemma = &self.external_lemmas[li];
                    (lemma.id, lemma.forgettable, lemma.add_count, lemma.size)
                };
                let _ = (forgettable, size);
                debug_assert!(add_count == 0 || forgettable);

                self.must_add_clause = true;
                self.must_add_idx = id;

                mlogc!(
                    self,
                    false,
                    "false (external clause  {}/{} is not satisfied: (forgettable: {}, size: {}): ",
                    id,
                    self.external_lemmas.len(),
                    forgettable as i32,
                    size
                );
                #[cfg(feature = "logging")]
                for k in 0..self.external_lemmas[li].size {
                    let l = self.external_lemmas[li].literals[k];
                    mlogc!(self, false, "{} ", l);
                }
                mlogc!(self, true, "\n");

                return false;
            }
        }

        mlogc!(self, true, "true\n");

        true
    }

    fn cb_has_external_clause_impl(&mut self, forgettable: &mut bool) -> bool {
        mlog!(self, false, "cb_has_external_clause returns: ");

        debug_assert!(self.compare_trails());

        *forgettable = false;

        if self.external_lemmas.is_empty() {
            mlogc!(self, true, "false (there are no external lemmas).\n");
            return false;
        }

        self.add_new_observed_var();

        if self.must_add_clause {
            self.must_add_clause = false;
            self.add_lemma_idx = self.must_add_idx;

            *forgettable = self.external_lemmas[self.must_add_idx].forgettable;

            mlogc!(
                self,
                true,
                "true (forced clause addition, forgettable: {} id: {}).\n",
                *forgettable as i32,
                self.add_lemma_idx
            );

            self.added_lemma_count += 1;
            return true;
        }

        if self.added_lemma_count > self.lemma_per_cb {
            self.added_lemma_count = 0;
            mlogc!(self, true, "false (lemma per CB treshold reached).\n");
            return false;
        }

        // Final model check will force to jump over some lemmas without
        // adding them. But if any of them is unsatisfied, it will force also
        // to set back the add_lemma_idx to them. So we do not need to start
        // the search here from 0.

        while self.add_lemma_idx < self.external_lemmas.len() {
            if self.external_lemmas[self.add_lemma_idx].add_count == 0
                && !self.external_lemmas[self.add_lemma_idx].propagation_reason
            {
                *forgettable = self.external_lemmas[self.add_lemma_idx].forgettable;

                mlogc!(
                    self,
                    true,
                    "true (new lemma was found, forgettable: {} id: {}).\n",
                    *forgettable as i32,
                    self.add_lemma_idx
                );

                self.added_lemma_count += 1;
                return true;
            }

            // Forgettable lemmas are added repeatedly to the solver only when
            // the final model falsifies it (recognized in cb_check_final_model).

            self.add_lemma_idx += 1;
        }
        mlogc!(self, true, "false.\n");

        false
    }

    fn cb_add_external_clause_lit_impl(&mut self) -> i32 {
        let lit = self.external_lemmas[self.add_lemma_idx].next_lit();

        mlog!(
            self,
            true,
            "cb_add_external_clause_lit {} (lemma {}/{})\n",
            lit,
            self.add_lemma_idx,
            self.external_lemmas.len()
        );

        if lit == 0 {
            let idx = self.add_lemma_idx;
            self.add_lemma_idx += 1;
            self.external_lemmas[idx].add_count += 1;
        }

        lit
    }

    fn cb_decide_impl(&mut self) -> i32 {
        mlog!(self, true, "cb_decide starts.\n");

        debug_assert!(self.compare_trails());

        if !self.unassigned_reasons.is_empty() {
            #[cfg(feature = "logging")]
            let mut del_count: usize = 0;
            mlog!(self, false, "clean up backtracked external propagation reasons: ");
            let lits: Vec<i32> = self.unassigned_reasons.iter().copied().collect();
            for lit in lits {
                let reason_id = *self.reason_map.entry(lit).or_insert(0) as usize;
                debug_assert!(reason_id < self.external_lemmas.len());
                self.external_lemmas[reason_id].propagation_reason = false;
                self.external_lemmas[reason_id].forgettable = true;
                self.reason_map.remove(&lit);
                #[cfg(feature = "logging")]
                {
                    mlogc!(self, false, "{} ", lit);
                    del_count += 1;
                }
            }
            mlogc!(self, true, "({} clauses)\n", del_count);
            self.unassigned_reasons.clear();
        }

        if self.observed_variables.is_empty() || self.observed_variables.len() <= 4 {
            mlog!(self, true, "cb_decide returns 0\n");
            return 0;
        }

        if self.observed_variables.len() % 5 == 0 && !self.new_observed_variables.is_empty() {
            let new_var = self.add_new_observed_var();
            if new_var != 0 {
                mlog!(self, true, "cb_decide returns new variable {}\n", -new_var);
                return -new_var;
            }
        }

        self.decision_loc += 1;
        let mut lit_sum: usize = 0; // sum of variables of satisfied observed literals
        let mut lowest_lit = 0; // the lowest satisfied observed literal
        let mut highest_lit = 0; // the highest satisfied observed literal
        let satisfied_literals = self.current_observed_satisfied_set(&mut lit_sum, &mut lowest_lit, &mut highest_lit);

        if self.decision_loc % self.observed_variables.len() == 0 {
            if (self.observed_variables.len() + self.forced_bt) % 11 == 0 && self.observed_trail.len() > 1 {
                let target =
                    std::cmp::min(self.observed_variables.len() % 5, self.observed_trail.len() - 2) as i32;
                mlog!(self, true, "cb_decide forces backtracking to level {}\n", target);
                self.solver().force_backtrack(target);
                self.forced_bt += 1;
            }
            let mut n = self.decision_loc / self.observed_variables.len();
            let is_unassigned =
                |lit: i32| !satisfied_literals.contains(&lit) && !satisfied_literals.contains(&-lit);
            if n < self.observed_variables.len() {
                // find the n-th unassigned variable from the beginning of observe
                let mut it = self.observed_variables.iter().peekable();
                let incr: usize = 0;
                while incr < n && it.peek().is_some() {
                    if is_unassigned(**it.peek().unwrap()) {
                        n += 1;
                    }
                    it.next();
                }
                if let Some(&&lit) = it.peek() {
                    if is_unassigned(lit) {
                        mlog!(self, true, "cb_decide returns unassigned{}\n", -lit);
                        return -lit;
                    }
                }
                mlog!(self, false, "cb_decide returns 0\n");
                return 0;
            } else {
                mlog!(self, true, "cb_decide returns 0\n");
                return 0;
            }
        }
        mlog!(self, true, "cb_decide returns 0\n");
        0
    }

    fn cb_propagate_impl(&mut self) -> i32 {
        mlogc!(self, true, "cb_propagate starts\n");
        debug_assert!(self.compare_trails());

        let mut lit_sum: usize = 0; // sum of variables of satisfied observed literals
        let mut lowest_lit = 0; // the lowest satisfied observed literal
        let mut highest_lit = 0; // the highest satisfied observed literal

        let satisfied_literals = self.current_observed_satisfied_set(&mut lit_sum, &mut lowest_lit, &mut highest_lit);

        if satisfied_literals.is_empty() {
            mlogc!(self, true, "cb_propagate returns 0 (there are no observed satisfied literals).\n");
            return 0;
        }

        mlogc!(self, true, "\n");
        debug_assert!(lowest_lit != 0);
        debug_assert!(highest_lit != 0);

        let mut unassigned_var = 0;
        for &v in &self.observed_variables {
            if !satisfied_literals.contains(&v) && !satisfied_literals.contains(&-v) {
                unassigned_var = v;
                break;
            }
        }

        if unassigned_var == 0 {
            mlog!(self, true, "cb_propagate returns 0 (there are no unassigned observed variables).\n");
            return 0;
        }

        debug_assert!(self.clause.is_empty());
        let mut propagated_lit = 0;

        if lit_sum % 5 == 0 && satisfied_literals.len() > 1 {
            self.clause = vec![unassigned_var, -lowest_lit, -highest_lit];
        } else if lit_sum % 7 == 0 && !satisfied_literals.is_empty() {
            self.clause = vec![unassigned_var, -highest_lit];
        } else if lit_sum % 11 == 0 {
            self.clause = vec![unassigned_var];
        } else if lit_sum > 15 && lowest_lit != 0 {
            // Propagate a falsified literal, ok if lowest == highest
            self.clause = vec![-lowest_lit, -highest_lit];
        }

        if !self.clause.is_empty() {
            propagated_lit = self.clause[0];
            let id = self.add_new_lemma(true);
            self.external_lemmas[id].propagation_reason = true;
            self.reason_map.insert(propagated_lit, id as i32);
            mlog!(self, true, "new clause added to reason map for {} with id {}\n", propagated_lit, id);
            self.clause.clear();
        }

        mlog!(self, true, "cb_propagate returns {}\n", propagated_lit);

        propagated_lit
    }

    fn current_observed_satisfied_set(
        &mut self,
        lit_sum: &mut usize,
        lowest_lit: &mut i32,
        highest_lit: &mut i32,
    ) -> BTreeSet<i32> {
        *lit_sum = 0;
        *lowest_lit = 0;
        *highest_lit = 0;
        let mut satisfied_literals = BTreeSet::new();

        for l in 0..self.observed_trail.len() {
            for k in 0..self.observed_trail[l].len() {
                let lit = self.observed_trail[l][k];
                if !self.solver().observed(lit) {
                    continue;
                }

                satisfied_literals.insert(lit);
                *lit_sum = lit_sum.wrapping_add(lit.wrapping_abs() as usize);

                if *lowest_lit == 0 {
                    *lowest_lit = lit;
                }
                *highest_lit = lit;
            }
        }

        satisfied_literals
    }

    fn cb_add_reason_clause_lit_impl(&mut self, plit: i32) -> i32 {
        // At that point there is no need to assume that the trails are in
        // synchron.
        debug_assert!(self.reason_map.contains_key(&plit));

        let reason_id = *self.reason_map.entry(plit).or_insert(0) as usize;

        let lit = self.external_lemmas[reason_id].next_lit();

        if lit == 0 {
            self.external_lemmas[reason_id].add_count += 1;
            mlog!(self, true, "reason clause (id: {}) is added.\n", reason_id);
        }

        lit
    }

    fn notify_assignment_impl(&mut self, lits: &[i32]) {
        mlog!(
            self,
            false,
            "notified {} new assignments on level {}",
            lits.len(),
            self.observed_trail.len().wrapping_sub(1)
        );
        #[cfg(debug_assertions)]
        mlogc!(self, false, ": [ ");
        #[cfg(not(debug_assertions))]
        mlogc!(self, true, "\n");
        for &lit in lits {
            self.observed_trail.last_mut().unwrap().push(lit);
            self.unassigned_reasons.remove(&lit);
            #[cfg(debug_assertions)]
            mlogc!(self, false, "{} ", lit);
        }
        #[cfg(debug_assertions)]
        mlogc!(self, true, "]\n");
    }

    fn notify_new_decision_level_impl(&mut self) {
        mlog!(
            self,
            true,
            "notify new decision level {} -> {}\n",
            self.observed_trail.len().wrapping_sub(1),
            self.observed_trail.len()
        );
        self.observed_trail.push(Vec::new());
    }

    fn notify_backtrack_impl(&mut self, new_level: usize) {
        mlog!(self, true, "notify backtrack: {} -> {}\n", self.observed_trail.len().wrapping_sub(1), new_level);
        debug_assert!(self.observed_trail.len() > 1 || new_level == 0);
        debug_assert!(self.observed_trail.len() == 1 || self.observed_trail.len() >= new_level + 1);
        while self.observed_trail.len() > new_level + 1 {
            // We can not remove reason clauses of backtracked assignments because
            // ILB might re-introduces them to the trail. Here we only save the
            // potential candidates to delete, and upon next cb_decide we delete
            // those ones that did not get re-assigned.
            let back = self.observed_trail.last().unwrap();
            for &lit in back {
                if self.reason_map.contains_key(&lit) {
                    self.unassigned_reasons.insert(lit);
                }
            }
            #[cfg(debug_assertions)]
            {
                mlog!(self, false, "unassign during backtrack from level {}: ", self.observed_trail.len() - 1);
                #[cfg(feature = "logging")]
                for &lit in self.observed_trail.last().unwrap() {
                    mlogc!(self, false, "{} ", lit);
                }
                mlogc!(self, true, "\n");
            }
            self.observed_trail.pop();
        }
    }

    /* ----------------- ExternalPropagator functions end ------------------*/
}

/// The C++ `MockPropagator` object is connected to the solver both as
/// external propagator and as fixed assignment listener, while it is also
/// owned (and deleted) by `Mobical` (`mock_pointer`).  The solver owns
/// these thin forwarding boxes instead.
struct MockPropagatorRef(*mut MockPropagator);

impl MockPropagatorRef {
    #[allow(clippy::mut_from_ref)]
    fn mp(&self) -> &mut MockPropagator {
        // SAFETY: 'mock_pointer' is deleted only after disconnecting it or
        // deleting the solver (as in C++).
        unsafe { &mut *self.0 }
    }
}

impl FixedAssignmentListener for MockPropagatorRef {
    fn notify_fixed_assignment(&mut self, lit: i32) {
        self.mp().notify_fixed_assignment_impl(lit)
    }
}

impl ExternalPropagator for MockPropagatorRef {
    fn notify_assignment(&mut self, lits: &[i32]) {
        self.mp().notify_assignment_impl(lits)
    }
    fn notify_new_decision_level(&mut self) {
        self.mp().notify_new_decision_level_impl()
    }
    fn notify_backtrack(&mut self, new_level: usize) {
        self.mp().notify_backtrack_impl(new_level)
    }
    fn cb_check_found_model(&mut self, model: &[i32]) -> bool {
        self.mp().cb_check_found_model_impl(model)
    }
    fn cb_decide(&mut self) -> i32 {
        self.mp().cb_decide_impl()
    }
    fn cb_propagate(&mut self) -> i32 {
        self.mp().cb_propagate_impl()
    }
    fn cb_add_reason_clause_lit(&mut self, propagated_lit: i32) -> i32 {
        self.mp().cb_add_reason_clause_lit_impl(propagated_lit)
    }
    fn cb_has_external_clause(&mut self, is_forgettable: &mut bool) -> bool {
        self.mp().cb_has_external_clause_impl(is_forgettable)
    }
    fn cb_add_external_clause_lit(&mut self) -> i32 {
        self.mp().cb_add_external_clause_lit_impl()
    }
}

/*------------------------------------------------------------------------*/

// This is the class for the Mobical application.

// We have the following modes, where 'RANDOM' mode can not be combined
// with any other mode and 'OUTPUT' mode requires that 'SEED' or 'INPUT'
// mode is set too, but it is not possible to combine 'SEED' and 'INPUT'.

const RANDOM: i32 = 1;
const SEED: i32 = 2;
const INPUT: i32 = 4;
const OUTPUT: i32 = 8;

pub(crate) struct Mobical {
    mode: i32, // No 'Mode mode' due to 'mode |= ...' below.

    // Global options (set by parsing command line options in 'main').
    donot: DoNot,
    force: Force,

    verbose: bool,
    quiet: bool,

    add_set_log_to_true: bool,
    add_dump_before_solve: bool,
    add_stats_after_solve: bool,
    add_plain_after_options: bool,

    shrinking: bool, // In the middle of shrinking.
    running: bool,   // In the middle of running.

    time_limit: i64,  // in seconds, none if zero
    space_limit: i64, // in MB, none if zero

    notified: Vec<u8>,

    progress_counter: i32,
    last_progress_time: f64,

    shared: *mut Shared, // shared among parent and child processes

    traces: i64,
    spurious: i64,

    mock_pointer: *mut MockPropagator, // to be able to clean up withouth disconnect
}

static mut MOBICAL: *mut Mobical = ptr::null_mut();

/// The global `mobical` object.
#[allow(clippy::mut_from_ref)]
fn m() -> &'static mut Mobical {
    // SAFETY: set at the start of 'main' and never freed.
    unsafe { &mut *MOBICAL }
}

/// `Terminal &terminal = terr;`
fn terminal() -> &'static Terminal {
    terr()
}

impl Mobical {
    fn new() -> Mobical {
        let prot = libc::PROT_READ | libc::PROT_WRITE;
        let flags = libc::MAP_ANON | libc::MAP_SHARED;
        // SAFETY: anonymous shared mapping.
        let shared =
            unsafe { libc::mmap(ptr::null_mut(), std::mem::size_of::<Shared>(), prot, flags, -1, 0) } as *mut Shared;
        Mobical {
            mode: 0,
            donot: DoNot::default(),
            force: Force::default(),
            verbose: false,
            quiet: false,
            add_set_log_to_true: false,
            add_dump_before_solve: false,
            add_stats_after_solve: false,
            add_plain_after_options: false,
            shrinking: false,
            running: false,
            time_limit: DEFAULT_TIME_LIMIT,
            space_limit: DEFAULT_SPACE_LIMIT,
            notified: Vec::new(),
            progress_counter: 0,
            last_progress_time: 0.0,
            shared,
            traces: 0,
            spurious: 0,
            mock_pointer: ptr::null_mut(),
        }
    }

    fn shared(&self) -> Option<&'static mut Shared> {
        if self.shared.is_null() {
            None
        } else {
            // SAFETY: shared anonymous mapping of one 'Shared'.
            Some(unsafe { &mut *self.shared })
        }
    }

    // The mode invariant of the last comment can be checked with this code:

    fn check_mode_valid() {
        #[cfg(debug_assertions)]
        {
            let mode = m().mode;
            debug_assert!(mode & (RANDOM | SEED | INPUT | OUTPUT) != 0);
            if mode & RANDOM != 0 {
                debug_assert!(mode & SEED == 0);
            }
            if mode & RANDOM != 0 {
                debug_assert!(mode & INPUT == 0);
            }
            if mode & RANDOM != 0 {
                debug_assert!(mode & OUTPUT == 0);
            }
            if mode & OUTPUT != 0 {
                debug_assert!(mode & (SEED | INPUT) != 0);
            }
            debug_assert!(!((mode & SEED != 0) && (mode & INPUT != 0)));
        }
    }

    /* As a formula this is

      (RANDOM | SEED | INPUT | OUTPUT) &
      (RANDOM -> !SEED)
      (RANDOM -> !INPUT) &
      (RANDOM -> !OUTPUT) &
      (OUTPUT -> SEED | INPUT) &
      !(SEED & INPUT)

    It has exactly the following 5 out of 16 models

      RANDOM !SEED !INPUT !OUTPUT
      !RANDOM SEED !INPUT !OUTPUT
      !RANDOM SEED !INPUT OUTPUT
      !RANDOM !SEED INPUT OUTPUT
      !RANDOM !SEED INPUT !OUTPUT
    */

    fn prefix_string() -> &'static str {
        if !terminal().colors() {
            "m "
        } else {
            "\x1b[34mm \x1b[0m"
        }
    }

    fn prefix() {
        if !m().quiet {
            cerr().s(Mobical::prefix_string()).flush();
        }
    }

    fn error_prefix() {
        fflush(c_stderr());
        fflush(c_stdout());
        terminal().bold();
        fputs("mobical: ", c_stderr());
        terminal().normal();
    }

    fn die(msg: &str) -> ! {
        Mobical::error_prefix();
        terminal().red(true);
        fputs("error: ", c_stderr());
        terminal().normal();
        fputs(msg, c_stderr());
        fputc(b'\n' as i32, c_stderr());
        fflush(c_stderr());
        terminal().reset();
        // SAFETY: 'exit' (flushes C stdio as in C++).
        unsafe { libc::exit(1) }
    }

    fn warning(msg: &str) {
        Mobical::error_prefix();
        terminal().yellow(false);
        fputs("warning: ", c_stderr());
        terminal().normal();
        fputs(msg, c_stderr());
        fputc(b'\n' as i32, c_stderr());
        fflush(c_stderr());
    }

    fn hline() {
        Mobical::prefix();
        terminal().normal();
        cerr().setfill('-').setw(76).s("").setfill(' ').endl();
        terminal().normal();
    }

    fn empty_line() {
        cerr().s(Mobical::prefix_string()).endl();
    }

    fn print_statistics() {
        let quiet = m().quiet;
        if !quiet {
            Mobical::hline();
        }
        Mobical::prefix();

        // SAFETY: plain static counters (single threaded).
        let (generated, ok, failed, executed) = unsafe { (GENERATED, OK, FAILED, EXECUTED) };

        cerr().s("generated ").d(generated).s(" traces: ");
        if ok > 0 {
            terminal().green(true);
        }
        cerr().d(ok).s(" ok ").d(rounded_percent(ok as f64, generated as f64)).s("%");
        if ok > 0 {
            terminal().normal();
        }
        cerr().s(", ");
        if failed > 0 {
            terminal().red(true);
        }
        cerr().d(failed).s(" failed ").d(rounded_percent(failed as f64, generated as f64)).s("%");
        if failed > 0 {
            terminal().normal();
        }
        cerr().s(", ").d(executed).s(" executed").endl().flush();

        if let Some(shared) = m().shared() {
            Mobical::prefix();
            cerr()
                .s("solved ")
                .d(shared.solved)
                .s(": ")
                .s(terr().blue_code())
                .d(shared.sat)
                .s(" sat ")
                .d(rounded_percent(shared.sat as f64, shared.solved as f64))
                .s("%")
                .s(terr().normal_code())
                .s(", ")
                .s(terr().magenta_code())
                .d(shared.unsat)
                .s(" unsat ")
                .d(rounded_percent(shared.unsat as f64, shared.solved as f64))
                .s("%")
                .s(terr().normal_code())
                .s(", ")
                .d(shared.incremental)
                .s(" incremental ")
                .d(rounded_percent(shared.incremental as f64, shared.solved as f64))
                .s("%")
                .s(terr().normal_code())
                .s(", ")
                .s(terr().yellow_code())
                .d(shared.oom)
                .s(" oom ")
                .d(rounded_percent(shared.oom as f64, shared.solved as f64))
                .s("%")
                .endl()
                .flush();
            if shared.memout != 0 || shared.timeout != 0 {
                Mobical::prefix();
                cerr()
                    .s("out-of-time ")
                    .d(shared.timeout)
                    .s(", ")
                    .s("out-of-memory ")
                    .d(shared.memout)
                    .endl()
                    .flush();
            }
        }

        let (spurious, traces) = (m().spurious, m().traces);
        if spurious != 0 {
            Mobical::prefix();
            cerr()
                .s("generated ")
                .d(spurious)
                .s(" spurious traces ")
                .d(rounded_percent(spurious as f64, traces as f64))
                .s("%")
                .endl()
                .flush();
        }
    }

    fn summarize(trace: &Trace, bright: bool) {
        if bright {
            terminal().cyan(bright);
        } else {
            terminal().blue(false);
        }
        cerr().right().setw(5).d(trace.size());
        terminal().normal();
        cerr().c(' ');
        terminal().magenta(bright);
        cerr().c(' ').right().setw(3).d(trace.vars());
        terminal().yellow(bright);
        cerr().c(' ').left().setw(4).d(trace.clauses());
        terminal().normal();
        cerr().c(' ');
        if bright {
            terminal().cyan(bright);
        } else {
            terminal().blue(false);
        }
        cerr().setw(2).right().d(trace.phases());
        terminal().normal();
    }

    fn progress(trace: &Trace) {
        Mobical::notify(trace, -1)
    }

    fn notify(trace: &Trace, ch: i8) {
        if m().quiet {
            return;
        }
        let first = m().notified.is_empty();
        if ch < 0 && (!terminal().connected() || m().verbose) {
            return;
        }
        let t = absolute_real_time();
        if ch > 0 {
            m().notified.push(ch as u8);
            m().progress_counter = 1;
        } else if ch < 0 {
            if t < m().last_progress_time + 0.3 {
                return;
            }
            m().progress_counter += 1;
        }
        if !first || (m().mode & OUTPUT) == 0 {
            terminal().erase_line_if_connected_otherwise_new_line();
        }
        Mobical::prefix();
        let traces = m().traces;
        if traces != 0 {
            cerr().c(' ').left().setw(12).d(traces);
        } else {
            cerr().left().setw(13).s("reduce:");
        }
        terminal().yellow(false);

        let notified = m().notified.clone();
        if !notified.is_empty() {
            let mut i = 0;
            while i + 1 < notified.len() {
                cerr().c(notified[i] as char);
                i += 1;
            }
            if m().progress_counter & 1 != 0 {
                terminal().inverse();
            }
            cerr().c(*notified.last().unwrap() as char);
            terminal().normal();
        }

        if notified.len() < 45 {
            cerr().setw(45 - notified.len() as i64).s(" ");
        }
        cerr().flush();
        Mobical::summarize(trace, false);
        if m().verbose {
            cerr().endl();
        }
        cerr().flush();
        m().last_progress_time = t;
    }

    fn is_unsigned_str(str: &str) -> bool {
        let p = str.as_bytes();
        if p.is_empty() {
            return false;
        }
        if !p[0].is_ascii_digit() {
            return false;
        }
        p[1..].iter().all(|c| c.is_ascii_digit())
    }

    fn parse_seed(str: &str) -> u64 {
        let max: u64 = !0u64;
        let mut res: u64 = 0;
        for &ch in str.as_bytes() {
            if max / 10 < res {
                Mobical::die(&format!("invalid seed '{}' (too many digits)", str));
            }
            res *= 10;
            debug_assert!(ch.is_ascii_digit());
            let digit = (ch as u32).wrapping_sub(b'0' as u32) as u64;
            if max - digit < res {
                Mobical::die(&format!("invalid seed '{}' (too large)", str));
            }
            res += digit;
        }
        res
    }

    fn header() {
        terminal().blue(false);
        cerr().s("calls");
        terminal().magenta(false);
        cerr().s(" vars");
        terminal().yellow(false);
        cerr().s(" clauses");
        terminal().normal();
    }
}

impl Handler for Mobical {
    fn catch_signal(&mut self, sig: i32) {
        Signal::set_received(sig);

        if (m().mode & RANDOM) == 0 && !m().shrinking {
            // SAFETY: plain static counters.
            unsafe {
                if EXECUTED != 0 && FAILED == 0 && OK == 0 {
                    debug_assert!(m().mode & (INPUT | SEED) != 0);
                    FAILED = 1;
                }
            }
            Signal::reset();
            // SAFETY: 'raise'.
            unsafe {
                libc::raise(sig);
            }
        }
    }
}

fn rounded_percent(a: f64, b: f64) -> i32 {
    (0.5 + percent(a, b)) as i32
}

/*------------------------------------------------------------------------*/

// Abstraction of individual API calls.  The call sequences are assumed to
// have the following structure
//
//   INIT
//   (SET|TRACEPROOF|ALWAYS)*
//   (
//     (ADD|ASSUME|ALWAYS)*
//     [
//       (SOLVE|SIMPLIFY|LOOKAHEAD)
//       (LEMMA|CONTINUE)*
//       (VAL|FLIP|FAILED|ALWAYS|CONCLUDE|FLUSHPROOFTRACE|CLOSEPROOFTRACE)*
//     ]
//   )*
//   [ RESET ]
//
// where 'ALWAYS' calls as defined below do not change the state.  With
// the other short-cuts below we can abstract this to
//
//   CONFIG* (BEFORE* [ PROCESS DURING* AFTER* ] )* [ RESET ]
//
// If traces are read then they are checked to have this structure.  We
// check that 'ADD' sequences terminate by adding zero literal before
// another call is made ('ASSUME|ALWAYS|SOLVE|SIMPLIFY|LOOKAHEAD').
//
// Furthermore the execution engine (both for read and generated traces)
// makes sure that additional contract requirements are always met.  For
// instance 'val' is only executed if the solver is in the 'SATISFIABLE'
// state, and similar for 'failed', 'melt' etc.
//
// If the user wants to understand why a trace obtained through
// 'CADICAL_API_TRACE' is violating an API contract, then these checks
// are problematic and can be disabled by using the command line option
// '--do-not-enforce-contracts'.
//
// Note that our model based tester is actually more restrictive and does
// not produce all these possible call sequences. For instance it first
// adds all clauses before making assumptions and also does not mix in
// these 'ALWAYS' calls in all possible ways.

const fn shift(bit: u64) -> u64 {
    1u64 << bit
}

type CallType = u64;

const INIT: CallType = shift(0);
const SET: CallType = shift(1);
const CONFIGURE: CallType = shift(2);

const VARS: CallType = shift(3);
const ACTIVE: CallType = shift(4);
const REDUNDANT: CallType = shift(5);
const IRREDUNDANT: CallType = shift(6);
const RESIZE: CallType = shift(7);

const PHASE: CallType = shift(8);

const ADD: CallType = shift(9);
const ASSUME: CallType = shift(10);

const SOLVE: CallType = shift(11);
const SIMPLIFY: CallType = shift(12);
const LOOKAHEAD: CallType = shift(13);
const CUBING: CallType = shift(14);
const PROPAGATE: CallType = shift(15);

const VAL: CallType = shift(16);
const FLIP: CallType = shift(17);
const FLIPPABLE: CallType = shift(18);
const FAILED_: CallType = shift(19);
const FIXED: CallType = shift(20);

const FREEZE: CallType = shift(21);
const FROZEN: CallType = shift(22);
const MELT: CallType = shift(23);

const LIMIT: CallType = shift(24);
const OPTIMIZE: CallType = shift(25);

const DUMP: CallType = shift(26);
const STATS: CallType = shift(27);

const RESET: CallType = shift(28);

const CONSTRAIN: CallType = shift(29);

const CONNECT: CallType = shift(30);
const OBSERVE: CallType = shift(31);
const LEMMA: CallType = shift(32);

const CONCLUDE: CallType = shift(33);
const DISCONNECT: CallType = shift(34);

const TRACEPROOF: CallType = shift(35);
const FLUSHPROOFTRACE: CallType = shift(36);
const CLOSEPROOFTRACE: CallType = shift(37);

const PROPAGATE_ASSUMPTIONS: CallType = shift(40);
const IMPLIED_LITERALS: CallType = shift(41);
const RESET_ASSUMPTIONS: CallType = shift(42);

const RESIZE_DIFFERENCE: CallType = shift(43);

const ALWAYS: CallType = VARS
    | ACTIVE
    | REDUNDANT
    | IRREDUNDANT
    | FREEZE
    | FROZEN
    | MELT
    | LIMIT
    | OPTIMIZE
    | DUMP
    | STATS
    | RESIZE
    | FIXED
    | PHASE
    | RESIZE_DIFFERENCE;
const CONFIG: CallType = INIT | SET | CONFIGURE | ALWAYS | TRACEPROOF;
const BEFORE: CallType = ADD | CONSTRAIN | ASSUME | ALWAYS | DISCONNECT | CONNECT | OBSERVE;
const PROCESS: CallType = SOLVE | SIMPLIFY | LOOKAHEAD | CUBING | PROPAGATE;
const DURING: CallType = LEMMA;
const LITTYPE: CallType =
    PHASE | ADD | ASSUME | VAL | FLIP | FLIPPABLE | FAILED_ | FIXED | FREEZE | FROZEN | MELT | CONSTRAIN | OBSERVE | LEMMA;
const EXTENDMAP: CallType = PHASE | ADD | ASSUME | FREEZE | CONSTRAIN;
const AFTER: CallType =
    VAL | FLIP | FLIPPABLE | FAILED_ | CONCLUDE | ALWAYS | FLUSHPROOFTRACE | CLOSEPROOFTRACE | PROPAGATE_ASSUMPTIONS;

/// The dynamic class of a C++ `Call` object.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Kind {
    Init,
    Vars,
    Active,
    Redundant,
    Irredundant,
    Resize,
    DeclareMoreVariables,
    DeclareOneMoreVariable,
    Phase,
    Set,
    Configure,
    Limit,
    Optimize,
    Reset,
    Add,
    Constrain,
    Connect,
    Observe,
    Lemma,
    Disconnect,
    Assume,
    Solve,
    Simplify,
    PropagateAssumptions,
    Implied,
    ResetAssumptions,
    Lookahead,
    Cubing,
    Propagate,
    Val,
    Flip,
    Flippable,
    Fixed,
    Failed,
    Conclude,
    Freeze,
    Melt,
    Frozen,
    Dump,
    Stats,
    TraceProof,
    FlushProofTrace,
    CloseProofTrace,
}

pub(crate) struct Call {
    kind: Kind,

    type_: CallType, // Explicit typing.

    arg: i32,             // Argument if necessary.
    res: i64,             // Compute result if any.
    name: Option<String>, // Option name for 'set' and 'config'
    val: i32,             // Option value for 'set'.

    path: String, // 'TraceProofCall::path'
}

fn config_type(t: CallType) -> bool {
    (t & CONFIG) != 0
}

fn before_type(t: CallType) -> bool {
    (t & BEFORE) != 0
}

fn process_type(t: CallType) -> bool {
    (t & PROCESS) != 0
}

fn after_type(t: CallType) -> bool {
    (t & AFTER) != 0
}

/// Access to the solver ('Solver *&s' dereferenced).
#[allow(clippy::mut_from_ref)]
fn sv(s: &*mut Solver) -> &mut Solver {
    // SAFETY: the solver is allocated by 'InitCall' with 'Box::into_raw'
    // and only deleted by 'ResetCall' / 'Trace::clear'.
    unsafe { &mut **s }
}

#[allow(clippy::mut_from_ref)]
fn em(e: *mut ExtendMap) -> &'static mut ExtendMap {
    // SAFETY: the 'extendmap' of the executed trace.
    unsafe { &mut *e }
}

impl Call {
    /// `Call (Type t, int a = 0, int r = 0, const char *o = 0, int v = 0)`.
    fn new(kind: Kind, t: CallType, a: i32, r: i32, o: Option<&str>, v: i32) -> Call {
        Call { kind, type_: t, arg: a, res: r as i64, name: o.map(|s| s.to_string()), val: v, path: String::new() }
    }

    // The constructors of the sub-classes (with C++ default arguments made
    // explicit).

    fn init() -> Call {
        Call::new(Kind::Init, INIT, 0, 0, None, 0)
    }
    fn vars() -> Call {
        Call::new(Kind::Vars, VARS, 0, 0, None, 0)
    }
    fn active() -> Call {
        Call::new(Kind::Active, ACTIVE, 0, 0, None, 0)
    }
    fn redundant() -> Call {
        Call::new(Kind::Redundant, REDUNDANT, 0, 0, None, 0)
    }
    fn irredundant() -> Call {
        Call::new(Kind::Irredundant, IRREDUNDANT, 0, 0, None, 0)
    }
    fn resize(max_var: i32) -> Call {
        Call::new(Kind::Resize, RESIZE, max_var, 0, None, 0)
    }
    fn declare_more_variables(max_var: i32) -> Call {
        Call::new(Kind::DeclareMoreVariables, RESIZE, max_var, 0, None, 0)
    }
    fn declare_one_more_variable() -> Call {
        Call::new(Kind::DeclareOneMoreVariable, RESIZE, 0, 0, None, 0)
    }
    fn phase(max_var: i32) -> Call {
        Call::new(Kind::Phase, PHASE, max_var, 0, None, 0)
    }
    fn set(o: &str, v: i32) -> Call {
        Call::new(Kind::Set, SET, 0, 0, Some(o), v)
    }
    fn configure(o: &str) -> Call {
        Call::new(Kind::Configure, CONFIGURE, 0, 0, Some(o), 0)
    }
    fn limit(o: &str, v: i32) -> Call {
        Call::new(Kind::Limit, LIMIT, 0, 0, Some(o), v)
    }
    fn optimize(v: i32) -> Call {
        Call::new(Kind::Optimize, OPTIMIZE, 0, 0, None, v)
    }
    fn reset() -> Call {
        Call::new(Kind::Reset, RESET, 0, 0, None, 0)
    }
    fn add(l: i32) -> Call {
        Call::new(Kind::Add, ADD, l, 0, None, 0)
    }
    fn constrain(l: i32) -> Call {
        Call::new(Kind::Constrain, CONSTRAIN, l, 0, None, 0)
    }
    fn connect() -> Call {
        Call::new(Kind::Connect, CONNECT, 0, 0, None, 0)
    }
    fn observe(l: i32) -> Call {
        Call::new(Kind::Observe, OBSERVE, l, 0, None, 0)
    }
    fn lemma(l: i32) -> Call {
        Call::new(Kind::Lemma, LEMMA, l, 0, None, 0)
    }
    fn disconnect() -> Call {
        Call::new(Kind::Disconnect, DISCONNECT, 0, 0, None, 0)
    }
    fn assume(l: i32) -> Call {
        Call::new(Kind::Assume, ASSUME, l, 0, None, 0)
    }
    /// `SolveCall (int r = 0)`.
    fn solve(r: i32) -> Call {
        Call::new(Kind::Solve, SOLVE, 0, r, None, 0)
    }
    /// `SimplifyCall (int rounds, int r = 0)`.
    fn simplify(rounds: i32, r: i32) -> Call {
        Call::new(Kind::Simplify, SIMPLIFY, rounds, r, None, 0)
    }
    /// `PropagateAssumptionsCall (int r = 0)`.
    fn propagate_assumptions(r: i32) -> Call {
        Call::new(Kind::PropagateAssumptions, PROPAGATE_ASSUMPTIONS, 0, r, None, 0)
    }
    /// `ImpliedCall (int r = 0)`.
    fn implied(r: i32) -> Call {
        Call::new(Kind::Implied, IMPLIED_LITERALS, 0, r, None, 0)
    }
    /// `ResetAssumptionsCall (int r = 0)`.
    fn reset_assumptions(r: i32) -> Call {
        Call::new(Kind::ResetAssumptions, RESET_ASSUMPTIONS, 0, r, None, 0)
    }
    /// `LookaheadCall (int r = 0)`.
    fn lookahead(r: i32) -> Call {
        Call::new(Kind::Lookahead, LOOKAHEAD, 0, r, None, 0)
    }
    /// `CubingCall (int r = 1)`.
    fn cubing(r: i32) -> Call {
        Call::new(Kind::Cubing, CUBING, 0, r, None, 0)
    }
    /// `PropagateCall (int r = 0)`.
    fn propagate(r: i32) -> Call {
        Call::new(Kind::Propagate, PROPAGATE, 0, r, None, 0)
    }
    /// `ValCall (int l, int r = 0)`.
    fn val(l: i32, r: i32) -> Call {
        Call::new(Kind::Val, VAL, l, r, None, 0)
    }
    /// `FlipCall (int l, int r = 0)`.
    fn flip(l: i32, r: i32) -> Call {
        Call::new(Kind::Flip, FLIP, l, r, None, 0)
    }
    /// `FlippableCall (int l, int r = 0)`.
    fn flippable(l: i32, r: i32) -> Call {
        Call::new(Kind::Flippable, FLIPPABLE, l, r, None, 0)
    }
    /// `FixedCall (int l, int r = 0)`.
    fn fixed(l: i32, r: i32) -> Call {
        Call::new(Kind::Fixed, FIXED, l, r, None, 0)
    }
    /// `FailedCall (int l, int r = 0)`.
    fn failed(l: i32, r: i32) -> Call {
        Call::new(Kind::Failed, FAILED_, l, r, None, 0)
    }
    fn conclude() -> Call {
        Call::new(Kind::Conclude, CONCLUDE, 0, 0, None, 0)
    }
    fn freeze(l: i32) -> Call {
        Call::new(Kind::Freeze, FREEZE, l, 0, None, 0)
    }
    fn melt(l: i32) -> Call {
        Call::new(Kind::Melt, MELT, l, 0, None, 0)
    }
    /// `FrozenCall (int l, int r = 0)`.
    fn frozen(l: i32, r: i32) -> Call {
        Call::new(Kind::Frozen, FROZEN, l, r, None, 0)
    }
    fn dump() -> Call {
        Call::new(Kind::Dump, DUMP, 0, 0, None, 0)
    }
    fn stats() -> Call {
        Call::new(Kind::Stats, STATS, 0, 0, None, 0)
    }
    fn trace_proof(p: &str) -> Call {
        let mut res = Call::new(Kind::TraceProof, TRACEPROOF, 0, 0, None, 0);
        res.path = p.to_string();
        res
    }
    fn flush_proof_trace() -> Call {
        Call::new(Kind::FlushProofTrace, FLUSHPROOFTRACE, 0, 0, None, 0)
    }
    fn close_proof_trace() -> Call {
        Call::new(Kind::CloseProofTrace, CLOSEPROOFTRACE, 0, 0, None, 0)
    }

    fn name(&self) -> &str {
        self.name.as_deref().unwrap_or("")
    }

    fn lit_type(&self) -> bool {
        (self.type_ & LITTYPE) != 0
    }

    fn extendmap_type(&self) -> bool {
        ((self.type_ as i32) & (EXTENDMAP as i32)) != 0
    }

    fn extend_map(&self, s: &mut *mut Solver, extendmap: *mut ExtendMap) {
        let map = &mut em(extendmap).map;
        if map.is_empty() {
            map.push(0); // 0 is always mapped to 0
        }
        if self.arg == 0 {
            return;
        }
        let abs_arg = self.arg.unsigned_abs();
        if (abs_arg as usize) < map.len() {
            return; // arg is already mapped
        }
        let diff = (abs_arg as i32).wrapping_sub(map.len() as i32).wrapping_add(1);
        let max_var = sv(s).vars();
        let map = &mut em(extendmap).map;
        let want = (max_var as i64 + diff as i64) as usize;
        if want > map.capacity() {
            map.reserve(want - map.len());
        }
        for i in 1..=diff {
            map.push(max_var + i);
        }
    }

    fn map_arg(&self, s: &mut *mut Solver, extendmap: *mut ExtendMap) -> i32 {
        if !self.lit_type() {
            return self.arg;
        }
        if self.extendmap_type() {
            self.extend_map(s, extendmap);
        }
        let map = &em(extendmap).map;
        let abs_arg = self.arg.wrapping_abs();
        let sign = if self.arg > 0 { 1 } else { -1 };
        let map_size = map.len() as i32;
        if abs_arg < map_size {
            return map[abs_arg as usize] * sign;
        }
        let max_var = sv(s).vars();
        let diff = abs_arg - map_size + 1;
        sign * (max_var + diff)
    }

    /// The 'execute' functions of the sub-classes.
    fn execute(&mut self, s: &mut *mut Solver, extendmap: *mut ExtendMap) {
        match self.kind {
            Kind::Init => {
                *s = Box::into_raw(Box::new(Solver::new()));
                sv(s).set("factorcheck", 0);
                debug_assert!(em(extendmap).map.is_empty());
            }
            Kind::Vars => {
                self.res = sv(s).vars() as i64;
            }
            Kind::Active => {
                self.res = sv(s).active() as i64;
            }
            Kind::Redundant => {
                self.res = sv(s).redundant();
            }
            Kind::Irredundant => {
                self.res = sv(s).irredundant();
            }
            Kind::Resize => {
                let a = self.map_arg(s, extendmap);
                sv(s).resize(a);
            }
            Kind::DeclareMoreVariables => {
                let a = self.map_arg(s, extendmap);
                sv(s).declare_more_variables(a);
            }
            Kind::DeclareOneMoreVariable => {
                sv(s).declare_one_more_variable();
            }
            Kind::Phase => {
                let a = self.map_arg(s, extendmap);
                sv(s).phase(a);
            }
            Kind::Set => {
                sv(s).set(self.name(), self.val);
            }
            Kind::Configure => {
                sv(s).configure(self.name());
                sv(s).set("factorcheck", 0);
            }
            Kind::Limit => {
                sv(s).limit(self.name(), self.val);
            }
            Kind::Optimize => {
                sv(s).optimize(self.val);
            }
            Kind::Reset => {
                em(extendmap).map.clear();
                if !s.is_null() {
                    // SAFETY: allocated with 'Box::into_raw' by 'InitCall'.
                    drop(unsafe { Box::from_raw(*s) });
                }
                *s = ptr::null_mut();
                if !m().mock_pointer.is_null() {
                    // SAFETY: allocated with 'Box::into_raw' by 'ConnectCall'.
                    drop(unsafe { Box::from_raw(m().mock_pointer) });
                    m().mock_pointer = ptr::null_mut();
                }
            }
            Kind::Add => {
                let a = self.map_arg(s, extendmap);
                sv(s).add(a);
            }
            Kind::Constrain => {
                let a = self.map_arg(s, extendmap);
                sv(s).constrain(a);
            }
            Kind::Connect => {
                // clean up if there was already one mock propagator
                let mut prev_pointer: *mut MockPropagator = ptr::null_mut();
                if !m().mock_pointer.is_null() {
                    prev_pointer = m().mock_pointer;
                }
                #[cfg(feature = "logging")]
                let with_logging = m().add_set_log_to_true;
                #[cfg(not(feature = "logging"))]
                let with_logging = false;
                m().mock_pointer = Box::into_raw(Box::new(MockPropagator::new(*s, extendmap, with_logging)));
                let mp = m().mock_pointer;
                sv(s).connect_external_propagator(Box::new(MockPropagatorRef(mp)));
                sv(s).connect_fixed_listener(Box::new(MockPropagatorRef(mp)));

                if !prev_pointer.is_null() {
                    // SAFETY: both are live 'Box::into_raw' allocations.
                    unsafe {
                        let prev_fixed = (*prev_pointer).observed_fixed.clone();
                        (*mp).add_prev_fixed(&prev_fixed);
                        drop(Box::from_raw(prev_pointer));
                    }
                } else {
                    // FixedAssignmentListener does not replay previous fixed assignment,
                    // collect them here explicitly -- EXPENSIVE
                    // In practice FixedAssignmentListener is there from the beginning if
                    // needed, in mobical we do not want to wire in this.

                    // SAFETY: live 'Box::into_raw' allocation.
                    unsafe { (*mp).collect_prev_fixed() };
                }
            }
            Kind::Observe => {
                // 'static_cast<MockPropagator *> (s->get_propagator ())': the
                // only external propagator ever connected is 'mock_pointer'.
                let has = sv(s).get_propagator().is_some();
                if has {
                    let mp = m().mock_pointer;
                    debug_assert!(!mp.is_null());
                    // SAFETY: the connected mock propagator.
                    unsafe { (*mp).add_observed_lit(self.arg) };
                }
            }
            Kind::Lemma => {
                let has = sv(s).get_propagator().is_some();
                if has {
                    let ok = if self.arg == 0 {
                        true
                    } else {
                        let a = self.map_arg(s, extendmap);
                        sv(s).observed(a)
                    };
                    if ok {
                        // || mobical.donot.enforce
                        let a = self.map_arg(s, extendmap);
                        let mp = m().mock_pointer;
                        debug_assert!(!mp.is_null());
                        // SAFETY: the connected mock propagator.
                        unsafe { (*mp).push_lemma_lit(a) };
                    }
                }
            }
            Kind::Disconnect => {
                let has = sv(s).get_propagator().is_some();
                let mp = if has { m().mock_pointer } else { ptr::null_mut() };
                if !mp.is_null() {
                    // SAFETY: the connected mock propagator.
                    unsafe { (*mp).remove_new_observed_var() };
                }
                drop(sv(s).disconnect_fixed_listener());
                if !mp.is_null() {
                    drop(sv(s).disconnect_external_propagator());
                    // SAFETY: allocated with 'Box::into_raw' by 'ConnectCall'.
                    drop(unsafe { Box::from_raw(mp) });
                    m().mock_pointer = ptr::null_mut();
                }
                debug_assert!(sv(s).external().propagator.is_none());
            }
            Kind::Assume => {
                let a = self.map_arg(s, extendmap);
                sv(s).assume(a);
            }
            Kind::Solve => {
                self.res = sv(s).solve() as i64;
            }
            Kind::Simplify => {
                self.res = sv(s).simplify(self.arg) as i64;
            }
            Kind::PropagateAssumptions => {
                sv(s).propagate();
            }
            Kind::Implied => {
                let mut entrailed: Vec<i32> = Vec::new();
                let state = sv(s).state();
                if m().donot.enforce || state == SATISFIED || state == INCONCLUSIVE {
                    sv(s).implied(&mut entrailed);
                }
            }
            Kind::ResetAssumptions => {
                sv(s).reset_assumptions();
            }
            Kind::Lookahead => {
                self.res = sv(s).lookahead() as i64;
            }
            Kind::Cubing => {
                let _ = sv(s).generate_cubes(self.arg, 0);
            }
            Kind::Propagate => {
                let res = sv(s).propagate();
                if res == 0 {
                    let mut implicants: Vec<i32> = Vec::new();
                    sv(s).implied(&mut implicants);
                }
            }
            Kind::Val => {
                if m().donot.enforce {
                    let a = self.map_arg(s, extendmap);
                    self.res = sv(s).val(a) as i64;
                } else if sv(s).state() == SATISFIED {
                    let a = self.map_arg(s, extendmap);
                    self.res = sv(s).val(a) as i64;
                } else {
                    self.res = 0;
                }
            }
            Kind::Flip => {
                if m().donot.enforce {
                    let a = self.map_arg(s, extendmap);
                    self.res = sv(s).flip(a) as i64;
                } else if sv(s).state() == SATISFIED {
                    let a = self.map_arg(s, extendmap);
                    self.res = sv(s).flip(a) as i64;
                } else {
                    self.res = 0;
                }
            }
            Kind::Flippable => {
                if m().donot.enforce {
                    let a = self.map_arg(s, extendmap);
                    self.res = sv(s).flippable(a) as i64;
                } else if sv(s).state() == SATISFIED {
                    let a = self.map_arg(s, extendmap);
                    self.res = sv(s).flippable(a) as i64;
                } else {
                    self.res = 0;
                }
            }
            Kind::Fixed => {
                let a = self.map_arg(s, extendmap);
                self.res = sv(s).fixed(a) as i64;
            }
            Kind::Failed => {
                if m().donot.enforce {
                    let a = self.map_arg(s, extendmap);
                    self.res = sv(s).failed(a) as i64;
                } else if sv(s).state() == UNSATISFIED {
                    let a = self.map_arg(s, extendmap);
                    self.res = sv(s).failed(a) as i64;
                } else {
                    self.res = 0;
                }
            }
            Kind::Conclude => {
                if m().donot.enforce {
                    sv(s).conclude();
                } else if sv(s).state() == UNSATISFIED || sv(s).state() == SATISFIED {
                    sv(s).conclude();
                }
            }
            Kind::Freeze => {
                let a = self.map_arg(s, extendmap);
                sv(s).freeze(a);
            }
            Kind::Melt => {
                let ok = m().donot.enforce || {
                    let a = self.map_arg(s, extendmap);
                    sv(s).frozen(a)
                };
                if ok {
                    let a = self.map_arg(s, extendmap);
                    sv(s).melt(a);
                }
            }
            Kind::Frozen => {
                let a = self.map_arg(s, extendmap);
                self.res = sv(s).frozen(a) as i64;
            }
            Kind::Dump => {
                sv(s).dump_cnf();
            }
            Kind::Stats => {
                sv(s).statistics();
            }
            Kind::TraceProof => {
                sv(s).trace_proof(&self.path);
            }
            Kind::FlushProofTrace => {
                sv(s).flush_proof_trace(false);
            }
            Kind::CloseProofTrace => {
                sv(s).close_proof_trace(false);
            }
        }
    }

    /// The 'print' functions of the sub-classes.
    fn print(&self, o: &mut OStream) {
        let (arg, res, val) = (self.arg, self.res, self.val);
        match self.kind {
            Kind::Init => o.s("init").endl(),
            Kind::Vars => o.s("vars").endl(),
            Kind::Active => o.s("active").endl(),
            Kind::Redundant => o.s("redundant").endl(),
            Kind::Irredundant => o.s("irredundant").endl(),
            Kind::Resize => o.s("resize ").d(arg).endl(),
            Kind::DeclareMoreVariables => o.s("declare_more_variables ").d(arg).endl(),
            Kind::DeclareOneMoreVariable => o.s("declare_one_more_variable").endl(),
            Kind::Phase => o.s("phase ").d(arg).endl(),
            Kind::Set => o.s("set ").s(self.name()).c(' ').d(val).endl(),
            Kind::Configure => o.s("configure ").s(self.name()).endl(),
            Kind::Limit => o.s("limit ").s(self.name()).c(' ').d(val).endl(),
            Kind::Optimize => o.s("optimize ").d(val).endl(),
            Kind::Reset => o.s("reset").endl(),
            Kind::Add => o.s("add ").d(arg).endl(),
            Kind::Constrain => o.s("constrain ").d(arg).endl(),
            Kind::Connect => o.s("connect mock-propagator").endl(),
            Kind::Observe => o.s("observe ").d(arg).endl(),
            Kind::Lemma => o.s("lemma ").d(arg).endl(),
            Kind::Disconnect => o.s("disconnect mock-propagator").endl(),
            Kind::Assume => o.s("assume ").d(arg).endl(),
            Kind::Solve => o.s("solve ").d(res).endl(),
            Kind::Simplify => o.s("simplify ").d(arg).s(" ").d(res).endl(),
            Kind::PropagateAssumptions => o.s("propagate_assumptions ").d(arg).s(" ").d(res).endl(),
            Kind::Implied => o.s("implied").endl(),
            Kind::ResetAssumptions => o.s("reset_assumptions").endl(),
            Kind::Lookahead => o.s("lookahead ").d(res).endl(),
            Kind::Cubing => o.s("cubing ").d(res).endl(),
            Kind::Propagate => o.s("propagate ").d(res).endl(),
            Kind::Val => o.s("val ").d(arg).c(' ').d(res).endl(),
            Kind::Flip => o.s("flip ").d(arg).c(' ').d(res).endl(),
            Kind::Flippable => o.s("flippable ").d(arg).c(' ').d(res).endl(),
            Kind::Fixed => o.s("fixed ").d(arg).c(' ').d(res).endl(),
            Kind::Failed => o.s("failed ").d(arg).c(' ').d(res).endl(),
            Kind::Conclude => o.s("conclude").endl(),
            Kind::Freeze => o.s("freeze ").d(arg).endl(),
            Kind::Melt => o.s("melt ").d(arg).endl(),
            Kind::Frozen => o.s("frozen ").d(arg).c(' ').d(res).endl(),
            Kind::Dump => o.s("dump").endl(),
            Kind::Stats => o.s("stats").endl(),
            Kind::TraceProof => o.s("trace_proof").c(' ').s(&self.path).endl(),
            Kind::FlushProofTrace => o.s("flush_proof_trace").endl(),
            Kind::CloseProofTrace => o.s("close_proof_trace").endl(),
        };
    }

    /// The 'keyword' functions of the sub-classes.
    fn keyword(&self) -> &'static str {
        match self.kind {
            Kind::Init => "init",
            Kind::Vars => "vars",
            Kind::Active => "active",
            Kind::Redundant => "redundant",
            Kind::Irredundant => "irredundant",
            Kind::Resize => "resize",
            Kind::DeclareMoreVariables => "declare_more_variables",
            Kind::DeclareOneMoreVariable => "declare_one_more_variable",
            Kind::Phase => "phase",
            Kind::Set => "set",
            Kind::Configure => "configure",
            Kind::Limit => "limit",
            Kind::Optimize => "optimize",
            Kind::Reset => "reset",
            Kind::Add => "add",
            Kind::Constrain => "constrain",
            Kind::Connect => "connect",
            Kind::Observe => "observe",
            Kind::Lemma => "lemma",
            Kind::Disconnect => "disconnect",
            Kind::Assume => "assume",
            Kind::Solve => "solve",
            Kind::Simplify => "simplify",
            Kind::PropagateAssumptions => "propagate_assumptions",
            Kind::Implied => "implied",
            Kind::ResetAssumptions => "reset_assumptions",
            Kind::Lookahead => "lookahead",
            Kind::Cubing => "cubing",
            Kind::Propagate => "propagate",
            Kind::Val => "val",
            Kind::Flip => "flip",
            Kind::Flippable => "flippable",
            Kind::Fixed => "fixed",
            Kind::Failed => "failed",
            Kind::Conclude => "conclude",
            Kind::Freeze => "freeze",
            Kind::Melt => "melt",
            Kind::Frozen => "frozen",
            Kind::Dump => "dump",
            Kind::Stats => "stats",
            Kind::TraceProof => "trace_proof",
            Kind::FlushProofTrace => "flush_proof_trace",
            Kind::CloseProofTrace => "close_proof_trace",
        }
    }

    /// The 'copy' functions of the sub-classes (note that the C++ result
    /// argument is an 'int', and that 'FlippableCall::copy' produces a
    /// 'FlipCall').
    fn copy(&self) -> Call {
        let (arg, res, val) = (self.arg, self.res as i32, self.val);
        match self.kind {
            Kind::Init => Call::init(),
            Kind::Vars => Call::vars(),
            Kind::Active => Call::active(),
            Kind::Redundant => Call::redundant(),
            Kind::Irredundant => Call::irredundant(),
            Kind::Resize => Call::resize(arg),
            Kind::DeclareMoreVariables => Call::declare_more_variables(arg),
            Kind::DeclareOneMoreVariable => Call::declare_one_more_variable(),
            Kind::Phase => Call::phase(arg),
            Kind::Set => Call::set(self.name(), val),
            Kind::Configure => Call::configure(self.name()),
            Kind::Limit => Call::limit(self.name(), val),
            Kind::Optimize => Call::optimize(val),
            Kind::Reset => Call::reset(),
            Kind::Add => Call::add(arg),
            Kind::Constrain => Call::constrain(arg),
            Kind::Connect => Call::connect(),
            Kind::Observe => Call::observe(arg),
            Kind::Lemma => Call::lemma(arg),
            Kind::Disconnect => Call::disconnect(),
            Kind::Assume => Call::assume(arg),
            Kind::Solve => Call::solve(res),
            Kind::Simplify => Call::simplify(arg, res),
            Kind::PropagateAssumptions => Call::propagate_assumptions(arg),
            Kind::Implied => Call::implied(arg),
            Kind::ResetAssumptions => Call::reset_assumptions(arg),
            Kind::Lookahead => Call::lookahead(res),
            Kind::Cubing => Call::cubing(res),
            Kind::Propagate => Call::propagate(res),
            Kind::Val => Call::val(arg, res),
            Kind::Flip => Call::flip(arg, res),
            Kind::Flippable => Call::flip(arg, res),
            Kind::Fixed => Call::fixed(arg, res),
            Kind::Failed => Call::failed(arg, res),
            Kind::Conclude => Call::conclude(),
            Kind::Freeze => Call::freeze(arg),
            Kind::Melt => Call::melt(arg),
            Kind::Frozen => Call::frozen(arg, res),
            Kind::Dump => Call::dump(),
            Kind::Stats => Call::stats(),
            Kind::TraceProof => Call::trace_proof(&self.path),
            Kind::FlushProofTrace => Call::flush_proof_trace(),
            Kind::CloseProofTrace => Call::close_proof_trace(),
        }
    }
}

/*------------------------------------------------------------------------*/

static mut GENERATED: i64 = 0;
static mut EXECUTED: i64 = 0;
static mut FAILED: i64 = 0;
static mut OK: i64 = 0;

// SIGNAL (SIGINT) SIGNAL (SIGSEGV) SIGNAL (SIGABRT) SIGNAL (SIGTERM)
// SIGNAL (SIGBUS) SIGNAL (SIGUSR1) SIGNAL (SIGUSR2) SIGNAL (SIGTSTP)
const CHILD_SIGNALS: [libc::c_int; 8] = [
    libc::SIGINT,
    libc::SIGSEGV,
    libc::SIGABRT,
    libc::SIGTERM,
    libc::SIGBUS,
    libc::SIGUSR1,
    libc::SIGUSR2,
    libc::SIGTSTP,
];

static mut OLD_CHILD_HANDLERS: [libc::sighandler_t; 8] = [0; 8];

pub(crate) struct Trace {
    id: i64,
    seed: u64,

    solver: *mut Solver,
    calls: Vec<Call>,
    // map from mobical vars to solver vars (skipping extension variables)
    // the map is strictly increasing and gets updated whenever a call with an
    // argument gets executed.
    extendmap: ExtendMap,

    observed_vars: Vec<i32>,
    in_connection: bool,
}

struct Segment {
    lo: usize,
    hi: usize,
}

impl Segment {
    fn new(l: usize, h: usize) -> Segment {
        debug_assert!(0 < l);
        debug_assert!(l < h);
        Segment { lo: l, hi: h }
    }
}

type Segments = Vec<Segment>;

impl Drop for Trace {
    fn drop(&mut self) {
        self.clear();
    }
}

impl Trace {
    fn new(i: i64, s: u64) -> Trace {
        Trace {
            id: i,
            seed: s,
            solver: ptr::null_mut(),
            calls: Vec::new(),
            extendmap: ExtendMap::default(),
            observed_vars: Vec::new(),
            in_connection: false,
        }
    }

    fn clear(&mut self) {
        while let Some(c) = self.calls.pop() {
            drop(c);
        }
        if !self.solver.is_null() {
            // SAFETY: allocated with 'Box::into_raw' by 'InitCall'.
            drop(unsafe { Box::from_raw(self.solver) });
        }
        self.solver = ptr::null_mut();
    }

    fn push_back(&mut self, c: Call) {
        self.calls.push(c);
    }

    fn print(&self, o: &mut OStream) {
        for i in 0..self.calls.len() {
            o.d(i).c(' ');
            self.calls[i].print(o);
        }
    }

    fn execute(&mut self) {
        // SAFETY: plain static counter.
        unsafe { EXECUTED += 1 };
        let mut first = true;
        let extendmap: *mut ExtendMap = &mut self.extendmap;
        for i in 0..self.calls.len() {
            if Signal::interrupted() {
                break;
            }
            let type_ = self.calls[i].type_;

            // They are (ideally) are executed already
            if type_ == LEMMA {
                continue;
            }
            // if (c->type == Call::CONTINUE)
            //   continue;

            if type_ == SOLVE {
                // Look ahead and collect LemmaCalls to be executed
                // before solve is executed
                for j in i + 1..self.calls.len() {
                    if self.calls[j].type_ == LEMMA {
                        self.calls[j].execute(&mut self.solver, extendmap);
                    } else {
                        break;
                    }
                }
            }
            match m().shared() {
                Some(shared) if process_type(type_) => {
                    shared.solved += 1;
                    if first {
                        first = false;
                    } else {
                        shared.incremental += 1;
                    }
                    self.calls[i].execute(&mut self.solver, extendmap);
                    if self.calls[i].res == 10 {
                        shared.sat += 1;
                    }
                    if self.calls[i].res == 20 {
                        shared.unsat += 1;
                    }
                }
                _ => self.calls[i].execute(&mut self.solver, extendmap),
            }
        }
    }

    fn vars(&self) -> i32 {
        let mut res = 0;
        for c in &self.calls {
            let tmp = c.arg.wrapping_abs();
            if tmp > res {
                res = tmp;
            }
        }
        res
    }

    fn clauses(&self) -> i64 {
        let mut res = 0;
        for c in &self.calls {
            if c.type_ == ADD && c.arg == 0 {
                res += 1;
            }
        }
        res
    }

    fn literals(&self) -> i64 {
        let mut res = 0;
        for c in &self.calls {
            if c.type_ == ADD && c.arg != 0 {
                res += 1;
            }
        }
        res
    }

    fn phases(&self) -> i64 {
        let mut res = 0;
        let mut last = true;
        for c in &self.calls {
            if last
                && c.type_ != VAL
                && c.type_ != FLIP
                && c.type_ != FLIPPABLE
                && c.type_ != FAILED_
                && c.type_ != FROZEN
                && c.type_ != RESET
            {
                res += 1;
                last = false;
            }
            if process_type(c.type_) {
                last = true;
            }
        }
        res
    }

    fn size(&self) -> usize {
        self.calls.len()
    }

    fn notify(&self, ch: i8) {
        Mobical::notify(self, ch)
    }

    fn progress(&self) {
        Mobical::progress(self)
    }

    /*--------------------------------------------------------------------*/

    fn first_option(&self) -> usize {
        let mut res = 0;
        while res < self.size() {
            if self.calls[res].type_ == SET {
                return res;
            }
            res += 1;
        }
        res
    }

    fn last_option(&self) -> usize {
        let mut res = 0;
        while res < self.size() {
            let c = &self.calls[res];
            if c.type_ == INIT {
                res += 1;
                continue;
            }
            if c.type_ == SET {
                res += 1;
                continue;
            }
            break;
        }
        res
    }

    fn find_option_by_prefix(&self, name: &str) -> Option<usize> {
        let last = self.last_option();
        let mut res: Option<usize> = None;
        let mut i = self.first_option();
        while i < last {
            let c = &self.calls[i];
            if let Some(r) = res {
                if self.calls[r].name().len() < c.name().len() {
                    i += 1;
                    continue;
                }
            }
            if has_prefix(name, c.name()) {
                res = Some(i);
            }
            i += 1;
        }
        res
    }

    fn find_option_by_name(&self, name: &str) -> Option<usize> {
        let last = self.last_option();
        let mut res: Option<usize> = None;
        let mut i = self.first_option();
        while i < last {
            let c = &self.calls[i];
            if c.name() == name {
                res = Some(i);
            }
            i += 1;
        }
        res
    }

    // Some options are never part of generated traces.
    //
    fn ignored_option(name: &str) -> bool {
        if name == "checkfrozen" {
            return true;
        }
        if name == "terminateint" {
            return true;
        }
        if name == "factorcheck" {
            return true;
        }
        false
    }

    // Check whether the trace already contains an option which disables the
    // option 'name'.  Here we assume that an option disables another one if the
    // disabling one has as name proper prefix of the disabled one and the value
    // of the former is set to zero in the trace.
    //
    fn ignore_option(&self, name: &str, max_var: i32) -> bool {
        if Trace::ignored_option(name) {
            return true;
        }

        // There are options which should be kept at their default value unless
        // the formula is really small.  Otherwise the solver might run 'forever'.
        //
        if max_var > SMALL && name == "reduce" {
            return true;
        }

        if let Some(ci) = self.find_option_by_prefix(name) {
            let c = &self.calls[ci];
            debug_assert!(has_prefix(name, c.name()));
            if c.name().len() < name.len() && c.val == 0 {
                return true;
            }
        }

        false
    }

    // For incomplete solving phases such as 'walk' we do not want to increase
    // the option value above the default and similarly for elimination bounds.
    //
    fn option_high_value(name: &str, def: i64, lo: i64, hi: i64) -> i64 {
        debug_assert!(lo <= def);
        debug_assert!(def <= hi);
        if name == "walkmaxeff" {
            return def;
        }
        if name == "walkmineff" {
            return def;
        }
        if name == "elimboundmax" {
            return 256;
        }
        if name == "elimboundmin" {
            return 256;
        }
        let _ = lo;
        hi
    }

    /*--------------------------------------------------------------------*/

    fn generate_options(&mut self, random: &mut Random, size: Size) {
        #[cfg(feature = "logging")]
        if m().add_set_log_to_true {
            self.push_back(Call::set("log", 1));
        }
        #[cfg(not(feature = "logging"))]
        if m().add_set_log_to_true {
            Mobical::warning("ignoring log option");
        }
        // In 10% of the cases do not change any options.
        //
        if random.generate_double() < 0.1 {
            return;
        }

        // In order to increase throughput we enable 'walk' in 5% tests, which
        // means disabling it in 95% of the tests.
        //
        if random.generate_double() < 0.95 {
            self.push_back(Call::set("walk", 0));
        }

        // Also for checking models and assumptions, but with 80% probability.
        //
        if random.generate_double() < 0.8 {
            self.push_back(Call::set("check", 1));
        }

        // In 10% of the remaining cases we use a configuration.
        //
        if random.generate_double() < 0.1 {
            let configs = Config::names();
            let size = configs.len() as i32;
            let pos = random.pick_int(0, size - 1);
            let config = configs[pos as usize];
            debug_assert!(Config::has(config));
            self.push_back(Call::configure(config));
        }

        // This is the fraction of options changed.
        //
        let fraction = random.generate_double();

        // Generate a list of options, different from default values.
        //
        for o in Options::iter() {
            // This should not be reachable unless the low and high value of an
            // option in 'options.hpp' are the same.
            //
            if o.lo == o.hi {
                continue;
            }

            // We ignore logging here and set it below to make mobical deterministic
            if o.name == "log" {
                continue;
            }
            if o.name == "logsort" {
                continue;
            }
            // We keep choosing the value for 'simplify' and 'walk' out of the loop
            // (see the arguments described above).
            //
            if o.name == "simplify" {
                continue;
            }
            if o.name == "walk" {
                continue;
            }

            // Probability to change an option is 'fraction'.
            //
            if random.generate_double() < fraction {
                continue;
            }

            // Unless we have to ignore it.
            //
            if self.ignore_option(o.name, size) {
                continue;
            }

            let mut val: i32;
            let hi = Trace::option_high_value(o.name, o.def as i64, o.lo as i64, o.hi as i64);
            if (o.lo as i64) < hi {
                let uniform = random.generate_double() < 0.05;
                if uniform {
                    loop {
                        val = random.pick_int(o.lo, hi as i32);
                        if val != o.def {
                            break;
                        }
                    }
                } else {
                    // log uniform
                    let mut range: i64 = hi - o.lo as i64;
                    let mut log: i32 = 0;
                    debug_assert!(range <= i32::MAX as i64);
                    while log < 30 && ((1i32 << log) as i64) < range {
                        if random.generate_bool() {
                            break;
                        }
                        log += 1;
                    }
                    if ((1i32 << log) as i64) < range {
                        range = 1i64 << log;
                    }
                    val = o.lo.wrapping_add(random.pick_int(0, range as i32));
                }
            } else {
                val = o.lo;
            }
            self.push_back(Call::set(o.name, val));
        }

        // Now setting the option for logging. Even if we do not generate the log
        // call, we need the side effect of generate_bool ()
        //
        // (The C++ 'find_if' predicates are 'strcmp (o.name, "log")' which
        // finds the first option *not* named 'log' resp. 'logsort'.)
        let log_option = Options::iter().find(|o| o.name != "log");
        let should_log = random.generate_bool();
        let logsort_option = Options::iter().find(|o| o.name != "logsort");
        let should_logsort = random.generate_bool();

        #[cfg(feature = "logging")]
        {
            // sanity check
            debug_assert!(log_option.is_some());
            debug_assert!(logsort_option.is_some());
        }
        if let Some(_o) = log_option {
            if should_log {
                // only if the option was found
                #[cfg(feature = "logging")]
                self.push_back(Call::set(_o.name, should_log as i32));
            }
        }
        if let Some(_o) = logsort_option {
            if should_logsort {
                #[cfg(feature = "logging")]
                self.push_back(Call::set(_o.name, should_logsort as i32));
            }
        }
    }

    /*--------------------------------------------------------------------*/

    fn generate_queries(&mut self, random: &mut Random) {
        if random.generate_double() < 0.02 {
            self.push_back(Call::vars());
        }
        if random.generate_double() < 0.02 {
            self.push_back(Call::active());
        }
        if random.generate_double() < 0.02 {
            self.push_back(Call::redundant());
        }
        if random.generate_double() < 0.02 {
            self.push_back(Call::irredundant());
        }
    }

    /*--------------------------------------------------------------------*/

    fn generate_resize(&mut self, random: &mut Random, max_var: i32) {
        if random.generate_double() > 0.01 {
            return;
        }
        let new_max_var = random.pick_int(0, (1.1 * max_var as f64) as i32);
        self.push_back(Call::resize(new_max_var));
    }

    /*--------------------------------------------------------------------*/

    fn generate_declare_more_variables(&mut self, random: &mut Random) {
        if random.generate_double() > 0.01 {
            return;
        }
        let new_max_var = random.pick_int(0, 100);
        self.push_back(Call::declare_more_variables(new_max_var));
    }

    fn generate_declare_one_more_variable(&mut self, random: &mut Random) {
        if random.generate_double() > 0.01 {
            return;
        }
        self.push_back(Call::declare_one_more_variable());
    }

    /*--------------------------------------------------------------------*/

    fn generate_implied(&mut self, random: &mut Random) {
        if random.generate_double() > 0.01 {
            return;
        }
        self.push_back(Call::implied(0));
    }

    /*--------------------------------------------------------------------*/

    fn generate_propagate(&mut self, random: &mut Random) {
        if random.generate_double() > 0.01 {
            return;
        }
        self.push_back(Call::propagate(0));
    }

    /*--------------------------------------------------------------------*/

    fn generate_limits(&mut self, random: &mut Random) {
        if random.generate_double() < 0.05 {
            let v = random.pick_log(0, 1e5 as i32);
            self.push_back(Call::limit("terminate", v));
        }
        if random.generate_double() < 0.05 {
            let v = random.pick_log(0, 1e4 as i32);
            self.push_back(Call::limit("conflicts", v));
        }
        if random.generate_double() < 0.05 {
            let v = random.pick_log(0, 1e4 as i32);
            self.push_back(Call::limit("decisions", v));
        }
        if random.generate_double() < 0.05 {
            let v = random.pick_log(0, 1e9 as i32);
            self.push_back(Call::limit("ticks", v));
        }
        if random.generate_double() < 0.1 {
            let v = random.pick_int(0, 10);
            self.push_back(Call::limit("preprocessing", v));
        }
        if random.generate_double() < 0.05 {
            let v = random.pick_int(0, 1);
            self.push_back(Call::limit("localsearch", v));
        }
        if random.generate_double() < 0.02 {
            let v = random.pick_int(0, 31);
            self.push_back(Call::optimize(v));
        }
    }

    /*--------------------------------------------------------------------*/

    fn generate_clause(&mut self, random: &mut Random, minvars: i32, maxvars: i32, uniform: i32) {
        debug_assert!(minvars <= maxvars);
        let maxsize = maxvars - minvars + 1;
        let size = if uniform != 0 { uniform } else { pick_size(random, maxsize) };
        let mut clause: Vec<i32> = Vec::new();
        for _ in 0..size {
            let lit = pick_literal(random, minvars, maxvars, &clause);
            self.push_back(Call::add(lit));
            clause.push(lit);
        }
        self.push_back(Call::add(0));
    }

    fn generate_constraint(&mut self, random: &mut Random, minvars: i32, maxvars: i32, uniform: i32) {
        if random.generate_double() < 0.95 {
            return;
        }
        debug_assert!(minvars <= maxvars);
        let maxsize = maxvars - minvars + 1;
        let size = if uniform != 0 { uniform } else { pick_size(random, maxsize) };
        let mut clause: Vec<i32> = Vec::new();
        for _ in 0..size {
            let lit = pick_literal(random, minvars, maxvars, &clause);
            self.push_back(Call::constrain(lit));
            clause.push(lit);
        }
        self.push_back(Call::constrain(0));
    }

    /*--------------------------------------------------------------------*/

    fn generate_propagator(&mut self, random: &mut Random, minvars: i32, maxvars: i32) {
        if random.generate_double() < 0.9 {
            return;
        }

        debug_assert!(minvars <= maxvars);
        if self.in_connection {
            self.push_back(Call::disconnect());
        }
        self.push_back(Call::connect());

        self.in_connection = true;

        self.observed_vars.clear();

        // Give a chance to add no observed variables at all
        if random.generate_double() < 0.05 {
            return;
        }

        for idx in minvars..=maxvars {
            if random.generate_double() < 0.6 {
                continue;
            }
            let lit = if random.generate_bool() { -idx } else { idx };
            self.push_back(Call::observe(lit));
            self.observed_vars.push(lit.abs());
        }
        self.push_back(Call::observe(0));
        let mut idx = maxvars + 1;
        while idx as f64 <= maxvars as f64 * 1.5 {
            if random.generate_double() < 0.75 {
                idx += 1;
                continue;
            }
            let lit = if random.generate_bool() { -idx } else { idx };
            self.push_back(Call::observe(lit));
            self.observed_vars.push(lit.abs());
            idx += 1;
        }
    }

    fn generate_lemmas(&mut self, random: &mut Random) {
        if self.observed_vars.is_empty() {
            return;
        }
        let nof_user_propagation_phases = random.pick_int(4, 7);

        for _p in 0..nof_user_propagation_phases {
            if random.generate_double() < 0.05 {
                // push_back (new ContinueCall ());
            } else {
                let nof_lemmas = random.pick_int(5, 11);
                let ovars = self.observed_vars.len() as i32;
                for _i in 0..nof_lemmas {
                    // Tiny tiny chance to generate an empty lemma
                    if random.generate_double() < 0.005 {
                        self.push_back(Call::lemma(0));
                    } else {
                        let mut count = pick_size(random, 4);
                        if count > ovars {
                            count = ovars;
                        }
                        let max_idx = ovars - 1;
                        let mut picked = vec![false; (max_idx + 1) as usize];
                        for _ in 0..count {
                            let mut idx;
                            loop {
                                idx = random.pick_int(0, max_idx);
                                if !picked[idx as usize] {
                                    break;
                                }
                            }
                            picked[idx as usize] = true;
                            let ov = self.observed_vars[idx as usize];
                            let lit = if random.generate_bool() { -ov } else { ov };
                            self.push_back(Call::lemma(lit));
                        }

                        drop(picked);
                        if random.generate_double() < 0.1 {
                            let idx = random.pick_int(0, max_idx);
                            let ov = self.observed_vars[idx as usize];
                            let lit = if random.generate_bool() { -ov } else { ov };
                            self.push_back(Call::lemma(lit));
                        }
                        self.push_back(Call::lemma(0));
                    }
                }
                // push_back (new ContinueCall ());
            }
        }
    }

    /*--------------------------------------------------------------------*/

    fn generate_assume(&mut self, random: &mut Random, vars: i32) {
        if random.generate_double() < 0.15 {
            return;
        }
        let count = if random.generate_bool() { 1 } else { random.pick_int(1, vars + 1) };
        let max_vars = vars + 2;
        let mut picked = vec![false; (max_vars + 1) as usize];
        for _ in 0..count {
            let mut idx;
            loop {
                idx = random.pick_int(1, max_vars);
                if !picked[idx as usize] {
                    break;
                }
            }
            picked[idx as usize] = true;
            let lit = if random.generate_bool() { -idx } else { idx };
            self.push_back(Call::assume(lit));
        }
        drop(picked);
        if random.generate_double() < 0.1 {
            let idx = random.pick_int(1, max_vars);
            let lit = if random.generate_bool() { -idx } else { idx };
            self.push_back(Call::assume(lit));
        }
    }

    fn generate_values(&mut self, random: &mut Random, vars: i32) {
        if random.generate_double() < 0.1 {
            return;
        }
        let fraction = random.generate_double();
        for idx in 1..=vars {
            if fraction < random.generate_double() {
                continue;
            }
            let lit = if random.generate_bool() { -idx } else { idx };
            let strict = random.generate_bool();
            self.push_back(Call::val(lit, strict as i32));
        }
        if random.generate_double() < 0.1 {
            let idx = random.pick_int(vars + 1, (vars as f64 * 1.5 + 1.0) as i32);
            let lit = if random.generate_bool() { -idx } else { idx };
            self.push_back(Call::val(lit, 1));
        }
    }

    fn generate_flipped(&mut self, random: &mut Random, vars: i32) {
        if random.generate_double() < 0.5 {
            return;
        }
        let fraction = random.generate_double();
        for idx in 1..=vars {
            if fraction < random.generate_double() {
                continue;
            }
            let lit = if random.generate_bool() { -idx } else { idx };
            if random.generate_double() < 0.5 {
                self.push_back(Call::flippable(lit, 0));
            } else {
                self.push_back(Call::flip(lit, 0));
            }
        }
        if random.generate_double() < 0.1 {
            let idx = random.pick_int(vars + 1, (vars as f64 * 1.5 + 1.0) as i32);
            let lit = if random.generate_bool() { -idx } else { idx };
            if random.generate_double() < 0.5 {
                self.push_back(Call::flippable(lit, 0));
            } else {
                self.push_back(Call::flip(lit, 0));
            }
        }
    }

    fn generate_failed(&mut self, random: &mut Random, vars: i32) {
        if random.generate_double() < 0.05 {
            return;
        }
        let fraction = random.generate_double();
        for idx in 1..=vars {
            if fraction < random.generate_double() {
                continue;
            }
            let lit = if random.generate_bool() { -idx } else { idx };
            self.push_back(Call::failed(lit, 0));
        }
        if random.generate_double() < 0.05 {
            let idx = random.pick_int(vars + 1, (vars as f64 * 1.5 + 1.0) as i32);
            let lit = if random.generate_bool() { -idx } else { idx };
            self.push_back(Call::failed(lit, 0));
        }
    }

    fn generate_conclude(&mut self, random: &mut Random) {
        if random.generate_double() < 0.05 {
            return;
        }
        if random.generate_double() < 0.05 {
            self.push_back(Call::conclude());
        }
    }

    fn generate_frozen(&mut self, random: &mut Random, vars: i32) {
        if random.generate_double() < 0.05 {
            return;
        }
        let fraction = random.generate_double();
        for idx in 1..=vars {
            if fraction < random.generate_double() {
                continue;
            }
            let lit = if random.generate_bool() { -idx } else { idx };
            self.push_back(Call::frozen(lit, 0));
        }
        if random.generate_double() < 0.05 {
            let idx = random.pick_int(vars + 1, (vars as f64 * 1.5 + 1.0) as i32);
            let lit = if random.generate_bool() { -idx } else { idx };
            self.push_back(Call::frozen(lit, 0));
        }
    }

    fn generate_melt(&mut self, random: &mut Random) {
        if random.generate_bool() {
            return;
        }
        let mm = self.vars();
        let mut frozen: Vec<i64> = vec![0; (mm + 1) as usize];
        for i in 1..=mm {
            frozen[i as usize] = 0;
        }
        for c in &self.calls {
            if c.type_ == MELT {
                let idx = c.arg.wrapping_abs();
                debug_assert!(idx != 0);
                debug_assert!(idx <= mm);
                debug_assert!(frozen[idx as usize] > 0);
                frozen[idx as usize] -= 1;
            } else if c.type_ == FREEZE {
                let idx = c.arg.wrapping_abs();
                debug_assert!(idx != 0);
                debug_assert!(idx <= mm);
                frozen[idx as usize] += 1;
            }
        }
        let mut candidates: Vec<i32> = Vec::new();
        for i in 1..=mm {
            if frozen[i as usize] != 0 {
                candidates.push(i);
            }
        }
        drop(frozen);
        let fraction = random.generate_double() * 0.4;
        for idx in candidates {
            if random.generate_double() <= fraction {
                continue;
            }
            let lit = if random.generate_bool() { -idx } else { idx };
            self.push_back(Call::melt(lit));
        }
    }

    fn generate_freeze(&mut self, random: &mut Random, vars: i32) {
        if random.generate_bool() {
            return;
        }
        let fraction = random.generate_double() * 0.5;
        for idx in 1..=vars {
            if random.generate_double() <= fraction {
                continue;
            }
            let lit = if random.generate_bool() { -idx } else { idx };
            self.push_back(Call::freeze(lit));
        }
    }

    fn generate_process(&mut self, random: &mut Random) {
        if m().add_dump_before_solve {
            self.push_back(Call::dump());
        }

        let fraction = random.generate_double();

        if fraction < 0.6 {
            self.push_back(Call::solve(0));
            if self.in_connection && !self.observed_vars.is_empty() {
                self.generate_lemmas(random);
            }
        } else if fraction > 0.99 {
            let depth = random.pick_int(0, 10);
            self.push_back(Call::cubing(depth));
        } else if fraction > 0.9 {
            self.push_back(Call::lookahead(0));
        } else if fraction > 0.85 {
            self.push_back(Call::propagate(0));
        } else {
            let rounds = random.pick_int(0, 10);
            self.push_back(Call::simplify(rounds, 0));
        }

        if m().add_stats_after_solve {
            self.push_back(Call::stats());
        }
    }

    fn generate(&mut self, i: u64, s: u64) {
        self.id = i as i64;
        self.seed = s;
        let mut random = Random::new(self.seed);

        self.push_back(Call::init());

        let size: Size = if m().force.size != NOSIZE {
            m().force.size
        } else {
            match random.pick_int(1, 3) {
                1 => SMALL,
                2 => MEDIUM,
                _ => BIG,
            }
        };

        self.generate_options(&mut random, size);

        if m().add_plain_after_options {
            self.push_back(Call::configure("plain"));
        }

        let calls = if m().force.phases < 0 { random.pick_int(1, 4) } else { m().force.phases };

        let mut minvars: i32;
        let mut maxvars: i32 = 0;

        for _call in 0..calls {
            let range: i32 = if size == TINY {
                random.pick_int(1, TINY)
            } else if size == SMALL {
                random.pick_int(1, SMALL)
            } else if size == MEDIUM {
                random.pick_int(SMALL + 1, MEDIUM)
            } else {
                random.pick_int(MEDIUM + 1, BIG)
            };

            let uniform: i32 = if random.generate_bool() {
                0
            } else if size == TINY {
                0
            } else if size == SMALL {
                random.pick_int(3, 7)
            } else if size == MEDIUM {
                random.pick_int(3, 4)
            } else {
                random.pick_int(3, 3)
            };

            let ratio: f64 = match uniform {
                4 => 9.931,
                5 => 21.117,
                6 => 43.37,
                7 => 87.79,
                _ => 4.267,
            };

            let clauses = (range as f64 * ratio) as i32;

            // TODO: Test empty clause database by uncommenting here
            // Note that it can lead to unvalid mobical states in the reduced
            // trace, so always check the original bug-trace too.
            // if (random.generate_double () < 0.01) clauses = 0;

            minvars = random.pick_int(1, maxvars + 1);
            maxvars = minvars + range;

            for _j in 0..clauses {
                self.generate_queries(&mut random);
                self.generate_resize(&mut random, maxvars);
                self.generate_declare_more_variables(&mut random);
                self.generate_declare_one_more_variable(&mut random);
                self.generate_implied(&mut random);
                self.generate_propagate(&mut random);
                self.generate_clause(&mut random, minvars, maxvars, uniform);
            }

            if self.in_connection && random.generate_bool() {
                self.observed_vars.clear();
                self.push_back(Call::disconnect());
                self.in_connection = false;
            } else {
                self.generate_propagator(&mut random, minvars, maxvars);
            }

            self.generate_constraint(&mut random, minvars, maxvars, uniform);
            self.generate_assume(&mut random, maxvars);
            self.generate_melt(&mut random);
            self.generate_freeze(&mut random, maxvars);
            self.generate_limits(&mut random);

            self.generate_process(&mut random);

            self.generate_values(&mut random, maxvars);
            if !self.in_connection {
                self.generate_flipped(&mut random, maxvars);
            }
            self.generate_failed(&mut random, maxvars);
            self.generate_conclude(&mut random);
            self.generate_frozen(&mut random, maxvars);
        }

        self.push_back(Call::reset());
    }

    /*--------------------------------------------------------------------*/

    fn reset_child_signal_handlers() {
        for (i, &sig) in CHILD_SIGNALS.iter().enumerate() {
            // SAFETY: restoring the saved handlers.
            unsafe {
                libc::signal(sig, OLD_CHILD_HANDLERS[i]);
            }
        }
    }

    extern "C" fn child_signal_handler(sig: libc::c_int) {
        let mut sig = sig;
        // SAFETY: 'getrusage' into a zeroed struct.
        let mut u: libc::rusage = unsafe { std::mem::zeroed() };
        if unsafe { libc::getrusage(libc::RUSAGE_SELF, &mut u) } == 0 {
            #[cfg(not(target_os = "macos"))]
            let maxrss_mb = (u.ru_maxrss as i64) >> 10;
            #[cfg(target_os = "macos")]
            let maxrss_mb = (u.ru_maxrss as i64) >> 20;
            if maxrss_mb >= m().space_limit {
                if let Some(shared) = m().shared() {
                    shared.memout += 1;
                }
                // Since there is no memout signal we just misuse SIXCPU to notify the
                // calling process that this is a out-of-resource situation.
                sig = libc::SIGXCPU;
            } else {
                let t = u.ru_utime.tv_sec as f64
                    + 1e-6 * u.ru_utime.tv_usec as f64
                    + u.ru_stime.tv_sec as f64
                    + 1e-6 * u.ru_stime.tv_usec as f64;
                if t >= m().time_limit as f64 {
                    if let Some(shared) = m().shared() {
                        shared.timeout += 1;
                    }
                    sig = libc::SIGXCPU;
                }
            }
        }
        Trace::reset_child_signal_handlers();
        Signal::reset();
        // SAFETY: 'raise'.
        unsafe {
            libc::raise(sig);
        }
    }

    fn init_child_signal_handlers() {
        let handler = Trace::child_signal_handler as extern "C" fn(libc::c_int);
        for (i, &sig) in CHILD_SIGNALS.iter().enumerate() {
            // SAFETY: installing a signal handler.
            unsafe {
                OLD_CHILD_HANDLERS[i] = libc::signal(sig, handler as libc::sighandler_t);
            }
        }
    }

    fn fork_and_execute(&mut self) -> i32 {
        cerr().flush();
        let child: libc::pid_t = if m().donot.fork {
            0
        } else {
            // SAFETY: 'fork' (single threaded).
            unsafe { libc::fork() }
        };
        let mut res = 0;

        if child != 0 {
            // SAFETY: plain static counter.
            unsafe { EXECUTED += 1 };

            // If SIGTSTP is used in the future rather use waitpid & WUNTRACED
            // int status;
            // pid_t other = waitpid (child, &status, WUNTRACED);

            let mut status: libc::c_int = 0;
            // SAFETY: 'wait' for the child.
            let other = unsafe { libc::wait(&mut status) };
            if other != child {
                res = 0;
            } else if libc::WIFEXITED(status) {
                res = libc::WEXITSTATUS(status);
            } else if !libc::WIFSIGNALED(status) {
                res = 0;
            } else if m().donot.ignore_resource_limits {
                res = 1;
            } else if libc::WTERMSIG(status) == libc::SIGUSR1 {
                res = 2; // Bad allocation caused signal.
            } else if libc::WTERMSIG(status) == libc::SIGUSR2 {
                res = 3; // Leaked allocation caused signal.
            } else {
                res = (libc::WTERMSIG(status) != libc::SIGXCPU) as i32;
            }
        } else {
            if !m().donot.fork && m().time_limit != 0 {
                // SAFETY: resource limits of this (child) process.
                unsafe {
                    let mut rlim: libc::rlimit = std::mem::zeroed();
                    if libc::getrlimit(libc::RLIMIT_CPU, &mut rlim) == 0 {
                        rlim.rlim_cur = m().time_limit as libc::rlim_t;
                        libc::setrlimit(libc::RLIMIT_CPU, &rlim);
                    }
                }
            }

            if !m().donot.fork && m().space_limit != 0 {
                // SAFETY: resource limits of this (child) process.
                unsafe {
                    let mut rlim: libc::rlimit = std::mem::zeroed();
                    if libc::getrlimit(libc::RLIMIT_AS, &mut rlim) == 0 {
                        rlim.rlim_cur = (m().space_limit * (1i64 << 20)) as libc::rlim_t;
                        libc::setrlimit(libc::RLIMIT_AS, &rlim);
                    }
                }
            }

            Trace::init_child_signal_handlers();
            // SAFETY: file descriptor juggling as in C++.
            let null = unsafe {
                libc::dup2(1, 3);
                libc::dup2(2, 4);
                let null = libc::open(b"/dev/null\0".as_ptr() as *const libc::c_char, libc::O_WRONLY);
                debug_assert!(null != 0);
                libc::dup2(null, 1);
                libc::dup2(null, 2);
                null
            };
            self.execute();
            // SAFETY: file descriptor juggling as in C++.
            unsafe {
                libc::close(1);
                libc::close(2);
                libc::close(null);
                libc::dup2(3, 1);
                libc::dup2(4, 2);
                libc::close(3);
                libc::close(4);
            }
            if m().donot.fork {
                m().mock_pointer = ptr::null_mut();
            }
            Trace::reset_child_signal_handlers();

            if !m().donot.fork {
                // SAFETY: 'exit' of the child process.
                unsafe { libc::exit(0) };
            }
        }

        res
    }

    /*--------------------------------------------------------------------*/

    // Delta-debugging algorithm on segments.

    fn shrink_segments(&mut self, segments: &mut Segments, expected: i32) -> bool {
        let n = segments.len();
        if n == 0 {
            return false;
        }
        let mut granularity = n;
        let mut removed = vec![false; n];
        let mut saved = vec![false; n];
        let mut ignore = vec![false; self.size()];
        for i in 0..n {
            removed[i] = false;
        }
        let mut res = false;
        loop {
            let mut l = 0;
            while l < n {
                let mut r = l + granularity;
                if r > n {
                    r = n;
                }
                let mut flipped: usize = 0;
                for i in 0..n {
                    saved[i] = false;
                }
                for i in l..r {
                    saved[i] = removed[i];
                    if !saved[i] {
                        removed[i] = true;
                        flipped += 1;
                    }
                }
                if flipped == 0 {
                    l = r;
                    continue;
                }
                for i in 0..self.size() {
                    ignore[i] = false;
                }
                for i in 0..n {
                    if !removed[i] {
                        continue;
                    }
                    let s = &segments[i];
                    for j in s.lo..s.hi {
                        ignore[j] = true;
                    }
                }
                let mut tmp = Trace::new(0, 0);
                tmp.clear();
                for i in 0..self.size() {
                    if !ignore[i] {
                        tmp.push_back(self.calls[i].copy());
                    }
                }
                self.progress();
                if tmp.fork_and_execute() != expected || Signal::received() != 0 {
                    // failed
                    for i in l..r {
                        removed[i] = saved[i];
                    }
                } else {
                    res = true; // succeeded to shrink
                }
                drop(tmp);
                if Signal::interrupted() {
                    break;
                }
                l = r;
            }
            if Signal::interrupted() {
                break;
            }
            if granularity == 1 {
                break;
            }
            granularity = (granularity + 1) / 2;
        }
        if res {
            for i in 0..self.size() {
                ignore[i] = false;
            }
            for i in 0..n {
                if !removed[i] {
                    continue;
                }
                let s = &segments[i];
                for j in s.lo..s.hi {
                    ignore[j] = true;
                }
            }
            let old = std::mem::take(&mut self.calls);
            for (i, c) in old.into_iter().enumerate() {
                if ignore[i] {
                    drop(c);
                } else {
                    self.calls.push(c);
                }
            }
            self.notify(0);
        }
        res
    }

    // Explicit grammar aware three-level hierarchical delta-debugging.
    // First level is in term of incremental solving phases where one phase
    // consists of maximal prefixes of intervals of calls of type
    // '(BEFORE*| PROCESS | DURING* | AFTER*)' or single non-configuration
    // calls.
    //
    fn shrink_phases(&mut self, expected: i32) -> bool {
        if m().donot.shrink.phases {
            return false;
        }
        if Signal::interrupted() {
            return false;
        }
        self.notify(b'p' as i8);
        let mut l: usize = 1;
        while l < self.size() && config_type(self.calls[l].type_) {
            l += 1;
        }
        let mut segments: Segments = Vec::new();
        let mut r: usize;
        while l < self.size() {
            r = l;
            while r < self.size() && before_type(self.calls[r].type_) {
                r += 1;
            }
            if r < self.size() && process_type(self.calls[r].type_) {
                r += 1;
            }
            while r < self.size() && self.calls[r].type_ == LEMMA {
                r += 1;
            }
            while r < self.size() && after_type(self.calls[r].type_) {
                r += 1;
            }
            if l < r {
                segments.push(Segment::new(l, r));
            } else {
                debug_assert!(l == r);
                if !config_type(self.calls[r].type_) {
                    debug_assert!(self.calls[r].type_ != LEMMA);
                    segments.push(Segment::new(r, r + 1));
                }
                r += 1;
            }
            l = r;
        }
        self.shrink_segments(&mut segments, expected)
    }

    // The second level tries to remove clauses.
    //
    fn shrink_clauses(&mut self, expected: i32) -> bool {
        if m().donot.shrink.clauses {
            return false;
        }
        if Signal::interrupted() {
            return false;
        }
        self.notify(b'c' as i8);
        let mut segments: Segments = Vec::new();
        let mut r = self.size();
        while r > 1 {
            let mut l = r - 1;
            let mut c = &self.calls[l];
            while l > 0 && (c.type_ != ADD || c.arg != 0) {
                l -= 1;
                c = &self.calls[l];
            }
            if l == 0 {
                break;
            }
            r = l + 1;
            loop {
                l -= 1;
                let c = &self.calls[l];
                if !(c.type_ == ADD && c.arg != 0) {
                    break;
                }
            }
            l += 1;
            segments.push(Segment::new(l, r));
            r = l;
        }
        self.shrink_segments(&mut segments, expected)
    }

    fn shrink_lemmas(&mut self, expected: i32) -> bool {
        if m().donot.shrink.lemmas {
            return false;
        }
        if Signal::interrupted() {
            return false;
        }
        self.notify(b'u' as i8);
        let mut segments: Segments = Vec::new();
        let mut r = self.size();
        while r > 1 {
            let mut l = r - 1;
            let mut c = &self.calls[l];
            while l > 0 && (c.type_ != LEMMA || c.arg != 0) {
                l -= 1;
                c = &self.calls[l];
            }
            if l == 0 {
                break;
            }
            r = l + 1;
            loop {
                l -= 1;
                let c = &self.calls[l];
                if !(c.type_ == LEMMA && c.arg != 0) {
                    break;
                }
            }
            l += 1;
            segments.push(Segment::new(l, r));
            r = l;
        }
        self.shrink_segments(&mut segments, expected)
    }

    // The third level tries to remove individual literals.
    //
    fn shrink_literals(&mut self, expected: i32) -> bool {
        if m().donot.shrink.literals {
            return false;
        }
        if Signal::interrupted() {
            return false;
        }
        self.notify(b'l' as i8);
        let mut segments: Segments = Vec::new();
        let mut l = self.size().wrapping_sub(1);
        while l > 0 && l != usize::MAX {
            let c = &self.calls[l];
            if c.type_ == ADD && c.arg != 0 {
                segments.push(Segment::new(l, l + 1));
            }
            if c.type_ == LEMMA && c.arg != 0 {
                segments.push(Segment::new(l, l + 1));
            }
            l -= 1;
        }
        self.shrink_segments(&mut segments, expected)
    }

    fn shrink_basic(&mut self, expected: i32) -> bool {
        if m().donot.shrink.basic {
            return false;
        }
        if Signal::interrupted() {
            return false;
        }
        self.notify(b'b' as i8);
        let mut segments: Segments = Vec::new();
        let mut l = self.size().wrapping_sub(1);
        while l > 0 && l != usize::MAX {
            let c = &self.calls[l];
            if is_basic(c) {
                segments.push(Segment::new(l, l + 1));
            }
            l -= 1;
        }
        self.shrink_segments(&mut segments, expected)
    }

    // We first add all non present possible options with their default value.

    fn add_options(&mut self, expected: i32) {
        if m().donot.add {
            return;
        }
        let max_var = self.vars();
        self.notify(b'a' as i8);
        debug_assert!(self.size() != 0);
        let mut extended = Trace::new(0, 0);
        let mut i: usize = 0;
        while i < self.size() {
            let c = &self.calls[i];
            if c.type_ != INIT {
                i += 1;
                continue;
            }
            extended.push_back(c.copy());
            i += 1;
        }
        while i < self.size() && self.calls[i].type_ == SET {
            extended.push_back(self.calls[i].copy());
            i += 1;
        }
        for o in Options::iter() {
            if self.find_option_by_name(o.name).is_some() {
                continue;
            }
            if self.ignore_option(o.name, max_var) {
                continue;
            }
            if extended.ignore_option(o.name, max_var) {
                continue;
            }
            extended.push_back(Call::set(o.name, o.def));
        }
        while i < self.size() {
            extended.push_back(self.calls[i].copy());
            i += 1;
        }
        self.progress();
        if extended.fork_and_execute() != expected {
            return;
        }
        self.clear();
        for i in 0..extended.size() {
            self.push_back(extended.calls[i].copy());
        }
        self.notify(0);
    }

    // Try to set as many options to their lower limit, which also tries to
    // disable as many boolean options.

    fn shrink_disable(&mut self, expected: i32) -> bool {
        if m().donot.disable {
            return false;
        }
        if Signal::interrupted() {
            return false;
        }
        let max_var = self.vars();

        self.notify(b'd' as i8);
        let last = self.last_option();
        let mut candidates: Vec<usize> = Vec::new();
        let mut lower: Vec<i32> = Vec::new();
        let mut saved: Vec<i32> = Vec::new();
        let mut i = self.first_option();
        while i < last {
            let c = &self.calls[i];
            if c.type_ != SET {
                i += 1;
                continue;
            }
            if self.ignore_option(c.name(), max_var) {
                i += 1;
                continue;
            }
            let o = match Options::has(c.name()) {
                Some(o) => o,
                None => {
                    i += 1;
                    continue;
                }
            };
            if c.val == o.lo {
                i += 1;
                continue;
            }
            candidates.push(i);
            lower.push(o.lo);
            saved.push(c.val);
            i += 1;
        }
        if candidates.is_empty() {
            return false;
        }
        let mut granularity = candidates.len();
        let mut res = false;
        loop {
            let n = candidates.len();
            let mut i = 0;
            while i < n {
                let mut reduce = false;
                let mut j = i;
                while j < n && j < i + granularity {
                    let k = candidates[j];
                    let c = &mut self.calls[k];
                    debug_assert!(c.type_ == SET);
                    saved[j] = c.val;
                    let new_val = lower[j];
                    if c.val == new_val {
                        j += 1;
                        continue;
                    }
                    c.val = new_val;
                    reduce = true;
                    j += 1;
                }
                if !reduce {
                    i += granularity;
                    continue;
                }
                self.progress();
                if self.fork_and_execute() == expected && !Signal::interrupted() {
                    res = true;
                } else {
                    let mut j = i;
                    while j < n && j < i + granularity {
                        let k = candidates[j];
                        let c = &mut self.calls[k];
                        debug_assert!(c.type_ == SET);
                        c.val = saved[j];
                        j += 1;
                    }
                }
                if Signal::interrupted() {
                    break;
                }
                i += granularity;
            }
            if Signal::interrupted() {
                break;
            }
            if granularity == 1 {
                break;
            }
            granularity = (granularity + 1) / 2;
        }
        self.notify(0);
        res
    }

    // Try to shrink the option values.

    fn reduce_values(&mut self, expected: i32) -> bool {
        if m().donot.reduce {
            return false;
        }
        if Signal::interrupted() {
            return false;
        }

        self.notify(b'r' as i8);

        debug_assert!(self.size() != 0);

        let mut changed = false;
        let mut res = false;
        loop {
            if Signal::interrupted() {
                res = false;
                break;
            }
            if changed {
                res = true;
            }
            changed = false;
            for i in 0..self.size() {
                let lo: i32;
                let hi: i32;

                {
                    let c = &self.calls[i];
                    if c.type_ == SET {
                        match Options::has(c.name()) {
                            Some(o) => {
                                lo = o.lo;
                                hi = o.hi;
                            }
                            None => continue,
                        }
                    } else if c.type_ == LIMIT {
                        if c.name() == "conflicts" || c.name() == "decisions" {
                            lo = -1;
                            hi = i32::MAX;
                        } else if c.name() == "terminate" || c.name() == "preprocessing" {
                            lo = 0;
                            hi = i32::MAX;
                        } else if c.name() == "localsearch" {
                            lo = 0;
                            hi = c.val; // too costly otherwise
                        } else {
                            continue;
                        }
                    } else if c.type_ == OPTIMIZE {
                        lo = 0;
                        hi = 9;
                    } else {
                        continue;
                    }
                }

                debug_assert!(lo <= hi);
                if self.calls[i].val == lo {
                    continue;
                }

                // First try to reach eagerly the low value
                // (includes the case that current value is too low).
                //
                let mut old_val = self.calls[i].val;
                self.calls[i].val = lo;
                self.progress();

                let success = (self.fork_and_execute() == expected) && !Signal::interrupted();
                if success {
                    debug_assert!(self.calls[i].val != old_val);
                    changed = true;
                } else {
                    self.calls[i].val = old_val;
                }

                if Signal::interrupted() {
                    break;
                }

                if success {
                    continue;
                }

                // Then try to limit to the high value if current value too large.
                //
                if self.calls[i].val > hi {
                    let old_val = self.calls[i].val;
                    self.calls[i].val = hi;
                    self.progress();
                    let success = (self.fork_and_execute() == expected) && !Signal::interrupted();
                    if success {
                        debug_assert!(self.calls[i].val != old_val);
                        changed = true;
                    } else {
                        self.calls[i].val = old_val;
                    }

                    if Signal::interrupted() {
                        break;
                    }
                    if !success {
                        continue;
                    }
                }

                // Now we do a delta-debugging inspired binary search for the smallest
                // value for which the execution produces a non-zero exit code.  It
                // kind of assumes monotonicity and if this is not the case might not
                // yield the smallest value, but remains logarithmic.
                //
                let granularity: i64 = ((old_val as i64 - lo as i64) + 1i64) / 2;
                debug_assert!(granularity > 0);
                let mut new_val: i64 = self.calls[i].val as i64 - granularity;
                while new_val > lo as i64 {
                    old_val = self.calls[i].val;
                    debug_assert!(new_val != old_val as i64);
                    debug_assert!((lo as i64) < new_val);
                    debug_assert!(new_val <= hi as i64);
                    self.calls[i].val = new_val as i32;
                    self.progress();
                    if (self.fork_and_execute() == expected) && !Signal::interrupted() {
                        debug_assert!(self.calls[i].val != old_val);
                        changed = true;
                    } else {
                        self.calls[i].val = old_val;
                    }
                    if Signal::interrupted() {
                        break;
                    }
                    new_val -= granularity;
                }
            }
            if !changed {
                break;
            }
        }

        self.notify(0);

        res
    }

    // Try to map variables to a contiguous initial range.

    fn map_variables(&mut self, expected: i32) {
        if m().donot.map {
            return;
        }
        if Signal::interrupted() {
            return;
        }
        let mut with_gaps = 0;
        while with_gaps <= 1 {
            self.notify(b'm' as i8);
            let mut variables: Vec<i32> = Vec::new();
            for c in &self.calls {
                if !has_lit_arg_type(c) {
                    continue;
                }
                if c.arg == 0 {
                    continue;
                }
                if c.arg == i32::MIN {
                    continue;
                }
                let idx = c.arg.abs();
                if variables.len() <= idx as usize {
                    variables.resize(1 + idx as usize, 0);
                }
                variables[idx as usize] += 1;
            }
            let mut gaps = 0;
            let mut max_idx = 0;
            let mut skipped = false;
            let mut i: i32 = 1;
            while (i as usize) < variables.len() {
                if variables[i as usize] == 0 {
                    if with_gaps != 0 && !skipped {
                        max_idx += 1;
                        skipped = true;
                    }
                    gaps += 1;
                } else {
                    max_idx += 1;
                    variables[i as usize] = max_idx;
                    skipped = false;
                }
                i += 1;
            }
            if gaps == 0 {
                self.notify(0);
                return;
            }
            let mut mapped = Trace::new(0, 0);
            for c in &self.calls {
                if c.arg == 0 || c.arg == i32::MIN {
                    mapped.push_back(c.copy());
                } else if has_lit_arg_type(c) {
                    let mut new_lit = variables[c.arg.abs() as usize];
                    debug_assert!(0 < new_lit);
                    debug_assert!(new_lit <= max_idx);
                    if c.arg < 0 {
                        new_lit = -new_lit;
                    }
                    let mut d = c.copy();
                    d.arg = new_lit;
                    mapped.push_back(d);
                } else {
                    mapped.push_back(c.copy());
                }
            }
            self.progress();
            if (mapped.fork_and_execute() == expected) && !Signal::interrupted() {
                self.clear();
                for i in 0..mapped.size() {
                    self.push_back(mapped.calls[i].copy());
                }
                self.notify(0);
                with_gaps = 2;
            }
            self.notify(0);
            if Signal::interrupted() {
                break;
            }
            with_gaps += 1;
        }
    }

    // Finally remove option calls.

    fn shrink_options(&mut self, expected: i32) {
        if m().donot.shrink.options {
            return;
        }
        if Signal::interrupted() {
            return;
        }
        self.notify(b'o' as i8);
        let mut segments: Segments = Vec::new();
        for i in 0..self.size() {
            if self.calls[i].type_ != SET {
                continue;
            }
            segments.push(Segment::new(i, i + 1));
        }

        let _ = self.shrink_segments(&mut segments, expected);
    }

    fn shrink(&mut self, expected: i32) {
        #[derive(PartialEq, Eq, Clone, Copy)]
        enum Shrinking {
            None,
            Phases,
            Clauses,
            Lemmas,
            #[allow(dead_code)]
            UPhases, // How many times the propagator answers
            Literals,
            Basic,
            Disable,
            Values,
        }

        m().shrinking = true;
        m().notified.clear();
        debug_assert!(!m().donot.shrink.atall);
        if self.size() == 0 {
            return;
        }
        self.add_options(expected);
        let mut l = Shrinking::None;
        loop {
            let mut s = false;
            if l != Shrinking::Phases && self.shrink_phases(expected) {
                s = true;
                l = Shrinking::Phases;
            }
            if l != Shrinking::Clauses && self.shrink_clauses(expected) {
                s = true;
                l = Shrinking::Clauses;
            }
            if l != Shrinking::Lemmas && self.shrink_lemmas(expected) {
                s = true;
                l = Shrinking::Lemmas;
            }
            if l != Shrinking::Literals && self.shrink_literals(expected) {
                s = true;
                l = Shrinking::Literals;
            }
            if l != Shrinking::Basic && self.shrink_basic(expected) {
                s = true;
                l = Shrinking::Basic;
            }
            if l != Shrinking::Disable && self.shrink_disable(expected) {
                s = true;
                l = Shrinking::Disable;
            }
            if l != Shrinking::Values && self.reduce_values(expected) {
                s = true;
                l = Shrinking::Values;
            }
            if !s {
                break;
            }
        }
        self.map_variables(expected);
        self.shrink_options(expected);
        // Execute one last time to get accurate results when memory fuzzing
        // is enabled.
        if !Signal::interrupted() {
            self.fork_and_execute();
        }
        cerr().flush();
        m().shrinking = false;
    }

    fn write_path(&self, path: &str) {
        if path == "-" {
            self.print(cout());
        } else {
            let mut os = open_ofstream(path);
            if os.own.is_null() {
                Mobical::die(&format!("can not write '{}'", path));
            }
            self.print(&mut os);
            close_ofstream(&mut os);
        }
    }

    fn write_prefixed_seed(&self, prefix: &str) {
        let name = format!("{}-{:020}.trace", prefix, self.seed);
        let mut os = open_ofstream(&name);
        if os.own.is_null() {
            Mobical::die(&format!("can not write '{}'", name));
        }
        self.print(&mut os);
        close_ofstream(&mut os);
        cerr().s(&name);
    }
}

/// `ofstream os (path)`.
fn open_ofstream(path: &str) -> OStream {
    let mut os = OStream::new(0);
    if let Ok(cpath) = std::ffi::CString::new(path) {
        // SAFETY: valid C strings.
        os.own = unsafe { libc::fopen(cpath.as_ptr(), b"w\0".as_ptr() as *const libc::c_char) };
    }
    os
}

fn close_ofstream(os: &mut OStream) {
    if !os.own.is_null() {
        // SAFETY: opened by 'open_ofstream'.
        unsafe { libc::fclose(os.own) };
        os.own = ptr::null_mut();
    }
}

fn pick_size(random: &mut Random, vars: i32) -> i32 {
    let mut res;
    let prop = random.generate_double();
    if prop < 0.0001 {
        res = 0;
    } else if prop < 0.001 {
        res = 1;
    } else if prop < 0.01 {
        res = 2;
    } else if prop < 0.90 {
        res = 3;
    } else if prop < 0.95 {
        res = 4;
    } else {
        res = random.pick_int(5, 20);
    }
    if res > vars {
        res = vars;
    }
    res
}

fn pick_literal(random: &mut Random, minvars: i32, maxvars: i32, clause: &[i32]) -> i32 {
    debug_assert!(minvars <= maxvars);
    let mut res = 0;
    while res == 0 {
        let idx = random.pick_int(minvars, maxvars);
        let prop = random.generate_double();
        if prop > 0.001 {
            let mut duplicated = false;
            let mut i = 0;
            while !duplicated && i < clause.len() {
                duplicated = clause[i].abs() == idx;
                i += 1;
            }
            if duplicated {
                continue;
            }
        }
        let sign = random.generate_bool();
        res = if sign { -idx } else { idx };
    }
    res
}

fn is_basic(c: &Call) -> bool {
    matches!(
        c.type_,
        ASSUME
            | SOLVE
            | SIMPLIFY
            | LOOKAHEAD
            | CUBING
            | PROPAGATE
            | VARS
            | ACTIVE
            | REDUNDANT
            | IRREDUNDANT
            | RESIZE
            | RESIZE_DIFFERENCE
            | VAL
            | FLIP
            | FLIPPABLE
            | FIXED
            | FAILED_
            | FROZEN
            | CONCLUDE
            | FREEZE
            | MELT
            | LIMIT
            | OPTIMIZE
            | OBSERVE
    )
}

fn has_lit_arg_type(c: &Call) -> bool {
    matches!(
        c.type_,
        ADD | CONSTRAIN | ASSUME | FREEZE | MELT | FROZEN | FLIP | FLIPPABLE | FIXED | FAILED_ | RESIZE | LEMMA | OBSERVE
    )
}

/*------------------------------------------------------------------------*/

struct Reader<'a> {
    trace: &'a mut Trace,

    path: String,
    file: *mut libc::FILE,
    lineno: i32,
    close: bool,
}

fn is_valid_char(ch: i32) -> bool {
    if ch == b' ' as i32 {
        return true;
    }
    if ch == b'-' as i32 {
        return true;
    }
    if (b'a' as i32..=b'z' as i32).contains(&ch) {
        return true;
    }
    if (b'0' as i32..=b'9' as i32).contains(&ch) {
        return true;
    }

    // For now proof file paths can only have these additional characters.
    // We should probably have an escape mechamism (quotes) for paths.

    if ch == b'_' as i32 || ch == b'/' as i32 || ch == b'.' as i32 || (b'A' as i32..=b'Z' as i32).contains(&ch) {
        return true;
    }

    false
}

/// Extract the zero terminated C string starting at 'start' of 'line'.
fn cstr_at(line: &[u8], start: usize) -> String {
    let mut end = start;
    while end < line.len() && line[end] != 0 {
        end += 1;
    }
    String::from_utf8_lossy(&line[start..end]).into_owned()
}

impl<'a> Reader<'a> {
    fn new(trace: &'a mut Trace, p: &str) -> Reader<'a> {
        let mut res = Reader { trace, path: String::new(), file: ptr::null_mut(), lineno: 1, close: false };
        if p == "-" {
            res.path = "<stdin>".to_string();
            res.file = crate::message::c_stdin();
            res.close = false;
        } else {
            let file = match std::ffi::CString::new(p) {
                // SAFETY: valid C strings.
                Ok(cpath) => unsafe { libc::fopen(cpath.as_ptr(), b"r\0".as_ptr() as *const libc::c_char) },
                Err(_) => ptr::null_mut(),
            };
            if file.is_null() {
                Mobical::die(&format!("can not read '{}'", p));
            }
            res.file = file;
            res.path = p.to_string();
            res.close = true;
        }
        res
    }

    fn next(&mut self) -> i32 {
        // SAFETY: 'file' is an open stream.
        unsafe { libc::fgetc(self.file) }
    }

    fn error(&self, msg: &str) -> ! {
        Mobical::error_prefix();
        terminal().red(true);
        fputs("parse error:", c_stderr());
        terminal().normal();
        fputs(&format!(" {}:{}: ", self.path, self.lineno), c_stderr());
        fputs(msg, c_stderr());
        fputc(b'\n' as i32, c_stderr());
        terminal().reset();
        // SAFETY: 'exit' as in C++.
        unsafe { libc::exit(1) }
    }

    fn parse(&mut self) {
        let mut lit: i32 = 0;
        let mut val: i32 = 0;
        let mut adding: i32 = 0;
        let mut constraining: i32 = 0;
        let mut lemma_adding: i32 = 0;
        let mut solved: i32 = 0;
        let mut state: u64 = 0;
        let enforce = !m().donot.enforce;
        let mut before_trigger: Option<(&'static str, i32)> = None;
        let mut line = [0u8; 80];
        loop {
            let mut ch = self.next();
            if ch == libc::EOF {
                break;
            }
            // Ignore comments (used for additional human readable information).
            if ch == b'#' as i32 {
                while ch != b'\n' as i32 {
                    ch = self.next();
                    if ch == libc::EOF {
                        self.error("unexpected end-of-file");
                    }
                }
                continue;
            }
            let mut n: usize = 0;
            while ch != b'\n' as i32 {
                if n + 2 >= line.len() {
                    self.error("line too large");
                }
                if !is_valid_char(ch) {
                    // SAFETY: 'isprint' on a character code.
                    if unsafe { libc::isprint(ch) } != 0 {
                        self.error(&format!("invalid character '{}'", ch as u8 as char));
                    } else {
                        self.error(&format!("invalid character code 0x{:02x}", ch));
                    }
                }
                line[n] = ch as u8;
                n += 1;
                ch = self.next();
                if ch == libc::EOF {
                    self.error("unexpected end-of-file");
                }
            }
            debug_assert!(n < line.len());
            line[n] = 0;
            let mut p: usize = 0;
            let isdigit = |c: u8| c.is_ascii_digit();
            if isdigit(line[p]) {
                loop {
                    p += 1;
                    if !isdigit(line[p]) {
                        break;
                    }
                }
                let c = line[p];
                if c == 0 {
                    self.error("incomplete line with only line number");
                }
                if c != b' ' {
                    self.error("expected space after line number");
                }
                p += 1;
            }
            let keyword_start = p;
            let mut c = line[p];
            if !(b'a'..=b'z').contains(&c) {
                self.error("expected keyword to start with lower case letter");
            }
            while p < n {
                p += 1;
                c = line[p];
                if !(c != 0 && ((b'a'..=b'z').contains(&c) || c == b'_')) {
                    break;
                }
            }
            let mut first: Option<String> = None;
            let mut second: Option<String> = None;
            c = line[p];
            if c == b' ' {
                line[p] = 0;
                p += 1;
                let first_start = p;
                c = line[p];
                if c == 0 {
                    self.error("first argument missing after trailing space");
                }
                if c == b' ' {
                    self.error("space in place of first argument");
                }
                loop {
                    p += 1;
                    c = line[p];
                    if !(c != 0 && c != b' ') {
                        break;
                    }
                }
                if c == b' ' {
                    line[p] = 0;
                    p += 1;
                    let second_start = p;
                    c = line[p];
                    if c == 0 {
                        self.error("second argument missing after trailing space");
                    }
                    if c == b' ' {
                        self.error("space in place of second argument");
                    }
                    loop {
                        p += 1;
                        c = line[p];
                        if !(c != 0 && c != b' ') {
                            break;
                        }
                    }
                    if c == b' ' {
                        line[p] = 0;
                        let s = cstr_at(&line, second_start);
                        self.error(&format!("unexpected space after second argument '{}'", s));
                    }
                    second = Some(cstr_at(&line, second_start));
                }
                first = Some(cstr_at(&line, first_start));
                c = 0;
            } else if c != 0 {
                self.error(&format!("unexpected character '{}' in keyword", c as char));
            }
            debug_assert!(c == 0);
            let keyword = cstr_at(&line, keyword_start);
            let keyword = keyword.as_str();
            let first_s = first.as_deref();
            let second_s = second.as_deref();
            // 'printf ("%s", NULL)' prints '(null)'.
            let fstr = first_s.unwrap_or("(null)");
            let sstr = second_s.unwrap_or("(null)");
            let parse_int = |s: Option<&str>, v: &mut i32| -> bool {
                match s {
                    Some(s) => parse_int_str(s, v),
                    None => false,
                }
            };
            let c: Call;
            if keyword == "init" {
                if first_s.is_some() {
                    self.error(&format!("unexpected argument '{}' after 'init'", fstr));
                }
                c = Call::init();
            } else if keyword == "set" {
                if first_s.is_none() {
                    self.error("first argument to 'set' missing");
                }
                if enforce && !Solver::is_valid_option(fstr) {
                    #[cfg(not(feature = "logging"))]
                    {
                        if fstr == "log" {
                            Mobical::warning(
                                "ignoring non-existing option name 'log' (compiled without '-DLOGGING')",
                            );
                        } else {
                            self.error(&format!("non-existing option name '{}'", fstr));
                        }
                    }
                    #[cfg(feature = "logging")]
                    self.error(&format!("non-existing option name '{}'", fstr));
                }
                if second_s.is_none() {
                    self.error("second argument to 'set' missing");
                }
                if !parse_int(second_s, &mut val) {
                    self.error(&format!("invalid second argument '{}' to 'set'", sstr));
                }
                c = Call::set(fstr, val);
            } else if keyword == "configure" {
                if first_s.is_none() {
                    self.error("first argument to 'configure' missing");
                }
                if enforce && !Solver::is_valid_configuration(fstr) {
                    self.error(&format!("non-existing configuration '{}'", fstr));
                }
                if second_s.is_some() {
                    self.error(&format!("additional argument '{}' to 'configure'", sstr));
                }
                c = Call::configure(fstr);
            } else if keyword == "limit" {
                if first_s.is_none() {
                    self.error("first argument to 'limit' missing");
                }
                if second_s.is_none() {
                    self.error("second argument to 'limit' missing");
                }
                if !parse_int(second_s, &mut val) {
                    self.error(&format!("invalid second argument '{}' to 'limit'", sstr));
                }
                c = Call::limit(fstr, val);
            } else if keyword == "optimize" {
                if first_s.is_none() {
                    self.error("argument to 'optimize' missing");
                }
                if !parse_int(first_s, &mut val) || val < 0 || val > 31 {
                    self.error(&format!("invalid argument '{}' to 'optimize'", fstr));
                }
                c = Call::optimize(val);
            } else if keyword == "vars" {
                if first_s.is_some() {
                    self.error(&format!("unexpected argument '{}' after 'vars'", fstr));
                }
                c = Call::vars();
            } else if keyword == "active" {
                if first_s.is_some() {
                    self.error(&format!("unexpected argument '{}' after 'active'", fstr));
                }
                c = Call::active();
            } else if keyword == "redundant" {
                if first_s.is_some() {
                    self.error(&format!("unexpected argument '{}' after 'redundant'", fstr));
                }
                c = Call::redundant();
            } else if keyword == "irredundant" {
                if first_s.is_some() {
                    self.error(&format!("unexpected argument '{}' after 'irredundant'", fstr));
                }
                c = Call::irredundant();
            } else if keyword == "resize" {
                if first_s.is_none() {
                    self.error("argument to 'resize' missing");
                }
                if !parse_int(first_s, &mut lit) {
                    self.error(&format!("invalid argument '{}' to 'resize'", fstr));
                }
                if second_s.is_some() {
                    self.error(&format!("additional argument '{}' to 'resize'", sstr));
                }
                c = Call::resize(lit);
            } else if keyword == "declare_more_variables" {
                if !parse_int(first_s, &mut lit) {
                    self.error(&format!("invalid argument '{}' to 'resize'", fstr));
                }
                c = Call::declare_more_variables(lit);
            } else if keyword == "phase" {
                if first_s.is_none() {
                    self.error("argument to 'phase' missing");
                }
                if !parse_int(first_s, &mut lit) {
                    self.error(&format!("invalid argument '{}' to 'phase'", fstr));
                }
                if second_s.is_some() {
                    self.error(&format!("additional argument '{}' to 'phase'", sstr));
                }
                c = Call::phase(lit);
            } else if keyword == "add" {
                if first_s.is_none() {
                    self.error("argument to 'add' missing");
                }
                if !parse_int(first_s, &mut lit) {
                    self.error(&format!("invalid argument '{}' to 'add'", fstr));
                }
                if second_s.is_some() {
                    self.error(&format!("additional argument '{}' to 'add'", sstr));
                }
                if enforce && lit == i32::MIN {
                    self.error(&format!("invalid literal '{}' as argument to 'add'", lit));
                }
                adding = lit;
                c = Call::add(lit);
            } else if keyword == "constrain" {
                if first_s.is_none() {
                    self.error("argument to 'constrain' missing");
                }
                if !parse_int(first_s, &mut lit) {
                    self.error(&format!("invalid argument '{}' to 'constrain'", fstr));
                }
                if second_s.is_some() {
                    self.error(&format!("additional argument '{}' to 'constrain'", sstr));
                }
                if enforce && lit == i32::MIN {
                    self.error(&format!("invalid literal '{}' as argument to 'constrain'", lit));
                }
                constraining = lit;
                c = Call::constrain(lit);
            } else if keyword == "connect" {
                c = Call::connect();
            } else if keyword == "disconnect" {
                c = Call::disconnect();
            } else if keyword == "observe" {
                if first_s.is_none() {
                    self.error("argument to 'observe' missing");
                }
                if !parse_int(first_s, &mut lit) {
                    self.error(&format!("invalid argument '{}' to 'observe'", fstr));
                }
                if second_s.is_some() {
                    self.error(&format!("additional argument '{}' to 'observe'", sstr));
                }
                c = Call::observe(lit);
            } else if keyword == "lemma" {
                if first_s.is_none() {
                    self.error("argument to 'lemma' missing");
                }
                if !parse_int(first_s, &mut lit) {
                    self.error(&format!("invalid argument '{}' to 'lemma'", fstr));
                }
                if second_s.is_some() {
                    self.error(&format!("additional argument '{}' to 'lemma'", sstr));
                }
                if enforce && lit == i32::MIN {
                    self.error(&format!("invalid literal '{}' as argument to 'lemma'", lit));
                }
                // if (!lemma_adding && !lit) error ("empty lemma is learned.");
                lemma_adding = lit;
                c = Call::lemma(lit);
            } else if keyword == "assume" {
                if first_s.is_none() {
                    self.error("argument to 'assume' missing");
                }
                if !parse_int(first_s, &mut lit) {
                    self.error(&format!("invalid argument '{}' to 'assume'", fstr));
                }
                if second_s.is_some() {
                    self.error(&format!("additional argument '{}' to 'assume'", sstr));
                }
                if enforce && (lit == 0 || lit == i32::MIN) {
                    self.error(&format!("invalid literal '{}' as argument to 'assume'", lit));
                }
                c = Call::assume(lit);
            } else if keyword == "solve" {
                if first_s.is_some() && !parse_int(first_s, &mut lit) {
                    self.error(&format!("invalid argument '{}' to 'solve'", fstr));
                }
                if first_s.is_some() && lit != 0 && lit != 10 && lit != 20 {
                    self.error(&format!("invalid result argument '{}' to 'solve'", lit));
                }
                debug_assert!(second_s.is_none());
                c = if first_s.is_some() { Call::solve(lit) } else { Call::solve(0) };
                solved += 1;
            } else if keyword == "simplify" {
                if first_s.is_none() {
                    self.error("argument to 'simplify' missing");
                }
                let mut rounds: i32 = 0;
                if !parse_int(first_s, &mut rounds) || rounds < 0 {
                    self.error(&format!("invalid argument '{}' to 'simplify'", fstr));
                }
                let mut tmp: i32 = 0;
                if second_s.is_some() && !parse_int(second_s, &mut tmp) {
                    self.error(&format!("invalid second argument '{}' to 'simplify'", sstr));
                }
                if second_s.is_some() && tmp != 0 && tmp != 10 && tmp != 20 {
                    self.error(&format!("invalid second argument '{}' to 'solve'", tmp));
                }
                c = if second_s.is_some() { Call::simplify(rounds, tmp) } else { Call::simplify(rounds, 0) };
                solved += 1;
            } else if keyword == "lookahead" {
                if first_s.is_some() && !parse_int(first_s, &mut lit) {
                    self.error(&format!("invalid argument '{}' to 'lookahead'", fstr));
                }
                debug_assert!(second_s.is_none());
                c = if first_s.is_some() { Call::lookahead(lit) } else { Call::lookahead(0) };
                solved += 1;
            } else if keyword == "cubing" {
                if first_s.is_some() && !parse_int(first_s, &mut lit) {
                    self.error(&format!("invalid argument '{}' to 'cubing'", fstr));
                }
                debug_assert!(second_s.is_none());
                c = Call::cubing(lit);
                solved += 1;
            } else if keyword == "propagate" {
                if first_s.is_some() && !parse_int(first_s, &mut lit) {
                    self.error(&format!("invalid argument '{}' to 'solve'", fstr));
                }
                if first_s.is_some() && lit != 0 && lit != 10 && lit != 20 {
                    self.error(&format!("invalid result argument '{}' to 'solve'", lit));
                }
                debug_assert!(second_s.is_none());
                c = if first_s.is_some() { Call::propagate(lit) } else { Call::propagate(0) };
            } else if keyword == "val" {
                if first_s.is_none() {
                    self.error("first argument to 'val' missing");
                }
                if !parse_int(first_s, &mut lit) {
                    self.error(&format!("invalid first argument '{}' to 'val'", fstr));
                }
                if enforce && (lit == 0 || lit == i32::MIN) {
                    self.error(&format!("invalid literal '{}' as argument to 'val'", lit));
                }
                if second_s.is_some() && !parse_int(second_s, &mut val) {
                    self.error(&format!("invalid second argument '{}' to 'val'", sstr));
                }
                if second_s.is_some() && val != -1 && val != 0 && val != 1 {
                    self.error(&format!("invalid result argument '{}' to 'val", val));
                }
                c = if second_s.is_some() { Call::val(lit, val) } else { Call::val(lit, 0) };
            } else if keyword == "flip" {
                if first_s.is_none() {
                    self.error("first argument to 'flip' missing");
                }
                if !parse_int(first_s, &mut lit) {
                    self.error(&format!("invalid first argument '{}' to 'flip'", fstr));
                }
                if enforce && (lit == 0 || lit == i32::MIN) {
                    self.error(&format!("invalid literal '{}' as argument to 'flip'", lit));
                }
                if second_s.is_some() && !parse_int(second_s, &mut val) {
                    self.error(&format!("invalid second argument '{}' to 'flip'", sstr));
                }
                if second_s.is_some() && val != 0 && val != 1 {
                    self.error(&format!("invalid result argument '{}' to 'flip", val));
                }
                c = if second_s.is_some() { Call::flip(lit, val) } else { Call::flip(lit, 0) };
            } else if keyword == "flippable" {
                if first_s.is_none() {
                    self.error("first argument to 'flippable' missing");
                }
                if !parse_int(first_s, &mut lit) {
                    self.error(&format!("invalid first argument '{}' to 'flippable'", fstr));
                }
                if enforce && (lit == 0 || lit == i32::MIN) {
                    self.error(&format!("invalid literal '{}' as argument to 'flippable'", lit));
                }
                if second_s.is_some() && !parse_int(second_s, &mut val) {
                    self.error(&format!("invalid second argument '{}' to 'flippable'", sstr));
                }
                if second_s.is_some() && val != 0 && val != 1 {
                    self.error(&format!("invalid result argument '{}' to 'flippable", val));
                }
                c = if second_s.is_some() { Call::flippable(lit, val) } else { Call::flippable(lit, 0) };
            } else if keyword == "fixed" {
                if first_s.is_none() {
                    self.error("first argument to 'fixed' missing");
                }
                if !parse_int(first_s, &mut lit) {
                    self.error(&format!("invalid first argument '{}' to 'fixed'", fstr));
                }
                if enforce && (lit == 0 || lit == i32::MIN) {
                    self.error(&format!("invalid literal '{}' as argument to 'fixed'", lit));
                }
                if second_s.is_some() && !parse_int(second_s, &mut val) {
                    self.error(&format!("invalid second argument '{}' to 'fixed'", sstr));
                }
                #[allow(clippy::nonminimal_bool)]
                if second_s.is_some() && val != -1 && val != 0 && val != -1 {
                    self.error(&format!("invalid result argument '{}' to 'fixed", val));
                }
                c = if second_s.is_some() { Call::fixed(lit, val) } else { Call::fixed(lit, 0) };
            } else if keyword == "failed" {
                if first_s.is_none() {
                    self.error("first argument to 'failed' missing");
                }
                if !parse_int(first_s, &mut lit) {
                    self.error(&format!("invalid first argument '{}' to 'failed'", fstr));
                }
                if enforce && (lit == 0 || lit == i32::MIN) {
                    self.error(&format!("invalid literal '{} 'as argument to 'failed'", lit));
                }
                if second_s.is_some() && !parse_int(second_s, &mut val) {
                    self.error(&format!("invalid second argument '{}' to 'failed'", sstr));
                }
                if second_s.is_some() && val != 0 && val != -1 {
                    self.error(&format!("invalid result argument '{}' to 'failed", val));
                }
                c = if second_s.is_some() { Call::failed(lit, val) } else { Call::failed(lit, 0) };
            } else if keyword == "conclude" {
                if first_s.is_some() {
                    self.error(&format!("additional argument '{}' to 'conclude'", fstr));
                }
                c = Call::conclude();
            } else if keyword == "freeze" {
                if first_s.is_none() {
                    self.error("argument to 'freeze' missing");
                }
                if !parse_int(first_s, &mut lit) {
                    self.error(&format!("invalid argument '{}' to 'freeze'", fstr));
                }
                if enforce && (lit == 0 || lit == i32::MIN) {
                    self.error(&format!("invalid literal {} as argument to 'freeze'", lit));
                }
                if second_s.is_some() {
                    self.error(&format!("additional argument '{}' to 'freeze'", sstr));
                }
                c = Call::freeze(lit);
            } else if keyword == "melt" {
                if first_s.is_none() {
                    self.error("argument to 'melt' missing");
                }
                if !parse_int(first_s, &mut lit) {
                    self.error(&format!("invalid argument '{}' to 'melt'", fstr));
                }
                if enforce && (lit == 0 || lit == i32::MIN) {
                    self.error(&format!("invalid literal '{}' as argument to 'melt'", lit));
                }
                if second_s.is_some() {
                    self.error(&format!("additional argument '{}' to 'melt'", sstr));
                }
                c = Call::melt(lit);
            } else if keyword == "frozen" {
                if first_s.is_none() {
                    self.error("first argument to 'frozen' missing");
                }
                if !parse_int(first_s, &mut lit) {
                    self.error(&format!("invalid first argument '{}' to 'frozen'", fstr));
                }
                if second_s.is_some() && !parse_int(second_s, &mut val) {
                    self.error(&format!("invalid second argument '{}' to 'frozen'", sstr));
                }
                if second_s.is_some() && val != 0 && val != 1 {
                    self.error(&format!("invalid result argument '{}' to 'frozen'", val));
                }
                c = if second_s.is_some() { Call::frozen(lit, val) } else { Call::frozen(lit, 0) };
            } else if keyword == "dump" {
                if first_s.is_some() {
                    self.error(&format!("additional argument '{}' to 'dump'", fstr));
                }
                c = Call::dump();
            } else if keyword == "stats" {
                if first_s.is_some() {
                    self.error(&format!("additional argument '{}' to 'stats'", fstr));
                }
                c = Call::stats();
            } else if keyword == "reset" {
                if first_s.is_some() {
                    self.error(&format!("additional argument '{}' to 'reset'", fstr));
                }
                c = Call::reset();
            } else if keyword == "trace_proof" {
                if first_s.is_none() {
                    self.error("first argument to 'trace_proof' missing");
                }
                if second_s.is_some() {
                    self.error(&format!("additional argument '{}' to 'trace_proof'", sstr));
                }
                c = Call::trace_proof(fstr);
            } else if keyword == "flush_proof_trace" {
                if first_s.is_some() {
                    self.error(&format!("additional argument '{}' to 'flush_proof_trace'", fstr));
                }
                c = Call::flush_proof_trace();
            } else if keyword == "close_proof_trace" {
                if first_s.is_some() {
                    self.error(&format!("additional argument '{}' to 'close_proof_trace'", fstr));
                }
                c = Call::close_proof_trace();
            } else if keyword == "propagate_assumptions" {
                c = Call::propagate_assumptions(0);
            } else if keyword == "implied" {
                c = Call::implied(0);
            } else if keyword == "reset_assumptions" {
                c = Call::reset_assumptions(0);
            } else if keyword == "declare_one_more_variable" {
                c = Call::declare_one_more_variable();
            } else {
                self.error(&format!("invalid keyword '{}'", keyword));
            }

            // This checks the legal structure of traces described above.
            //
            if enforce {
                if state == 0 && c.type_ != INIT {
                    self.error("first call has to be an 'init' or 'maxalloc' call");
                }

                if state == RESET {
                    self.error(&format!("'{}' after 'reset'", c.keyword()));
                }

                if adding != 0 && c.type_ != ADD && c.type_ != RESET {
                    self.error(&format!("'{}' after 'add {}' without 'add 0'", c.keyword(), adding));
                }

                if lemma_adding != 0 && c.type_ != LEMMA && c.type_ != RESET {
                    self.error(&format!("'{}' after 'lemma {}' without 'lemma 0'", c.keyword(), lemma_adding));
                }

                if constraining != 0 && c.type_ != FIXED && c.type_ != CONSTRAIN && c.type_ != RESET {
                    self.error(&format!(
                        "'{}' after 'constrain {}' without 'constrain 0'",
                        c.keyword(),
                        constraining
                    ));
                }

                let mut new_state = state;

                match c.type_ {
                    INIT => {
                        if state != 0 {
                            self.error("invalid second 'init' call");
                        }
                        new_state = CONFIG;
                    }

                    SET | CONFIGURE => {
                        if solved == 0 && state == BEFORE {
                            debug_assert!(before_trigger.is_some());
                            let (kw, arg) = before_trigger.unwrap_or(("", 0));
                            self.error(&format!(
                                "'{}' can only be called after 'init' before '{} {}'",
                                c.keyword(),
                                kw,
                                arg
                            ));
                        } else if state != CONFIG {
                            self.error(&format!("'{}' can only be called right after 'init'", c.keyword()));
                        }
                        debug_assert!(new_state == CONFIG);
                    }

                    ADD | ASSUME | OBSERVE => {
                        if state != BEFORE {
                            before_trigger = Some((c.keyword(), c.arg));
                        }
                        new_state = BEFORE;
                    }

                    VAL | FLIP | FLIPPABLE | FAILED_ | CONCLUDE => {
                        if solved == 0 && (state == CONFIG || state == BEFORE) {
                            self.error(&format!("'{}' can only be called after 'solve'", c.keyword()));
                        }
                        if solved != 0 && state == BEFORE {
                            debug_assert!(before_trigger.is_some());
                            let (kw, arg) = before_trigger.unwrap_or(("", 0));
                            self.error(&format!(
                                "'{}' only valid after last 'solve' and before '{} {}'",
                                c.keyword(),
                                kw,
                                arg
                            ));
                        }
                        debug_assert!(
                            state == SOLVE
                                || state == SIMPLIFY
                                || state == LOOKAHEAD
                                || state == CUBING
                                || state == PROPAGATE
                                || state == OBSERVE
                                || state == LEMMA
                                || state == AFTER
                        );
                        new_state = AFTER;
                    }

                    SOLVE | SIMPLIFY | LOOKAHEAD | CUBING | PROPAGATE | RESET | CONNECT | LEMMA | DISCONNECT => {
                        new_state = c.type_;
                    }

                    _ => {}
                }

                state = new_state;
            }

            #[cfg(feature = "logging")]
            if self.trace.size() == 1 && m().add_set_log_to_true {
                self.trace.push_back(Call::set("log", 1));
            }

            let ctype = c.type_;

            if m().add_dump_before_solve && process_type(ctype) {
                self.trace.push_back(Call::dump());
            }

            self.trace.push_back(c);

            if m().add_stats_after_solve && process_type(ctype) {
                self.trace.push_back(Call::stats());
            }

            self.lineno += 1;
        }
        if adding != 0 {
            self.error(&format!("EOF after 'add {}' without 'add 0'", adding));
        }
        if lemma_adding != 0 {
            self.error(&format!("EOF after 'lemma {}' without 'lemma 0'", lemma_adding));
        }
        if constraining != 0 {
            self.error(&format!("EOF after 'constrain {}' without 'constrain 0'", constraining));
        }
    }
}

impl<'a> Drop for Reader<'a> {
    fn drop(&mut self) {
        if self.close {
            // SAFETY: opened by 'Reader::new'.
            unsafe { libc::fclose(self.file) };
        }
    }
}

/*------------------------------------------------------------------------*/

/// C `atol` (as used on digit only strings: saturates like 'strtol').
fn atol(str: &str) -> i64 {
    let mut res: i64 = 0;
    for &ch in str.as_bytes() {
        if !ch.is_ascii_digit() {
            break;
        }
        res = match res.checked_mul(10).and_then(|r| r.checked_add((ch - b'0') as i64)) {
            Some(r) => r,
            None => return i64::MAX,
        };
    }
    res
}

/// C `atoi` (`(int) strtol (...)`).
fn atoi(str: &str) -> i32 {
    atol(str) as i32
}

/// `Mobical::main`.
fn mobical_main(argv: &[String]) -> i32 {
    let argc = argv.len();

    // First parse command line options and determine mode.
    //
    let mut seed_str: Option<String> = None;
    let mut input_path: Option<String> = None;
    let mut output_path: Option<String> = None;

    let mut limit: i64 = -1;

    // Error message in 'die' also uses colors.
    //
    for arg in argv.iter().skip(1) {
        if is_color_option(arg) {
            tout().force_colors();
            terr().force_colors();
        } else if is_no_color_option(arg) {
            terminal().force_no_colors();
        } else if arg == "--no-terminal" {
            terminal().disable();
        }
    }

    let mut i = 1;
    while i < argc {
        let arg = argv[i].as_str();
        let b = arg.as_bytes();
        if arg == "-h" {
            let usage = USAGE
                .replacen("%d", &DEFAULT_TIME_LIMIT.to_string(), 1)
                .replacen("%d", &DEFAULT_SPACE_LIMIT.to_string(), 1);
            fputs(&usage, c_stdout());
            // SAFETY: 'exit'.
            unsafe { libc::exit(0) };
        } else if arg == "--version" {
            fputs(version(), c_stdout());
            fputc(b'\n' as i32, c_stdout());
            // SAFETY: 'exit'.
            unsafe { libc::exit(0) };
        } else if arg == "--build" {
            tout().disable();
            Solver::build(c_stdout(), "");
            // SAFETY: 'exit'.
            unsafe { libc::exit(0) };
        } else if arg == "-v" || arg == "--verbose" {
            m().verbose = true;
        } else if arg == "-q" || arg == "--quiet" {
            terminal().disable();
            m().quiet = true;
        } else if is_color_option(arg) || is_no_color_option(arg) {
        } else if arg == "--no-terminal" {
            debug_assert!(!terminal().connected());
        } else if arg == "--do-not-execute" {
            m().donot.execute = true;
        } else if arg == "--do-not-fork" {
            m().donot.fork = true;
        } else if arg == "--do-not-enforce-contracts" {
            m().donot.enforce = true;
        } else if arg == "--no-seeds" {
            m().donot.seeds = true;
        } else if arg == "--do-not-shrink" || arg == "--do-not-shrink-at-all" {
            m().donot.shrink.atall = true;
        } else if arg == "--do-not-add-options" || arg == "--do-not-add-options-before-shrinking" {
            m().donot.add = true;
        } else if arg == "--do-not-shrink-phases" {
            m().donot.shrink.phases = true;
        } else if arg == "--do-not-shrink-clauses" {
            m().donot.shrink.clauses = true;
        } else if arg == "--do-not-shrink-lemmas" {
            m().donot.shrink.lemmas = true;
        } else if arg == "--do-not-shrink-literals" {
            m().donot.shrink.literals = true;
        } else if arg == "--do-not-shrink-basic" || arg == "--do-not-shrink-basic-calls" {
            m().donot.shrink.basic = true;
        } else if arg == "--do-not-shrink-options" {
            m().donot.shrink.options = true;
        } else if arg == "--do-not-disable" || arg == "--do-not-disable-options" {
            m().donot.disable = true;
        } else if arg == "--do-not-shrink-variables" {
            m().donot.map = true;
        } else if arg == "--do-not-reduce" || arg == "--do-not-reduce-values" || arg == "--do-not-reduce-option-values"
        {
            m().donot.reduce = true;
        } else if arg == "--tiny" {
            m().force.size = TINY;
        } else if arg == "--small" {
            m().force.size = SMALL;
        } else if arg == "--medium" {
            m().force.size = MEDIUM;
        } else if arg == "--big" {
            m().force.size = BIG;
        } else if arg == "-l" || arg == "--log" {
            m().add_set_log_to_true = true;
        } else if arg == "-d" || arg == "--dump" {
            m().add_dump_before_solve = true;
        } else if arg == "-s" || arg == "--stats" {
            m().add_stats_after_solve = true;
        } else if arg == "-p" || arg == "--plain" {
            m().add_plain_after_options = true;
        } else if arg == "-L" {
            if limit >= 0 {
                Mobical::die("multiple '-L' options (try '-h')");
            }
            i += 1;
            if i == argc {
                Mobical::die("argument to '-L' missing (try '-h')");
            }
            let a = argv[i].as_str();
            if !Mobical::is_unsigned_str(a) || {
                limit = atol(a);
                limit < 0
            } {
                Mobical::die(&format!("invalid argument '{}' to '-L' (try '-h')", a));
            }
        } else if b.len() >= 2 && b[0] == b'-' && b[1] == b'L' {
            if limit >= 0 {
                Mobical::die("multiple '-L' options (try '-h')");
            }
            if !Mobical::is_unsigned_str(&arg[2..]) || {
                limit = atol(&arg[2..]);
                limit < 0
            } {
                Mobical::die(&format!("invalid argument in '{}' (try '-h')", arg));
            }
        } else if arg == "--time" {
            i += 1;
            if i == argc {
                Mobical::die("argument to '--time' missing (try '-h')");
            }
            let a = argv[i].as_str();
            if !Mobical::is_unsigned_str(a) || {
                m().time_limit = atol(a);
                m().time_limit < 0 || m().time_limit as f64 > 1e9
            } {
                Mobical::die(&format!("invalid argument '{}' to '--time' (try '-h')", a));
            }
        } else if arg == "--space" {
            i += 1;
            if i == argc {
                Mobical::die("argument to '--space' missing (try '-h')");
            }
            let a = argv[i].as_str();
            if !Mobical::is_unsigned_str(a) || {
                m().space_limit = atol(a);
                m().space_limit < 0 || m().space_limit as f64 > 1e9
            } {
                Mobical::die(&format!("invalid argument '{}' to '--space' (try '-h')", a));
            }
        } else if arg == "--bad-alloc" {
            Mobical::die("--bad-alloc requires memory fuzzing to be enabled at compile time");
        } else if arg == "--leak-alloc" {
            Mobical::die("--leak-alloc requires memory fuzzing to be enabled at compile time");
        } else if arg == "--do-not-ignore-resource-limits" {
            m().donot.ignore_resource_limits = true;
        } else if !b.is_empty() && b[0] == b'-' && Mobical::is_unsigned_str(&arg[1..]) {
            m().force.phases = atoi(&arg[1..]);
            if m().force.phases < 0 {
                Mobical::die(&format!("invalid number of phases '{}'", arg));
            }
        } else if b.len() >= 2 && b[0] == b'-' {
            Mobical::die(&format!("invalid option '{}' (try '-h')", arg));
        } else if Mobical::is_unsigned_str(arg) {
            if let Some(s) = &seed_str {
                Mobical::die(&format!("can not handle multiple seeds '{}' and '{}' (try '-h')", s, arg));
            }
            if let Some(p) = &input_path {
                Mobical::die(&format!("can not combine input trace '{}' and seed '{}' (try '-h')", p, arg));
            }
            seed_str = Some(arg.to_string());
        } else if let Some(o) = &output_path {
            debug_assert!(input_path.is_some());
            Mobical::die(&format!(
                "too many trace files specified: '{}', '{}' and '{}' (try '-h')",
                input_path.as_deref().unwrap_or("(null)"),
                o,
                arg
            ));
        } else if let Some(p) = input_path.clone() {
            if let Some(s) = &seed_str {
                Mobical::die(&format!("seed '{}' with two output files '{}' and '{}' ", s, p, arg));
            }
            if p != "-" && p == arg {
                Mobical::die(&format!("input '{}' and output '{}' are the same", p, arg));
            }
            output_path = Some(arg.to_string());
        } else {
            if seed_str.is_none() && arg != "-" && !File::exists(arg) {
                Mobical::die(&format!("can not access input trace '{}' (try '-h')", arg));
            }
            input_path = Some(arg.to_string());
        }
        i += 1;
    }

    /*----------------------------------------------------------------------*/

    // If a seed and a file (in that order) are specified the file is actually
    // not an input file but an output file.  To streamline the code below
    // swap input and output here.
    //
    if input_path.is_some() && seed_str.is_some() {
        debug_assert!(output_path.is_none());
        output_path = input_path.take();
    }

    if let Some(o) = &output_path {
        if !File::writable(o) {
            Mobical::die(&format!("can not write output trace '{}' (try '-h')", o));
        }
    }

    /*----------------------------------------------------------------------*/

    // Check illegal combinations of options.

    if let Some(p) = &input_path {
        if m().donot.seeds {
            Mobical::die(&format!("can not use '--no-seeds' while specifying input '{}' explicitly", p));
        }
    }

    if let Some(p) = &input_path {
        if limit >= 0 {
            Mobical::die(&format!("can not combine '-L' and input '{}'", p));
        }
    }

    if let Some(o) = &output_path {
        if limit >= 0 {
            Mobical::die(&format!("can not combine '-L' and output '{}'", o));
        }
    }

    if output_path.is_none() && m().donot.execute {
        Mobical::die("can not use '--do-no-execute' without '<output>'");
    }

    if input_path.is_none() && m().donot.enforce {
        Mobical::die("can not use '--do-not-enforce-contracts' without '<input>'");
    }

    if output_path.is_some() && m().donot.enforce {
        Mobical::die("can not use '--do-not-enforce-contracts' with both '<input>' and '<output>'");
    }

    /*----------------------------------------------------------------------*/

    // Set mode.

    if limit >= 0 {
        m().mode = RANDOM;
    } else {
        m().mode = if seed_str.is_some() || input_path.is_some() { 0 } else { RANDOM };
        if seed_str.is_some() {
            m().mode |= SEED;
        }
        if input_path.is_some() {
            m().mode |= INPUT;
        }
        if output_path.is_some() {
            m().mode |= OUTPUT;
        }
    }
    Mobical::check_mode_valid();

    /*----------------------------------------------------------------------*/

    if !m().quiet {
        // Print banner.

        Mobical::prefix();
        terminal().magenta(true);
        fputs("Model Based Tester for the CaDiCaL SAT Solver Library\n", c_stderr());
        terminal().normal();
        Mobical::prefix();
        terminal().magenta(true);
        fputs(&format!("{}\n", copyright()), c_stderr());
        terminal().normal();
        Mobical::prefix();
        terminal().magenta(true);
        fputs(&format!("{}\n", authors()), c_stderr());
        terminal().normal();
        Mobical::prefix();
        terminal().magenta(true);
        fputs(&format!("{}\n", affiliations()), c_stderr());
        terminal().normal();
        Mobical::empty_line();
        Solver::build(c_stderr(), Mobical::prefix_string());
        terminal().normal();
        Mobical::empty_line();

        /*------------------------------------------------------------------*/

        // Print resource limits (per executed trace).

        Mobical::prefix();
        let time_limit = m().time_limit;
        if m().donot.fork {
            cerr().s("not using any time limit due to '--do-not-fork'");
        } else if time_limit == DEFAULT_TIME_LIMIT {
            cerr().s("using default time limit of ").d(time_limit).s(" seconds");
        } else if time_limit != 0 {
            cerr().s("using explicitly specified time limit of ").d(time_limit).s(" seconds");
        } else {
            cerr().s("explicitly using no time limit");
        }
        cerr().endl().flush();

        Mobical::prefix();
        let space_limit = m().space_limit;
        if m().donot.fork {
            cerr().s("not using any space limit due to '--do-not-fork'");
        } else if space_limit == DEFAULT_SPACE_LIMIT {
            cerr().s("using default space limit of ").d(space_limit).s(" MB");
        } else if space_limit != 0 {
            cerr().s("using explicitly specified space limit of ").d(space_limit).s(" MB");
        } else {
            cerr().s("explicitly using no space limit");
        }
        cerr().endl().flush();

        if m().add_plain_after_options {
            Mobical::prefix();
            cerr().s("generating only plain instances (--plain)").endl().flush();
        }

        /*------------------------------------------------------------------*/

        // Report mode.

        let mode = m().mode;
        if mode & RANDOM != 0 {
            Mobical::prefix();
            if limit >= 0 {
                cerr().s("randomly generating ").d(limit).s(" traces").endl();
            } else {
                cerr().s("randomly generating traces");
                if terminal().connected() {
                    terminal().magenta(false);
                    cerr().s(" (press ");
                    terminal().blue(false);
                    cerr().s("'<control-c>'");
                    terminal().magenta(false);
                    cerr().s(" to stop)");
                    terminal().normal();
                }
                cerr().endl();
            }
            Mobical::empty_line();
        }
        if mode & SEED != 0 {
            debug_assert!(seed_str.is_some());
            Mobical::prefix();
            cerr().s("generating single trace from seed '").s(seed_str.as_deref().unwrap_or("")).c('\'').endl();
        }
        if mode & INPUT != 0 {
            debug_assert!(input_path.is_some());
            Mobical::prefix();
            cerr().s("reading single trace from input '").s(input_path.as_deref().unwrap_or("")).c('\'').endl();
        }
        if mode & OUTPUT != 0 {
            debug_assert!(output_path.is_some());
            Mobical::prefix();
            cerr()
                .s("writing ")
                .s(if m().donot.shrink.atall { "original" } else { "shrunken" })
                .s(" trace to output '")
                .s(output_path.as_deref().unwrap_or(""))
                .c('\'')
                .endl();
        }
        cerr().flush();
    }

    // END_OF_BANNER_AND_OPTIONS:

    /*----------------------------------------------------------------------*/

    // SAFETY: the global 'mobical' object lives until the end of the process.
    Signal::set(unsafe { MOBICAL } as *mut dyn Handler);

    let mut res = 0;

    if m().mode & (SEED | INPUT) != 0 {
        // trace given through input or seed

        let quiet = m().quiet;
        if !quiet {
            Mobical::prefix();
            cerr().right().setw(58).s("");
            Mobical::header();
            cerr().endl();
            Mobical::hline();
        }

        let mut trace = Trace::new(0, 0);

        if let Some(seed_s) = &seed_str {
            // seed

            let seed = Mobical::parse_seed(seed_s);

            if quiet {
                cerr().s("seed: ");
                cerr().setfill('0').right().setw(20).d(seed);
                cerr().endl().flush();
            } else {
                Mobical::prefix();
                cerr().left().setw(13).s("seed:");
                debug_assert!(Mobical::is_unsigned_str(seed_s));
                terminal().green(false);
                cerr().setfill('0').right().setw(20).d(seed);
                terminal().normal();
                cerr().setfill(' ').setw(24).s("");
            }

            // SAFETY: plain static counter.
            unsafe { GENERATED += 1 };

            trace.generate(0, seed);
        } else {
            // input

            let input = input_path.clone().unwrap_or_default();
            {
                let mut reader = Reader::new(&mut trace, &input);
                reader.parse();
            }

            if !quiet {
                Mobical::prefix();
                cerr().left().setw(13).s("input: ");
                debug_assert!(input_path.is_some());
                cerr().left().setw(44).s(&input);
            }
        }

        if !quiet {
            cerr().c(' ');
            Mobical::summarize(&trace, false);
            cerr().endl().flush();
        }

        if let Some(output) = &output_path {
            if !m().donot.execute {
                res = trace.fork_and_execute();
                if res != 0 {
                    res = trace.fork_and_execute();
                    if res == 0 {
                        m().spurious += 1;
                    }
                }

                if res != 0 {
                    if !m().donot.shrink.atall {
                        if !quiet {
                            terminal().cursor(false);
                        }

                        // SAFETY: plain static counter.
                        unsafe { FAILED += 1 };
                        trace.shrink(res); // shrink
                        if !quiet {
                            if !m().verbose && !terminal().connected() {
                                cerr().endl();
                            } else {
                                terminal().erase_line_if_connected_otherwise_new_line();
                            }
                        }
                    }
                } else {
                    // SAFETY: plain static counter.
                    unsafe { OK += 1 };
                }
            }

            if !quiet {
                Mobical::prefix();
                cerr().left().setw(13).s("output:");
            }

            trace.write_path(output); // output

            if !quiet {
                if res != 0 {
                    terminal().red(true);
                }
                cerr().left().setw(44);
                if output == "-" {
                    cerr().s("<stdout>");
                } else {
                    cerr().s(output);
                }
                terminal().normal();
                cerr().c(' ');
                Mobical::summarize(&trace, false);
                cerr().endl().flush();
            }
        } else {
            trace.execute(); // execute
            // SAFETY: plain static counter.
            unsafe { OK += 1 };
        }
        drop(trace);
    } else {
        // otherwise generate random traces forever

        let mut random = Random::new_random(); // initialized by time and machine id

        if limit < 0 {
            limit = i64::MAX;
        }

        if let Some(seed_s) = &seed_str {
            let seed = Mobical::parse_seed(seed_s);
            if !m().quiet {
                terminal().green(false);
            }
            random.set_seed(seed);
        }

        let quiet = m().quiet;
        if quiet {
            cerr().s("seed: ");
            cerr().setfill('0').right().setw(20).d(random.seed());
            cerr().endl().flush();
        } else {
            Mobical::prefix();
            cerr().s("start seed ");
            terminal().green(false);
            cerr().d(random.seed());
            terminal().normal();
            cerr().endl();
            Mobical::empty_line();

            Mobical::prefix();
            cerr().left().setw(14).s("count");
            terminal().green(false);
            cerr().s("seed");
            terminal().black(false);
            cerr().c('/');
            terminal().red(false);
            cerr().s("buggy");
            terminal().black(false);
            cerr().c('/');
            terminal().yellow(false);
            cerr().s("reducing");
            terminal().black(false);
            cerr().c('/');
            terminal().red(true);
            cerr().s("reduced");
            cerr().left().setw(17).s("");
            Mobical::header();
            cerr().endl();
            Mobical::hline();

            terminal().cursor(false);
        }

        m().traces = 1;
        while m().traces <= limit {
            if Signal::interrupted() {
                break;
            }

            let traces = m().traces;
            let seeds = !m().donot.seeds;

            if !quiet && seeds {
                Mobical::prefix();
                cerr().c(' ').left().setw(15).d(traces).c(' ');
                terminal().green(false);
                cerr().setfill('0').right().setw(20).d(random.seed());
                terminal().normal();
                cerr().setfill(' ').flush();
            }

            let mut trace = Trace::new(0, 0);
            // SAFETY: plain static counter.
            unsafe { GENERATED += 1 };
            trace.generate(traces as u64, random.seed()); // generate

            if !quiet && seeds {
                cerr().setw(21).s("");
                Mobical::summarize(&trace, false);
                terminal().erase_until_end_of_line();
                cerr().flush();
            }

            m().running = true;
            res = trace.fork_and_execute(); // execute
            if res != 0 {
                res = trace.fork_and_execute();
                if res == 0 {
                    m().spurious += 1;
                }
            }
            // SAFETY: plain static counters.
            unsafe {
                if res != 0 {
                    FAILED += 1;
                } else {
                    OK += 1;
                }
            }

            if !quiet {
                if seeds && limit != traces {
                    terminal().erase_line_if_connected_otherwise_new_line();
                } else if seeds && limit == traces {
                    cerr().endl().flush();
                }
            }

            if res != 0 {
                // failed

                if !quiet {
                    Mobical::prefix();
                    cerr().c(' ').left().setw(11).d(traces).c(' ');
                    terminal().red(false);
                }
                trace.write_prefixed_seed("bug"); // output
                if quiet {
                    cerr().endl().flush();
                } else {
                    terminal().normal();
                    cerr().setw(15).s("");
                    Mobical::summarize(&trace, false);
                    if terminal().connected() {
                        cerr().endl().flush();
                    }
                }

                m().running = false;

                if !m().donot.shrink.atall {
                    trace.shrink(res); // shrink
                    if quiet {
                        //  TODO remove: cerr << endl << flush;
                    } else if !terminal().connected() && !m().verbose {
                        cerr().endl();
                    } else {
                        terminal().erase_line_if_connected_otherwise_new_line();
                    }
                }

                if !quiet {
                    Mobical::prefix();
                    cerr().c(' ').left().setw(11).d(traces).c(' ');
                    terminal().red(true);
                }

                trace.write_prefixed_seed("red"); // output

                if quiet {
                    cerr().endl().flush();
                } else {
                    terminal().normal();
                    cerr().setw(15).s("");
                    Mobical::summarize(&trace, true);
                    cerr().endl().flush();
                }
            }

            drop(trace);
            random.next();
            m().traces += 1;
        }
    }

    let sig = Signal::received();
    let reraise = Signal::interrupted();
    Signal::reset();

    if reraise && ((terminal().connected() && (m().mode & RANDOM) != 0) || m().shrinking || m().running) {
        cerr().endl();
    }
    terminal().reset();
    Mobical::print_statistics();

    if reraise {
        // SAFETY: 'raise'.
        unsafe {
            libc::raise(sig);
        }
    }

    // SAFETY: plain static counter.
    (unsafe { FAILED } > 0) as i32
}

/*------------------------------------------------------------------------*/

/// The `main` function of the `mobical` binary.
pub fn main() -> i32 {
    let argv: Vec<String> = std::env::args_os().map(|a| a.to_string_lossy().into_owned()).collect();
    main_with_args(&argv)
}

/// `main (argc, argv)` with explicit arguments (`argv[0]` included).
pub fn main_with_args(argv: &[String]) -> i32 {
    // SAFETY: constructing the global 'mobical' object ('Mobical::Mobical')
    // once; it is never freed (as a C++ global object it is only destroyed
    // at exit, where the destructor only unmaps memory).
    unsafe {
        if MOBICAL.is_null() {
            MOBICAL = Box::into_raw(Box::new(Mobical::new()));
        }
    }
    // Failing C++ assertions abort (raise 'SIGABRT'), which the (forked)
    // trace execution relies on to detect failures ('Trace::fork_and_execute'
    // treats a signal as failure, while an exit code would be taken as is).
    // Make Rust panics (failed 'debug_assert!' etc.) behave the same even if
    // compiled with 'panic = "unwind"'.
    let default_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |info| {
        default_hook(info);
        // SAFETY: 'abort' as a failing C++ 'assert'.
        unsafe { libc::abort() };
    }));
    mobical_main(argv)
}

# Porting CaDiCaL to Rust: conventions

The reference sources live in `./cadical` (CaDiCaL 3.0.1, commit c6073042).
The goal is a **faithful, function-by-function port** so that, for the same
input and options, `cadical-rs` behaves *identically* to the C++ solver:
same decisions, same conflicts, same statistics, and (with the `logging`
feature) the same `-l` log lines.  Exact behavioural equivalence is our
main debugging oracle, so do not "improve" algorithms, reorder loops,
change heuristics, or replace data structures with ones that iterate in a
different order.

## Crate layout

* Package `cadical-rs`, library crate name `cadical`, binaries `cadical`
  (port of `cadical.cpp`, the `App`) and `mobical` (port of `mobical.cpp`).
* One Rust module per C++ translation unit, same base name:
  `src/analyze.rs` ports `analyze.cpp`; header and implementation with the
  same base name share one module (`clause.hpp` + `clause.cpp` ->
  `src/clause.rs`).  `kitten.c` -> `src/kitten.rs`.  `cadical.cpp` (the
  command line app) -> `src/app.rs` (used by `src/bin/cadical.rs`);
  `cadical.hpp` (public API) -> `src/solver.rs` together with `solver.cpp`.
* `Internal` methods are implemented in `impl Internal { ... }` blocks in
  the module of the `.cpp` file that defines them in C++.  Same for
  `External`.  Keep the C++ function order inside each file.
* File-local helpers (static functions, comparator structs, lambdas) stay
  private to the module that ports that `.cpp` file.

## Types

| C++                    | Rust                                  |
|------------------------|---------------------------------------|
| `int` / `unsigned`     | `i32` / `u32`                         |
| `int64_t` / `uint64_t` | `i64` / `u64`                         |
| `size_t`               | `usize`                               |
| `double`               | `f64`                                 |
| `signed char`          | `i8`                                  |
| `std::vector<T>`       | `Vec<T>`                              |
| `Clause *`             | `CRef` (copyable raw handle, see below) |
| `assert (...)`         | `debug_assert!(...)`                  |
| `#ifndef NDEBUG` code  | `#[cfg(debug_assertions)]`            |
| `#ifdef LOGGING` code  | `#[cfg(feature = "logging")]`         |

* Unsigned arithmetic that relies on wrap-around (hashing, random numbers,
  `unsigned` counters that intentionally overflow) must use
  `wrapping_*`.  Signed overflow is UB in C++ and never intended, so plain
  operators are fine there (debug builds will then catch bugs).
* `(unsigned) x`, `(int) x` etc. become `as` casts with identical
  semantics.  Beware `abs(INT_MIN)`, `-x` on unsigned, and shifts.
* Where C++ uses `sizeof (T)` in a computation that influences behaviour
  (e.g. `cache_lines`, arena and ticks accounting) use the value C++ would
  compute on a 64-bit platform.  `size_of::<Clause>() == 24` and
  `size_of::<Watch>() == 16` are asserted in the crate so those match.

## Clauses

`Clause` is `#[repr(C)]` with the exact C++ header layout (24 bytes: `id`
(which doubles as the `copy` pointer when `moved`), a `u32` holding all bit
flags incl. the 5-bit `used`, `glue`, `size`, `pos`) followed by the
literals.  Clauses are allocated either with the global allocator or inside
the `Arena`, exactly as C++ does.  They are referred to by `CRef`, a
`Copy` wrapper around `*mut Clause` (null allowed: `CRef::NULL`,
`c.is_null()`), which compares by address.  `CRef` offers accessor methods
(`c.size()`, `c.set_size(n)`, `c.garbage()`, `c.set_garbage(true)`,
`c.lit(i)`, `c.set_lit(i, l)`, `c.lits()` (shared slice), `c.lits_mut()`,
`c.id()`, `c.copy()`, ...).  **Never keep a slice obtained from `lits()`
alive across a write to the same clause**; use index based access in
loops that modify the clause.

## References across calls, aliasing, `unsafe`

C++ code often keeps `Watches &ws = watches (lit)` or `Var &v = var (idx)`
alive while calling other methods on `this`.  Preferred Rust patterns,
in this order:

1. Re-index (`self.wtab[i]`) after each call, or copy scalar fields out.
2. Split borrows of disjoint fields (`let vals = &self.vals; ...`).
3. Where the C++ semantics really requires holding a reference across a
   call (e.g. the watch list in `propagate` while `search_assign` pushes
   watches of *other* literals), take a raw pointer
   (`let ws: *mut Watches = &mut self.wtab[idx];`) and dereference it in a
   small `unsafe` block, with a one line `// SAFETY:` comment explaining why
   the vector is neither reallocated nor aliased mutably.

Never use `std::mem::take` on a data structure that the callee might read
or modify (that silently changes semantics).

`Internal` and `External` point to each other with raw pointers
(`self.external()` / `self.internal()` return `&mut`), mirroring C++.
Both are boxed inside `Solver` so the addresses are stable.

## Sorting and ordering

Behavioural equivalence requires identical orderings:

* `std::sort` -> `crate::sort::std_sort(slice, less)`, a port of LLVM
  libc++ 21's `std::sort` (the version the reference is built with), so
  that ties are resolved identically.  **Do not use `slice::sort_by` or
  `sort_unstable_by` for a C++ `std::sort`.**
* `std::stable_sort` -> `slice::sort_by` (stable, identical result).
* `rsort` / `MSORT` -> `crate::radix::rsort` / `msort` (ports of
  `radix.hpp`).
* `std::nth_element`, `std::partial_sort`, heaps -> ports in
  `crate::sort` mirroring libc++ where the result order can matter.
* No `HashMap`/`HashSet` where iteration order matters; port the C++ hash
  tables as written (C++ `unordered_set` iteration order is never relied
  on in CaDiCaL, but check).
* `Random` is ported bit-exactly.

## Messages, logging, errors

* `MSG`, `VERBOSE`, `PHASE`, `SECTION`, `WARNING`, `LOG`, `START`, `STOP`
  etc. are macros in `src/message.rs`, `src/logging.rs`, `src/profile.rs`
  taking Rust `format!` style arguments.  Keep the exact output text of
  the C++ `printf` format (translate `%d` -> `{}`, `%5.2f` -> `{:5.2}`,
  `%s` -> `{}`, `%g` -> `crate::format::fmt_g(x)`, etc.).
* `LOG (...)` lines must print exactly what C++ prints with `-l`, since we
  diff logs against a C++ build configured with `-l`.
* `fatal (...)`, `error (...)` and API contract violations
  (`REQUIRE`, `TRACE`) print the same message as C++ and then abort
  (`crate::message::fatal*`).  The C++ API tracing (`CADICAL_API_TRACE`)
  is ported too (mobical traces rely on it).

## Callbacks in the public API

`Terminator`, `Learner`, `FixedAssignmentListener`, `ExternalPropagator`,
`ClauseIterator`, `WitnessIterator` and proof `Tracer` are Rust traits
with the same method names.  The `Solver` takes ownership as
`Box<dyn Trait>`; `disconnect_*` returns the box.  Users who need to share
state wrap it (`Rc<RefCell<..>>`, `Arc<..>`) inside their implementation.

## Stubs

Initially every `Internal` / `External` / `Solver` / tracer / checker
method exists with its final signature and body `todo!("port <file>:<fn>")`.
Filling in a module means replacing those bodies with the port; do **not**
change the signature of a method owned by another module without
coordinating (grep for callers).  When a C++ overload set maps to several
Rust names, the chosen names are listed in `src/<module>.rs` doc comments.

## Performance

Build profiles: `dev` has debug assertions (== C++ `-c`), `release` is
`opt-level=3`, `lto = "fat"`, `codegen-units = 1`, `panic = "abort"`.
Hot loops (propagate, analyze) may use `get_unchecked` *after* the port
is known correct, with `debug_assert!` bounds checks.

## Internal layout

`Internal` (`src/internal.rs`) has every field of the C++ class with the
same name and a Rust type following the table above.  Notable choices:

* **Ownership.**  `Solver` owns the `Internal` and the `External` through
  raw pointers obtained from `Box::into_raw` (`Solver::internal`,
  `Solver::external`), freed in `Drop for Solver`.  Both live at stable
  heap addresses, so the back pointers `Internal::external: *mut External`
  and `External::internal: *mut Internal` stay valid.  Accessors
  `internal.external() -> &mut External`, `external.internal() -> &mut
  Internal`, `solver.internal()`, `solver.external()` dereference them
  (unsafe inside, like C++).  `Internal::new () -> Box<Internal>` and
  `External::new (internal) -> Box<External>` (which also sets
  `internal.external`) are implemented; the `Solver` constructor itself is
  in `solver.rs` (stub).
* **No `internal` self pointer.**  The C++ `Internal *internal` member
  ("proxy to 'this' in macros") does not exist; macros take the internal
  explicitly (see below).  Sub-objects that need their owner keep a
  `*mut Internal` (`Options`, `Profiles`, `Arena`, `score_smaller`,
  `Proof`, tracers, `Closure`, `Sweeper`, `Walker`, ...).  They are
  patched in `Internal::new` after boxing.
* **`vals`.**  `vals: *mut i8` points into `vals_storage: Vec<i8>` at
  offset `vsize` (of that allocation), so `*vals.offset (lit)` is valid for
  `lit` in `[-max_var, max_var]` exactly as in C++.  Use `val (lit)` and
  `set_val (lit, v)`; `enlarge_vals` is implemented.  Hot loops may copy
  the raw pointer (`let vals = self.vals;`).
* **Accessors.**  C++ helpers returning non-const references come in two
  versions: `var (lit) -> &Var` / `var_mut (lit) -> &mut Var`, likewise
  `link`, `flags`, `bins`, `occs`, `watches`; for scalars `bumped`,
  `propfixed`, `score`, `noccs` return the value and `*_mut` a reference.
  `unit_clauses (uidx) -> &mut i64` as in C++.
* **Iteration.**  `self.vars ()` (`1..=max_var`) and `self.lits ()`
  (`-1, 1, -2, 2, ...`) return iterators over a snapshot of `max_var`
  (like the C++ range-for) that do not borrow `self`.
* **Clauses.**  `CRef` (`src/clause.rs`) wraps `*mut Clause`.  Clauses
  outside the arena are allocated with `libc::malloc` (`CRef::alloc`,
  `CRef::dealloc` = `free`, so shrunken clauses can be freed without
  knowing their original size); the arena (`src/arena.rs`) also uses
  `malloc`ed spaces, so `pointer_rank` sorting of arena clauses follows the
  copy order as in C++.  Flags are bits in one `u32` word
  (`c.garbage ()` / `c.set_garbage (b)`, `c.used ()` / `c.set_used (u)`
  truncates to 5 bits).  `Internal::decision_reason ()` returns the address
  of a static zeroed `Clause` (C++ static member `decision_reason`);
  `internal.external_reason` is initialized with the static
  `external_reason_clause` (`clause::external_reason_clause ()`).
  `dummy_binary` is a `calloc`ed binary clause.
* **Termination.**  `termination_forced: Arc<AtomicBool>` (relaxed loads).
  `Solver::termination_handle ()` returns a `TerminationHandle` that can be
  sent to another thread (or used from a signal handler) to force
  termination (Rust addition; C++ users call `terminate ()` from another
  thread).  `terminated_asynchronously (factor)` and `search_limits_hit`
  are ported inline.
* **Proof and tracers.**  `proof: Option<Box<Proof>>`.  Connected tracers
  are owned by `Internal` in `tracers: Vec<Box<dyn Tracer>>`,
  `file_tracers: Vec<Box<dyn FileTracer>>` and
  `stat_tracers: Vec<Box<dyn StatTracer>>` (C++ also deletes still
  connected tracers in `~Internal`).  `Proof::tracers` /
  `Proof::file_tracers` hold raw `*mut dyn Tracer` / `*mut dyn FileTracer`
  pointers into these boxes (stable addresses).  The C++ class hierarchy
  is mapped to traits `Tracer` <- `InternalTracer` <- `StatTracer` /
  `FileTracer` (`src/tracer.rs`, all event methods default to no-ops;
  upcasting `Box<dyn FileTracer>` to `*mut dyn Tracer` is plain trait
  upcasting).  `connect_proof_tracer*` returns a `TracerRef` (the address
  of the boxed object) which `disconnect_proof_tracer*` takes and which
  returns the box again (`None` = C++ `false`).
* **Call-backs** (`Terminator`, `Learner`, `FixedAssignmentListener`,
  `ExternalPropagator`) are `Option<Box<dyn ...>>` fields of `External`;
  `Solver::disconnect_*` returns the box.  The data members
  `ExternalPropagator::is_lazy` and `are_reasons_forgettable` are trait
  methods with default `false`.
* **Kitten.**  `citten: Option<Box<Kitten>>`.  The kitten API
  (`src/kitten.rs`) keeps the C function names; `void *state` +
  function-pointer call backs become `&mut dyn FnMut` closures, except
  `kitten_set_terminator` which keeps a `*mut c_void` state and `fn`
  pointer.
* **Options** (`src/options.rs`): plain `i32` fields (`opts.restart`), the
  table (`Opt`, renamed from C++ `Option`) and all of `options.cpp` are
  generated by one macro from the same list as `options.hpp`.  `log` and
  `logsort` only exist with the `logging` feature (like `LOGOPT`).
  `Options::reportdefault ()` / `set_reportdefault (v)` replace the static
  data member.
* **Profiles** (`src/profile.rs`): an array indexed by `ProfileId`
  (`self.profiles[ProfileId::search]`); `start_profiling` /
  `stop_profiling` take a `ProfileId` instead of `Profile &`.
  `PROFILE_MODE` (and thus `stable.cpp` / `unstable.cpp`) is not ported.
* **Stats** (`src/stats.rs`): nested anonymous C++ structs are named
  `Stats<Member>` (`StatsTicks`, `StatsClauses` for `current`/`added`,
  `StatsVars` for `all`/`now`, ...).  `Stats::print (internal: &mut
  Internal)` is an associated function.
* **Delays / limits.**  `limit.hpp`'s `Delay` is `crate::limit::Delay`
  (used by `Internal`); the unused `delay.hpp` `Delay` is
  `crate::delay::Delay`.
* **Terminals.**  `tout ()` / `terr ()` return `&'static Terminal`
  (atomics inside, lazily initialized with `isatty`).  Colors take the
  C++ default argument explicitly (`tout ().magenta (false)`).
* **Output.**  All output goes through the C `FILE` streams
  (`message::c_stdout ()`, `c_stderr ()`; `cprintf!`, `cfprintf!`,
  `fputs`, `fputc`, `fflush`) so buffering and interleaving match C++
  exactly.  Never use `print!`/`println!`.  For C `printf` float
  conversions use `format::fmt_g`, `format::fmt_f`,
  `format::cfmt_f64 ("%7.2f", x)` (implemented with `snprintf`).

### Macros

The first argument of `log!`, `msg!`, `verbose!`, `phase!`, `warning!`,
`loglit!` is anything implementing `internal::InternalRef` (`self` in
`Internal` or `External` methods, or a `*mut Internal` back pointer).
`section!`, `start!`/`stop!`, `start_simplifier!`/`stop_simplifier!`,
`start_inner_walk!` etc., `update_average!`, `init_ema!` and
`set_effort_limit!` need a `&mut Internal` expression (usually `self`).

| C++                                  | Rust                                          |
|--------------------------------------|-----------------------------------------------|
| `LOG ("fmt", ...)`                   | `log!(self, "fmt", ...)`                      |
| `LOG (c, "fmt", ...)`                | `log!(self, c, "fmt", ...)` (`CRef`, `&Vec<i32>`, `&[i32]`, `&Vec<i64>`, `&[i64]`, `*const Gate`) |
| `LOGLIT (lit)`                       | `loglit!(self, lit)` (logging feature only)   |
| `MSG (...)`, `LINE ()`               | `msg!(self, ...)`, `msg!(self)`               |
| `VERBOSE (l, ...)`                   | `verbose!(self, l, ...)`                      |
| `PHASE (p, ...)`, `PHASE (p, n, ...)`| `phase!(self, p, "fmt", ...)`, `phase!(self, p, n, "fmt", ...)` |
| `SECTION (t)`                        | `section!(self, t)`                           |
| `WARNING (...)`, `FATAL (...)`       | `warning!(self, ...)`, `fatal!(...)`          |
| `START (p)` / `STOP (p)`             | `start!(self, p)` / `stop!(self, p)`          |
| `START_SIMPLIFIER (S, M)`            | `start_simplifier!(self, S, M)`               |
| `UPDATE_AVERAGE (A, Y)`              | `update_average!(self, averages.current.glue.fast, y)` |
| `INIT_EMA (E, W)`                    | `init_ema!(self, averages.current.jump, self.opts.emajump)` |
| `SET_EFFORT_LIMIT (L, N, T)`         | `set_effort_limit!(self, l, n, t)` (`t` must be a `bool`) |
| `REQUIRE (c, ...)`                   | `require!(func, file, c, ...)`                |
| `COVER (c)`                          | `cover!(c)`                                   |
| `printf`, `fprintf`                  | `cprintf!`, `cfprintf!`                       |

### Iterators and pointers in signatures

* `std::vector<int>::reverse_iterator` / `const_iterator` parameters
  (shrink, restore, logging) are `usize` indices (for reverse iterators:
  the position counted from `rbegin`).  `lit_implications::const_iterator`
  ranges in congruence are slices.
* `GatesTable::iterator` is `Option<*mut Gate>` (`None` == `end ()`).
* `DFS *` arrays are `&mut [DFS]`.  `Quotient *`, `Gate *`, checker
  clauses are raw pointers (linked structures, allocated with `Box` or
  `malloc` by their modules).
* `const char *` results that may be null are `Option<String>` (parse
  errors) or `&'static str` (constant strings).
* C++ default arguments become explicit parameters; the default is
  documented in the doc comment (`/// 'x' defaults to 'false' in C++`).

## Overload renames

C++ overload sets (and a few other names that cannot be used in Rust) map
to the following Rust names.  Where not listed the C++ name is kept.

**Internal**

| C++                                            | Rust |
|------------------------------------------------|------|
| `bool active (int lit)` / `int active () const`| `active (lit)` / `active_count ()` |
| `Flags &flags (int)` (+ const)                 | `flags (lit) -> &Flags`, `flags_mut (lit)` (same pattern for `var`, `link`, `bins`, `occs`, `watches`, `bumped`, `propfixed`, `score`, `noccs`) |
| `mark (int)` / `mark (Clause *)`               | `mark (lit)` / `mark_clause_literals (c)` |
| `mark2 (int)` / `mark2 (Clause *)`             | `mark2 (lit)` / `mark2_clause_literals (c)` |
| `unmark (int)` / `unmark (vector<int> &)` / `unmark (Clause *)` | `unmark (lit)` / `unmark_lits (&[i32])` / `unmark_clause_literals (c)` |
| `mark_added (int, int, bool)` / `mark_added (Clause *)` | `mark_added_lit (lit, size, red)` / `mark_added (c)` |
| `mark_removed (int)` / `mark_removed (Clause *, int = 0)` | `mark_removed_lit (lit)` / `mark_removed (c, except)` |
| `cache_lines (size_t)` / `cache_lines (size_t, size_t)` | `cache_lines (bytes)` / `cache_lines_n (n, bytes)` |
| `walk_pick_lit (Walker &, ClauseOrBinary / Clause * / TaggedBinary)` | `walk_pick_lit` / `walk_pick_lit_clause` / `walk_pick_lit_binary` |
| `phase (int lit)`                              | `phase (lit)` |
| `phase (const char *, fmt, ...)` / `phase (const char *, int64_t, fmt, ...)` | `phase_message (phase, args)` / `phase_message_count (phase, count, args)` (use `phase!`) |
| `message (fmt, ...)` / `message ()` (+ `vmessage`) | `message (args)` / `message_empty ()` (use `msg!`) |
| `verbose (int, fmt, ...)` / `verbose (int)` (+ `vverbose`) | `verbose (level, args)` / `verbose_empty (level)` |
| `error (fmt, ...)` / `verror`                  | `error (args) -> !` |
| `warning (fmt, ...)`                           | `warning (args)` |
| `copy_phases`, `save_assigned_phases`, `clear_phases (vector<signed char> &)` | take a `PhaseKind` selector (`Best`, `Forced`, `Prev`, `Saved`, `Target`) |
| `start_profiling (Profile &, double)` / `stop_profiling` | take a `ProfileId` |
| `connect_proof_tracer (Tracer * / InternalTracer * / StatTracer * / FileTracer *, ...)` | `connect_proof_tracer` / `connect_proof_tracer_internal` / `connect_proof_tracer_stat` / `connect_proof_tracer_file` (return `TracerRef`) |
| `disconnect_proof_tracer (Tracer * / StatTracer * / FileTracer *)` | `disconnect_proof_tracer` / `_stat` / `_file` (take `TracerRef`, return `Option<Box<...>>`) |
| `dump (Clause *)` / `dump ()`                  | `dump_clause (c)` / `dump ()` |
| `parse_dimacs (FILE *)` / `(const char *)`, `parse_solution` | declared but never defined in C++: not ported |
| `static Clause *decision_reason`               | `Internal::decision_reason ()` |
| `report (char type, int verbose_level = 0)`    | `report (type_: u8, verbose_level)` |

**External**: `push_clause_on_extension_stack (Clause *)` /
`(Clause *, int witness)` → `push_clause_on_extension_stack (c)` /
`push_clause_on_extension_stack_with_witness (c, witness)`;
`restore_clause (begin, end, id)` takes indices into `extension`;
`check_assignment` takes `fn (&External, i32) -> i32`.

**Solver**

| C++ | Rust |
|-----|------|
| `clause (int)` ... `clause (int, int, int, int, int)` | `clause1` ... `clause5` |
| `clause (const std::vector<int> &)` / `clause (const int *, size_t)` | `clause (&[i32])` / `clause_array (&[i32])` |
| `trace_proof (FILE *, const char *)` / `trace_proof (const char *)` | `trace_proof_file` / `trace_proof` |
| `read_dimacs (FILE *, name, vars, strict = 1)` | `read_dimacs_file` |
| `read_dimacs (path, vars, strict = 1)` | `read_dimacs` |
| `read_dimacs (FILE *, name, vars, strict, incremental, cubes)` | `read_dimacs_file_inccnf` |
| `read_dimacs (path, vars, strict, incremental, cubes)` | `read_dimacs_inccnf` |
| private `read_dimacs (File *, ...)` | `read_dimacs_internal` |
| `trace_api_call (s)`, `(s, i)`, `(s, i, j)`, `(s, t)`, `(s, t, i)` | `trace_api_call`, `trace_api_call_i`, `_ii`, `_s`, `_si` |
| `message (fmt, ...)` / `message ()` | `message (args)` / `message_empty ()` |
| `connect_proof_tracer` / `disconnect_proof_tracer` overloads | as for `Internal` |
| `disconnect_terminator ()` etc. | return the connected box |
| `CubesWithStatus` (nested struct) | `internal::CubesWithStatus` (re-exported) |

**Proof**: private notifiers without arguments `add_original_clause
(restore)`, `add_derived_clause ()`, `add_assumption_clause ()`,
`delete_clause ()`, `demote_clause ()`, `weaken_minus ()`, `strengthen
()`, `finalize_clause ()`, `add_assumption ()`, `add_constraint ()` →
`emit_*`; `add_literals (Clause *)` → `add_literals_clause`;
`add_derived_clause (int64_t, bool, vector, chain)` →
`add_derived_clause_lits` (the `Clause *` version keeps the name);
likewise `delete_clause_lits`, `weaken_minus_lits`, `weaken_plus_lits`,
`finalize_clause_lits`, `add_derived_rat_clause_lits`;
`add_assumption_clause (int64_t, int, chain)` →
`add_assumption_clause_unit`; `disconnect (Tracer *)` takes a `TracerRef`.

**Tracers / checkers**: the private `delete_clause (XClause *)` of
`Checker`, `LratChecker`, `IdrupTracer`, `LidrupTracer`, `VeripbTracer` →
`deallocate_clause`; `FratTracer::frat_add_derived_clause (id, clause,
chain)` → `frat_add_derived_clause_with_chain`;
`VeripbTracer::veripb_add_derived_clause` (id, red, witness, clause) /
(id, red, clause, chain) / (id, red, clause) →
`veripb_add_derived_clause_witness` / `_chain` / `veripb_add_derived_clause`.
`Checker::print_stats` / `LratChecker::print_stats` (in `stats.cpp`) are
implemented in the `StatTracer` impls in `checker.rs` / `lratchecker.rs`.

**Closure (congruence)**: `representative (lit) const` / `int
&representative (lit)` → `representative` / `representative_mut` (same
for `representative_id`, `eager_representative`,
`eager_representative_id`); `merge_literals (Gate *, Gate *, ...)` →
`merge_literals_gates`; `push_id_on_chain (chain, Clause *)` /
`(chain, vector<LitClausePair>)` / `(chain, my_dummy_optional)` /
`(chain, Rewrite, int)` → `push_id_on_chain` / `_pairs` / `_optional` /
`_rewrite`; `remove_gate (GatesTable::iterator)` → `remove_gate_at`;
`produce_rewritten_clause_lrat_and_clean (my_dummy_optional &, ...)` /
`(..., size_t &, size_t &, ...)` → `..._optional` / `..._positions`;
`produce_rewritten_clause_lrat (vector<LitClausePair> &, ...)` →
`produce_rewritten_clause_lrat_pairs`; `gate_sort_lrat_reasons
(LitClausePair &, ...)` → `gate_sort_lrat_reason`; `Hash::operator()` →
`Hash::hash`; `Gate::operator==` → `Gate::equals`;
`my_dummy_optional::operator()` / `operator=` → `is_set` / `set`;
`GateEqualTo` → `gate_equal_to`; the declared but undefined
`extract_and_gates (Closure &)`, `push_lrat_id`, `simplify_xor_clause`,
`extract_congruence` are not ported.

**Other**

| C++ | Rust |
|-----|------|
| `struct Option` | `options::Opt` |
| `Options::set (Option *, int)` | `Options::set_option (idx, val)` |
| `Options::begin ()` / `end ()` | `Options::table ()` / `Options::iter ()` |
| `Config::begin ()` / `end ()` | `Config::names ()` |
| `File::put (char / unsigned char / const char * / int / int64_t / uint64_t)` | `put_char (u8)` / `put_str` / `put_int` / `put_i64` / `put_u64` |
| `File::read (Internal *, FILE *, name)` / `File::write (..., FILE *, name)` | `read_fp` / `write_fp` (path versions keep the name) |
| `File::match` | `File::matches` |
| `Logger::log` overloads | `log`, `log_clause`, `log_gate`, `log_lits` (also the iterator range version), `log_ids`, `log_int_array` (dispatch through `log!`) |
| `Reluctant::operator bool ()` | `Reluctant::triggered ()` |
| `EMA::operator double ()` | `EMA::value ()` (or the `value` field) |
| `Random (seed)`, `Random ()`, `operator=`, `operator+=` | `Random::new (seed)`, `Random::new_random ()`, `set_seed`, `+=` (`AddAssign<u64>`) |
| `Clause::bytes (int size)` (static) | `Clause::bytes_for (size)` (`c.bytes ()` for a `CRef`) |
| `Watch (b, c)` / `Watch (bool, b, c)` | `Watch::new (b, c)` / `Watch::new_binary (b, c)` |
| `Level (d, t)` | `Level::new (d, t)` |
| `ClauseOrBinary` (tagged union) | Rust `enum ClauseOrBinary { Clause (CRef), Binary (TaggedBinary) }` |
| `TaggedBinary (c, lit, other)` / `TaggedBinary (c)` | `TaggedBinary::new` / `TaggedBinary::from_clause` |
| `lit_implication (f, s)`, `lit_equivalence (f, s)` | `new2 (f, s)` |
| `ClauseSize (Clause *)` | `ClauseSize::from_clause` |
| `Counter (c, d)` (walk_full_occs) | `Counter::new_unbroken` |
| `WalkerFO::connect_clause (int, Clause *, unsigned)` / `(Clause *, unsigned)` | `connect_clause_lit` / `connect_clause`; const `occs` → `occs_ref` |
| `Vivifier::schedule_tier1` ... (reference members) | methods `schedule_tier1 ()` ... |
| `Instantiator::operator bool ()` | `has_candidates ()` |
| `elim_more`, `block_more_occs_size`, `factor_occs_size`, `score_smaller` `operator()` | `HeapLess::less` impls |
| `App::set (const char *)` / `set (const char *, int)` | `set_long_option` / `set` |
| `Handler`, `Signal::set (Handler *)` | trait `Handler`, `Signal::set (*mut dyn Handler)` |

## Stub conventions

* Every function still to be ported has the body
  `todo!("port <file>.cpp:<Class>::<function>")`; `grep -n 'todo!(' src/`
  lists the remaining work.  Stubs for destructors are `Drop` impls whose
  `todo!` is guarded by `if !std::thread::panicking ()`.
* Stub modules start with `use crate::prelude::*;` (`src/prelude.rs`
  re-exports the commonly used types; not part of the C++ code base).
* File-local C++ helpers (static functions, comparators, lambdas, local
  structs such as `Report` in `report.cpp` or `Wrapper` in
  `ccadical.cpp`) are not stubbed; they are written together with the
  functions using them.  Types declared in `.cpp` files but used in
  `Internal` signatures (`Coveror`, `Walker`, `WalkerFO`, `Tagged`,
  `Counter`) are defined in their modules.

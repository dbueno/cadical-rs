# cadical-rs

A faithful Rust port of the [CaDiCaL](https://github.com/arminbiere/cadical)
SAT solver, version **3.0.1** (upstream commit `c6073042`).

The port is function-by-function: given the same input and options,
`cadical-rs` makes the same decisions and conflicts, prints the same
statistics and produces the same proofs as the C++ solver. It includes
the whole solver (CDCL search, inprocessing, local search, congruence
closure, kitten, proof tracers and checkers), the `cadical` command line
tool, the `mobical` model based tester, and the C / IPASIR API. The only
dependency is `libc`.

The library crate is called `cadical` (the package is `cadical-rs`).

## Building

With cargo:

```sh
cargo build --release          # target/release/{cadical,mobical}, libcadical.{rlib,a}
cargo build --release --features logging   # like './configure -l' (enables '-l')
```

With nix (flake):

```sh
nix build                      # the Rust solver
nix build .#cadical-ref        # the C++ reference solver, pinned to the same commit
nix develop                    # shell with cargo, the reference solver and the proof checkers
```

## Command line

`target/release/cadical` accepts the same options and prints the same
output as the C++ `cadical` binary:

```sh
cadical formula.cnf                    # solve, print 's SATISFIABLE' + model
cadical formula.cnf proof.drat         # write a DRAT proof (binary by default)
cadical --lrat formula.cnf proof.lrat  # LRAT proof
cadical -t 60 --sat formula.cnf.xz     # 60s limit, 'sat' configuration, compressed input
cadical --help                         # all options
```

Exit codes are the SAT competition ones: 10 (satisfiable), 20
(unsatisfiable), 0 (unknown).

## Library

Add the dependency (for example as a path or git dependency, the package
name is `cadical-rs`):

```toml
[dependencies]
cadical = { package = "cadical-rs", path = "../cadical-rs" }
```

```rust
use cadical::Solver;

let mut solver = Solver::new();
solver.clause(&[1, 2]);
solver.clause(&[-1, 2]);
assert!(solver.solve_result().is_sat());
assert_eq!(solver.val(2), 2);             // IPASIR: returns lit if true, -lit if false

solver.assume(-2);                        // valid for the next solve only
assert!(solver.solve_result().is_unsat());
assert!(solver.failed(-2));               // part of the unsatisfiable core
```

The API mirrors `cadical.hpp`: the same method names, the integer status
codes (`10`, `20`, `0`) and the same API contracts (violations abort with
the C++ error message). On top of that there are small Rust conveniences:
`SolveResult`, `solve_result`, `add_clause`, `assume_all`, `value`,
`model`, closures as terminators, listeners, clause/witness iterators and
learners (`connect_learner_fn`), `Rc<RefCell<T>>` / `Arc<Mutex<T>>`
implementations of all call-back traits (to keep access to a connected
call-back), `termination_handle` (stop `solve` from another thread or a
signal handler) and `trace_api_calls(path)`.

`Solver` is not `Send`: call-backs may hold `Rc`s and raw pointers (the C
API and `mobical` need that). Create a solver on the thread that uses it,
and use `termination_handle()` to interrupt it from elsewhere.

The crate documentation (`cargo doc --open`) has a quick-start covering
incremental solving, assumptions, termination, learners, proofs and
external propagators (IPASIR-UP). Runnable examples:

```sh
cargo run --release --example nqueens -- 8        # enumerate all solutions
cargo run --release --example incremental         # assumptions and failed literals
cargo run --release --example learner -- 7 p.drat # call-backs, termination, proof output
```

The C API (`ccadical_*`) and IPASIR (`ipasir_*`) functions are exported by
the static library `target/release/libcadical.a`.

All other public modules are the solver internals, exposed for the tests
and tools in this repository. They are not a stable API.

## Testing and verification

Exact behavioural equivalence with the C++ solver is the main oracle.

* **Upstream test suites**: the Rust `cadical` and `mobical` binaries run
  the upstream drivers `cadical/test/{cnf,trace,usage,mbt}/run.sh`
  (point `CADICALBUILD` to a build directory holding the Rust binaries,
  the upstream `makefile` and the checkers `dimocheck`, `drat-trim`,
  `lrat-trim` from `nix build .#cadical-checkers`). All solutions and
  proofs are checked.
* **API tests**: every upstream API and contrib test
  (`cadical/test/api/*.cpp`, `cadical/test/contrib/*.cpp`) is ported to
  `tests/`, run with `cargo test`. `scripts/compare-api-tests.sh` diffs
  their output against the C++ tests
  (`scripts/run-cpp-api-tests.sh`), `scripts/run-c-api-tests.sh` runs the
  C API tests against the Rust static library.
* **Head-to-head**: all instances in `cadical/test/cnf` are solved by the
  C++ reference and the Rust port; exit codes and the conflict, decision
  and propagation counts must be identical.
* **Fuzzing**: long runs of the ported `mobical` (random API call
  sequences with model, core and proof checking).
* **Benchmarks**: `scripts/bench.py` runs a solver over an instance list
  with a time limit, checks models (`dimocheck`) and proofs (`drat-trim`,
  `lrat-trim`), and compares statuses and search statistics with a
  reference run of the C++ solver.

### Results (macOS / Apple Silicon, reference built by `nix build .#cadical-ref`)

| Check | Result |
|---|---|
| upstream `cnf` / `usage` / `trace` suites | 282 / 35 / 79 ok, 0 failed (same counts as C++) |
| upstream `mbt` + extra mobical fuzzing | 1,000 + 140,000 random traces, 0 failed |
| ported API tests | 17/17 pass; stdout and written proof/trace files identical to C++ |
| C API tests (`ctest`, `cfreeze`, `cipasir`) linked against the Rust staticlib | pass |
| `test/cnf` head-to-head (default and 8 other configurations) | 85/85 identical statistics each |
| SAT Competition 2022–2024 + anniversary track instances solved by the reference in ≤ 300 s | 1,453/1,453 same answer, identical conflicts/decisions/propagations |
| SAT models (`dimocheck`) | 796/796 verified |
| LRAT proofs (`lrat-trim`), UNSAT instances solved in < 30 s | 261/261 verified |
| DRAT proofs (`drat-trim`), UNSAT instances solved in < 10 s | 217/217 verified |
| speed, 40 instances of 20–120 s, interleaved runs | Rust/C++ wall time 1.006 |

About 1,000 of the ~3,000 downloaded competition instances were not
classified within the available time (the largest ones) and are not
included above.

While benchmarking we found an upstream out-of-bounds read in
`tier.cpp` (`print_tier_usage_statistics` loops with
`glue <= stats.used[stable].size ()`), which makes the hardened-libc++
reference build trap (exit 133) while printing statistics after solving
some instances. The Rust port reads 0 there instead.

See `PORTING.md` for the porting conventions.

## License and credits

MIT, like CaDiCaL (see `LICENSE`, copied from upstream).

CaDiCaL is developed by Armin Biere, Katalin Fazekas, Mathias Fleury,
Nils Froleyks, Florian Pollitt and Tobias Faller at Johannes Kepler
University Linz, TU Wien and the University of Freiburg. All algorithms,
heuristics and documentation comments in this port are theirs; bugs in the
translation are ours. Please cite the CaDiCaL papers when using this solver
in research (see <https://github.com/arminbiere/cadical>).

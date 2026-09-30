> **Status: complete.** All modules below are fully ported (0 `todo!()`
> remaining). The per-module "stub" counts and work packages are historical
> (they describe how the port was split up). Verification: upstream cnf,
> usage, trace, mbt and API test suites pass; the 85 regression CNFs give
> bit-identical statistics to the C++ reference; 140k mobical fuzz traces pass.

# Port status

Generated from the source tree after the foundation step.  "Stubs" is the
number of `todo!(` bodies in the module (`grep -c 'todo!(' src/<module>.rs`).
"C++ lines" counts the `.cpp`/`.c` implementation lines the module ports.

The crate builds with `cargo build`, `cargo build --features logging`,
`cargo build --release` and `cargo test` (only the foundation unit tests
run; everything else panics with `todo!`).

## Modules

| Module (`src/`) | C++ source(s) | Stubs | Status | Package | C++ lines |
|---|---|---:|---|---|---:|
| `analyze.rs` | `analyze.cpp` | 32 | stub | P1 CDCL core | 1476 |
| `app.rs` | `cadical.cpp` | 13 | stub (header part done) | P10 CLI app, parser, files, statistics output, report, signals | 1031 |
| `arena.rs` | `arena.hpp`, `arena.cpp` | 0 | done | - | 30 |
| `assume.rs` | `assume.cpp` | 9 | stub | P8 Public API, assumptions, external propagator, C API | 616 |
| `averages.rs` | `averages.hpp`, `averages.cpp` | 0 | done | - | 34 |
| `backbone.rs` | `backbone.cpp` | 14 | stub | P5 Vivification, backbone, factor, lucky, lookahead | 635 |
| `backtrack.rs` | `backtrack.cpp` | 4 | stub | P1 CDCL core | 177 |
| `backward.rs` | `backward.cpp` | 5 | stub | P3 Variable elimination | 231 |
| `bins.rs` | `bins.hpp`, `bins.cpp` | 0 | done | - | 22 |
| `block.rs` | `block.hpp`, `block.cpp` | 12 | stub (header part done) | P3 Variable elimination | 824 |
| `ccadical.rs` | `ccadical.h`, `ccadical.cpp` | 32 | stub | P8 Public API, assumptions, external propagator, C API | 208 |
| `checker.rs` | `checker.hpp`, `checker.cpp` | 33 | stub | P9 Proof layer, tracers and checkers | 649 |
| `clause.rs` | `clause.hpp`, `clause.cpp` | 25 | stub (header part done) | P2 Internal driver, clause database, external layer | 667 |
| `collect.rs` | `collect.cpp` | 16 | stub | P2 Internal driver, clause database, external layer | 545 |
| `compact.rs` | `compact.cpp` | 2 | stub | P2 Internal driver, clause database, external layer | 550 |
| `condition.rs` | `condition.cpp` | 12 | stub | P4 Probing, subsumption and small inprocessors | 942 |
| `config.rs` | `config.hpp`, `config.cpp` | 0 | done | - | 101 |
| `congruence.rs` | `congruence.hpp`, `congruence.cpp` | 174 | stub (header part done) | P7 Congruence closure | 7925 |
| `constrain.rs` | `constrain.cpp` | 3 | stub | P8 Public API, assumptions, external propagator, C API | 64 |
| `contract.rs` | `contract.hpp`, `contract.cpp` | 0 | done | - | 27 |
| `cover.rs` | `cover.hpp`, `cover.cpp` | 8 | stub (header part done) | P3 Variable elimination | 704 |
| `decide.rs` | `decide.cpp` | 11 | stub | P1 CDCL core | 347 |
| `decompose.rs` | `decompose.hpp`, `decompose.cpp` | 7 | stub (header part done) | P4 Probing, subsumption and small inprocessors | 742 |
| `deduplicate.rs` | `deduplicate.cpp` | 2 | stub | P4 Probing, subsumption and small inprocessors | 275 |
| `definition.rs` | `definition.cpp` | 1 | stub | P3 Variable elimination | 283 |
| `delay.rs` | `delay.hpp` | 0 | done | - | 0 |
| `drattracer.rs` | `drattracer.hpp`, `drattracer.cpp` | 13 | stub | P9 Proof layer, tracers and checkers | 153 |
| `elim.rs` | `elim.hpp`, `elim.cpp` | 18 | stub (header part done) | P3 Variable elimination | 1175 |
| `elimfast.rs` | `elimfast.cpp` | 6 | stub | P3 Variable elimination | 583 |
| `ema.rs` | `ema.hpp`, `ema.cpp` | 0 | done | - | 95 |
| `extend.rs` | `extend.cpp` | 12 | stub | P2 Internal driver, clause database, external layer | 289 |
| `external.rs` | `external.hpp`, `external.cpp` | 47 | stub (header part done) | P2 Internal driver, clause database, external layer | 1036 |
| `external_propagate.rs` | `external_propagate.cpp` | 31 | stub | P8 Public API, assumptions, external propagator, C API | 1601 |
| `factor.rs` | `factor.hpp`, `factor.cpp` | 31 | stub (header part done) | P5 Vivification, backbone, factor, lucky, lookahead | 1018 |
| `file.rs` | `file.hpp`, `file.cpp` | 22 | stub (header part done) | P10 CLI app, parser, files, statistics output, report, signals | 506 |
| `flags.rs` | `flags.hpp`, `flags.cpp` | 0 | done | - | 135 |
| `flip.rs` | `flip.cpp` | 2 | stub | P2 Internal driver, clause database, external layer | 269 |
| `format.rs` | `format.hpp`, `format.cpp` | 0 | done | - | 89 |
| `frattracer.rs` | `frattracer.hpp`, `frattracer.cpp` | 19 | stub | P9 Proof layer, tracers and checkers | 277 |
| `gates.rs` | `gates.cpp` | 17 | stub | P3 Variable elimination | 766 |
| `heap.rs` | `heap.hpp` | 0 | done | - | 0 |
| `idruptracer.rs` | `idruptracer.hpp`, `idruptracer.cpp` | 39 | stub | P9 Proof layer, tracers and checkers | 566 |
| `instantiate.rs` | `instantiate.hpp`, `instantiate.cpp` | 5 | stub (header part done) | P4 Probing, subsumption and small inprocessors | 365 |
| `internal.rs` | `internal.hpp`, `internal.cpp` | 33 | stub (header part done) | P2 Internal driver, clause database, external layer | 1275 |
| `ipasir.rs` | `ipasir.h`, `ipasir.cpp` | 10 | stub | P8 Public API, assumptions, external propagator, C API | 47 |
| `kitten.rs` | `kitten.h`, `kitten.c`, `random.h`, `stack.h` | 40 | stub | P11 Kitten | 2599 |
| `level.rs` | `level.hpp` | 0 | done | - | 0 |
| `lidruptracer.rs` | `lidruptracer.hpp`, `lidruptracer.cpp` | 39 | stub | P9 Proof layer, tracers and checkers | 657 |
| `limit.rs` | `limit.hpp`, `limit.cpp` | 0 | done | - | 146 |
| `logging.rs` | `logging.hpp`, `logging.cpp` | 0 | done | - | 214 |
| `lookahead.rs` | `lookahead.cpp` | 9 | stub | P5 Vivification, backbone, factor, lucky, lookahead | 520 |
| `lratchecker.rs` | `lratchecker.hpp`, `lratchecker.cpp` | 35 | stub | P9 Proof layer, tracers and checkers | 833 |
| `lrattracer.rs` | `lrattracer.hpp`, `lrattracer.cpp` | 15 | stub | P9 Proof layer, tracers and checkers | 200 |
| `lucky.rs` | `lucky.cpp` | 12 | stub | P5 Vivification, backbone, factor, lucky, lookahead | 528 |
| `message.rs` | `message.hpp`, `message.cpp` | 0 | done | - | 218 |
| `minimize.rs` | `minimize.cpp` | 5 | stub | P1 CDCL core | 224 |
| `occs.rs` | `occs.hpp`, `occs.cpp` | 0 | done | - | 52 |
| `options.rs` | `options.hpp`, `options.cpp` | 0 | done | - | 359 |
| `parse.rs` | `parse.hpp`, `parse.cpp` | 9 | stub (header part done) | P10 CLI app, parser, files, statistics output, report, signals | 477 |
| `phases.rs` | `phases.hpp`, `phases.cpp` | 0 | done | - | 56 |
| `prelude.rs` | - | 0 | done (Rust only) | - | 0 |
| `probe.rs` | `probe.cpp` | 23 | stub | P4 Probing, subsumption and small inprocessors | 992 |
| `profile.rs` | `profile.hpp`, `profile.cpp` | 0 | done | - | 107 |
| `proof.rs` | `proof.hpp`, `proof.cpp` | 63 | stub (header part done) | P9 Proof layer, tracers and checkers | 691 |
| `propagate.rs` | `propagate.cpp` | 10 | stub | P1 CDCL core | 579 |
| `queue.rs` | `queue.hpp`, `queue.cpp` | 0 | done | - | 90 |
| `radix.rs` | `radix.hpp` | 0 | done | - | 0 |
| `random.rs` | `random.hpp`, `random.cpp` | 0 | done | - | 207 |
| `range.rs` | `range.hpp` | 0 | done | - | 0 |
| `reap.rs` | `reap.hpp`, `reap.cpp` | 0 | done | - | 127 |
| `reduce.rs` | `reduce.cpp` | 6 | stub | P1 CDCL core | 277 |
| `reluctant.rs` | `reluctant.hpp` | 0 | done | - | 0 |
| `rephase.rs` | `rephase.cpp` | 8 | stub | P1 CDCL core | 402 |
| `report.rs` | `report.cpp` | 1 | stub | P10 CLI app, parser, files, statistics output, report, signals | 313 |
| `resources.rs` | `resources.hpp`, `resources.cpp` | 0 | done | - | 164 |
| `restart.rs` | `restart.cpp` | 4 | stub | P1 CDCL core | 178 |
| `restore.rs` | `restore.cpp` | 2 | stub | P2 Internal driver, clause database, external layer | 267 |
| `score.rs` | `score.hpp`, `score.cpp` | 0 | done | - | 51 |
| `shrink.rs` | `shrink.cpp` | 11 | stub | P1 CDCL core | 507 |
| `signal.rs` | `signal.hpp`, `signal.cpp` | 8 | stub (header part done) | P10 CLI app, parser, files, statistics output, report, signals | 150 |
| `solution.rs` | `solution.cpp` | 4 | stub | P2 Internal driver, clause database, external layer | 50 |
| `solver.rs` | `cadical.hpp`, `solver.cpp` | 115 | stub (header part done) | P8 Public API, assumptions, external propagator, C API | 1872 |
| `sort.rs` | `(libc++ std::sort)` | 3 | placeholder (separate agent) | (separate) | 0 |
| `stable.rs` | `stable.cpp` | 0 | done | - | 31 |
| `stats.rs` | `stats.hpp`, `stats.cpp` | 2 | stub (header part done) | P10 CLI app, parser, files, statistics output, report, signals | 920 |
| `subsume.rs` | `subsume.cpp` | 6 | stub | P4 Probing, subsumption and small inprocessors | 646 |
| `sweep.rs` | `sweep.hpp`, `sweep.cpp` | 53 | stub (header part done) | P6 Local search and SAT sweeping | 1976 |
| `terminal.rs` | `terminal.hpp`, `terminal.cpp` | 0 | done | - | 38 |
| `ternary.rs` | `ternary.cpp` | 7 | stub | P4 Probing, subsumption and small inprocessors | 452 |
| `testing.rs` | `testing.hpp` | 0 | done | - | 0 |
| `tier.rs` | `tier.cpp` | 2 | stub | P1 CDCL core | 189 |
| `tracer.rs` | `tracer.hpp` | 0 | done | - | 0 |
| `transred.rs` | `transred.cpp` | 1 | stub | P4 Probing, subsumption and small inprocessors | 253 |
| `unstable.rs` | `unstable.cpp` | 0 | done | - | 29 |
| `util.rs` | `util.hpp`, `util.cpp` | 0 | done | - | 129 |
| `var.rs` | `var.hpp`, `var.cpp` | 0 | done | - | 39 |
| `veripbtracer.rs` | `veripbtracer.hpp`, `veripbtracer.cpp` | 30 | stub | P9 Proof layer, tracers and checkers | 427 |
| `version.rs` | `version.hpp`, `version.cpp` | 0 | done | - | 107 |
| `vivify.rs` | `vivify.hpp`, `vivify.cpp` | 22 | stub (header part done) | P5 Vivification, backbone, factor, lucky, lookahead | 1893 |
| `walk.rs` | `walk.hpp`, `walk.cpp` | 15 | stub (header part done) | P6 Local search and SAT sweeping | 1088 |
| `walk_full_occs.rs` | `walk_full_occs.cpp` | 17 | stub (header part done) | P6 Local search and SAT sweeping | 966 |
| `warmup.rs` | `warmup.cpp` | 4 | stub | P6 Local search and SAT sweeping | 405 |
| `watch.rs` | `watch.hpp`, `watch.cpp` | 0 | done | - | 124 |
| `bin/mobical.rs` | `mobical.cpp` | 1 | stub | P12 Mobical | 5671 |

Total stubs: 1302.

Notes:

* `Checker::print_stats` and `LratChecker::print_stats` are defined in
  `stats.cpp` but live in the `StatTracer` impls in `checker.rs` /
  `lratchecker.rs` (package P9).
* `Eliminator::enqueue`, `dequeue` and its destructor are defined in
  `backward.cpp` and stubbed in `backward.rs` (package P3).
* Fully ported foundation `.cpp` files: arena, averages, bins, config,
  contract, ema, flags, format, limit, logging, message, occs, options,
  phases, profile, queue, random, reap, resources, score, terminal, util,
  var, version, watch (plus `stable.cpp` / `unstable.cpp`, empty without
  `PROFILE_MODE`), and from `internal.cpp` the constructor, destructor and
  `enlarge_vals`, from `external.cpp` the constructor, from `proof.cpp`
  the `Proof` constructor.
* `src/sort.rs` is a placeholder for the libc++ `std::sort` port written
  separately (all sorting in the port must go through it).

## Work packages

Each package is a set of related modules that can be ported in parallel
with the others (signatures of functions owned by other packages must not
be changed without coordination).

### P1 CDCL core

Modules: `propagate`, `analyze`, `minimize`, `shrink`, `backtrack`, `decide`, `restart`, `reduce`, `tier`, `rephase`  
C++ lines: 4356, stubs: 93.

### P2 Internal driver, clause database, external layer

Modules: `internal`, `clause`, `collect`, `compact`, `external`, `extend`, `flip`, `restore`, `solution`  
C++ lines: 4948, stubs: 143.

### P3 Variable elimination

Modules: `elim`, `elimfast`, `gates`, `definition`, `backward`, `block`, `cover`  
C++ lines: 4566, stubs: 67.

### P4 Probing, subsumption and small inprocessors

Modules: `probe`, `subsume`, `deduplicate`, `instantiate`, `ternary`, `transred`, `decompose`, `condition`  
C++ lines: 4667, stubs: 63.

### P5 Vivification, backbone, factor, lucky, lookahead

Modules: `vivify`, `backbone`, `factor`, `lucky`, `lookahead`  
C++ lines: 4594, stubs: 88.

### P6 Local search and SAT sweeping

Modules: `walk`, `walk_full_occs`, `warmup`, `sweep`  
C++ lines: 4435, stubs: 89.

### P7 Congruence closure

Modules: `congruence`  
C++ lines: 7925, stubs: 174.

### P8 Public API, assumptions, external propagator, C API

Modules: `solver`, `assume`, `constrain`, `external_propagate`, `ccadical`, `ipasir`  
C++ lines: 4408, stubs: 200.

### P9 Proof layer, tracers and checkers

Modules: `proof`, `checker`, `lratchecker`, `drattracer`, `frattracer`, `lrattracer`, `idruptracer`, `lidruptracer`, `veripbtracer`  
C++ lines: 4453, stubs: 286.

### P10 CLI app, parser, files, statistics output, report, signals

Modules: `app`, `parse`, `file`, `stats`, `report`, `signal`  
C++ lines: 3397, stubs: 55.

### P11 Kitten

Modules: `kitten`  
C++ lines: 2599, stubs: 40.

### P12 Mobical

Modules: `bin/mobical`  
C++ lines: 5671, stubs: 1.


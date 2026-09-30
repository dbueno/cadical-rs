#!/bin/sh
# Head-to-head comparison of the upstream C++ API / contrib tests (built
# against the reference library by scripts/run-cpp-api-tests.sh) with their
# Rust ports (tests/api_*.rs, tests/contrib_*.rs).
#
# Usage: scripts/compare-api-tests.sh [test ...]
#
# Runs every Rust port with 'cargo test --release --test <name>' (stdout
# to "$OUT/rust/<test>.stdout", 'CADICALBUILD' pointing to "$OUT/rust"),
# then compares normalized stdout and the files the tests write against
# "$OUT/cpp" (run scripts/run-cpp-api-tests.sh first).  Paths, process ids
# and pointers are normalized; outputs that depend on timing or thread
# scheduling ('terminate', 'parcompwrite' order) are compared after sorting
# or reported as 'nondeterministic'.
#
# Environment: OUT (default /Volumes/Shampoo/cadical-rs/apitests),
# CARGO_TARGET_DIR (passed to cargo).

set -u

ROOT=$(cd "$(dirname "$0")/.." && pwd)
OUT=${OUT:-/Volumes/Shampoo/cadical-rs/apitests}
CPP="$OUT/cpp"
RS="$OUT/rust"
DIFFS="$OUT/diffs"
mkdir -p "$RS" "$DIFFS"

all="newdelete unit morenmore example example_declare_one_more_variable
example_constraint example_tracer terminate learn traverse incproof
propagate_assumptions example_propagators parcompwrite apitrace
craigtracer craigtracer_incremental"
[ $# -gt 0 ] && tests="$*" || tests="$all"

normalize () {
  sed -E \
    -e "s,$CPP,BUILD,g" -e "s,$RS,BUILD,g" \
    -e 's,[^ '"'"']*(cadical-api-test-[a-z-]+)-[0-9]+,TMP/\1-PID,g' \
    -e 's,0x[0-9a-f]+,PTR,g' "$1"
}

same=0
different=0
nondet=0
for t in $tests; do
  case $t in
    craigtracer*) rt="contrib_$t" ;;
    *) rt="api_$t" ;;
  esac
  (cd "$ROOT" && CADICALBUILD="$RS" CADICAL_APITEST_PARCOMPWRITE=1 cargo test -q --release --test "$rt" \
     > "$RS/$t.stdout" 2> "$RS/$t.stderr")
  echo $? > "$RS/$t.status"
  if [ ! -f "$CPP/$t.stdout" ]; then
    echo "$t: missing C++ output (run scripts/run-cpp-api-tests.sh)"
    continue
  fi
  normalize "$CPP/$t.stdout" > "$DIFFS/$t.cpp.stdout"
  normalize "$RS/$t.stdout" > "$DIFFS/$t.rust.stdout"
  case $t in
    parcompwrite)
      sort "$DIFFS/$t.cpp.stdout" -o "$DIFFS/$t.cpp.stdout"
      sort "$DIFFS/$t.rust.stdout" -o "$DIFFS/$t.rust.stdout"
      ;;
  esac
  status="rust exit $(cat "$RS/$t.status"), c++ exit $(cat "$CPP/$t.status")"
  if [ "$t" = terminate ]; then
    echo "$t: nondeterministic (timer based), $status, stdout lines: c++ $(wc -l < "$CPP/$t.stdout"), rust $(wc -l < "$RS/$t.stdout")"
    nondet=$((nondet + 1))
    continue
  fi
  if diff "$DIFFS/$t.cpp.stdout" "$DIFFS/$t.rust.stdout" > "$DIFFS/$t.stdout.diff"; then
    echo "$t: stdout identical ($(wc -l < "$CPP/$t.stdout") lines), $status"
    same=$((same + 1))
    rm -f "$DIFFS/$t.stdout.diff"
  else
    echo "$t: stdout DIFFERS, $status (see $DIFFS/$t.stdout.diff)"
    different=$((different + 1))
  fi
done

# Files written by the tests.
for f in test-api-traverse.clauses test-api-traverse.extensions \
    test-api-apitrace-inctrace1.drup test-api-apitrace-inctrace1.lrat \
    test-api-apitrace-inctrace2.drup test-api-apitrace-inctrace2.lrat \
    test-api-propagate-propagate_assumptions.lidrup \
    test-api-apitrace-file1.trace test-api-apitrace-file2.trace \
    test-api-apitrace-environment1.trace test-api-apitrace-environment2.trace
do
  [ -f "$CPP/$f" ] && [ -f "$RS/$f" ] || continue
  if cmp -s "$CPP/$f" "$RS/$f"; then
    echo "file $f: identical"
  else
    diff "$CPP/$f" "$RS/$f" > "$DIFFS/$f.diff"
    echo "file $f: DIFFERS (see $DIFFS/$f.diff)"
    different=$((different + 1))
  fi
done

echo "compare: $same identical, $different different, $nondet nondeterministic"
exit $different

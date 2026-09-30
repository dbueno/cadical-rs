#!/bin/sh
# Build and run the upstream C++ API tests (cadical/test/api/*.cpp) and
# contrib tests (cadical/test/contrib/*.cpp) against the *reference* C++
# library, to compare their stdout with the Rust ports in tests/api_*.rs
# and tests/contrib_*.rs (see scripts/compare-api-tests.sh).
#
# Usage: scripts/run-cpp-api-tests.sh [test ...]
#
# Environment:
#   REF      reference install prefix (lib/libcadical.a, include/)
#            default /Volumes/Shampoo/cadical-rs/result
#   OUT      output directory, default /Volumes/Shampoo/cadical-rs/apitests/cpp
#
# Must be run with a C++ compiler in PATH, e.g.
#   nix develop /Users/dbueno/proj/cadical-rs -c scripts/run-cpp-api-tests.sh

set -u

ROOT=$(cd "$(dirname "$0")/.." && pwd)
REF=${REF:-/Volumes/Shampoo/cadical-rs/result}
OUT=${OUT:-/Volumes/Shampoo/cadical-rs/apitests/cpp}
CXX=${CXX:-c++}
CXXFLAGS=${CXXFLAGS:-"-Wall -Wextra -O3 -DNDEBUG -DNCLOSEFROM -std=c++11"}

mkdir -p "$OUT"
# Several tests write into '$CADICALBUILD' (traverse, incproof,
# propagate_assumptions, apitrace).
export CADICALBUILD="$OUT"

api_tests="newdelete unit morenmore example example_declare_one_more_variable
example_constraint example_tracer terminate learn traverse incproof
propagate_assumptions example_propagators parcompwrite apitrace"
contrib_tests="craigtracer craigtracer_incremental"

[ $# -gt 0 ] && selected="$*" || selected="$api_tests $contrib_tests"

ok=0
failed=0
for t in $selected; do
  if [ -f "$ROOT/cadical/test/api/$t.cpp" ]; then
    src="$ROOT/cadical/test/api/$t.cpp"
    extra=""
    [ "$t" = parcompwrite ] && extra="-pthread"
  elif [ -f "$ROOT/cadical/test/contrib/$t.cpp" ]; then
    src="$ROOT/cadical/test/contrib/$t.cpp"
    extra="-I$ROOT/cadical/src -I$ROOT/cadical/contrib"
  else
    echo "unknown test '$t'" >&2
    exit 1
  fi
  exe="$OUT/test-$t"
  rm -f "$exe" "$OUT/$t.stdout" "$OUT/$t.stderr" "$OUT/$t.build.log"
  if ! $CXX $CXXFLAGS $extra -o "$exe" "$src" "$REF/lib/libcadical.a" \
      > "$OUT/$t.build.log" 2>&1; then
    echo "$t: BUILD FAILED (see $OUT/$t.build.log)"
    failed=$((failed + 1))
    continue
  fi
  (cd "$OUT" && "$exe" > "$OUT/$t.stdout" 2> "$OUT/$t.stderr")
  status=$?
  echo "$status" > "$OUT/$t.status"
  if [ $status = 0 ]; then
    echo "$t: ok"
    ok=$((ok + 1))
  else
    echo "$t: FAILED (exit status $status)"
    failed=$((failed + 1))
  fi
done
echo "C++ reference API tests: $ok ok, $failed failed (outputs in $OUT)"
exit $failed

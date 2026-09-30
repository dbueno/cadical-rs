#!/bin/sh
# Build the upstream C API test drivers (cadical/test/api/{ctest,cfreeze,
# cipasir}.c) with 'cc' against the Rust static library
# (target/release/libcadical.a, i.e. the 'staticlib' crate type which
# exports the 'ccadical_*' and 'ipasir_*' C functions) and run them.
#
# Usage: scripts/run-c-api-tests.sh [--no-build] [test ...]
#
# Environment:
#   CARGO_TARGET_DIR  cargo target directory (default: ./target)
#   OUT               output directory
#                     (default: /Volumes/Shampoo/cadical-rs/apitests/c)
#   CC                C compiler (default: cc)
#   REF               if set, link against "$REF/lib/libcadical.a" (the
#                     C++ reference library, needs 'c++' for linking)
#                     instead of the Rust library, for comparison
#
# Stdout / stderr of each test go to "$OUT/<test>.stdout" / ".stderr",
# the exit status to "$OUT/<test>.status".

set -u

ROOT=$(cd "$(dirname "$0")/.." && pwd)
TARGET=${CARGO_TARGET_DIR:-$ROOT/target}
OUT=${OUT:-/Volumes/Shampoo/cadical-rs/apitests/c}
CC=${CC:-cc}
CFLAGS=${CFLAGS:-"-Wall -Wextra -O2 -std=c11"}
REF=${REF:-}

build=yes
if [ $# -gt 0 ] && [ "$1" = "--no-build" ]; then
  build=no
  shift
fi

[ $# -gt 0 ] && tests="$*" || tests="ctest cfreeze cipasir"

mkdir -p "$OUT"

if [ -n "$REF" ]; then
  LIB="$REF/lib/libcadical.a"
  LINK="${CXX:-c++}"
  LIBS=""
else
  LIB="$TARGET/release/libcadical.a"
  LINK="$CC"
  # System libraries needed by the Rust standard library.
  case "$(uname -s)" in
    Darwin) LIBS="-lSystem -lc -lm -liconv -framework CoreFoundation" ;;
    *) LIBS="-lpthread -ldl -lm -lc" ;;
  esac
  if [ $build = yes ]; then
    echo "cargo build --release (CARGO_TARGET_DIR=$TARGET)"
    (cd "$ROOT" && CARGO_TARGET_DIR="$TARGET" cargo build --release --lib) \
      > "$OUT/cargo-build.log" 2>&1 || {
      echo "cargo build failed (see $OUT/cargo-build.log)"
      exit 1
    }
  fi
fi

[ -f "$LIB" ] || { echo "can not find '$LIB'"; exit 1; }

ok=0
failed=0
for t in $tests; do
  src="$ROOT/cadical/test/api/$t.c"
  [ -f "$src" ] || { echo "can not find '$src'"; exit 1; }
  exe="$OUT/$t"
  rm -f "$exe" "$OUT/$t.o" "$OUT/$t.stdout" "$OUT/$t.stderr" "$OUT/$t.status"
  if ! { $CC $CFLAGS -c -o "$OUT/$t.o" "$src" &&
         $LINK -o "$exe" "$OUT/$t.o" "$LIB" $LIBS; } > "$OUT/$t.build.log" 2>&1
  then
    echo "$t: BUILD FAILED (see $OUT/$t.build.log)"
    failed=$((failed + 1))
    continue
  fi
  (cd "$OUT" && "$exe" > "$OUT/$t.stdout" 2> "$OUT/$t.stderr")
  status=$?
  echo $status > "$OUT/$t.status"
  if [ $status = 0 ]; then
    echo "$t: ok"
    ok=$((ok + 1))
  else
    echo "$t: FAILED (exit status $status, see $OUT/$t.stderr)"
    failed=$((failed + 1))
  fi
done

echo "C API tests: $ok ok, $failed failed (outputs in $OUT)"
exit $failed

#!/usr/bin/env bash
#
# Build an ASan+UBSan kernel and run it over a short, representative set of
# modules and error fixtures.
#
# Why this exists: a null ExpressionPointer reached `makeApplication` and
# died at address 0x40 with no line number, no goal, and no clue — the
# first symptom was `dumped core`. The sanitizers turn that class of
# failure into a report that names the file and line. Worth running after
# any change to the prover's control flow, where the invariant "a tactic
# returns a proof or throws" is easy to break by accident.
#
# Not wired into `make`: the build takes several minutes and the run is
# roughly 10x slower than the normal kernel, so it is a deliberate act,
# not part of the loop.
set -u
cd "$(dirname "$0")/.."

OUT=${1:-/tmp/asan}
mkdir -p "$OUT"

SRCS=$(sed -n '/^SRCS := /,/^$/p' Makefile | sed 's/SRCS := //; s/\\//' | tr '\n' ' ')

echo "building $OUT/kernel-asan …"
g++ -std=c++20 -O1 -g -fsanitize=address,undefined -fno-omit-frame-pointer \
    -fno-sanitize-recover=undefined -Isrc \
    $SRCS -o "$OUT/kernel-asan" -lgmpxx -lgmp || exit 1

export ASAN_OPTIONS=detect_leaks=0:abort_on_error=0
export UBSAN_OPTIONS=print_stacktrace=1

findings=0
run() {
    local label="$1"; shift
    local out rc
    out=$("$@" 2>&1); rc=$?
    if [ $rc -ne 0 ] || echo "$out" | grep -qiE "runtime error|AddressSanitizer"; then
        echo "FINDING  $label (rc=$rc)"
        echo "$out" | grep -iE "runtime error|AddressSanitizer|^ *#[0-9]" | head -12
        findings=$((findings+1))
    else
        printf "clean    %s\n" "$label"
    fi
}

for f in library/Plane/*.math library/Real/cluster.math \
         library/Real/archimedean.math library/Natural/frequently.math \
         library/Natural/subsequence.math; do
    run "$f" timeout 900 "$OUT/kernel-asan" verify --source "$f" \
        --output /tmp/sanitizer_probe.mathv --cache-root build
done

# The error paths are where a tactic is most likely to hand back a null.
for f in library/ErrorTest/*.math; do
    out=$(timeout 300 "$OUT/kernel-asan" verify --source "$f" \
              --output /tmp/sanitizer_probe.mathv --cache-root build 2>&1)
    if echo "$out" | grep -qiE "runtime error|AddressSanitizer"; then
        echo "FINDING  $f"
        echo "$out" | grep -iE "runtime error|AddressSanitizer" | head -6
        findings=$((findings+1))
    fi
done
echo "sanitizer scan: $findings finding(s)"
[ "$findings" -eq 0 ]

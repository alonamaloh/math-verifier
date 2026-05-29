#!/bin/bash
# Wrapper that times `./kernel verify ...` and emits a [file] line on
# stderr alongside whatever the kernel itself prints (including the
# [time] per-declaration lines from MATH_TIME_DECLARATIONS=1).
#
# Usage: time_verify.sh SOURCE.math OUT.mathv -- <kernel verify args...>

set -e
source="$1"; shift
output="$1"; shift
# Remaining args are passed to the kernel.

t0=$(python3 -c 'import time; print(time.time())')
./kernel verify --source "$source" --output "$output" "$@"
rc=$?
t1=$(python3 -c 'import time; print(time.time())')
ms=$(python3 -c "print(round(($t1 - $t0) * 1000))")
echo "[file] $source: ${ms} ms" >&2
exit $rc

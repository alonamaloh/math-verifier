#!/usr/bin/env bash
#
# Error-message regression harness.
#
# For each library/ErrorTest/<name>.math (an intentionally-broken proof):
#   1. assert it FAILS to verify (non-zero exit), and
#   2. assert its combined stdout+stderr contains every substring listed
#      in the sidecar library/ErrorTest/<name>.expected
#      (one substring per line; blank lines and `#` comments ignored).
#
# A file that unexpectedly verifies, lacks a sidecar, or whose message has
# drifted away from an expected substring is a FAILURE. This makes
# "the error message says the informative thing" a checked invariant —
# see docs/error_message_corpus.md for the rationale and the catalogue.
#
# Each kernel run is wrapped in `ulimit -t` so a non-terminating
# elaboration dies on its own instead of hanging the suite.

set -u
cd "$(dirname "$0")/.."

KERNEL=./kernel
CACHE=build
DIR=library/ErrorTest

if [ ! -x "$KERNEL" ]; then
  echo "error_tests: ./kernel not built (run: make -j 16 kernel)" >&2
  exit 1
fi

shopt -s nullglob
files=("$DIR"/*.math)
if [ ${#files[@]} -eq 0 ]; then
  echo "error_tests: no test files under $DIR" >&2
  exit 1
fi

pass=0
fail=0
for f in "${files[@]}"; do
  exp="${f%.math}.expected"
  out=$( ( ulimit -t 60; "$KERNEL" verify --source "$f" --cache-root "$CACHE" ) 2>&1 )
  rc=$?

  problems=()
  if [ "$rc" -eq 0 ]; then
    problems+=("expected verification to FAIL, but it succeeded (exit 0)")
  fi
  if [ ! -f "$exp" ]; then
    problems+=("no .expected sidecar at $exp")
  else
    while IFS= read -r line || [ -n "$line" ]; do
      [ -z "$line" ] && continue
      case "$line" in \#*) continue ;; esac
      if ! grep -qF -- "$line" <<<"$out"; then
        problems+=("missing expected substring: $line")
      fi
    done < "$exp"
  fi

  if [ ${#problems[@]} -eq 0 ]; then
    pass=$((pass + 1))
    echo "PASS  $f"
  else
    fail=$((fail + 1))
    echo "FAIL  $f"
    printf '        %s\n' "${problems[@]}"
    echo "        --- actual output ---"
    sed 's/^/        | /' <<<"$out"
  fi
done

echo "error-tests: $pass passed, $fail failed"
[ "$fail" -eq 0 ]

#!/usr/bin/env bash
set -euo pipefail

kernel=${1:-./kernel}
cache=${2:-build/library/Test/expected_carrier_propagation_test.mathv}
declaration=Test.carrier_equality_cast_normal_form

line=$("$kernel" dump "$cache" | grep -F "$declaration ")
expected='(Rational.to_real (a + b)) = (Rational.to_real a) + (Rational.to_real b)'

if [[ "$line" != *"$expected"* ]]; then
  echo "carrier-normal-form-check: FAIL — equality coercion changed the elaborated proposition"
  echo "  expected declaration to contain: $expected"
  echo "  actual: $line"
  exit 1
fi

echo "carrier-normal-form-check: PASS"

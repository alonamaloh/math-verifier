#!/usr/bin/env bash
set -euo pipefail

kernel=${1:-./kernel}
cache=${2:-build/library/Test/expected_carrier_propagation_test.mathv}
dump=$("$kernel" dump "$cache")

check_shape() {
  local declaration=$1
  local expected=$2
  local line
  line=$(grep -F "$declaration " <<<"$dump")

  if [[ "$line" != *"$expected"* ]]; then
    echo "carrier-normal-form-check: FAIL — coercion changed the elaborated proposition"
    echo "  declaration: $declaration"
    echo "  expected declaration to contain: $expected"
    echo "  actual: $line"
    exit 1
  fi
}

check_shape \
  Test.carrier_equality_cast_normal_form \
  '(Rational.to_real (a + b)) = (Rational.to_real a) + (Rational.to_real b)'
check_shape \
  Test.carrier_unary_cast_normal_form \
  '(Integer.to_rational (-a)) = -(Integer.to_rational a)'

echo "carrier-normal-form-check: PASS"

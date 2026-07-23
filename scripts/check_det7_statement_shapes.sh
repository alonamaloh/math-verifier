#!/usr/bin/env bash
set -euo pipefail

kernel=${1:-./kernel}
cache=${2:-build/library/Test/det_seven_safe_converse_test.mathv}
dump=$("$kernel" dump "$cache")

declaration_line() {
  local declaration=$1
  local line
  line=$(grep -F "$declaration " <<<"$dump")
  if [[ -z "$line" ]]; then
    echo "det7-statement-shape-check: FAIL — declaration is missing"
    echo "  declaration: $declaration"
    exit 1
  fi
  printf '%s' "$line"
}

check_contains() {
  local declaration=$1
  local expected=$2
  local line
  line=$(declaration_line "$declaration")
  if [[ "$line" != *"$expected"* ]]; then
    echo "det7-statement-shape-check: FAIL — a guarded declaration changed"
    echo "  declaration: $declaration"
    echo "  expected declaration to contain: $expected"
    echo "  actual: $line"
    exit 1
  fi
}

# These checks are filled from the elaborated declaration, not from source
# text, so a coercion or binder regression cannot hide behind successful
# verification.
check_contains Test.detSevenSafe_definition_shape 'Not ((Natural.modulo n 12) = 7)'
check_contains Test.detSevenSafe_definition_shape 'Not ((Natural.modulo n 12) = 10)'
check_contains Test.detSevenSafe_definition_shape 'Not ((Natural.modulo n 49) = 0)'
check_contains Test.detSevenSafe_definition_shape 'Not ((Natural.modulo n 49) = 21)'
check_contains Test.detSevenSafe_definition_shape 'Not ((Natural.modulo n 49) = 35)'
check_contains Test.detSevenSafe_definition_shape 'Not ((Natural.modulo n 49) = 42)'
check_contains Test.detSevenSafeConverse_definition_shape \
  'Matrix.DetSevenSafeConverse = ((n : Natural) → 1 ≤ n → Natural.IsDetSevenSafe n → Matrix.Represents (1 + 2) (Matrix.squarePlusDoubleSquareOddForm (Natural.to_integer 4)) (Natural.to_integer n))'

echo "det7-statement-shape-check: PASS"

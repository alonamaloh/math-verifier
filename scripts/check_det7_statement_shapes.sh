#!/usr/bin/env bash
set -euo pipefail

kernel=${1:-./kernel}
shift || true

if [[ $# -eq 0 ]]; then
  set -- \
    build/library/Test/det_seven_safe_converse_test.mathv \
    build/library/Algebra/truant_squarefree.mathv \
    build/library/Algebra/det_seven_rank_four_infrastructure.mathv
fi

dump=
for cache in "$@"; do
  dump+=$'\n'"$("$kernel" dump "$cache")"
done

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
check_contains Test.squarefree_definition_shape \
  '(Natural.IsSquarefree n) = ((d : Natural) → 2 ≤ d → Not (d * d ∣ n))'
check_contains Matrix.IsTruant.squarefree \
  'Matrix.IsTruant n A truant → Natural.IsSquarefree truant'

check_contains Matrix.detSeven_zero_residue_orthogonal_lift \
  'Matrix.squarePlusDoubleSquareOddRankFourRepresentative (Natural.to_integer 4) (Natural.to_integer 0) corner'
check_contains Matrix.detSeven_zero_residue_orthogonal_lift \
  '(residual + corner * (t * t))'
check_contains Matrix.detSeven_nonzero_residue_orthogonal_lift \
  '(residual + ((Natural.to_integer 49) * corner - (Natural.to_integer 28) * (residue * residue)) * (t * t))'

check_lift() {
  local declaration=$1
  local residue=$2
  local corner=$3
  local norm=$4
  local expected_form="Matrix.squarePlusDoubleSquareOddRankFourRepresentative (Natural.to_integer 4) (Natural.to_integer ${residue}) (Natural.to_integer ${corner})"
  local expected_norm="(residual + (Natural.to_integer ${norm}) * (t * t))"
  check_contains "$declaration" "$expected_form"
  check_contains "$declaration" "$expected_norm"
}

check_lift Matrix.oddC4R0C7_orthogonal_lift 0 7 7
check_lift Matrix.oddC4R1C6_orthogonal_lift 1 6 266
check_lift Matrix.oddC4R1C7_orthogonal_lift 1 7 315
check_lift Matrix.oddC4R2C8_orthogonal_lift 2 8 280
check_lift Matrix.oddC4R2C9_orthogonal_lift 2 9 329
check_lift Matrix.oddC4R3C10_orthogonal_lift 3 10 238
check_lift Matrix.oddC4R3C11_orthogonal_lift 3 11 287

echo "det7-statement-shape-check: PASS"

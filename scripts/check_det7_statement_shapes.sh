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

check_residual_cover() {
  local declaration=$1
  local multiplier=$2
  local choices=$3
  check_contains "$declaration" "And (Natural.${choices} t)"
  check_contains "$declaration" \
    "n = ${multiplier} * t * t + residual → Natural.IsDetSevenSafe residual"
}

check_residual_cover Natural.detSevenResiduals_m7 7 DetSevenChoices12346
check_residual_cover Natural.detSevenResiduals_m266 266 DetSevenChoices123456
check_residual_cover Natural.detSevenResiduals_m280 280 DetSevenChoices123469
check_residual_cover Natural.detSevenResiduals_m329 329 DetSevenChoices123469
check_residual_cover Natural.detSevenResiduals_m238 238 DetSevenChoices123456
check_residual_cover Natural.detSevenResiduals_m287 287 DetSevenChoices123469
check_residual_cover Natural.detSevenOddResiduals_m315 315 DetSevenChoices123456
check_contains Natural.detSevenOddResiduals_m315 '(Natural.modulo n 2) = 1'

check_contains Natural.detSevenResidueCover_m7_selected \
  'Natural.DetSevenGenericSelectedResidueCover 7 Natural.DetSevenChoices12346 Natural.DetSevenSelectedM7'
check_contains Natural.detSevenResidueCover_m329_selected \
  'Natural.DetSevenGenericSelectedResidueCover 329 Natural.DetSevenChoices123469 Natural.DetSevenSelectedM329'
check_contains Matrix.detSevenFiniteCover_q0c7 \
  'Matrix.DetSevenFiniteCover (Matrix.squarePlusDoubleSquareOddRankFourRepresentative (Natural.to_integer 4) (Natural.to_integer 0) (Natural.to_integer 7)) 7 Natural.DetSevenSelectedM7'
check_contains Matrix.detSevenFiniteCover_q2c9 \
  'Matrix.DetSevenFiniteCover (Matrix.squarePlusDoubleSquareOddRankFourRepresentative (Natural.to_integer 4) (Natural.to_integer 2) (Natural.to_integer 9)) 329 Natural.DetSevenSelectedM329'

check_generic_universal() {
  local declaration=$1
  local residue=$2
  local corner=$3
  check_contains "$declaration" \
    'Matrix.DetSevenSafeConverse → Matrix.IsUniversal'
  check_contains "$declaration" \
    "Matrix.squarePlusDoubleSquareOddRankFourRepresentative (Natural.to_integer 4) (Natural.to_integer ${residue}) (Natural.to_integer ${corner})"
}

check_generic_universal Matrix.oddC4R0C7_universal_of_det_seven_safe_converse 0 7
check_generic_universal Matrix.oddC4R1C6_universal_of_det_seven_safe_converse 1 6
check_generic_universal Matrix.oddC4R2C8_universal_of_det_seven_safe_converse 2 8
check_generic_universal Matrix.oddC4R2C9_universal_of_det_seven_safe_converse 2 9
check_generic_universal Matrix.oddC4R3C10_universal_of_det_seven_safe_converse 3 10
check_generic_universal Matrix.oddC4R3C11_universal_of_det_seven_safe_converse 3 11
check_contains Matrix.detSeven_six_generic_universal \
  'Matrix.DetSevenSafeConverse → And'

check_contains Natural.detSevenOddResidueCover_m315_selected \
  'Natural.DetSevenOddSelectedResidueCover 315 Natural.DetSevenChoices123456 Natural.DetSevenSelectedM315Odd'
check_contains Matrix.detSevenFiniteCover_q1c7odd \
  'Matrix.DetSevenFiniteCover (Matrix.squarePlusDoubleSquareOddRankFourRepresentative (Natural.to_integer 4) (Natural.to_integer 1) (Natural.to_integer 7)) 315 Natural.DetSevenSelectedM315Odd'
check_contains Matrix.detSevenEvenFiniteCover_q1c7 \
  '(Natural.modulo n 2) = 0'
check_contains Matrix.oddC4R1C7_even_section_orthogonal_lift \
  '((Natural.to_integer 2) * residual + (Natural.to_integer 90) * (t * t))'
check_contains Matrix.oddC4R1C7_represents_even_above_ninety \
  'Matrix.ThreeSquaresConverse →'
check_contains Matrix.oddC4R1C7_universal_of_det_seven_and_three_squares \
  'Matrix.DetSevenSafeConverse → Matrix.ThreeSquaresConverse → Matrix.IsUniversal'
check_contains Matrix.detSeven_seven_universal \
  'Matrix.DetSevenSafeConverse → Matrix.ThreeSquaresConverse → And'

echo "det7-statement-shape-check: PASS"

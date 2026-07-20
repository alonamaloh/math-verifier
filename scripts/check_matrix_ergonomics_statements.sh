#!/usr/bin/env bash
set -euo pipefail

kernel=${1:-./kernel}
cache=${2:-build/library/Test/matrix_ergonomics_test.mathv}
dump=$("$kernel" dump "$cache")

check_shape() {
  local declaration=$1
  local expected=$2
  local line
  line=$(grep -F "$declaration " <<<"$dump")

  if [[ "$line" != *"$expected"* ]]; then
    echo "matrix-ergonomics-statement-check: FAIL — a control declaration changed"
    echo "  declaration: $declaration"
    echo "  expected declaration to contain: $expected"
    echo "  actual: $line"
    exit 1
  fi
}

# Symbolic expansion: ordered products T·D and D·N remain distinct.
check_shape \
  Test.matrix_ordered_word_expansion \
  '(r * n n n T D)) (r + n n (r * n n n D N) (r * n n n (r * n n n T D) N))'
check_shape \
  Test.matrix_one_add_multiply_one_subtract \
  '(r - n n (Matrix.identity r n) (r * n n n N N))'
check_shape \
  Test.matrix_rectangular_product_is_ordered_ring_atom \
  '(r * n m n A B) Z) = (r + n n Z (r * n m n A B))'

# Relation evidence remains an explicit premise of the square-zero theorem.
check_shape \
  Test.matrix_square_zero_inverse_right_baseline \
  '(r * n n n N N) = (Matrix.zero r n n) →'

# The block control requires symmetry, leading block, border column, and corner.
check_shape \
  Test.symmetric_bordered_equal_baseline \
  '(Matrix.borderColumn r n B) = (Matrix.borderColumn r n C) → (Matrix.corner r n B) = (Matrix.corner r n C) → B = C'
check_shape \
  Test.symmetric_bordered_equal_blockwise \
  '(Matrix.borderColumn r n B) = (Matrix.borderColumn r n C) → (Matrix.corner r n B) = (Matrix.corner r n C) → B = C'

# Closed 3×3 controls must retain their fixed dimension and named witnesses.
check_shape \
  Test.matrix_concrete_three_by_three_product_baseline \
  'Test.matrixErgonomicsShear Test.matrixErgonomicsShearInverse) = (Matrix.identity Integer.commutative_ring_bundle (1 + 2))'
check_shape \
  Test.matrix_concrete_three_by_three_inverse_baseline \
  'Matrix.IsInvertible Integer.commutative_ring_bundle (1 + 2) Test.matrixErgonomicsShear'
check_shape \
  Test.matrix_concrete_three_by_three_pullback_baseline \
  '(Matrix.diagonalExtension Integer.commutative_ring_bundle 2 Matrix.sumOfTwoSquaresForm (Natural.to_integer 2))'

echo "matrix-ergonomics-statement-check: PASS"

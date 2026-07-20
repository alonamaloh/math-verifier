# Quadratic forms and the Fifteen Theorem

This development formalizes the escalation route toward the Fifteen Theorem.
The final theorem and the deduplicated rank-three/rank-four classifications
are not yet proved; the foundations, the raw rank-three candidate family,
and the first exact rank-three truant are.

## Main definitions

- A symmetric matrix and its quadratic form: `Matrix.IsSymmetric` and
  `Matrix.quadraticForm(A, x)` in `quadratic_form.math`.
- Representation, universality, and positive definiteness:
  `Matrix.Represents`, `Matrix.IsUniversal`, and
  `Matrix.IsPositiveDefinite` in `integer_quadratic_form.math`.
- Integral isometry: `Matrix.IsIsometric`; it uses an invertible change of
  basis.
- Positive leading principal minors:
  `Matrix.HasPositiveLeadingMinors` in `sylvester.math`.
- The rank-one form \(x^2\): `Matrix.squareForm` in `square_form.math`.
- The least missed positive integer: `Matrix.IsTruant` and the total function
  `Matrix.truant` in `truant.math`. On a universal form the function has the
  harmless fallback value zero.
- An extension by the parent's truant: `Matrix.IsEscalation`; a form reachable
  from the empty form by repeated extensions: `Matrix.IsEscalator`.
- Canonical bordered matrices: `Matrix.borderedAssembly(A, b, c)`, with
  `Matrix.IsEscalation.eq_borderedAssembly` reconstructing every escalation.

## Main theorems

- Pullback and sublattice transport:
  `Matrix.quadraticForm_pullback` and `Matrix.represents_of_sublattice`.
- Isometry invariance: `Matrix.isometric_represents`,
  `Matrix.isometric_universal`, `Matrix.isometric_positive_definite`, and
  `Matrix.isometric_determinant`.
- Direct sums: `Matrix.directSum_quadraticForm`,
  `Matrix.directSum_represents_left`, `Matrix.directSum_represents_sum`, and
  `Matrix.directSum_positive_definite`.
- Sylvester's criterion:
  `Matrix.positive_leading_minors_of_positive_definite` and
  `Matrix.positive_definite_of_positive_leading_minors`. The fraction-free
  Schur identities are in `schur_complement.math`.
- Finite-search bounds: `Matrix.cauchy_schwarz_entry_bound`,
  `Matrix.positive_definite_box_bound`, and
  `Matrix.represents_within_box`.
- Rank one: `Matrix.squareForm_represents_only_squares` and
  `Matrix.squareForm_truant`.
- Escalation: `Matrix.escalation_represents_truant`,
  `Matrix.escalation_border_bound`, and `Matrix.escalation_exists`.
- Tree structure: `Matrix.escalator_step`, `Matrix.escalator_split`,
  `Matrix.escalator_symmetric`, and `Matrix.escalator_positive_definite`.
- Low ranks: `Matrix.escalator_rank_one` identifies \(x^2\);
  `Matrix.rank_two_escalators` and `Matrix.escalator_rank_two` classify rank
  two up to isometry as \(x^2+y^2\) or \(x^2+2y^2\). Their truants are
  respectively 3 and 5 (`Matrix.sumOfTwoSquaresForm_truant` and
  `Matrix.squarePlusDoubleSquareForm_truant`).
- Rank-three search boxes:
  `Matrix.sumOfTwoSquares_escalation_border_values` confines each border
  coordinate to \(\{-1,0,1\}\);
  `Matrix.squarePlusDoubleSquare_escalation_first_border_values` and
  `Matrix.squarePlusDoubleSquare_escalation_second_border_values` give
  the raw box \(\{-2,\ldots,2\}\times\{-3,\ldots,3\}\). The coupled theorem
  `Matrix.squarePlusDoubleSquare_escalation_coupled_border_bound` sharpens
  this to \(2a^2+b^2<10\), and
  `Matrix.squarePlusDoubleSquare_escalation_border_pairs` groups the exactly
  23 surviving pairs into the \(a=0\), \(a=\pm1\), and \(a=\pm2\) bands.
  `Matrix.sumOfTwoSquares_escalation_nine_candidates` and
  `Matrix.squarePlusDoubleSquare_escalation_twenty_three_candidates` then
  turn the 9 + 23 coordinate pairs into canonical bordered matrices. Isometry
  deduplication of those 32 raw matrices remains.
- First rank-three truant: the zero-border candidate
  `Matrix.sumOfTwoSquaresPlusTripleSquareForm`, representing
  \(x^2+y^2+3z^2\), represents 1 through 5 and misses 6. Thus
  `Matrix.sumOfTwoSquaresPlusTripleSquareForm_truant` proves its exact truant
  is 6. Generic value-lifting lemmas for diagonal extensions are
  `Matrix.diagonalExtension_represents_parent` and
  `Matrix.diagonalExtension_represents_corner`.

## Module path

Read `quadratic_form` → `integer_quadratic_form` first. Then use
`matrix_direct_sum`, `schur_complement`/`sylvester`, and
`representation_bound` as needed. The escalation spine is
`square_form` → `truant` → `escalation` → `rank_two_escalators` →
`rank_two_truants` → `rank_three_escalation_bounds` →
`rank_three_truants` → `escalator_tree`.
`PLAN_15_THEOREM.md` records unfinished stages.

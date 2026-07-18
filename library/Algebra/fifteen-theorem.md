# Quadratic forms and the Fifteen Theorem

This development formalizes the escalation route toward the Fifteen Theorem.
The final theorem and the rank-three/rank-four classification are not yet
proved; the foundations and the escalator tree through rank two are.

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
  two up to isometry as \(x^2+y^2\) or \(x^2+2y^2\).

## Module path

Read `quadratic_form` → `integer_quadratic_form` first. Then use
`matrix_direct_sum`, `schur_complement`/`sylvester`, and
`representation_bound` as needed. The escalation spine is
`square_form` → `truant` → `escalation` → `rank_two_escalators` →
`escalator_tree`. `PLAN_15_THEOREM.md` records unfinished stages.

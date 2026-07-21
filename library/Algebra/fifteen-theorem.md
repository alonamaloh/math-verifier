# Quadratic forms and the Fifteen Theorem

This development formalizes the escalation route toward the Fifteen Theorem.
The final theorem and the exact rank-four isometry count are not yet proved.
The foundations, the complete deduplicated rank-three classification, and
finite kernel-checked coverage of every resulting rank-four branch are.

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
  turn the 9 + 23 coordinate pairs into canonical bordered matrices.
- Exact rank-three truants: the zero-border candidate
  `Matrix.sumOfTwoSquaresPlusTripleSquareForm`, representing
  \(x^2+y^2+3z^2\), represents 1 through 5 and misses 6. Thus
  `Matrix.sumOfTwoSquaresPlusTripleSquareForm_truant` proves its exact truant
  is 6. The diagonal representative `Matrix.sumOfThreeSquaresForm` represents
  1 through 6 and misses 7, so `Matrix.sumOfThreeSquaresForm_truant` gives
  exact truant 7. The generic integral completion-of-squares theorem
  `Matrix.topShear_pullback_diagonalExtension` shows that every raw border
  \((a,b)\) with \(a^2=b^2=1\) is isometric to this representative; hence
  all four \((\pm1,\pm1)\) candidates have truant 7. The diagonal form
  `Matrix.sumOfTwoSquaresPlusDoubleSquareForm`, representing
  \(x^2+y^2+2z^2\), represents 1 through 13 and misses 14. Thus
  `Matrix.sumOfTwoSquaresPlusDoubleSquareForm_truant` proves its exact
  truant is 14. The parameterized theorem
  `Matrix.sumOfTwoSquaresPlusDoubleSquareForm_isometric_oneUnitBorderCandidate`
  identifies it with every border satisfying \(a^2+b^2=1\); hence all four
  \((\pm1,0),(0,\pm1)\) candidates have truant 14. The nine raw candidates
  over \(x^2+y^2\) are now completely classified into the truant-6,
  truant-7, and truant-14 orbits. Generic value-lifting lemmas for diagonal
  extensions are
  `Matrix.diagonalExtension_represents_parent` and
  `Matrix.diagonalExtension_represents_corner`; truant transport across a
  proved isometry is `Matrix.isometric_isTruant`.
- The 23 candidates over \(x^2+2y^2\) are deduplicated in
  `Algebra/rank_three_orbits` to eight proved representatives:
  \(x^2+2y^2+cz^2\) for \(c=1,\ldots,5\), \(x^2+y^2+z^2\), and
  \(x^2+2y^2+2yz+cz^2\) for \(c=4,5\).
  `Matrix.topShear_pullback_borderedAssembly` gives the generic bordered
  shear identity, and
  `Matrix.squarePlusDoubleSquareCandidate_isometric_shear` specializes it
  to these candidates. The theorem
  `Matrix.squarePlusDoubleSquare_escalation_eight_representatives` is the
  complete reduction from any escalation of \(x^2+2y^2\). The eight exact
  representative truants are \(14,7,10,14,10,7,7,7\) in the displayed
  order. `Matrix.squarePlusDoubleSquareRankThreeRepresentative_truant`
  packages those cases, while
  `Matrix.squarePlusDoubleSquare_escalation_rank_three_truant` concludes
  that every such escalation has truant 7, 10, or 14. Together with
  `Matrix.sumOfTwoSquares_escalation_rank_three_truant`, every rank-three
  escalation over either rank-two parent is now classified.
- Every ternary-parent branch now has an end-to-end rank-four finite
  classifier. Above `x²+y²+z²`,
  `Matrix.sumOfThreeSquaresRankFourEscalation_classified` places every actual
  escalation in one of seven determinant-separated squared-norm classes.
  Above `x²+y²+3z²`,
  `Matrix.sumOfTwoSquaresPlusTripleSquareRankFourEscalation_classified` derives
  the exact bound `3a²+3b²+c² < 18`; signed-coordinate isometries reduce its
  18 top-shear forms to at most 12. Above `x²+y²+2z²`, the analogous exact
  bound leaves 319 borders and 25 determinant-separated forms.
- `Algebra/rank_four_diagonal_family` factors the reusable part of the latter
  argument for every parent `diag(1,1,d)`: coordinate action, quadratic value,
  top-shear reduction, and the fraction-free positive-definiteness bound
  `d a²+d b²+c² < d t` for a child whose corner is `t`.
- `Algebra/rank_four_weighted_diagonal_family` handles all five remaining
  diagonal parents `diag(1,2,d)`, `d=1,…,5`. A single structural coverage
  theorem feeds five generated finite classifiers. Together they certify
  1,877 admissible borders. `Algebra/rank_four_parent_automorphisms` lifts a
  symmetric integral parent automorphism to its bordered child, and
  `Algebra/rank_four_weighted_diagonal_orbits` specializes it to reflection of
  the `d`-weighted coordinate followed by residue reduction, and supplies the
  involutive coordinate swap for `diag(1,2,2)`. The five lists now expose
  25+18+36+68+52 = 199 certified branch alternatives. The same swap carries
  the entire 25-form `diag(1,2,1)` list to the existing `diag(1,1,2)` list, so
  the former predicate is now an alias of the latter and adds no global forms.
- `Algebra/rank_four_odd_diagonal_family` handles the two non-diagonal parents
  `x²+2y²+2yz+Cz²`, `C=4,5`. Its fraction-free adjugate bound is
  `(2C-1)a²+(C-1)b²+(b-c)²+c² < 7(2C-1)`. Centered lattice residues followed
  by a sign isometry reduce 203 and 241 admissible borders to 26 and 32
  alternatives respectively.
- The four deterministic generators are guarded by
  `make rank-four-generated-check`. Across the ten distinct ternary parents the
  current global result names 276 distinct representatives across its coverage
  theorem family.
  This is intentionally not called the expected ≈207-class classification:
  completing that count requires quotienting the remaining lists by larger
  parent automorphism groups and proving cross-list identifications.

## Module path

Read `quadratic_form` → `integer_quadratic_form` first. Then use
`matrix_direct_sum`, `schur_complement`/`sylvester`, and
`representation_bound` as needed. The escalation spine is
`square_form` → `truant` → `escalation` → `rank_two_escalators` →
`rank_two_truants` → `rank_three_escalation_bounds` →
`rank_three_truants` → `escalator_tree` → `rank_three_orbits` →
`rank_three_representative_truants` → `rank_four_pilot` →
`rank_four_diagonal_branch_coverage` → `rank_four_double_diagonal_branch_coverage`
→ `rank_four_weighted_diagonal_branches_coverage` →
`rank_four_odd_diagonal_branches_coverage`.
`PLAN_15_THEOREM.md` records unfinished stages.

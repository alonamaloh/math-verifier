# Quadratic forms and the Fifteen Theorem

This development formalizes the escalation route toward the Fifteen Theorem.
The final theorem is not yet proved. The foundations, the complete
deduplicated rank-three classification, and a kernel-checked cover of every
rank-four escalator by 207 selected normal forms are.

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
- Low-rank critical truants: `Matrix.escalator_rank_zero_truant`,
  `Matrix.escalator_rank_one_truant`, `Matrix.escalator_rank_two_truant`, and
  `Matrix.escalator_rank_three_truant` prove that escalators of ranks zero
  through three have truants in `{1}`, `{2}`, `{3,5}`, and
  `{6,7,10,14}` respectively.  These theorems transport exact truants across
  the classified isometries; the remaining critical value 15 belongs to the
  rank-four universality stage.
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
- The deterministic rank-four generators are guarded by
  `make rank-four-generated-check`. Their ten historical parent branches name
  276 alternatives. The exhaustive discovery tool
  `scripts/classify_rank_four_normal_forms.py` finds 207 integral-isometry
  classes and 69 cross-branch or within-branch identifications. All 69 are
  replayed in the kernel with explicit unimodular matrices and inverse/action
  certificates. `Matrix.escalator_rank_three` unifies the ternary parents,
  and `Matrix.escalator_rank_four` proves that every rank-four escalator is
  isometric to one of the 207 selected normal forms. Pairwise minimality of the
  number 207 remains an exhaustive-search audit; the 207-way cover needed by
  downstream proofs is fully kernel-checked.
- A direct value sweep through 15 isolates six exceptional selected
  rank-four forms. `Algebra/rank_four_exceptional_truants` supplies reusable
  coordinate formulas, compact witness tables, and completed-square bounds;
  its deterministic generated companion checks the final finite tables.
  Two exceptional forms have exact truant 10 and four have exact truant 15.
  `Algebra/rank_four_short_values` and its generated certificate chunks prove
  in the kernel that each of the other 201 selected forms represents every
  value from 1 through 15, using 3,015 explicit witnesses. The resulting
  `Matrix.escalator_rank_four_short_value_classification` transports the
  selected-form result back to every rank-four escalator: it either has exact
  truant 10 or 15, or represents all fifteen test values. Proving those 201
  through-15 forms universal is the remaining rank-four representation-theory
  stage.
- The rank-four universality templates are now algebraically complete.
  `Algebra/rank_four_pilot_universality` identifies the seven selected forms
  above (x^2+y^2+z^2) with the diagonal forms
  (x^2+y^2+z^2+d w^2), (1\le d\le7). The proposition
  `Matrix.ThreeSquareResidualCover(d)` isolates their remaining arithmetic
  input, and `Matrix.selectedRankFourPilot_universal` turns the seven such
  residual-cover facts into universality of the whole selected pilot family.
  `Algebra/rank_four_d2_zero_residue_universality` then transports those
  covers through the integral parity equivalence between three squares and
  `x^2+2y^2+2z^2`, proving six more selected forms conditionally universal.
  `Algebra/rank_four_d2_unit_residue_universality` handles the four selected
  forms `x^2+2y^2+2z^2+2yw+2zw+c w^2`, for `c=2,3,6,7`.  Its reusable
  identity
  `x^2+2y^2+2z^2+2yw+2zw+c w^2 = x^2+p^2+q^2+(c-1)w^2`
  has `p=y+z+w` and `q=y-z`; a modulo-four lemma arranges the parity needed
  to recover `y,z`.  Consequently 17 selected rank-four forms now have
  complete universality proofs conditional only on the three-squares
  converse. `Algebra/rank_four_d2_third_residue_universality` closes the
  remaining six selected `d=2` forms, with residues `(0,1)`, by doubling
  and completing the square:
  `2Q=(2y)^2+(2z+w)^2+2x^2+(2c-1)w^2`.  Taking `w=1` above the finite
  range leaves the odd residual `2(m-c)+1`; twice that residual has the
  automatically admissible shape `4(m-c)+2`, and its oddness supplies the
  parity needed to recover `y,z`.  The existing through-15 tables cover the
  smaller targets.  Thus 23 selected rank-four forms now have complete
  conditional universality proofs, including every selected weighted
  `d=2` form. `Algebra/rank_four_double_unit_residue_universality` treats
  all ten selected `x^2+y^2+2z^2+2zw+c w^2` forms.  The completed identity
  `2Q=(x+y)^2+(x-y)^2+(2z+w)^2+(2c-1)w^2` reduces them directly to three
  squares.  In an obstructed doubled target `4^e(8b+7)`, necessarily
  `e>0`; taking `w=2^(e-1)` leaves `4^(e-1)(32b+k)`, where each of the ten
  constants `k` is 1, 3, or 5 modulo 8.  A parity lemma recovers all three
  completed coordinates from any residual representation.  The conditional
  total is therefore 33 selected rank-four forms.
  `Algebra/rank_four_double_zero_residue_universality` applies the companion
  identity `2Q=(x+y)^2+(x-y)^2+(2z)^2+2c w^2` to ten of the twelve selected
  diagonal extensions of `x^2+y^2+2z^2`.  Their obstruction residuals have
  one of the uniformly admissible even cores
  `2,4,6,8,10,12,14,18,20,24`.  This raises the conditional total to 43;
  a piecewise obstruction-resolver then handles the two nonuniform diagonal
  coefficients `c=6,14`.  The `c=6` resolver switches to a doubled `w` after
  the first obstruction parameter; the `c=14` resolver uses residuals
  `0,32,64` in its three small branches and the admissible core 12
  thereafter.  Thus all 22 selected double forms are conditionally
  universal.  A global coordinate-swap certificate then transports the
  otherwise-unselected `double.r0.c3` proof to `triple.r0.c2`, so the overall
  total is 46 selected rank-four forms.  The diagonal part of the triple
  branch now uses Dirichlet's independent converse for
  `x²+y²+3z²`, whose exceptional shape is `9^a(9b+6)`.  A reusable
  9-adic separation lemma handles coefficients 3, 4, and 5 directly; for
  coefficient 6, a second fourth-coordinate choice handles the case where
  the inner quotient is itself exceptional.  All five selected diagonal
  triple forms are therefore conditionally universal, raising the total to
  50.  For the five residue-one triple forms, completing the square changes
  the ternary part to `x²+3y²+3z²`.  The library now proves that this
  form represents `n` whenever `x²+y²+3z²` represents `3n`, including the
  modulo-three descent and the sign choice that recovers `3z+w`.  Its
  obstruction `9^a(3b+2)` is therefore derived from the same Dirichlet
  converse, and one uniform residual calculation closes all five forms.
  Thus all ten selected triple forms are conditionally universal, and the
  selected total is 55.  The eight diagonal extensions of
  `x²+2y²+3z²` are now also conditionally universal from the classical
  converse whose exceptional set is `4^a(16b+10)`.  For coefficients
  `3,…,9`, subtracting `c(2^a)^2` leaves the admissible core `10-c`; the
  core 4 case is handled by extracting one further factor of four.  For
  coefficient 10, a three-way split on the obstruction parameter leaves
  residual 0, a pure square, or core 2.  This closes the complete selected
  weighted-`d=3`, zero-residue chunk and raises the selected total to 63.
  The seven selected forms with second residue one and third residue zero
  reduce instead to `x²+2y²+6z²`, whose exceptional set is
  `4^a(8b+5)`.  Completing the square gives
  `2Q=(2y+w)²+2x²+6z²+(2c-1)w²`; the equation itself forces the
  represented first root to have the parity of `w`, so no extra congruence
  hypothesis is needed.  One uniform obstruction residual closes all seven
  coefficients and raises the selected total to 70.
  The forms with second residue zero and third residue one are handled
  by the one-three-six local converse in
  `Algebra/rank_four_weighted_d3_third_unit_universality`.  The identity
  `3Q=(3z+w)^2+3x^2+6y^2+(3c-1)w^2` makes the square-residue condition modulo
  three automatic, while explicit 4-adic residual covers settle all eight
  coefficients `c=3,...,10`.  The two exceptional covers split the small
  unscaled quotients for `c=5` and the first two 4-adic scales for `c=9`
  before reaching their uniform residual cores.  The import-only
  `Algebra/rank_four_weighted_d3_third_unit_covers` collects these results,
  raises the selected conditional total to 78.
  `Algebra/rank_four_completed_cover_universality` gives fraction-free
  completed-square interfaces for all other constructors. Its scaled-square,
  weighted, and odd cover predicates account for the 32, 140, and 28
  nonpilot selected forms. The identities and matrix witnesses are proved once;
  future per-form work consists only of explicit arithmetic/congruence cover
  facts.
- The obstruction half of Legendre's three-squares theorem is now complete.
  `Algebra/three_squares_obstruction` classifies square residues modulo eight,
  and a deterministic 27-case certificate proves that three squares cannot
  sum to seven modulo eight. `Algebra/three_squares_descent` proves the
  modulo-four parity step, while `Algebra/three_squares_power_descent` extracts
  even coordinates and cancels a common factor of four. Consequently
  `Integer.four_power_times_eight_plus_seven_not_three_squares` and its
  matrix-level companion exclude every value of the form
  `4^a(8b+7)` from `Matrix.sumOfThreeSquaresForm`. The converse direction of
  the three-squares theorem remains the substantial representation-theory
  obligation. `Algebra/three_squares_theorem` packages that converse as
  `Matrix.ThreeSquaresConverse`. Elementary forbidden-shape arithmetic in
  `Algebra/three_squares_obstruction_arithmetic` and seven independently
  cached `Algebra/three_squares_residual_cover_*` modules prove every residual
  cover for `d=1,...,7` from that single converse. Thus
  `Matrix.selectedRankFourPilot_universal_of_three_squares_converse` makes the
  whole seven-form pilot family universal as soon as the converse is supplied.

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
`rank_four_odd_diagonal_branches_coverage` →
`rank_three_global_classification` → `critical_truants` and
`rank_four_global_classification` → `rank_four_exceptional_truants` →
`rank_four_exceptional_truants_generated` → `rank_four_short_values` →
`rank_four_short_values_generated` → `rank_four_pilot_universality`.
Then use `rank_four_completed_cover_universality` for the other rank-four
families. The elementary three-squares obstruction is layered as
`three_squares_obstruction` → `three_squares_mod_eight` →
`three_squares_mod_eight_generated` → `three_squares_base_obstruction` →
`three_squares_mod_four` → `three_squares_descent` →
`three_squares_power_descent` → `three_squares_full_obstruction` →
`three_squares_theorem` → `three_squares_obstruction_arithmetic` →
`three_squares_residual_cover_common` and the seven
`three_squares_residual_cover_*` cases → `three_squares_residual_covers`.
`PLAN_15_THEOREM.md` records unfinished stages.

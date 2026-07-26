# Algebra

This directory contains both abstract algebra and finite-dimensional linear
algebra. Prefer bundled structures (`Group`, `Ring`, `CommutativeRing`, `Field`)
in reusable developments; the unbundled predicates (`IsGroup`, `IsRing`,
`IsField`) are mainly for constructing instances.

The quadratic-form vocabulary lives here; the Fifteen Theorem built on top
of it lives outside the library, in `projects/FifteenTheorem/` — see
"Quadratic forms" below.

## Main definitions

- `IsMonoid`, `IsGroup`, `IsAbelianGroup`, `IsRing`, `IsCommutativeRing`, and
  `IsField` in `monoid`, `group`, `ring`, and `field`
- Bundles `Group`, `Ring`, `CommutativeRing`, and `Field` in the corresponding
  `*_bundle` modules
- `IsHomomorphism`, `IsSubgroup`, `IsNormalSubgroup`, `QuotientGroup`, and
  `GroupHomomorphism.kernel` / `.image`
- Ring divisibility, `Ring.IsIdeal`, `IntegralDomain`, `EuclideanDomain`, and
  `PrincipalIdealDomain`

Flattened bundle projections such as `Ring.add_associative`,
`Field.multiply_commutative`, and `Group.inverse_left` are the normal theorem
interface.

## Main theorems

- Group cancellation and inverse laws in `group_lemmas`
- The first, second, and third isomorphism developments in their named modules
- `PrincipalIdealDomain.bezout` and
  `PrincipalIdealDomain.irreducible_is_prime`
- `EuclideanDomain.ideal_is_principal` (every ideal of a Euclidean domain
  is principal)
- `IntegralDomain.prime_factorization_unique`
- `CommutativeRing.binomial_theorem`

The factorization tower is:
`IntegralDomain → EuclideanDomain → PrincipalIdealDomain`, with irreducibility,
prime elements, associates, and uniqueness handled in `irreducible`,
`associate`, `factorization_list`, and `unique_factorization`.

## Linear algebra

- `VectorSpace(f)`, scalar action `•`, `IsLinearMap`, `Subspace`, and
  `LinearMap.kernel` / `.image`
- `VectorSpace.Spans`, `VectorSpace.LinearlyIndependent`,
  `VectorSpace.IsBasis`, and `VectorSpace.FinitelyGenerated`
- Coordinate families and matrices: `CoordinateSpace`, `Matrix`,
  `Matrix.multiply`, `Matrix.identity`, and `Matrix.applyVector`
- Determinant and characteristic polynomial:
  `Matrix.determinant`, `Matrix.characteristicPolynomial`, and
  `Matrix.adjugate`

Headline results include `VectorSpace.extend_to_basis`,
`LinearMap.rank_nullity`, `Matrix.determinant_multiply`,
`Matrix.multiply_adjugate`, and the two Freek-100 entries
`Matrix.cayley_hamilton` (#49) and `Matrix.cramer` (#97).

## Quadratic forms

Symmetric integer matrices and their forms (`Matrix.IsSymmetric`,
`Matrix.quadraticForm`), `Matrix.Represents`, `Matrix.IsUniversal`,
`Matrix.IsPositiveDefinite`, `Matrix.IsIsometric`, the least missed value
`Matrix.truant`, and Conway–Schneeberger `Matrix.IsEscalation` /
`Matrix.IsEscalator`. Landed here: the truant and escalation machinery,
isometry-transport of truants, universality and positive-definiteness, the
rank-two and rank-three classifications, and the general
rank-one-through-four `diagonal_forms`.

The three-squares development went to the project with everything else that
only the fifteen theorem uses. Its biconditional rests on a converse nothing
discharges, and even its proved half is
spelled `Matrix.Represents(Matrix.sumOfThreeSquaresForm, (n : ℤ))` rather
than `∃ x y z : ℤ. n = x² + y² + z²` — fifteen-theorem vocabulary, not
something a number theorist would find here. When the converse lands,
Legendre's theorem earns a library home in the natural spelling.

The Fifteen Theorem itself — the rank-four classification, the 207-form
cover, the determinant-seven converses, and their machine-generated
certificate tables — is **not part of the library**. It lives in
`projects/FifteenTheorem/` (built by `make projects`), because ~320k lines
of generated case tables would otherwise be re-verified on every elaborator
change for no library benefit. Map: **`projects/FifteenTheorem/fifteen-theorem.md`**;
stage-by-stage plan: **`PLAN_15_THEOREM.md`** (repo root).

## Where to look

- Groups: `group_bundle` through `third_isomorphism`, plus `group_action`
- Rings and fields: `ring_bundle`, `commutative_ring_bundle`, `field_bundle`
- Factorization: `integral_domain` through `pid_unique_factorization`
- Spans and dimension: `vector_space`, `linear_combination`, `span`,
  `basis_pruning`, `exchange_lemma`, `dimension`, `rank_nullity`
- Matrices: `matrix`, `matrix_ring`, `matrix_vector`, `matrix_transpose`,
  `determinant*`, `adjugate`, `characteristic_polynomial`, `cayley_hamilton`
- Quadratic forms and escalation: `quadratic_form`, `integer_quadratic_form`,
  `square_form`, `diagonal_forms`, `truant`, `escalation`, `escalator_tree`,
  `rank_two_*`, `rank_three_*`, `gram`, `unimodular`
- Finite permutations and signs: `finite_permutation`, `permutation_*`

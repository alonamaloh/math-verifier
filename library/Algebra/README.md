# Algebra

This directory contains both abstract algebra and finite-dimensional linear
algebra. Prefer bundled structures (`Group`, `Ring`, `CommutativeRing`, `Field`)
in reusable developments; the unbundled predicates (`IsGroup`, `IsRing`,
`IsField`) are mainly for constructing instances.

For the quadratic-form and Fifteen Theorem development, start with
[fifteen-theorem.md](fifteen-theorem.md).

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
- `EuclideanDomain.to_principal_ideal_domain`
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
- Integer quadratic forms: `Matrix.quadraticForm`, `Matrix.Represents`,
  `Matrix.IsUniversal`, `Matrix.IsPositiveDefinite`, and `Matrix.IsIsometric`

Headline results include `VectorSpace.extend_to_basis`,
`LinearMap.rank_nullity`, `Matrix.determinant_multiply`,
`Matrix.multiply_adjugate`, and `Matrix.cayley_hamilton`.

## Where to look

- Groups: `group_bundle` through `third_isomorphism`, plus `group_action`
- Rings and fields: `ring_bundle`, `commutative_ring_bundle`, `field_bundle`
- Factorization: `integral_domain` through `pid_unique_factorization`
- Spans and dimension: `vector_space`, `linear_combination`, `span`,
  `basis_pruning`, `exchange_lemma`, `dimension`, `rank_nullity`
- Matrices: `matrix`, `matrix_ring`, `matrix_vector`, `matrix_transpose`,
  `determinant*`, `adjugate`, `characteristic_polynomial`, `cayley_hamilton`
- Quadratic forms and escalation: see [fifteen-theorem.md](fifteen-theorem.md)
- Finite permutations and signs: `finite_permutation`, `permutation_*`

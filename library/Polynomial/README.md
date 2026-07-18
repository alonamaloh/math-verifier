# Polynomials

Polynomials are finite coefficient lists, low degree first, quotiented by
coefficientwise equality so trailing zeros disappear. The coefficient ring is
passed as a bundled `Ring`.

## Main definitions

- `Polynomial(R, zero)`, `Polynomial.Coefficients`, `Polynomial.make`, and
  coefficient lookup `Polynomial.nth` in [basics.math](basics.math)
- `Polynomial.add`, `.negate`, `.subtract`, `.multiply`, `.zero`, and `.one`
- Bundled polynomial ring `Polynomial.ring`
- Public coefficient function `Polynomial.coefficientOf`
- Degree bound predicate `Polynomial.DegreeLessThan`; degree is intentionally
  not a total function in the core development
- `Polynomial.monomial`, `Polynomial.IsUnit`, and
  `Polynomial.IsIrreducible`

## Main theorems

- Coefficient extensionality: `Polynomial.equal_of_coefficientOf_equal`
- Ring laws packaged by `Polynomial.is_ring`; commutative structure in
  `Polynomial.commutative`
- Multiplication coefficients and laws in `multiply_coefficient` and
  `multiply_laws`
- Degree: `Polynomial.HasDegree_product` and the degree-bound closure lemmas
- Division: `Polynomial.division_with_remainder`
- Bézout: `Polynomial.gcd_bezout`
- Quotient field: `Polynomial.quotient_is_field`

`division`, `bezout`, and `quotient_field` assume field-like invertibility as
needed. `degree_function` adds a chosen numeric degree only under stronger
decidability hypotheses.

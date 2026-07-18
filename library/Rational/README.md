# Rationals

Rationals are fractions of integers with a nonzero denominator, quotiented by
cross multiplication. Use `ℚ` and its public operations; representatives are a
construction boundary.

## Main definitions

- `Rational` / `ℚ`, `RationalRepresentative`, and `RationalEquivalent` in
  [basics.math](basics.math)
- `Rational.add`, `Rational.negate`, `Rational.subtract`,
  `Rational.multiply`, and `Rational.divide`
- Embedding `Integer.to_rational`; `Natural.divide` is rational-valued division
- Sign and order: `Rational.IsNonneg`, `Rational.LessOrEqual`, and
  `Rational.LessThan`
- `Rational.absolute_value`, `Rational.power`, and the reciprocal function
- Bundles `Rational.ring_bundle` and `Rational.field_bundle`

## Main theorems

- Ring and field interfaces: `Rational.is_field`, `Rational.divide_cancel`,
  and `Rational.divide_cross_multiply`
- Embedding preservation for addition, multiplication, negation, subtraction,
  and order
- `Rational.triangle_inequality` and
  `Rational.absolute_value_multiplicative`
- Order linearity: `Rational.LessOrEqual.linear`
- Archimedean property: `Rational.archimedean_for_positives`
- Power estimates: `Rational.power_bernoulli` and
  `Rational.power_decay_witness`
- Countability: `Rational.is_enumerable`

Analysis-oriented helpers live in `linearity`, `minimum`, `positive`,
`triangle_more`, `archimedean`, and `reciprocal_function`.

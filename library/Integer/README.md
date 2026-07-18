# Integers

Integers are a quotient of pairs of naturals: `(a, b)` represents `a-b`.
Consumers should use `ℤ`, arithmetic operators, and the public theorems rather
than `IntegerRepresentative`.

## Main definitions

- `Integer` / `ℤ` and equivalence `IntegerEquivalent` in [basics.math](basics.math)
- `Integer.add`, `Integer.negate`, `Integer.subtract`, and `Integer.multiply`
- Embedding `Natural.to_integer`
- Order predicates `Integer.IsNonneg`, `Integer.LessOrEqual`, and
  `Integer.LessThan`
- Absolute values `Integer.absolute_value : ℤ → ℤ` and
  `Integer.absolute_value_natural : ℤ → ℕ`
- Divisibility `Integer.divides`
- Honest natural subtraction `Natural.subtract : ℕ → ℕ → ℤ`

## Main theorems

- Ring laws in [ring.math](ring.math), packaged by `Integer.is_ring` and
  `Integer.is_commutative_ring`
- Embedding laws `Natural.to_integer.add_preserves`,
  `.multiply_preserves`, `.injective`, and order preservation/reflection
- `Integer.sign_split` and `Integer.triangle_inequality`
- `Integer.absolute_value_multiplicative`
- `Integer.multiply_cancel_right_by_nonzero` and `Integer.multiply_nonzero`
- Positive-factor cancellation:
  `Integer.cancel_le_by_positive` and `Integer.cancel_lt_by_positive`
- `Integer.divide_balanced` for nearest/balanced quotient and remainder
- `Integer.sum_of_squares_zero`

`Integer.absolute_value` is implemented from `Natural.distance`; the
natural-valued form is the norm used by Euclidean and divisibility arguments.

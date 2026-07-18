# Finite fields

`FiniteField(p, f)` is `F_p[x]/(f)`, implemented by composing `IntegerMod`,
`Polynomial`, and `RingModulo`. The current development constructs the field
from a supplied irreducible polynomial; it does not prove that such a
polynomial exists for every degree.

## Main definitions

- `IntegerMod.polynomial_ring` and
  `IntegerMod.polynomial_commutative_ring`
- `FiniteField(p, f)`

## Main theorems

- `FiniteField.is_commutative_ring`: the quotient is a commutative ring for any
  modulus polynomial
- `FiniteField.is_field`: if `p` is prime and `f` is irreducible over `F_p`,
  the quotient is a field

Read [basics.math](basics.math) for the assembled carrier and
[field.math](field.math) for the instantiation of the polynomial quotient-field
theorem.

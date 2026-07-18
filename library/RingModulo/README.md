# Quotient rings

`RingModulo(c, m)` is a commutative ring modulo the principal ideal generated
by `m`: elements are quotient classes under divisibility of differences.
This construction underlies `IntegerMod`, `ComplexNumber`, `GaussianInteger`,
and `FiniteField`.

## Main definitions

- Congruence `Ring.CongruentModulo`
- Quotient carrier `RingModulo(c, m)`
- Operations `RingModulo.add`, `.negate`, `.subtract`, `.multiply`, `.zero`,
  and `.one`

## Main theorems

- Equivalence: `Ring.CongruentModulo.reflexive`, `.symmetric`, and `.transitive`
- Well-defined operations: `Ring.CongruentModulo.add_respects`,
  `.negate_respects`, and `.multiply_respects`
- Ring laws in [ring.math](ring.math)
- Structure witnesses `RingModulo.is_ring` and
  `RingModulo.is_commutative_ring`
- Modulus relation `RingModulo.modulus_is_zero`

The base is a bundled `CommutativeRing`; its commutativity proof is recovered
from the quotient's type rather than passed separately to every operation.

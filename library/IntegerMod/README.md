# Integers modulo a natural

`IntegerMod(n)` is `ℤ/nℤ`, constructed as integer representatives modulo
divisibility of their difference. It is a commutative ring for every modulus
and a field when the modulus is prime.

## Main definitions

- `Integer.CongruentModulo` and `IntegerMod(modulus)` in [basics.math](basics.math)
- Quotient operations and class constructor in `operations`
- Natural representative machinery in `representative` and residue lists in
  `residues`
- Unit predicate and unit residue enumeration in `units` and `euler_fermat`

## Main theorems

- Ring structure: `IntegerMod.is_ring` and `IntegerMod.is_commutative_ring`
- Prime field: `IntegerMod.nonzero_invertible` and `IntegerMod.is_field`
- Units: `IntegerMod.unit_of_coprime` and
  `IntegerMod.coprime_of_unit_representative`
- Wilson: `IntegerMod.wilson`, `Natural.wilson`, and
  `Natural.prime_of_divides_factorial_plus_one`
- Fermat: the results in [fermat_little.math](fermat_little.math)
- Euler: `IntegerMod.euler_fermat` and `Natural.euler_fermat`
- Square root of `-1` for the relevant prime moduli in
  `square_root_of_minus_one`

Use [field.math](field.math) when the proof needs cancellation or inverses; the
plain ring modules do not assume primality.

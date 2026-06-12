# Freek's 100 theorems — what the library has

The library tracks [Freek Wiedijk's *Formalizing 100 Theorems*
list](https://www.cs.ru.nl/~freek/100/) as a goal thread. This file is
the index of the entries verified so far: the list number, the headline
theorem(s) as declared, and the file where each lives.

**15 of 100** as of 2026-06-11.

| # | Theorem | Declaration | File |
|---|---------|-------------|------|
| 1 | The irrationality of √2 | `Natural.sqrt_two_irrational` | `library/Natural/sqrt_two_irrational.math` |
| 3 | The denumerability of the rational numbers | `Rational.is_enumerable` | `library/Rational/enumerable.math` |
| 10 | Euler's generalization of Fermat's little theorem | `Natural.euler_fermat`, `IntegerMod.euler_fermat` | `library/IntegerMod/euler_fermat.math` |
| 11 | The infinitude of primes | `Natural.infinitely_many_primes` | `library/Natural/euclid.math` |
| 20 | All primes ≡ 1 mod 4 are sums of two squares | `Natural.prime_one_mod_four_sum_of_two_squares` | `library/GaussianInteger/fermat_two_squares.math` |
| 22 | The non-denumerability of the continuum | `Real.not_enumerable`, `Real.enumeration_misses_a_real` | `library/Real/uncountable.math` |
| 34 | Divergence of the harmonic series | `Real.harmonic_series_diverges` | `library/Real/harmonic_series.math` |
| 42 | Sum of the reciprocals of the triangular numbers | `Real.triangular_reciprocals_sum_to_two` | `library/Real/triangular_series.math` |
| 51 | Wilson's theorem | `Natural.wilson` (and the converse, `Natural.prime_of_divides_factorial_plus_one`) | `library/IntegerMod/wilson.math` |
| 63 | Cantor's theorem | `Cantor.no_surjection_onto_powerset` | `library/Set/cantor.math` |
| 66 | Sum of a geometric series | `Real.geometric_series` | `library/Real/series.math` |
| 69 | Greatest common divisor algorithm | `Natural.bezout` (Euclidean recursion; gcd via Bézout), with the `Natural.is_gcd` theory | `library/Natural/bezout.math`, `library/Natural/gcd.math` |
| 78 | The Cauchy–Schwarz inequality | `Real.cauchy_schwarz` | `library/Real/cauchy_schwarz.math` |
| 79 | The intermediate value theorem | `Real.intermediate_value` | `library/Real/intermediate_value.math` |
| 80 | The fundamental theorem of arithmetic | `Natural.fundamental_theorem_of_arithmetic` | `library/Natural/prime_factorization_unique.math` |

## Near-term targets

The finite-sum toolkit in `library/Real/series.math` is complete
(split, comparison, linearity, telescoping, constant blocks). **#38** (arithmetic/geometric mean) waits on a √ construction.
Also reachable: **#25** (Schröder–Bernstein, on the Set/equinumerous
machinery), **#44** (binomial theorem, factorials already in place).

When a new entry lands, add the row here and tag the theorem's file
header with the list number.

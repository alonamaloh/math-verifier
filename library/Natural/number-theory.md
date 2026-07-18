# Natural number theory

## Three kinds of division

- `Natural.floor_divide(n, d)` and `Natural.modulo(n, d)` are total functions.
  Their main interface is `Natural.floor_divide_modulo_decompose`,
  `Natural.modulo_bound`, `Natural.divides_implies_modulo_zero`, and
  `Natural.modulo_zero_implies_divides`.
- `Natural.divide_with_remainder(divisor, positiveDivisor, dividend)` gives
  existential `q, r` with `dividend = q*divisor + r` and `r < divisor`.
- `Natural.divide` is not natural floor division; it is the rational-valued
  operation defined later in `Rational/natural_division.math`.

`Natural.divides(d, n)` / `d ∣ n` means `n = d*q` for some natural `q`.
Useful closure theorems are `Natural.divides_reflexive`,
`Natural.divides_transitive`, `Natural.divides_add`, and
`Natural.divides_multiple_left`.

## GCD and coprimality

`Natural.is_gcd(g, a, b)` is the universal property: `g` divides both inputs
and every common divisor divides `g`. `Natural.gcd(a, b)` is the Euclidean
algorithm, with:

- `Natural.gcd_is_gcd`
- `Natural.gcd_divides_left`, `Natural.gcd_divides_right`
- `Natural.gcd_greatest`

`Natural.bezout(a, b)` proves the existential predicate `Natural.has_bezout`:
the gcd is an integer linear combination of `a` and `b`.
`Natural.coprime(a, b)` means `Natural.is_gcd(1, a, b)`;
`Natural.coprime_bezout` is the coefficient form used by modular arithmetic.

## Primes and factorization

`Natural.is_prime(p)` means `2 ≤ p` and every divisor of `p` is `1` or `p`.
The main accessors are `Natural.is_prime.at_least_two`,
`Natural.is_prime.positive`, and `Natural.is_prime.divisor_one_or_self`.

The central results are:

- `Natural.has_prime_divisor`: every `n ≥ 2` has a prime divisor.
- `Natural.prime_divides_product`: Euclid's lemma.
- `Natural.prime_factorization_exists_list`: factorization into a `List(ℕ)`.
- `Natural.prime_factorization_unique`: equality of products of prime lists
  implies `List.Permutation`.
- `Natural.fundamental_theorem_of_arithmetic`: existence and uniqueness.
- `Natural.infinitely_many_primes`: a prime exists outside any given prime list.

Factorization products use `Natural.listProduct`. Specialized results include
`Natural.is_prime_two`, `Natural.prime_square_factor`, and
`Natural.sqrt_two_irrational`.

## Combinatorial arithmetic

`Natural.factorial` (`n!`) has recurrence `Natural.factorial_add_one` and
positivity `Natural.factorial_positive`. `Natural.binomial(n, k)` follows
Pascal recursion; use `Natural.binomial_zero_right`,
`Natural.binomial_zero_succ`, `Natural.binomial_pascal`, and
`Natural.binomial_overflow`. Its factorial identity is
`Natural.binomial_factorial`.

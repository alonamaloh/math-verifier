# Natural numbers

Start here when a proof uses `ℕ`. This directory defines the sealed natural
number type, arithmetic and order, then builds division, finite counting tools,
and elementary number theory. Imports are fine-grained: import the module that
owns the definitions or theorems you use.

## Consumer rule: do not use `successor`

Modules outside `Natural/` must treat `ℕ` as an arithmetic type, not as an
exposed inductive type. Write `n + 1` or `1 + n`, never `successor(n)`. Likewise,
use ordinary `by induction`, arithmetic case splits such as `n = 0` /
`n = 1 + k`, and the named theorems below rather than constructor-level
recursion or pattern matching.

The seal is implemented in [basics.math](basics.math): public `Natural` is an
opaque alias over the inductive `Natural.Raw`. The names `zero` and `successor`
exist to implement the Natural boundary, but `successor` is not part of the
consumer vocabulary. The bridge modules [one_plus_induction.math](one_plus_induction.math)
and [peano.math](peano.math) publish arithmetic-facing induction, case, and
zero/nonzero facts across that boundary.

For more detail, see [core.md](core.md) for arithmetic, order, induction, and
recursion, or [number-theory.md](number-theory.md) for division, gcd, and primes.

## Main definitions

- **Natural number** — `Natural` / `ℕ` in [basics.math](basics.math).
  `Natural.Raw`, `zero`, and `successor` are construction-level names;
  consumers use numerals and arithmetic.
- **Addition and multiplication** — `Natural.add` (`+`) and `Natural.multiply`
  (`*`) in [basics.math](basics.math).
- **Strict and non-strict order** — `Natural.LessThan` (`<`) and
  `Natural.LessOrEqual` (`≤`) in [order.math](order.math). Strict order is opaque;
  use `Natural.lt_intro` and `Natural.lt_elim` instead of unfolding it.
- **Truncated subtraction** — `Natural.monus` (`∸`) in [monus.math](monus.math).
  This is `max(0, a-b)`; ordinary subtraction belongs to `Integer`.
- **Floor quotient and remainder** — `Natural.floor_divide` and `Natural.modulo`
  in [floor_divide.math](floor_divide.math). Argument order is `(dividend,
  divisor)`; division by zero returns `0`, while modulo by zero returns the
  dividend.
- **Divisibility and primality** — `Natural.divides` (`∣`) in
  [divisibility.math](divisibility.math), and `Natural.is_prime` in
  [prime.math](prime.math).
- **Greatest common divisor** — the predicate `Natural.is_gcd` in
  [gcd.math](gcd.math), and the function `Natural.gcd` in
  [euclidean_algorithm.math](euclidean_algorithm.math).
- **Powers, factorials, and binomial coefficients** — `Natural.power` (`^`),
  `Natural.factorial` (`!`), and `Natural.binomial` in
  [power.math](power.math), [factorial.math](factorial.math), and
  [binomial.math](binomial.math).
- **Eventually** — `Natural.Eventually` in [eventually.math](eventually.math),
  the threshold-based predicate behind `eventually (n). P(n)`.

## Main theorems

- Arithmetic laws: `Natural.add_commutative`, `Natural.add_associative`,
  `Natural.multiply_commutative`, `Natural.multiply_associative`, and
  `Natural.distributivity_left` in [arithmetic.math](arithmetic.math).
- Order interface: `Natural.lt_trichotomy`, `Natural.lt_transitive`,
  `Natural.LessOrEqual.transitive`, and `Natural.le_antisymmetric` in
  [order.math](order.math) and [subtraction.math](subtraction.math).
- Induction: `Natural.induction_on_one_plus` and `Natural.strong_induction` in
  [one_plus_induction.math](one_plus_induction.math) and
  [strong_recursion.math](strong_recursion.math).
- Division: `Natural.floor_divide_modulo_decompose`, `Natural.modulo_bound`,
  and the existential `Natural.divide_with_remainder`.
- GCD and Bézout: `Natural.gcd_is_gcd` and `Natural.bezout`.
- Primes: `Natural.prime_divides_product`,
  `Natural.fundamental_theorem_of_arithmetic`, and
  `Natural.infinitely_many_primes`.
- Small-square bounds in [multiply_bounds.math](multiply_bounds.math):
  `Natural.below_two`, `Natural.positive_below_five`,
  `Natural.square_below_two`/`_four`/`_six`/`_ten`,
  `Natural.two_is_not_a_square`, `Natural.three_not_sum_of_two_squares`,
  and `Natural.five_not_square_plus_double_square`.

## Where to look

- Constructors and computation: `basics`, `peano`, `arithmetic`
- Order and induction: `order`, `add_order`, `one_plus_induction`,
  `strong_recursion`, `well_founded`
- Subtraction and bounds: `subtraction`, `monus`, `distance`, `maximum`,
  `multiply_order`, `multiply_bounds`
- Decisions and data-producing comparison: `decide`, `decide_divides`,
  `compare`, `classical_decidable`
- Division and gcd: `floor_divide`, `division`, `divisibility`, `gcd`,
  `euclidean_algorithm`, `bezout`
- Primes and factorization: `prime`, `prime_split`, `prime_divisor`,
  `prime_divides_product`, `factorization`, `prime_factorization_unique`
- Finite/combinatorial tools: `power`, `factorial`, `binomial`, `triangular`,
  `list_product`, `pairing`, `totient`
- Standalone results: `euclid` (infinitely many primes),
  `sqrt_two_irrational`

## Downstream use

`Integer` uses `Natural.distance` for absolute value; `Rational` relies on
multiplicative cancellation; `Set` uses `Natural.compare_strict` and
quotient/remainder uniqueness for finite bijections. Analysis over `Real` and
`ComplexNumber` repeatedly uses `Natural.maximum`, `Natural.Eventually`,
comparison, powers, factorials, and binomial coefficients. Algebra and modular
arithmetic use division, gcd, primes, and totients.

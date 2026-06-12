# Library guide

A map of `library/`. Imports flow **up** the dependency layers: a module
may import from its own layer and below, never above. (Build/layout depth:
`docs/conventions/build-and-layout.md`.)

## Foundations

- **`axioms.math`** — the small set of assumed axioms everything rests on.
- **`Logic/`** — the logical connectives as inductives/definitions: `And`,
  `Or`, `Not`, `Exists`, plus `excluded_middle` / classical `Decidable`,
  function/extensionality lemmas, `product`/`sum`/`sigma`, and the
  `Quotient` type (the workhorse for constructed number systems).
- **`Equality/`** — equality and its transport/congruence machinery.

## Numbers

- **`Natural/`** (the largest area) — Peano `Natural`: `arithmetic`,
  `order`, `divisibility`, `gcd`/`bezout`, primality and prime
  factorization, division-with-remainder + `modulo`, truncated subtraction
  (`monus`), `strong_recursion`, and decidability of `=`/`≤`/`∣`.
- **`Integer/`** — ℤ as a quotient of `Natural × Natural`: ring laws,
  `order`, `sign`, `absolute_value`, divisibility, the `Natural ↪ Integer`
  embedding.
- **`Rational/`** — ℚ as a quotient of `Integer × nonzero`: `field`,
  `order`, `absolute_value`, triangle inequality.
- **`Real/`** — ℝ as Cauchy sequences of rationals: `field`, `order`,
  `supremum`, `convergence`, `absolute_value`.

## Abstract algebra

- **`Algebra/`** — bundled structures and their theory: `monoid`, `group`
  (+ homomorphisms, subgroups, normal subgroups, quotient groups, the
  isomorphism theorems), `ring`/`commutative_ring`, `field`,
  `integral_domain` → `principal_ideal_domain` → `unique_factorization`,
  `euclidean_domain`, `ideal`, `group_action`.
- **`Polynomial/`** — the polynomial ring over a coefficient ring:
  `addition`/`multiplication`, `degree` (+ degree-of-product), `division`,
  `bezout`, `irreducible`, `units`, `quotient_field`.
- **`RingModulo/`** — the generic quotient `R / (ideal)` construction that
  the concrete towers below instantiate.

## Constructed number systems (the "towers")

Each builds a new structure on the layers above and proves its algebraic
laws:

- **`IntegerMod/`** — ℤ/(m): ring, and a field when m is prime.
- **`ComplexNumber/`** — ℂ = ℝ[x]/(x²+1): commutative ring, field, `i²=−1`,
  coordinates (re, im) out of the quotient, the modulus |z| = √(re²+im²)
  with multiplicativity, the triangle inequality, and coordinate bounds,
  completeness (every Cauchy sequence converges, coordinate-wise), and the
  complex exponential exp(z) = Σ zᵏ/k! (limit by definite description,
  dominated in modulus by the real series at |z|).
- **`GaussianInteger/`** — ℤ[i] = ℤ[x]/(x²+1).
- **`FiniteField/`** — F_{p^k} = F_p[x]/(f) for irreducible f.
- **`PAdic/`** — the p-adic numbers with their absolute value.

## Other

- **`Set/`** — the finite-cardinality / counting layer: `Equinumerous`,
  `HasSize`, pigeonhole, sum/product/power rules, Cantor, enumerability.
- **`Lists/`** — `NaturalList` and `Permutation`.

## Not math content

- **`Test/`** — feature exercises for the elaborator (verified by
  `make tests`, not `make library`). The place to look for a worked
  example of any surface construct.
- **`ErrorTest/`** — intentionally-broken proofs for the error-message
  regression suite (`make error-tests`); see `docs/error_message_corpus.md`.

## Finding things

- By goal shape: `kernel search --goal <pattern>` / `--mentions <name>`;
  a failing proof also suggests candidate lemmas in its error.
- The `MEMORY.md` notes (per-area status) track what each tower has proved
  and what's next.

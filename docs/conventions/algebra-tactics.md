# Algebra tactics: ring, field, linear_combination

The `ring`/`field` tactics, foundational-vs-derived ring lemmas, and `linear_combination` (ring with equational hypotheses).

*(Part of the project conventions; see `CLAUDE.md` for the index.)*

## `ring` — try it first

`ring` (polynomial normalisation: distributivity, commutativity,
associativity, like-term collection at arbitrary signed integer
coefficients, total cancellation, unit-multiplication strip, subtract
sugar, and Integer numeric literals) handles essentially every
commutative-ring identity you'd write by hand in a calc block. The
default for any equality between ring expressions on Natural, Integer,
Rational, Real, or PAdic is `:= ring` (top-level) or `(ring : LHS =
RHS)` (as a `rewrite` equation). Reach for explicit `add_commutative`
/ `add_associative` / `congruenceOf` ONLY after ring fails with a
real limitation:

- **Halving / division.** `Rational.halve(ε) + Rational.halve(ε) = ε`
  is NOT a ring identity — it needs `Rational.halve_doubled` (which
  internally is a non-ring fact: `halve(x) := x * (1/2)` and the `1/2`
  identity isn't a polynomial relation). Same for any reciprocal
  reasoning — use the `field(h1, h2, …)` tactic instead, which extends
  ring with `t_i * reciprocal_function(t_i) = 1` side-relations from
  the supplied nonzero-hypotheses.
- **`ring` requires the carrier's `.add`, `.multiply`, and ring laws
  in scope.** For Real proofs, that typically means importing
  `Real.addition`, `Real.multiplication`, `Real.negation`, `Real.ring`,
  AND `Real.algebra` (which provides `multiply_associative` etc.).
  For goals that touch zero (`(0 : Integer) * x = 0`) or negation in a
  product (`-a * b`), also import `<carrier>.instances` (for
  `<carrier>.is_ring`) and `Algebra.ring_lemmas` — `ring` derives the
  multiplicative annihilation and `multiply_negate_*` lemmas
  abstractly from the IsRing instance rather than looking up per-
  carrier wrappers (Rational/Real no longer have them). If `ring` says
  "carrier X is missing axiom Y", add the import.
- **Scalar Integer multiplication at Rational/Real.** Use the
  `*` operator on `(Integer, R)` (or `(R, Integer)`) — registered
  via `R.from_integer_multiply(n, x) := (n : R) * x` for R in
  {Rational, Real}. So `(2 : Integer) * x` for `x : Rational` is a
  real operation, not an implicit conversion of `2`. Ring sees this
  pattern as "coefficient n of atom x" and handles it identically to
  the Integer-on-Integer case. Both `(n : Integer) * x` and
  `x * (n : Integer)` work; ring recognizes the Integer literal
  through the full coercion chain `Natural.to_integer(succ^k(zero))`
  → wrapped by `Integer.to_rational` for Rational, then by
  `Rational.to_real` for Real. The named constants `Integer.one` /
  `Rational.one` etc. are also recognized as literal 1.

- **Bare-literal Rational/Real (not multiplied).** Each numeric
  literal still parses as a Natural — bare `1 + 1` for a Rational
  target fails, and `x + 2` for `x : Integer/Rational/Real` errors
  (no implicit coercion: the user writes `(2 : Integer)` to say which
  `2` they mean). For a Rational two, write `Rational.one +
  Rational.one` or ascribe `(2 : Integer) * x` (scalar pattern). The
  literal default stays Natural by design — coercions are explicit
  only, never inferred from a neighbouring operand.

When the goal is `(ring : Foo = Bar)` and you intend to `rewrite` with
it, double-check the direction: `rewrite(eq, term)` looks for the LHS
of `eq` in `term`'s type. Putting it the wrong way round gives the
"left endpoint does not appear (structurally) in term's type" error.

## Ring lemmas: foundational vs. derived

Two flavours of ring lemma; they live in different places and you
write them differently.

**Foundational axioms** — the things `IsRing` bundles: `add_associative`,
`add_commutative`, `multiply_associative`, `multiply_commutative`,
`zero_add` / `add_zero`, `one_multiply` / `multiply_one`,
`add_negate_left` / `add_negate_right`, `distributivity_left` /
`distributivity_right`. These have to be proved per-carrier (they're
the inputs that `<carrier>.is_ring` packages up). Live in the
carrier's `ring.math` / `algebra.math`. Foundational means: the `ring`
normaliser looks them up by `<carrier>.<axiom>` name when it needs them.

**Derived lemmas** — provable from `IsRing` alone: `zero_multiply`,
`multiply_zero`, `multiply_negate_left`, `multiply_negate_right`,
`negate_multiply_negate`, and friends. These live ONCE in
`Algebra/ring_lemmas.math` as `Ring.<lemma>` over a generic `IsRing(R,
…)`. There's no need to restate them per-carrier. To use them at a
specific carrier, either:

- Cite the abstract form by hand:
  `Ring.zero_multiply(Rational, Rational.add, Rational.zero,
  Rational.negate, Rational.multiply, Rational.one, Rational.is_ring,
  x)` — verbose but mechanical.
- Just `:= ring` (or in a calc step, a step that needs the lemma).
  The `ring` normaliser finds `Ring.<lemma>` plus `<carrier>.is_ring` in scope and
  emits the abstract application internally.

**Don't add `Rational.zero_multiply` / `Real.zero_multiply` /
`Real.multiply_negate_left` / etc. as one-line wrappers around the
abstract form.** Such wrappers cost more than they buy: they're an
extra import target, an extra name to know, and they have to be kept
in sync with the abstract.

Integer is the exception — `Integer.multiply_zero_left` / `_right` /
`multiply_negate_left` / `_right` are proved at the representative
level via `reflexivity` through Quotient.lift, which is shorter than
the abstract derivation would compile to. The `ring` normaliser's helpers
(`buildRingAnnihilatorProof`, `buildRingMultiplyNegateProof`) prefer
the abstract form when both it and `<carrier>.is_ring` are in scope,
fall back to the per-carrier name otherwise.

When adding a new ring carrier:

1. Define the carrier and its operations.
2. Prove the foundational axioms per-carrier.
3. Bundle them into `<carrier>.is_ring : IsRing(...)` in
   `<carrier>/instances.math`. Import `Algebra.ring_lemmas` there so
   downstream uses of `ring` find the abstract lemmas.
4. That's it — `ring` works. No per-carrier `zero_multiply` etc.

## `linear_combination(e)` — ring with equational hypotheses

`ring` proves identities that hold *unconditionally*. When the goal
holds only **given some equation hypotheses**, use
`linear_combination(e)`: it closes a commutative-ring equality goal
`goalL = goalR` from a linear combination `e` of hypotheses, checking
the bridge `goalL − goalR = combL − combR` with the ring normaliser
and assembling via `Ring.equal_of_linear_combination`.

`e` is a `+`/`*`/`-` expression whose leaves are either **equality
proofs** (hypotheses `h : a = b`) or **scalar ring coefficients**. The
elaborator walks the tree, scaling and summing the equations (a scalar
`c` denotes the trivial `c = c`; `c * h` scales `h` by `c`; `h1 + h2`
adds them), and builds the combined proof by congruence + transitivity.

```math
-- subtract a common term: a = b from h : a + k = b + k
theorem _ (a b k : Integer) (h : a + k = b + k) : a = b :=
  linear_combination(h)

-- scale a hypothesis: c*a = c*b from h : a = b
theorem _ (a b c : Integer) (h : a = b) : c * a = c * b :=
  linear_combination(c * h)

-- the full c1·h1 + c2·h2 shape
theorem _ (a b c d c1 c2 : Integer) (h1 : a = b) (h2 : c = d)
        : c1 * a + c2 * c = c1 * b + c2 * d :=
  linear_combination(c1 * h1 + c2 * h2)

-- difference of hypotheses: a − c = b − d from h1 : a = b, h2 : c = d
theorem _ (a b c d : Integer) (h1 : a = b) (h2 : c = d) : a - c = b - d :=
  linear_combination(h1 - h2)
```

Works as a calc-step `by` proof too. Scope/limits:
- **Concrete carriers** (Integer/Rational/Real/…) **and the bundled
  commutative-ring carrier `CommutativeRing.carrier(c)`** (the ops are
  resolved as the `CommutativeRing.*(c)` projections and the instance
  as `CommutativeRing.is_ring(c)`, mirroring how `ring` threads the
  structure argument). A *plain* `Ring.carrier(s)` is NOT supported —
  the ring bridge needs multiplicative commutativity (same limit as
  `ring`); cite `Ring.equal_of_linear_combination` by hand there.
- **Coefficients** may be variables (`c1 * h1 + c2 * h2`) or explicit
  literals (`(2 : Integer) * h1 + (3 : Integer) * h2`). Write the
  literal's carrier explicitly — `(2 : Integer)`, never bare `2` (no
  implicit coercion). Both forms are fine; the variable form is the
  lightest when the coefficient is already in scope.
- Leaves that aren't equality proofs are treated as scalars (the
  trivial `v = v`), so a malformed combination surfaces as a ring
  bridge that doesn't normalise.

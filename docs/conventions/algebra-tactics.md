# Algebra tactics: ring, field, linear_combination

The `ring`/`field` tactics, foundational-vs-derived ring lemmas, and `linear_combination` (ring with equational hypotheses).

*(Part of the project conventions; see `CLAUDE.md` for the index.)*

## `ring` — try it first

`ring` (polynomial normalisation: distributivity, commutativity,
associativity, like-term collection at arbitrary signed integer
coefficients, total cancellation, unit-multiplication strip, subtract
sugar, and Integer numeric literals) handles essentially every
commutative-ring identity you'd write by hand in a relation chain. The
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
  the supplied nonzero-hypotheses. `field` also clears small *literal*
  denominators automatically (`2 ≠ 0` etc. are discharged for you): the
  square-gap identity `x*y = ((x+y)/2) * ((x+y)/2) - ((x-y)/2) * ((x-y)/2)`
  is a one-line `by field`, replacing the `Rational.one_half` +
  `linear_combination` + `halfSum` scaffolding it used to need. Prefer
  writing a mean as `(x + y) / 2`, not `(x + y) * (Rational.one_half :
  Real)`, so `field` (and the reader) see the division directly.
  Better still: the by-less equality battery tries `field` itself when
  an endpoint mentions the carrier's `/` or reciprocal and the nonzero
  facts are ground or in scope — so routine division arithmetic
  (`ε/4 + ε/4 = ε/2`, `(1/a)·(1/b) = 1/(a·b)`) closes as a bare
  relation step or claim, no `by field` needed. Write the hint only
  when the bare step genuinely fails (pinned by
  `Test/field_battery_test.math`).
- **`let`-bound values are transparent to `ring`/`field` (and the sign
  battery); still atoms to `linear_combination`.** `ring` and `field`
  ζ-unfold local `let`s in the goal (and `field` reads its nonzero
  hypotheses at the same let-free spelling), so
  `mean * mean - x*y = halfDiff * halfDiff by field` with
  `let mean := (x+y)/2` closes as written; so do bare sign/positivity
  claims over a `let` (`let tolerance := ε / 2 / fRoof;
  tolerance > 0;` — pinned by `Test/zeta_let_test.math`). The one
  remaining blind spot is `linear_combination`: its cited hypothesis
  equations feed the coefficient bookkeeping at their stated
  spellings, so keep explicit forms on those identities. See
  `numerals-and-naming.md`.
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

- **Bare literals and the carrier.** A numeric literal parses as a
  `Natural`; whether it then lifts to the ring's carrier depends on the
  *position* (full rules in `numerals-and-naming.md`). In an
  operator-operand or function-argument position against a higher-tower
  operand it **does** coerce now: `x + 2` for `x : Real` lifts `2` to
  `(2 : Real)` via the coercion-join, and `Real.power(2, m)` lifts the
  base. But as a `linear_combination` **coefficient** it does not —
  write the carrier explicitly there, `(2 : Integer) * h`, never bare
  `2`. And mind that `1 + 1`, `Real.one + Real.one`, and `(2 : Real)`
  (the tower) are three *different terms* — all ring-equal, but they do
  NOT match structurally, so don't mix them across a `≤`-step or a lemma
  citation (the `2`-vs-`1+1` rule in `numerals-and-naming.md`).

When you state a `(ring : Foo = Bar)` fact for the transport bridge,
double-check the direction: the bridge looks for one side of the
equation in the fact being transported. Stating it the wrong way round
gives the "left endpoint does not appear (structurally)" error.

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
- Just `:= ring` (or in a chain step, a step that needs the lemma).
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

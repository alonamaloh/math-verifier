# calc, let, and rewrite

`calc` with mixed relations, `let` abbreviations (ζ), preferring `calc` over nested transitivity, `calc … as NAME`, `rewrite`, diff-inferred congruence, and rewrite-under-binder.

*(Part of the project conventions; see `CLAUDE.md` for the index.)*

## `calc` with mixed relations

`calc` chains support all five relations as step separators: `=`,
`≤`, `<`, `≥`, `>`. The chain's result picks the strongest relation
across its steps (any `<`/`>` makes it strict; otherwise `≤`/`≥` if
present; else `=`). Mixing forward (`<`/`≤`) with backward (`>`/`≥`)
is rejected — `=` is allowed in either direction.

```math
calc Rational.absolute_value(s(m) * (t(m) - t(n)))
   = Rational.absolute_value(s(m))
       * Rational.absolute_value(t(m) - t(n))   by abs_first_eq
   ≤ (successor(K_s) : Rational)
       * Rational.absolute_value(t(m) - t(n))   by first_factor_bound
   ≤ (successor(K_s) : Rational) * delta_t     by first_factor_bound_2
   ≤ Rational.halve(Rational.halve(epsilon))   by succ_K_s_delta_t_bound
```

The carrier-specific transitivity lemmas (`<T>.LessOrEqual.transitive`,
`<T>.LessThan.transitive_left/right`, `<T>.LessThan.weaken`,
`<T>.LessOrEqual.reflexive`) are looked up via the same operator
registry that drives binary `≤`/`<`. `=` steps get upgraded to `≤`
on the fly whenever the chain isn't all-`=`. `≥`/`>` work as
expression-level operators too: `a ≥ b` desugars to `b ≤ a` against
the existing `≤` registration.

Step proofs are parsed at the parseAdditive level — `=`/`≤`/`<`/`≥`/`>`
are reserved as separators, so step proofs containing those operators
must be parenthesised.

A by-less `=` step now runs the **full** auto-prover (not just the
reflexivity / diff / AC battery): if the cheap battery fails it falls back
to the same `autoProveClaim` an equality `claim` uses — context-fact
match, the equality bridge, and the symmetry flip (so `0 = b` closes from
a `b = 0` fact). A calc `=` step and an equality claim are one prover.

## `calc` over preorders (`∣`, `⊆`, `≈`, …)

`calc` also chains any transitive relation, not just the order ones. A
step separated by `∣` (divides), `⊆` (subset), or `≈` (equinumerous)
routes the whole chain to a generic-preorder fold that uses the carrier's
relation and its transitivity lemma (`<R>.transitive` or `<R>_transitive`),
absorbing interleaved `=` steps by transport:

```math
calc p
   ∣ 0                 -- p divides 0   (auto: divides_zero)
   = b                 -- 0 = b         (auto: the b = 0 fact, flipped)
```

proves `p ∣ b`, and `calc a = b ∣ c = d` proves `a ∣ d`. A single chain
uses one non-`=` relation. The carrier may even be `Type(0)` itself — `≈`
(`Equinumerous`, registered `operator (≈) on (_, _)`) chains types:
`calc X ≈ Y ≈ NaturalsBelow(n)` (see `Set/finite.math`). Reusing one of the
existing relation symbols (`∣`/`⊆`/`≈`) needs only its operator + a
`<R>.transitive` lemma in scope; a brand-new symbol also needs a lexer/parser
token (the relation separators are a fixed set).

### `let` for local abbreviations — the auto-prover sees through

`let X : T := V;` introduces a local abbreviation. The kernel
ζ-reduces references to `X` back to `V` whenever the auto-prover or
`isDefinitionallyEqual` need it, and the auto-prover's structural
matchers (lemma-index lookup, calc-step path-walk) ζ-unfold `X` to
`V` on match attempts. Both directions are wired:

- **Equality checks**: `isDefinitionallyEqual` carries the let-value on
  the kernel `ContextEntry`; FreeVariables for let-binders δ-reduce to
  their values during comparison. So `claim foo : X = V by …` works
  even when `foo`'s proof has the unfolded type.
- **Structural matching**: the auto-prover (in `autoProveCalcStep`)
  ζ-unfolds let-binders in the calc endpoints before running its
  pipeline, so library lemmas about `V` apply to goals stated in
  terms of `X`.

Use this for proofs where one long expression appears many times and
its structure is irrelevant to the surrounding argument. The
canonical example is `Rational.padic_absolute_value_at_representative(p, RationalRepresentative.make(nx, dx))` — abbreviating it to `absXAtRep`
shortens proofs dramatically without losing any kernel guarantees:

```math
let absXAtRep : Rational :=
    Rational.padic_absolute_value_at_representative(
        p, RationalRepresentative.make(nx, dx));
let absYAtRep : Rational :=
    Rational.padic_absolute_value_at_representative(
        p, RationalRepresentative.make(ny, dy));
-- … use absXAtRep, absYAtRep freely in calc chains …
```

The library-wide convention is still "spell out the long name once,
abbreviate when it appears 3+ times in the surrounding proof."

### Prefer `calc` to `Equality.transitivity`

Nested `Equality.transitivity(A, transitivity(B, C))` — common in older
code — encodes a chain in a right-associated binary tree. A reader has
to mentally flatten the tree to see the actual chain. Rewriting as a
calc surfaces the intermediate forms as the math:

```math
-- Hard to read (5 lines of nesting):
by Equality.transitivity(
       Equality.symmetry(lemmaA),
       Equality.transitivity(
           congruenceOf(f, hyp),
           lemmaB))

-- Reads as the math (4-link calc):
by calc lhs
      = midpoint1   by Equality.symmetry(lemmaA)
      = midpoint2   by congruenceOf(f, hyp)
      = rhs         by lemmaB
```

Bonus: under `CHECK_REDUNDANT_BY=1` (default), the auto-prover will
often close several of the `by` annotations on its own — local
hypotheses match via the in-scope hypothesis lookup, and library lemmas
match via the lemma index. The naturalProduct claim in
`PAdic/absolute_value.math` went from 5-deep transitivity to a 4-link
calc with ZERO `by` clauses this way.

Sibling diagnostic: pass `--check-redundant-calc-steps` to the
verifier (off by default — the per-pair auto-prover dispatch is
expensive on long chains) to also warn when an intermediate calc
TERM (not just a `by` annotation) is redundant — i.e., the
auto-prover can close the combined step from the previous endpoint
directly to the next-next endpoint. The warning cites the line of
the redundant intermediate so you know which `= midpoint` to
delete. Useful for trimming over-written calc proofs after the
auto-prover gains a new rule.

Two-step transitivity (`Equality.transitivity(stepA, stepB)`) is
borderline — a 3-link calc is the same length. Use whichever reads
more clearly; calc usually wins because the intermediate form is named.

### `calc … as NAME;` and bare `calc …;` at statement position

A calc at statement position (inside a `{ … }` block, terminated by
`;`) binds its result into local scope, no `claim` ceremony required:

```math
-- Named binding — for downstream references:
calc (aInt * yPrime - qInt * bInt * yPrime)
   = (aInt - qInt * bInt) * yPrime
   = rInt * yPrime                                  as factoredEqualsRYPrime;

-- Anonymous binding — auto-prover still finds it by type-match:
calc a = b
     = c;
-- Later:
calc a = c        -- this step auto-closes via the binding above
     = d
```

Both forms bind `first <strongest-relation> last` (from the calc's
endpoints) into scope; the anonymous form synthesises a name like
`_calc_<line>_<col>`. Either way the binding is in scope for the rest of
the block, so the auto-prover's local-hypothesis matcher picks it up.

**Never hand-write `claim T by calc …`.** It restates exactly what the
calc already concludes — the bare `calc …;` (or `calc … as NAME;`) *is*
that claim, without the ceremony. This is a hard style rule.

Mixed-relation chains work at statement position too: the binding gets
the chain's strongest relation. `calc a ≤ b = c as h;` binds `h : a ≤ c`;
the bare `calc a ≤ b = c;` binds it anonymously. (There is no "all-`=`
only" restriction — that earlier claim was wrong. `claim NAME : TYPE by
calc …` is never needed.)

Restriction:
- The `as NAME` postfix lives at the END of the calc, after the last
  step's optional `by`. Parses cleanly: `calc … = rhs by lemma as foo;`.

Math-reading rationale: a textbook proof reads "by calculation: A = B
= C; call this (∗); now…". The `as` form matches that phrasing
exactly. The anonymous form matches "by a calculation: A = B = C; now
…" where the auxiliary fact is used implicitly.

Lint: if you write `calc … as NAME;` and NAME is never *textually*
referenced in the rest of the block, the elaborator warns "drop the
`as NAME` to use the anonymous form" (downstream calc steps consume
the equation by type-match either way, so the name is dead weight).
Pick `as NAME` only when a later step or claim spells the name out.

## `rewrite(lemma)` / `rewrite(lemma, term)`

**Prefer `calc` or `by substituting eq`.** Raw `rewrite(…)` is transport
plumbing in a function-call costume and is now counted as a CIC leak by
`scripts/cic_leak_report`. A `calc` step absorbs `=` rewrites and reads as
the chain it is; `claim T by substituting eq` reads as "by substituting the
equation" (and is *not* a leak). Reach for raw `rewrite(eq, term)` only
when neither fits — typically a transport in a non-`calc` term position
where `substituting` cannot be threaded. The mechanics below are for those
residual cases.

Two forms, disambiguated by argument count.

**1-arg, in `calc` context**: `by rewrite(L)` for `L : a = b` finds
the unique structural occurrence of `a` on the calc step's LHS and
replaces with `b`. Only works in calc context (needs the step's
target as expected type). If `a` occurs multiple times or zero
times, fall back to explicit `congruenceOf((z) ↦ …, L)`.

**2-arg, term-level**: `rewrite(eq, term)` for `eq : a = b` and
`term : P(a)` returns a term of type `P(b)`. Desugars to
`Equality.transport_proposition(T, λz. P[a↦z], a, b, eq, term)` —
the motive is recovered by locating the unique structural
occurrence of `a` in `term`'s inferred type. Use this wherever the
6-arg `Equality.transport_proposition(...)` was the only option
(outside calc — `≤`/`∣` witness contexts, `Or.introduceRight(...)`
arguments, etc.).

The matcher tries six combos: (term type × LHS) × (unreduced,
head-WHNF, deep-β). If you get "left endpoint does not appear
(structurally) in term's type" and you're confident the equality is
true, check the equation direction first; then check whether the LHS
appears modulo a definitional unfold not covered by WHNF.

## `by lemma` in calc context — diff-inferred congruence

In a calc `=` step, if the `by` proof has type `Equality(T, a, b)` and
the step's two endpoints differ in a unique single-position slot at
exactly `(a, b)`, the elaborator auto-wraps with `Equality.congruence`.
The user just supplies the equation; the elaborator finds the slot.

```math
-- Used to require an explicit motive lambda:
calc Natural.power(Natural.padic_valuation(p, (1 + dy + dx*(1+dy))), p)
   = Natural.power(Natural.padic_valuation(p, (1+dx))
                       + Natural.padic_valuation(p, (1+dy)), p)
       by congruenceOf(
              (m : Natural) ↦ Natural.power(m, p),
              Natural.padic_valuation_multiplicative(
                  p, (1+dx), (1+dy), primality, succDxPos, succDyPos))

-- Now: the elaborator infers `λm. Natural.power(m, p)` from the diff.
calc Natural.power(Natural.padic_valuation(p, (1 + dy + dx*(1+dy))), p)
   = Natural.power(Natural.padic_valuation(p, (1+dx))
                       + Natural.padic_valuation(p, (1+dy)), p)
       by Natural.padic_valuation_multiplicative(
              p, (1+dx), (1+dy), primality, succDxPos, succDyPos)
```

How it works: the elaborator's `tryDiffApplyUserProof` walks the step's
`(previous, next)` in lockstep through `Application` nodes. At each
level, it tests whether the current `(subLeft, subRight)` matches the
proof's `(a, b)` modulo `isDefinitionallyEqual` (forward) or `(b, a)`
(symmetric — wraps in `Equality.symmetry`). On match, it wraps from
the innermost level outward with `Equality.congruence` calls,
reconstructing the path with the saved sibling subexpressions.

Limits:
- Single-position diff only. Multi-position diffs (the diff appears in
  two independent slots) fall through. Use explicit
  `congruenceOf(λm. …, eq)` or split into multiple calc steps.
- The user's proof has to elaborate without the step's expected type
  as a guide. Lemma calls with all arguments supplied are fine;
  underspecified lemma calls that needed the expected type to
  disambiguate won't reach the fallback.
- The match uses kernel `isDefinitionallyEqual`, so it sees through
  β/ζ/ι reductions. Plain `rewrite(eq)` does a stricter structural
  match — diff inference catches cases like `v_p((1+dx)*(1+dy))` (the
  lemma's LHS) vs `v_p(1+dy+dx*(1+dy))` (the step's slot) where
  multiplication reduces structurally.
- **Subtraction must surface the same way on both sides.** `a - b`
  (`subtract(a, b)`) and `a + -b` (`add(a, -b)`) print alike and are
  ring-equal, but the structural diff treats them as DISTINCT heads — so a
  lemma stated with `+ -` won't bridge a step written with `-` (or vice
  versa), and the rejection looks inexplicable because both relations print
  identically. The elaborator now hints at this ("this step involves
  subtraction …"). Fix: write both endpoints the same way, or close the step
  with `ring` (or a `by substituting` bridge).

## Rewrite under a binder — `by ((x) ↦ …)` in calc

When a calc `=` step's endpoints are the **same function `F` applied to
argument lists that differ in exactly one position — a binder body
`λx. f` vs `λx. g`** — the step is a congruence under that binder: it
holds as soon as `f(x) = g(x)` pointwise. Write the per-index proof
directly as the `by` step; the elaborator reads `f`/`g` and every shared
argument off the endpoints and discharges the step with the registered
congruence lemma. The canonical case is rewriting the summand of a
`Polynomial.Sum`:

```math
-- Verbose: respell BOTH summands + the Sum.extensional wrapper.
= Polynomial.Sum(r, (i) ↦ coefficient(p, i) * (coefficient(q, k−i) + coefficient(s, k−i)), k)
      by Polynomial.Sum.extensional(r,
             (i) ↦ (coefficient(p, i) * coefficient(q, k−i)) + (coefficient(p, i) * coefficient(s, k−i)),
             (i) ↦ coefficient(p, i) * (coefficient(q, k−i) + coefficient(s, k−i)),
             (i) ↦ Ring.distributivity_left(r, coefficient(p, i), coefficient(q, k−i), coefficient(s, k−i)),
             k)

-- Idiomatic: just the per-index proof. f, g, r, k are read off the
-- endpoints. Note the PARENS around the lambda (see below).
= Polynomial.Sum(r, (i) ↦ coefficient(p, i) * (coefficient(q, k−i) + coefficient(s, k−i)), k)
      by ((i : Natural) ↦
             Ring.distributivity_left(r, coefficient(p, i), coefficient(q, k−i), coefficient(s, k−i)))
```

**Registering a congruence lemma.** The mechanism is driven by a
registry, not a naming convention. Register the lemma for the function
head once, next to where it's defined:

```math
congruence_under_binder Polynomial.Sum := Polynomial.Sum.extensional
```

A `congruence_under_binder <F> := <L>` makes `L` available to discharge
under-binder steps on `F`. It is generic over `F` and over `L`'s argument
order: the elaborator applies `L` to the shared prefix + `f` + `g`, then
fills its remaining binders by walking them — the author's lambda goes to
the unique **pointwise-equality** binder (a `Pi` chain ending in `=`,
wherever it sits), every other binder from the next shared suffix argument
of `F`. So a range-restricted variant with a different layout works from
the same surface — register it too and the elaborator tries each in turn:

```math
congruence_under_binder Polynomial.Sum := Polynomial.Sum.extensional_range
-- now `by ((i) (smaller : i ≤ k) ↦ …)` closes a Sum step from
-- the range-restricted pointwise proof (Sum.extensional is tried first,
-- fails on the 2-binder lambda, then Sum.extensional_range matches).
```

How it fires: gated to a calc `=` step whose endpoints are a
single-binder-diff application of a head with a registered lemma AND
whose `by` proof is syntactically a lambda — so an ordinary lemma proof
of a `Sum = Sum` step (e.g. `by Sum.add(…)`) takes the normal path
untouched. The assembled proof is type-checked before use, so a wrong
guess never shadows a real step.

Gotchas / limits:
- **Parens are required:** `by ((x) ↦ …)`. A bare
  `by (x) ↦ …` parses wrong — the lambda body is greedy and
  eats the next calc step. Keep the parens.
- **One binder argument per step.** The endpoints must differ in exactly
  one position. Chained rewrites under the same Σ are separate steps.
- The lambda's binder count selects the variant (1 binder →
  `extensional`, 2 → `extensional_range`), since elaboration against the
  wrong lemma's pointwise type fails and falls through.

### `let` and ζ — current status

The 2026-era kernel does ζ-unfold let-binders in
`isDefinitionallyEqual` (the auto-prover, the rewrite matcher, and
the `decide` walker all see through them, per the section above on
let-for-local-abbreviations). The old advice "don't use `let` for
value abbreviations" — driven by a kernel that didn't ζ-track
let-binders through `congruenceOf`'s motive checks — no longer
applies.

Use `let` freely for value abbreviations. `ring` also ζ-unfolds the
goal up front (2026-06-12), so a let-bound ring constant is seen
structurally rather than as an opaque atom — the canonical use is

```math
let zero : ComplexNumber :=
    RingModulo.zero(Real.polynomial_commutative_ring, Complex.definingPolynomial);
let one : ComplexNumber :=
    RingModulo.one(Real.polynomial_commutative_ring, Complex.definingPolynomial);
calc ComplexNumber.partialSum((k : Natural) ↦ c * s(k), 0)
   = zero
   = c * zero    by ring
```

instead of spelling the full `RingModulo.zero(…, …)` wall at every
site. This is scoped to `ring` only — `field` and `linear_combination`
cancel the goal against cited HYPOTHESES whose types keep the let
spelling, so ζ-unfolding only the goal there desynchronises the atoms
(use the let-free spelling, or cite a let-typed claim, in those).

Two caveats remain:

- **Implicit-argument inference** may use the ζ-unfolded form rather
  than the let-bound name. For example, `Logic.Decidable.yes(midIsUpper)`
  inside `Real.bisectionStepWithDec(subset, intervals, _)` infers its
  implicit `P` from the third arg's signature (the unfolded form), not
  from `midIsUpper`'s declared type (the let-bound `midReal`). Two
  kernel-equal-but-not-structurally-equal terms result — fine for the
  kernel, but it matters if the surface tactic does literal subterm
  matching. The decide elaborator ζ-unfolds the target up front; other
  paths may need explicit ζ-unfold or `claim`-binding to align shapes.

- **Function-valued `let`s are not β-reduced after ζ.** `let f := (k) ↦
  g(k);` makes `f(i)` unfold to `(λk. g k) i`, NOT to `g(i)` — so `ring`
  and `since`/citation matching treat `f(i)` and `g(i)` as distinct
  atoms (the unfold substitutes the value but stops short of β). Either
  do the algebra in the `g(i)` form and let a by-less `=` step fold to
  `f(i)` (the full defeq path *does* β-reduce), or pass explicit
  arguments through the let (`by lemma(g(i))`, not argument-free
  `since`).

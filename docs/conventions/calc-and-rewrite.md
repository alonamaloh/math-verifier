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

Both forms desugar to `claim NAME : (first = last) by calc …` where
`first` and `last` come from the calc's endpoints. The anonymous form
synthesises a name like `_calc_<line>_<col>`. Either way the binding
is in scope for the rest of the block, so the auto-prover's local-
hypothesis matcher picks it up.

Restrictions:
- All-`=` chains only. For mixed `=`/`≤`/`<` calcs at statement
  position, use the explicit `claim NAME : TYPE by calc …;` form so
  the resulting relation type is unambiguous.
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

Two forms, disambiguated by argument count.

**1-arg, in `calc` context**: `by rewrite(L)` for `L : a = b` finds
the unique structural occurrence of `a` on the calc step's LHS and
replaces with `b`. Only works in calc context (needs the step's
target as expected type). If `a` occurs multiple times or zero
times, fall back to explicit `congruenceOf(function (z) => …, L)`.

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
              function (m : Natural) => Natural.power(m, p),
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

## Rewrite under a binder — `by (function (x) => …)` in calc

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
= Polynomial.Sum(r, function (i) => coefficient(p, i) * (coefficient(q, k−i) + coefficient(s, k−i)), k)
      by Polynomial.Sum.extensional(r,
             function (i) => (coefficient(p, i) * coefficient(q, k−i)) + (coefficient(p, i) * coefficient(s, k−i)),
             function (i) => coefficient(p, i) * (coefficient(q, k−i) + coefficient(s, k−i)),
             function (i) => Ring.distributivity_left(r, coefficient(p, i), coefficient(q, k−i), coefficient(s, k−i)),
             k)

-- Idiomatic: just the per-index proof. f, g, r, k are read off the
-- endpoints. Note the PARENS around the lambda (see below).
= Polynomial.Sum(r, function (i) => coefficient(p, i) * (coefficient(q, k−i) + coefficient(s, k−i)), k)
      by (function (i : Natural) =>
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
-- now `by (function (i) (smaller : i ≤ k) => …)` closes a Sum step from
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
- **Parens are required:** `by (function (x) => …)`. A bare
  `by function (x) => …` parses wrong — the lambda body is greedy and
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

Use `let` freely for value abbreviations. The one remaining caveat:
when constructing a term whose IMPLICIT arguments are inferred from a
sibling expression, the elaborator may infer the implicit using the
ζ-unfolded form rather than the let-bound name. For example,
`Logic.Decidable.yes(midIsUpper)` inside
`Real.bisectionStepWithDec(subset, intervals, _)` infers its implicit
`P` from the third arg's signature (which references the unfolded
form), not from `midIsUpper`'s declared type (which may reference a
let-bound `midReal`). Two terms result that are kernel-equal but not
structurally equal — fine for the kernel, but matters if the
surface tactic does literal subterm matching. The decide elaborator
handles this by ζ-unfolding the target up front; other code paths
may need explicit ζ-unfold or `claim`-binding to align shapes.

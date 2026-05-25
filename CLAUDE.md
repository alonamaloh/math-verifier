# CLAUDE.md — project conventions and idioms

This file is auto-loaded into Claude's context. It documents the
**idiomatic** way to write proofs in this library, so future sessions
don't fall back to verbose patterns.

## Build

`make -j 16 library` from the project root. The dep graph is parallel;
warm rebuilds are sub-second. Always use `-j 16` (don't use bare `make`).

## Quotient idioms — use the short forms

The elaborator has type-and-relation inference for every Quotient
operation. Use the SHORT forms by default. The verbose forms exist
only as fallbacks when the elaborator can't infer; expect that to
be rare.

### Quotient.mk(rep)

```math
-- Short (preferred): T inferred from rep's type, R from expected type.
definition Rational.zero : Rational :=
  Quotient.mk(RationalRepresentative.make(Integer.zero, zero))

-- Verbose (avoid unless necessary):
definition Rational.zero : Rational :=
  Quotient.mk(RationalRepresentative, RationalEquivalent,
              RationalRepresentative.make(Integer.zero, zero))
```

The short form needs an expected type of shape `Quotient(T, R)` from
context (the surrounding theorem's return type, or an enclosing
function argument). The short form does NOT fire in these positions:
- Operand of unary `-`, binary `+`, `*`, `=`, `<`, `≤`.
- Third arg of `Equality.transport_proposition(A, P, x, ...)` (the
  carrier `A` doesn't propagate inward).
- Arguments of polymorphic functions like `reflexivity`,
  `Equality.transitivity`, `congruenceOf`, `Or.eliminate`,
  `Exists.eliminate` (those elaborate args without an expected type).
- Inside `congruenceOf` lambdas without an explicit annotation.

**Trick:** in those positions, an explicit type ascription on the
`mk` recovers the inference: `(Quotient.mk(rep) : Rational)`. The
ascription is the expected type the short form needs.

```math
-- Fails:
Rational.absolute_value(Quotient.mk(rep))

-- Works:
Rational.absolute_value((Quotient.mk(rep) : Rational))

-- Also works (verbose fallback):
Rational.absolute_value(
    Quotient.mk(RationalRepresentative, RationalEquivalent, rep))
```

### Quotient.sound(x, y, proof)

```math
-- Short (preferred): T from x's type, R from proof.
Quotient.sound(rep1, rep2, equivProof)

-- Verbose:
Quotient.sound(RationalRepresentative, RationalEquivalent,
                rep1, rep2, equivProof)
```

### Quotient.lift(f, h, q)

```math
-- Short (preferred): T, R, U all inferred.
Quotient.lift(
    function (rep) => ...,
    function (rep1 rep2 hyp) => ...,
    q)

-- Verbose:
Quotient.lift(RationalRepresentative, RationalEquivalent, Rational,
               function ...,
               function ...,
               q)
```

### Quotient.induct(motive, atRep, q)

```math
-- Short (preferred): T, R inferred from q.
Quotient.induct(
    function (xArg : Rational) => P(xArg),
    function (rep : RationalRepresentative) => proofAtRep(rep),
    x)
```

### Quotient.induct_two(motive, atRep, q1, q2)

Same pattern, 4 args. For binary laws.

### Quotient.induct_three(motive, atRep, q1, q2, q3)

5 args, for ternary laws (associativity, distributivity). This was
added to avoid the awkward `function (yArg) (zArg) =>
Quotient.induct_two(yArg, zArg)` lambda-wrap that the older library
files use. New 3-arg laws should prefer `induct_three`.

## Name-bound conventions

`convention p [q ...] : T [with H1 [, H2 ...]];` at the file top
registers a name as an auto-prepended implicit binder. Mirrors the
math-book "throughout this chapter, p and q denote prime numbers"
convention.

```math
convention p : Natural with Natural.is_prime(p)

-- Subsequent theorems mentioning `p` get
-- {p : Natural} {_ : Natural.is_prime(p)} prepended implicitly.
theorem prime_self_divides : p ∣ p :=
  ⟨successor(zero), ...⟩
```

Notes:
- No semicolon at the end (matches other top-level declarations).
- If the user shadows the convention name with their own binder, the
  convention does NOT fire for that declaration.
- v1 fires on `definition` and `theorem`. Inductive declarations and
  axioms are not yet covered.
- Call sites still rely on the existing implicit-arg machinery —
  arguments uniquely determined by another argument's type are
  inferred; purely propositional arguments may need to be passed
  explicitly.

## Implicit arguments

`{x : T}` binder syntax is supported on `definition`, `theorem`, and
`axiom`. Use this when a parameter is determined by another's type:

```math
theorem refl_implicit {T : Type(0)} (x : T) : x = x :=
  reflexivity(T, x)

-- Call site doesn't pass T:
refl_implicit(n)  -- T inferred as Natural
```

PAdic operations currently thread `(p : Natural) (primality :
Natural.is_prime(p))` explicitly. If you're writing NEW PAdic code,
consider making them implicit: `{p : Natural} {primality :
Natural.is_prime(p)}`. Existing PAdic code uses explicit form for
historical reasons; migration is a planned cleanup.

## Naming

- **No abbreviations in identifiers.** `representative`, not `rep` (in
  declaration names). Local-variable `rep` is fine.
- Long fully-qualified names (`Rational.padic_absolute_value`) are
  searchable. Don't shorten.
- `IsX` (predicate) and `X_is_Y` (witness) conventions match the
  algebraic-instance pattern in `library/Rational/instances.math`.

## Prefer `1 + n` over `successor(n)` in expressions

`successor(n)` is the Peano constructor; `1 + n` is the same value in
the carrier's `+`. They are definitionally equal (kernel reduces
`1 + n = successor(0) + n = successor(0 + n) = successor(n)`), so they
typecheck interchangeably wherever an EXPRESSION is expected. The `1 + n`
form reads as math; `successor(...)` reads as bureaucracy.

Same applies to deeper successors: prefer `2 + n` over
`successor(successor(n))`, and `n + 1` is fine when it parses more
naturally (commutativity is also definitional via `add_commutative` but
even better, the kernel reduces either form to the constructor chain).

A goal stated as `1 ≤ successor(k)` reads better as `1 ≤ 1 + k` or just
`1 ≤ k + 1`. The corresponding helper `Natural.successor_positive`
proves it either way.

**Exception: patterns.** Pattern positions (`| successor(k) => ...`)
require the bare constructor — the parser doesn't accept `1 + k` there.
Companion memory: [[prefer_numeric_literals]] covers the related
`0`/`1`/`2` over `zero`/`successor(zero)`/`two` rule.

**When `successor(n)` wins anyway.** Two situations where the
substitution makes the proof *harder* to read, learned the hard way:

- **Structural reduction sites.** `Natural.add` and `Natural.multiply`
  are defined by recursion on the `successor` constructor of the first
  argument, so `successor(k) + b ≡ successor(k + b)` and
  `d * successor(q) ≡ d + d * q` are definitional reductions the
  kernel will perform. Rewrite-matchers and calc-step matchers see the
  `successor(...)` form structurally, but they don't always see the
  reduced form behind `1 + k`. Concretely: in
  `library/Natural/arithmetic.math:60` (`add_commutative`'s successor
  case), the calc starts at the REDUCED form `successor(predecessor + b)`
  precisely so a downstream rewrite can find `predecessor + b` as a
  subterm. Writing `(1 + predecessor) + b` instead breaks that.
  Foundational Natural arithmetic files (`basics`, `peano`,
  `arithmetic`, plus `divide`, `divides_subtract`, `divisibility`,
  `power`) keep `successor(...)` for this reason.

- **Structural-atom slots.** When `successor(n)` appears uniformly as a
  "positive successor" atom (e.g. positive denominator in Rational
  cross-multiplication), `(succ(d) : Integer)` reads as one concept —
  "the *d*th positive denominator." `((1 + d) : Integer)` adds an
  extra paren pair (the inner one is forced by `+`'s precedence under
  type ascription) and makes the reader parse a sum before recognising
  the slot. Saw this on `Rational/basics.math:transitive_natural`
  where the substitution made the proof noticeably noisier.

Rule of thumb: prefer `1 + n` when the `+1` is doing arithmetic work
the reader cares about (`1 ≤ 1 + k`, `1 + k = succ(k)` reductions).
Keep `successor(n)` when it's a structural placeholder.

## Prefer `cases` / `by_induction` over pattern-match definitions

The pattern-match definition form (`theorem foo | zero => … |
successor(k) => …`) is supported but NOT the preferred style.
Mathematicians don't write proofs as separated equation cases at the
outer-syntax level — they write a body that opens with "by cases"
or "by induction on n" and then handles each constructor.

Translation:

```math
-- Pattern-match (legacy):
theorem Natural.foo : (n : Natural) → P(n)
  | zero          => baseProof
  | successor(k)  => stepProof(k)

-- Preferred — non-recursive case split:
theorem Natural.foo (n : Natural) : P(n) :=
  cases n {
    | zero          => baseProof
    | successor(k)  => stepProof(k)
  }

-- Preferred — recursive (k's IH needed in stepProof):
theorem Natural.foo (n : Natural) : P(n) :=
  by_induction on n with IH {
    case zero:           baseProof
    case successor(k):   stepProof(k, IH)  -- IH : P(k)
  }
```

Pattern-match definitions remain unavoidable for direct recursion
that doesn't fit `by_induction`'s motive shape — for example when
the conclusion is universally quantified over a parameter that the
IH must be polymorphic over (`Natural.decides_equality` recursing on
`a` while the IH must work for all `b`). Use the `cases` body style
by default; reach for pattern-match definitions only when the
recursion really demands it.

### Multi-pattern bindings (when the pattern-match form is used)

Constructor patterns at non-scrutinee positions of a pattern-match
definition properly refine the types of later-bound function args
(including dependent equality hypotheses). Write all destructures in
one row:

```math
theorem IntegerEquivalent.symmetric
        : (x y : IntegerRepresentative)
          → IntegerEquivalent(x, y)
          → IntegerEquivalent(y, x)
  | IntegerRepresentative.make(a, b),
    IntegerRepresentative.make(c, d),
    aPlusDEqualsBPlusC =>
      …
```

The elaborator emits a nested recursor chain whose motives abstract
the destructured position AND every later position binder, so a
hypothesis like `aPlusDEqualsBPlusC` arrives in its refined
Natural-level form. v1 supports inner constructor patterns on
single-constructor non-indexed non-recursive (parameterised OK)
inductives — covers `IntegerRepresentative.make`,
`RationalRepresentative.make`, `PAdicCauchySequence.make`. Multi-
constructor inner positions would need per-row coverage analysis
that isn't yet wired up.

## `cases ... with` — case-split with retained equation

To case-split on an expression and retain an equation between the
expression and the matched form, add `with <equalityHypothesisName>`:

```math
cases Integer.absolute_value_natural(x) with refinedEquation {
  | zero          => ...refinedEquation : Integer.absolute_value_natural(x) = zero...
  | successor(k)  => ...refinedEquation : Integer.absolute_value_natural(x) = successor(k)...
}
```

The elaborator desugars this to the convoy pattern (`function (caseScrutinee : T) (equalityOuter : X = caseScrutinee) => …`) — the user just picks a name. Each arm gets `refinedEquation` in scope with the type refined per branch.

Constructor patterns with arguments (e.g. `successor(predecessor)`) are reconstructed as expressions for the equation type; tuple patterns aren't yet supported.

## `decide P { yes m => … | no n => … }` — classical case-split

The canonical form for classical case-splits. Replaces both:

- `cases Logic.excluded_middle(P) { | Or.introduceLeft(m) => … | Or.introduceRight(n) => … }` (for plain "P or not P" reasoning at the proposition level), AND
- `cases Logic.classical_decidable(P) with decisionEq { | Decidable.yes(m) => transport(…, m) | Decidable.no(n) => transport(…, n) }` (for the bisection-style pattern where the goal contains `bisectionStepWithDec(…, classical_decidable(P))` and we want each arm checked at the ι-reduced shape).

```math
-- Simple proposition-level case split (no goal abstraction needed):
decide x = Real.zero {
  | yes xEqZero  => Or.introduceLeft(IsNonneg(x), IsNonneg(-x), rewrite(…))
  | no  xNotZero => /* recurse with the inequality */
}

-- Bisection-style: the goal `Real.IsUpperBound(subset, right(bisectionStep(…)))`
-- has `classical_decidable(IsUpperBound(subset, midpoint))` buried five δ
-- unfoldings deep. The elaborator finds it (head-directed WHNF walker)
-- and abstracts the motive automatically — each arm proves its
-- ι-reduced shape.
decide Real.IsUpperBound(subset, (midpoint : Real)) {
  | yes midIsUpper => midIsUpper      -- new_right = midpoint
  | no  _          => IH              -- new_right = right(predecessor)
}
```

Semantics: builds `Logic.Decidable_recursor(P, motive, λp. arm_yes, λn. arm_no, Logic.classical_decidable(P))`. The motive abstracts every structural occurrence of `Logic.classical_decidable(P)` in the goal (after δ unfolds chained definitions like `bisectionStep`); if none appears, motive defaults to `λ_. Goal` and each arm proves the goal directly with `p` / `notP` in scope.

What it eliminates:
- The motive-as-lambda boilerplate (`function (decision : Logic.Decidable(…)) => …`).
- The explicit `Equality.transport_proposition(…)` call wrapping each arm.
- The `with decisionEq` equation plumbing.
- The `Or.introduceLeft` / `Or.introduceRight` constructor names.

When `decide` doesn't apply: the goal mentions some OTHER decidable expression (not the user's `P`), so the head-directed search finds no `classical_decidable(P)` and the motive falls back to constant. That's fine — it's the same as the old `cases Logic.excluded_middle(P)` pattern, just spelled more clearly. Either binder name may be `_`.

Error diagnostic: if the assembled `Decidable_recursor` application doesn't typecheck, the elaborator pre-checks it and dumps each of the 5 arg slots (proposition / motive / yes case / no case / scrutinee) with its inferred type, so the error points at which slot is the culprit. Generic kernel "Application: argument type does not match Pi domain" errors anywhere in the file now also print `expected type:` and `actual type:` lines.

## `ring` — try it first

`ring` (currently v2: polynomial normalisation, distributivity,
commutativity, associativity, ±1 coefficients) handles essentially
every commutative-ring identity you'd write by hand in a calc block.
The default for any equality between ring expressions on Natural,
Integer, Rational, Real, or PAdic is `:= ring` (top-level) or
`(ring : LHS = RHS)` (as a `rewrite` equation). Reach for explicit
`add_commutative` / `add_associative` / `congruenceOf` ONLY after
ring fails with a real limitation:

- **Coefficient > ±1.** `x + x = 2 * x` and `-(a/2) + -(a/2) = -a`
  hit this — error: "monomial with coefficient ±k, v2 only handles
  coefficients in {-1, +1}". Workaround: a manual calc using
  `negate_add` / domain-specific halving lemmas (`halve_doubled`).
- **Empty-polynomial cancellation.** `0 = x - x` fails with
  "proveAddMerge total-cancellation case not implemented". Use
  `Equality.symmetry(Rational.add_negate_right(x))` directly.
- **`ring` requires the carrier's `.add`, `.multiply`, and ring laws
  in scope.** For Real proofs, that typically means importing
  `Real.addition`, `Real.multiplication`, `Real.negation`, `Real.ring`,
  AND `Real.algebra` (which provides `multiply_associative` etc.).
  If `ring` says "carrier X is missing axiom Y", add the import.

When the goal is `(ring : Foo = Bar)` and you intend to `rewrite` with
it, double-check the direction: `rewrite(eq, term)` looks for the LHS
of `eq` in `term`'s type. Putting it the wrong way round gives the
"left endpoint does not appear (structurally) in term's type" error.

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

## Proof style — write proofs that read like math

The overriding goal is that a proof reads like what a mathematician
would write in a textbook, with the kernel doing the typechecking. A
human should be able to scan the proof and follow the argument
without parsing CIC bureaucracy. The optimization target is
**readability**, not terseness.

Concretely:

- **No abbreviations.** Both in identifiers (see the Naming section
  above — `representative`, not `rep`, in declared names) and in
  binders within proofs. Verbosity that aids comprehension is a
  feature, not a cost — `halvedEpsilonPositive`, not `hep`.

- **Math-like phrasing.** Compose the proof out of named
  mathematical steps. A reader should see "triangle inequality on
  (a − b) and b", "subtract |b| from both sides", "case split on
  the sign of (|a| − |b|)" — not a wall of `congruenceOf` /
  `transport_proposition` calls.

- **Length is fine if it's pedagogical.** Don't golf. A 40-line
  proof that explains each step in mathematical language is better
  than a 10-line proof that requires unwinding three nested
  `Quotient.lift` calls in your head to follow. Inline comments
  describing the strategy ("`|x| = |(a−b)+b| ≤ |a−b| + |b|` then
  subtract `|b|`") earn their keep.

- **`calc` is encouraged.** It mirrors how a mathematician writes
  an equation chain. Use it whenever you can name each intermediate
  form. Even a two-step calc is usually clearer than the equivalent
  `Equality.transitivity(...)`.

- **Sequence-of-claims style is encouraged.** When a proof has
  several distinct subgoals, write them as a sequence of `claim
  <name> : <type> by <proof>` lines and then assemble the result
  from the named claims. This makes the structure of the argument
  legible and lets a reader skim the claims to see the shape before
  reading the inner proofs.

### Statement-level proof sugar

Inside a `{ … }` proof block, the following statement forms compose
naturally and read as math prose. All end with `;` and the block
returns its final non-`;`-terminated expression.

- `claim <name> : <type> by <proof>;` — assert and discharge.
  Synonym: `goal <name> by <proof>` (when the type comes from the
  surrounding expected type), `done` / `okay` (bare claim,
  auto-prover closes the goal).
- `claim <type> by <hint>;` — anonymous claim. Hints include `by
  substitution` (auto-find equality + body), `by substituting
  <eqProof>` (narrowed to a supplied equation), `by cases { … }`,
  `by cases on E { case A: … case B: … }`, `by induction { … }`.
- `obtain ⟨a, b⟩ from <existentialOrAnd>;` — destructure an
  `∃ x. P(x)` or `And(A, B)` into named binders.
- `choose N such that P(N);` — sugar for `obtain ⟨N, _⟩` followed
  by a `claim P(N) by …`; reads as the textbook phrasing.
- `let <name> ∈ <type> [with <predicate>];` — introduce a typed
  variable that can later be refined.
- `let <name> [: <type>] := <value>;` — ζ-tracked abbreviation
  (kernel sees through it; see the `let` section above).
- `suppose <proposition> as <name>;` — introduce a hypothesis as a
  step (useful for breaking implication arrows into named pieces).
- `unfold <Foo> in <body>` — temporarily mark `Foo` transparent
  inside `<body>` (for opaque definitions; see the opaque section).

Outermost-arm shorthands for case-splits:

- `by_induction on n with IH { case zero: … case successor(k): … }` —
  preferred over a pattern-match definition.
- `by_induction on n with IH refining h1, h2 { … }` — also refine
  the listed in-scope binders' types per case (so hypotheses about
  `n` get the right shape in each arm).
- `by_induction on n using <strongRecursionLemma> { … }` — route
  the recursion through a user-supplied recursion principle.
- `by_strong_induction on n with IH { … }` — strong induction on a
  Natural; IH has type `(k : Natural) → k < n → P(k)`.

The bare keywords `done`, `okay`, `goal` are pure aliases — pick
whichever spells the proof's intent. "the proof is done here"
(`done`), "okay, that proves it" (`okay`), "the goal is closed by
…" (`goal by …`).

The remaining subsections are about *CIC noise* — bureaucracy that
the kernel demands but a mathematician would never write. Those
should be hidden behind named helpers; the rules below collect the
ones that come up most often. None of these rules trade away
readability — they only remove ceremony.

### `<order>.weaken` over `And.left` on a `<` hypothesis

`Rational.LessThan(x, y)` unfolds to `And(LessOrEqual(x, y),
Not(x = y))`. With `h : x < y` and a goal needing `x ≤ y`, prefer

```math
Rational.LessThan.weaken(x, y, h)         -- 1 line
```

over

```math
And.left(Rational.LessOrEqual(x, y), Not(x = y), h)   -- 3-5 lines
```

Same for `Rational.LessThan.distinct(x, y, h) : ¬(x = y)` vs
`And.right(...)`. Helpers live in `Rational/order_arithmetic.math`
alongside `LessOrEqual.negate`, `LessThan.negate`,
`negate_LessThan_zero_of_positive`, `LessOrEqual_zero_of_negate_IsNonneg`.

### Pattern-match at constructor reps for Quotient-lifted proofs

The bad shape (~80 lines): `Quotient.induct_two` whose at-rep body
threads bridge lemmas (`sequenceFunction_add`, etc.) through a calc
chain to reach a pointwise Rational fact.

The good shape (~20 lines): a separate `*_at_make` theorem that
pattern-matches the reps to expose the underlying sequences, plus a
top-level `Quotient.induct[_two|_three]` lift. When the rep is in
constructor form, the kernel's β/ι reduces every
`sequenceFunction(add(make(sx, _), make(sy, _)), n)` to
`sx(n) + sy(n)` and the bridge proofs become reflexivity.

```math
theorem Foo_at_make
        : (rep_x rep_y : CauchyRationalSequence) → … (Quotient.mk rep_x) … (Quotient.mk rep_y) …
  | CauchyRationalSequence.make(sx, sx_cauchy),
    CauchyRationalSequence.make(sy, sy_cauchy) =>
      Quotient.sound(…, …, function (n : Natural) => Rational.foo(sx(n), sy(n)))

theorem Foo (x y : Real) : … :=
  Quotient.induct_two(motive, Foo_at_make, x, y)
```

Caveat: when the at-make body needs to refer to a rep AGAIN
(typically when passing it to `Quotient.sound` or
`equivalent_when_sequenceFunction_equal`), the pattern wildcards must
each have a fresh NAME (`sx_cauchy`, `sy_cauchy`). Using `_` makes
the kernel re-bind a single fresh variable and the Cauchy proofs
collapse to the wrong type.

### Avoid auxiliary `CauchyXxx` definitions for one-off proofs

A standalone `definition CauchyRationalSequence.foo_residual : … →
CauchyRationalSequence` plus a `sequenceFunction_foo_residual`
bridge lemma is almost always a red flag — pattern-matching at make
inside an `at_make` theorem subsumes it without the auxiliary
definition. A previous draft of the triangle-inequality proof spent
200 lines on this pattern; the at-make refactor took 40.

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

## `opaque definition` — hide a function's body from kernel reduction

The kernel normally δ/ι-reduces freely during typechecking. For a
function defined by recursion on a constructor, this means a goal
of the form `monus(succ k, succ j) ≤ ...` silently collapses to
`monus(k, j) ≤ ...` the instant the kernel peels the outer
constructors. Goal/term shapes the user wrote then aren't there
when `rewrite` or pattern-match-on-goal tries to find them.

**`opaque definition Foo : ... := ...`** marks `Foo` so the kernel
won't δ-unfold it. The term `Foo(args...)` stays as a stuck
application; the kernel treats it like an axiom for reduction
purposes. Downstream proofs are forced to reason about `Foo`
through **characterising lemmas** — published equations that
describe `Foo`'s behaviour — rather than relying on automatic
unfolding.

**`unfold Foo in <body>`** is the escape hatch: temporarily flips
`Foo` to transparent while elaborating `<body>`. Used only inside
the characterising lemmas themselves (which need to peek at `Foo`'s
body exactly once) and in the rare proof that genuinely needs the
unreduced view.

### When to mark a definition opaque

Recursive-on-constructor functions where downstream proofs would
get tangled by the kernel's automatic reduction. Concrete markers:

- The function pattern-matches on its first/structural arg and
  recurses.
- Proofs about it use `rewrite` against goal terms containing the
  function applied to constructor-shaped args.
- The function's defining equations (`f(0) = …`, `f(succ k) = …`)
  are already published as named theorems.

If those three apply, opacity removes a class of "where did the
term go" surprises.

Currently opaque: `Natural.monus`, `Natural.divide_step`,
`Natural.modulo_step`, `Natural.padic_valuation_step`,
`Natural.power`.

### When NOT to mark opaque — the cost / benefit lesson

Tried and reverted: `Natural.distance`. The pattern is the same
(recursive, defines `distance(0,_)=_`, `distance(succ,succ)=…`)
but proofs about distance are *computational* — they evaluate
distance on concrete pieces toward a value, not pattern-match
against goals that mention distance. Opacity forced ~200 lines of
bridge rewrites (`Equality.transport_proposition` with explicit
motives, because intermediate `LessOrEqual.reflexivity(x)` proofs
had `x` appearing twice and `rewrite` couldn't disambiguate)
without removing any real surprise.

Heuristic: opacity helps when the proof shape SAYS something
about `f(args)` and would prefer the kernel not to silently
restructure it. Opacity hurts when the proof shape COMPUTES
`f(args)` and benefits from the kernel completing the
computation.

In practice: convert one candidate, audit the failures, count the
bridge sites. If most fixes look like "I added an explicit lemma
citation that makes the proof clearer," keep going. If most fixes
look like "I wrapped reflexivity in transport_proposition with a
synthetic motive because two `b`s collided," revert.

### Discipline at the opacity boundary

1. Mark `Foo` `opaque definition`.
2. Write the **characterising lemmas** — one per defining
   equation. Each one's body is `unfold Foo in
   reflexivity(<expected RHS>)` (or `unfold Foo in
   Equality.transport_proposition(...)` when the equation
   case-splits on something).
   Example for `Natural.monus`:
   ```math
   theorem Natural.monus_zero_left (b : Natural)
           : Natural.monus(0, b) = 0 :=
     unfold Natural.monus in reflexivity(Natural, 0)
   theorem Natural.monus_succ_zero (k : Natural)
           : Natural.monus(successor(k), 0) = successor(k) :=
     unfold Natural.monus in reflexivity(Natural, successor(k))
   theorem Natural.monus_succ_succ (k j : Natural)
           : Natural.monus(successor(k), successor(j))
             = Natural.monus(k, j) :=
     unfold Natural.monus in
       reflexivity(Natural, Natural.monus(k, j))
   ```
3. Audit downstream proofs. Each `reflexivity` that used to close
   via `Foo`'s ι-reduction now needs a citation to a
   characterising lemma. Common idioms:
   - `claim equation_for_foo : Foo(args) = explicit_value by
     <characterising lemma>` then continue.
   - Bridge `rewrite` failures by ascribing the goal's `Foo(…)`
     subexpression to the form the lemma produces.
   - For inductively recursive proofs that previously rode the
     kernel's ι, add an explicit calc step `Foo(succ k) =
     <recursive case body> by <succ_succ lemma>`.

### Failure modes to expect

- **`addDefinition: body type does not match declared type`** at
  the theorem boundary — the proof's inferred type sits in the
  unfolded view and the declared type in the opaque view. Wrap the
  proof body in `unfold Foo in <body>` if it really should compute,
  or add a characterising-lemma citation to bridge.
- **`rewrite(eq, term): left endpoint does not appear`** — the
  goal type was the un-reduced opaque shape but you handed
  `rewrite` an equation whose LHS is from the unfolded view. Apply
  the characterising lemma first to align shapes.
- **`Application: argument type does not match Pi domain`** when
  recursing — the recursive call expects the un-reduced shape but
  you fed it the reduced one. Bridge with the appropriate
  characterising lemma (typically `Foo_succ_succ` or
  `Foo_succ_fits`).

### The Test/opaque_test.math demo

`library/Test/opaque_test.math` covers the smallest end-to-end:
`myDouble` opaque, `unfold myDouble in reflexivity(4)` to prove
`myDouble(2) = 4`. Read that file first if the discipline above
feels abstract.

## File organization

```
library/
  axioms.math          -- foundational axioms (propext, function ext, etc.)
  Logic/               -- Equality, Quotient machinery, exists, etc.
  Natural/             -- Naturals, all the way to bezout, padic_valuation
  Integer/             -- Integers as Natural × Natural quotient
  Rational/            -- Rationals as (Integer, Natural) quotient
  Real/                -- Reals as Cauchy quotient of Rationals
  PAdic/               -- p-adics as p-adic-Cauchy quotient of Rationals
  Algebra/             -- IsMonoid, IsGroup, IsRing, IsCommutativeRing
  Test/                -- small test files for features (not math content)
```

Each module's files are layered (basics → operations → laws →
instances). Imports flow up; you can't import a layer above you.

## Kernel quirks to know

See `~/.claude/projects/-Users-alvaro-claude-math/memory/kernel_quirks.md`
for the full list. Highlights:

- **No large elimination from Prop.** Non-empty Prop inductives have
  motive fixed at Prop. Empty Prop inductives (False) admit large
  elimination.
- **Function-wrapping for cases-on-expression** (see "cases with
  hypothesis" above).
- **Identical-printed-types universe issues** can arise when nested
  polymorphic functions get inferred universe parameters that don't
  unify the way the user expects. Workaround: add explicit `.{u, v}`
  annotations.

## Memory

The user has persistent memory at
`~/.claude/projects/-Users-alvaro-claude-math/memory/`. See `MEMORY.md`
there for the index. Notable entries:

- `padic_construction_status.md` — p-adic construction is complete
  (operations + ring laws + IsCommutativeRing instance).
- `software_engineering_for_math.md` — math library design follows
  SE best practices (descriptive names, refactoring), not math
  writing traditions.
- `keep_git_current.md` — commit coherent pieces as they land.

## Operator overloading

`operator (sym) on (T1, T2) := F;` registers `sym` to dispatch on
the heads of T1 and T2. T1 and T2 must be the heads of types, not
parameterized type applications. So:

- `operator (+) on (Integer, Integer)` works.
- `operator (+) on (PAdic, PAdic)` would conceptually work but
  `PAdic.add` takes `(p, primality, x, y)`, not `(x, y)`. Once `(p,
  primality)` become implicit on `PAdic.add`, the operator overload
  will work.

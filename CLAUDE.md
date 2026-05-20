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

## Multi-pattern bindings

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

### `let` does not ζ-reduce across calc steps

```math
let halvedEpsilon : Rational := Rational.halve(epsilon);
…
calc -halvedEpsilon + -halvedEpsilon
   = -(halvedEpsilon + halvedEpsilon)
       by Equality.symmetry(
              Rational.negate_add(halvedEpsilon, halvedEpsilon))
   = -epsilon
       by congruenceOf(Rational.negate,
              Rational.halve_doubled(epsilon))
```

The calc fails at the second step: the kernel sees
`Rational.halve_doubled(epsilon) : Rational.halve(epsilon) +
Rational.halve(epsilon) = epsilon` and won't ζ-unfold
`halvedEpsilon` to align the types. Don't use `let` for value
abbreviations — write the long names out, or factor the repeated
expression into its own top-level theorem.

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

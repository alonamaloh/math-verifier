# Quotient idioms

Short forms for every Quotient operation, the `construction` intro form, and pattern-binders (`by_representatives`, `cases`, `take`, `suppose`) on quotients.

*(Part of the project conventions; see `CLAUDE.md` for the index.)*

*For the complete machinery (kernel primitives, the auto-prover
sound-coercion / exact-bridge, the cases the sugar can't yet express, and a
diagnosis of the bloat with directions for a smaller design), see
`docs/quotients-reference.md`.*

## Quotient idioms — use the short forms

The elaborator has type-and-relation inference for every Quotient
operation. Use the SHORT forms by default. The verbose forms exist
only as fallbacks when the elaborator can't infer; expect that to
be rare.

### Quotient.class_of(rep)

```math
-- Short (preferred): T inferred from rep's type, R from expected type.
-- (`Rational` is opaque, so the class_of is pierced once with `unfold Rational`;
-- normally you'd write `Rational.fraction(…)` and never see this.)
definition Rational.zero : Rational :=
  unfold Rational in
    Quotient.class_of(RationalRepresentative.make(
        Integer.zero, Integer.one, Integer.one_is_nonzero))

-- Verbose (avoid unless necessary):
definition Rational.zero : Rational :=
  unfold Rational in
    Quotient.class_of(RationalRepresentative, RationalEquivalent,
                RationalRepresentative.make(
                    Integer.zero, Integer.one, Integer.one_is_nonzero))
```

The short form needs an expected type of shape `Quotient(T, R)` from
context (the surrounding theorem's return type, or an enclosing
argument). The short form does NOT fire in these positions:
- Operand of unary `-`, binary `+`, `*`, `=`, `<`, `≤`.
- Third arg of `Equality.transport_proposition(A, P, x, ...)` (the
  carrier `A` doesn't propagate inward).
- Arguments of polymorphic functions like `reflexivity`,
  `Equality.transitivity`, `congruenceOf`, `Or.eliminate`,
  `Exists.eliminate` (those elaborate args without an expected type).
- Inside `congruenceOf` lambdas without an explicit annotation.

**Trick:** in those positions, an explicit type ascription on the
`mk` recovers the inference: `(Quotient.class_of(rep) : Rational)`. The
ascription is the expected type the short form needs.

```math
-- Fails:
Rational.absolute_value(Quotient.class_of(rep))

-- Works:
Rational.absolute_value((Quotient.class_of(rep) : Rational))

-- Also works (verbose fallback):
Rational.absolute_value(
    Quotient.class_of(RationalRepresentative, RationalEquivalent, rep))
```

### Quotient.sound(x, y, proof)

```math
-- Short (preferred): T from x's type, R from proof.
Quotient.sound(rep1, rep2, equivProof)

-- Verbose:
Quotient.sound(RationalRepresentative, RationalEquivalent,
                rep1, rep2, equivProof)
```

### Equal classes ⇒ equivalent representatives (the `exact`-bridge)

The converse of `Quotient.sound`: from a proof that two classes are equal,
`Quotient.exact` recovers the equivalence of their representatives. You never
name it. The auto-prover discharges a goal `R(a, b)` whenever an in-scope
hypothesis proves `Quotient.class_of(a) = Quotient.class_of(b)` — so a proof reads "since
the classes are equal" and the goal closes as a bare stated fact or a
by-less chain step. The class-equality endpoints may be `construction`
forms or coercions that δ-reduce to `mk` (the match WHNFs them).

```math
-- Hypothesis in scope: `equality : (b : Integer) = -(m : Integer)`,
-- i.e. the classes [b/0] and [0/m] are equal.

-- Before — naming the axiom:
IntegerEquivalent(IntegerRepresentative.make(b, 0),
                  IntegerRepresentative.make(0, m))
  by Quotient.exact(IntegerRepresentative.make(b, 0),
         IntegerRepresentative.make(0, m), equality)
  as representativeEquivalence;

-- After — the bridge closes it from `equality`:
IntegerEquivalent(IntegerRepresentative.make(b, 0),
                  IntegerRepresentative.make(0, m))
  as representativeEquivalence;
```

The goal may be stated as the relation `R(a, b)` or in its unfolded form (the
cross-multiplied equation, e.g. as a chain step) — the match is up to
definitional equality, so both work. A flipped fact (`mk b = mk a` for a goal
`R(a, b)`) is caught via the symmetry-flip retry recursing onto `R(b, a)`;
this is what lets nested `0 ≠ 1`-style descents (Rational → Integer → Natural)
collapse to a sequence of bare stated facts with no `Equality.symmetry`:

```math
theorem Rational.zero_not_equal_one : Not(Rational.zero = Rational.one) :=
  (zeroEqOne : Rational.zero = Rational.one) ↦ {
    Integer.zero = Integer.one as integerZeroEqualsOne;
    (1 : Natural) = 0;
    done
  }
```

Scope: any quotient whose carrier has a **registered** `IsEquivalenceRelation`
instance — with or without parameters. No-parameter instances cover the
Integer / Rational / Real / PAdic representatives; parameterised ones are
resolved by unification (e.g. `IntegerMod.equivalence(m)` for relation
`CongruentModulo(m)` over the plain `Integer` carrier). Still keep the
explicit `Quotient.exact(T, R, instance, x, y, proof)` when (a) the carrier
is itself a complex application with a Ring/CommutativeRing impedance the
unifier can't bridge (`RingModulo` / `ComplexNumber` embedding —
`Ring.carrier(CommutativeRing.ring(c))`), or (b) the equivalence is a *local*
hypothesis rather than a registered instance (the `Group.SameCoset` coset
proofs).

### Quotient.lift(f, h, q)

```math
-- Short (preferred): T, R, U all inferred.
Quotient.lift(
    (rep) ↦ ...,
    (rep1 rep2 hyp) ↦ ...,
    q)

-- Verbose:
Quotient.lift(RationalRepresentative, RationalEquivalent, Rational,
               ...,
               ...,
               q)
```

### `definition … by representatives … well_defined by …`

The preferred way to define a **function out of a quotient**: state the
formula on a representative and the well-definedness proof, and never name
`Quotient.lift` / `Quotient.sound`. Reads as the textbook "define `F` by
picking a representative; this is well-defined because the formula
respects the relation".

```math
definition Rational.negate : Rational → Rational
  by representatives rep ↦ Quotient.class_of(Rational.negate_representatives(rep))
  well_defined by Rational.negate_respects
```

Desugars to `(x) ↦ Quotient.lift((rep) ↦ <body>, <proof>, x)`; the
short-form lift infers `(T, R, U)`. The `well_defined` proof discharges
the respect obligation `(x y : T) → R(x, y) → <body>[rep:=x] =
<body>[rep:=y]`, and a proof of the bare equivalence `R(g x, g y)` (when
the body is `mk(g rep)`) is accepted directly — the elaborator wraps
`Quotient.sound`. Both a named lemma (`well_defined by Rational.negate_respects`)
and an inline `(a b) (e) ↦ …` proof work.

Scope: **unary or binary**, **bare-name** representatives. Apply a
representative-level function in the body (`mk(negate_representatives(rep))`),
as the library does — do not destructure the representative in the pattern.

A binary operation gives two representatives and two `well_defined` proofs —
the first- and second-argument respect proofs, in that order — and the
elaborator synthesises the nested lift (no `Quotient.lift`/`Quotient.sound`
named):

```math
definition Integer.add : Integer → Integer → Integer
  by representatives a, c ↦ Quotient.class_of(Integer.add_representatives(a, c))
  well_defined by Integer.add_respects_first, Integer.add_respects_second
```

Still hand-written (no sugar yet): a lift over a quotient argument that is
**not the sole argument** (e.g. `Polynomial.coefficientOf(p, index)` lifts
over `p` with `index` alongside), and a lift whose definition is `opaque`
(e.g. `Rational.IsNonneg`, deliberately opaque — see opaque.md). Parameterised
carriers (`Group.SameCoset(G, ·)`, …) likewise keep the explicit lift.

### Quotient.induct(motive, atRep, q) — and motive inference

The motive can be omitted (or written as `_`) when it would be
recoverable from the surrounding goal type by abstracting the
scrutinee(s). This is the default-style for any quotient elimination
whose goal mentions the scrutinees.

```math
-- Shortest form: motive inferred. Goal is abstracted over q to form
-- the motive.
Quotient.induct(atRep, q)

-- Equivalent with explicit `_` (sometimes clearer in code review).
Quotient.induct(_, atRep, q)

-- Verbose, when you want a specific motive shape (e.g. to thread
-- additional hypotheses).
Quotient.induct(
    (xArg : Rational) ↦ P(xArg),
    (rep : RationalRepresentative) ↦ proofAtRep(rep),
    x)
```

### Quotient.induct_two(motive, atRep, q1, q2)

Same pattern, 3 or 4 args. For binary laws.

```math
Quotient.induct_two(at_make_lemma, x, y)
```

### Quotient.induct_three(motive, atRep, q1, q2, q3)

4 or 5 args, for ternary laws (associativity, distributivity).

```math
Quotient.induct_three(at_make_lemma, x, y, z)
```

### `construction` — name the quotient introduction form

`construction Name(args) : T := <intro body>` declares a **canonical
introduction form** for a quotient. It is an ordinary *transparent*
definition (the kernel δ-reduces `Name(args)` to the body), so it is
def-equal to the underlying `Quotient.class_of(...)` and needs no special
support in `cases` / `lift` / `reflexivity`. The win is readability:
proofs and printed goals say `Rational.fraction(n, d, dNonzero)` instead of
`Quotient.class_of(RationalRepresentative.make(n, d, dNonzero))`. (`Rational` is an
opaque type, so the body pierces it once with `unfold Rational`; see
`opaque.md`.)

```math
construction Rational.fraction
        (n d : Integer) (dNonzero : ¬(d = Integer.zero)) : Rational :=
  unfold Rational in Quotient.class_of(RationalRepresentative.make(n, d, dNonzero))

-- Downstream, prefer the named form:
definition Rational.zero : Rational :=
  Rational.fraction(Integer.zero, Integer.one, Integer.one_is_nonzero)
```

It parses exactly like a `definition` (same binder / `: T` / `:= body`
syntax), so the return type is written explicitly — that expected type
is also what lets the short `Quotient.class_of(rep)` body infer its relation.

**Soft convention (preferred, not enforced):** once a quotient has a
`construction` intro and a `by_representatives` eliminator, prefer them
over naming the raw representative constructor
(`RationalRepresentative.make`) outside the quotient's defining module.
The raw constructor remains available as an escape hatch; this is a
readability convention, not an elaborator-enforced restriction.

## Public quotient destructuring

The unifying principle: a binder accepts a pattern, and the elaborator
picks the eliminator from the type. This is the standard idiom for
"WLOG pick a representative" / "let n = k + 1" intros.

### `by_representatives` — the multi-scrutinee elimination idiom

`by_representatives x as <pat>, y as <pat>, … => body` is the preferred
"WLOG pick representatives" form. It applies the quotient eliminator once
per scrutinee while keeping that machinery off the page. The pattern after
`as` is a tuple `⟨a, b⟩` (the carrier's
sole constructor is resolved from the type — `RationalRepresentative.make`
need not be named), an explicit constructor pattern, or a bare name.

```math
theorem Rational.triangle_inequality (x y : Rational)
        : abs(x + y) ≤ abs(x) + abs(y) :=
  by_representatives x as ⟨n1, d1⟩, y as ⟨n2, d2⟩ =>
    Rational.triangle_inequality_at_representatives(n1, n2, d1, d2)
```

### Hypotheses refine through representative selection

Hypotheses about `x` (e.g. `xPos : 0 < x`) are threaded through the
destructure automatically, so the inner body sees their representative-level
forms.

```math
theorem Rational.multiply_positive_positive
        (x y : Rational) (xPos : 0 < x) (yPos : 0 < y)
        : 0 < x * y :=
  by_representatives
      x as ⟨n_x, d_x, dxNonzero⟩,
      y as ⟨n_y, d_y, dyNonzero⟩ => {
    …use xPos (seen here as 0 < [n_x/d_x]) …
  }
```

### `take x as <pattern> : T;` — statement-level intro with destructure

In a `{ … }` block body, `take x as <pattern> : T;` introduces a
Pi-binder of type T and immediately destructures it through the type’s
registered public eliminator.

For a quotient, the preferred pattern is the mathematical
`representative(…)` spelling (A5) — the carrier's constructor is
resolved from the type and never appears on the page:

```math
theorem Integer.triangle_inequality
        : (x y : Integer)
          → abs(x + y) ≤ abs(x) + abs(y) := {
  take x as representative(a, b) : Integer;
  take y as representative(c, d) : Integer;
  Integer.triangle_inequality_at_representatives(a, b, c, d)
}
```

For existential hypotheses, use `choose` rather than destructuring their
internal tuple representation:

```math
choose witness such that P(witness) from existenceProof;
```

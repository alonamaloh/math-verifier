# Quotient idioms

Short forms for every Quotient operation, the `construction` intro form, and pattern-binders (`by_representatives`, `cases`, `take`, `suppose`) on quotients.

*(Part of the project conventions; see `CLAUDE.md` for the index.)*

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
argument). The short form does NOT fire in these positions:
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

### Equal classes ⇒ equivalent representatives (the `exact`-bridge)

The converse of `Quotient.sound`: from a proof that two classes are equal,
`Quotient.exact` recovers the equivalence of their representatives. You never
name it. The auto-prover discharges a goal `R(a, b)` whenever an in-scope
hypothesis proves `Quotient.mk(a) = Quotient.mk(b)` — so a proof reads "since
the classes are equal" and the goal closes as a bare claim or a by-less calc
step. The class-equality endpoints may be `construction` forms or coercions
that δ-reduce to `mk` (the match WHNFs them).

```math
-- Hypothesis in scope: `equality : (b : Integer) = -(m : Integer)`,
-- i.e. the classes [b/0] and [0/m] are equal.

-- Before — naming the axiom:
claim representativeEquivalence
      : IntegerEquivalent(IntegerRepresentative.make(b, 0),
                          IntegerRepresentative.make(0, m))
  by Quotient.exact(IntegerRepresentative.make(b, 0),
         IntegerRepresentative.make(0, m), equality);

-- After — the bridge closes it from `equality`:
claim representativeEquivalence
      : IntegerEquivalent(IntegerRepresentative.make(b, 0),
                          IntegerRepresentative.make(0, m));
```

The goal may be stated as the relation `R(a, b)` or in its unfolded form (the
cross-multiplied equation, e.g. as a calc step) — the match is up to
definitional equality, so both work. A flipped fact (`mk b = mk a` for a goal
`R(a, b)`) is caught via the symmetry-flip retry recursing onto `R(b, a)`;
this is what lets nested `0 ≠ 1`-style descents (Rational → Integer → Natural)
collapse to a sequence of bare claims with no `Equality.symmetry`:

```math
theorem Rational.zero_not_equal_one : Not(Rational.zero = Rational.one) :=
  (zeroEqOne : Rational.zero = Rational.one) ↦ {
    claim integerZeroEqualsOne : Integer.zero = Integer.one;
    claim successorZeroEqualsZero : successor(0) = (0 : Natural);
    Natural.successor_not_zero(0, successorZeroEqualsZero)
  }
```

Scope: concrete-carrier quotients — those whose carrier has a registered
`IsEquivalenceRelation` instance with no parameters (Integer / Rational /
Real / PAdic representatives, …). Parameterised carriers
(`CongruentModulo(m)`, `SameCoset(G, ·)`) are not yet covered; there, keep the
explicit `Quotient.exact(T, R, instance, x, y, proof)`.

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
  by representatives rep ↦ Quotient.mk(Rational.negate_representatives(rep))
  well_defined by Rational.negate_respects
```

Desugars to `(x) ↦ Quotient.lift((rep) ↦ <body>, <proof>, x)`; the
short-form lift infers `(T, R, U)`. The `well_defined` proof discharges
the respect obligation `(x y : T) → R(x, y) → <body>[rep:=x] =
<body>[rep:=y]`, and a proof of the bare equivalence `R(g x, g y)` (when
the body is `mk(g rep)`) is accepted directly — the elaborator wraps
`Quotient.sound`. Both a named lemma (`well_defined by Rational.negate_respects`)
and an inline `(a b) (e) ↦ …` proof work.

Scope (current): **unary**, **bare-name** representative. Apply a
representative-level function in the body (`mk(negate_representatives(rep))`),
as the library does — do not destructure the representative in the
pattern. Binary operations still write the nested `Quotient.lift` form by
hand.

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
def-equal to the underlying `Quotient.mk(...)` and needs no special
support in `cases` / `lift` / `reflexivity`. The win is readability:
proofs and printed goals say `Rational.fraction(n, d)` instead of
`Quotient.mk(RationalRepresentative.make(n, d))`.

```math
construction Rational.fraction (n : Integer) (d : Natural) : Rational :=
  Quotient.mk(RationalRepresentative.make(n, d))

-- Downstream, prefer the named form:
definition Rational.zero : Rational := Rational.fraction(Integer.zero, 0)
```

It parses exactly like a `definition` (same binder / `: T` / `:= body`
syntax), so the return type is written explicitly — that expected type
is also what lets the short `Quotient.mk(rep)` body infer its relation.

**Soft convention (preferred, not enforced):** once a quotient has a
`construction` intro and a `by_representatives` eliminator, prefer them
over naming the raw representative constructor
(`RationalRepresentative.make`) outside the quotient's defining module.
The raw constructor remains available as an escape hatch; this is a
readability convention, not an elaborator-enforced restriction.

## Patterns in binders — `take`, `suppose`, `cases` on quotients

The unifying principle: a binder accepts a pattern, and the elaborator
picks the eliminator from the type. This is the standard idiom for
"WLOG pick a representative" / "let n = k + 1" intros.

### `by_representatives` — the multi-scrutinee elimination idiom

`by_representatives x as <pat>, y as <pat>, … ↦ body` is the preferred
"WLOG pick representatives" form. It desugars to nested quotient-`cases`
(one per scrutinee), so it is exactly the nested `cases` below but reads
as one line. The pattern after `as` is a tuple `⟨a, b⟩` (the carrier's
sole constructor is resolved from the type — `RationalRepresentative.make`
need not be named), an explicit constructor pattern, or a bare name.

```math
theorem Rational.triangle_inequality (x y : Rational)
        : abs(x + y) ≤ abs(x) + abs(y) :=
  by_representatives x as ⟨n1, d1⟩, y as ⟨n2, d2⟩ ↦
    Rational.triangle_inequality_at_representatives(n1, n2, d1, d2)
```

### `cases` on a quotient — direct destructure

The pattern can be a bare name (bind the rep), a constructor pattern
over the carrier type (destructure the rep), a tuple `⟨a, b⟩` (same, with
the constructor name resolved from the type), or the explicit
`Quotient.mk(<inner>)` wrap (legacy). Prefer `by_representatives` (above)
when destructuring one or more scrutinees with no extra `cases` plumbing.

```math
-- Bare name: bind rep_x to the representative.
cases x { | rep_x ↦ …use rep_x… }

-- Constructor pattern: destructure the rep directly.
cases x { | IntegerRepresentative.make(a, b) =>
    …use a and b… }

-- Tuple pattern: destructure without naming the constructor.
cases x { | ⟨a, b⟩ => …use a and b… }

-- Two-binder cases nest naturally (or use `by_representatives`):
cases x { | IntegerRepresentative.make(a, b) =>
  cases y { | IntegerRepresentative.make(c, d) =>
    …use a, b, c, d… } }
```

### `cases x refining h1, h2 { … }` — destructure with hypothesis refinement

When you've named hypotheses about `x` (e.g. `xPos : 0 < x`), use
`refining` to thread them through the destructure so the inner body
sees their refined types. Works on inductive scrutinees AND quotient
scrutinees, with any number of refining names.

```math
theorem Rational.multiply_positive_positive
        (x y : Rational) (xPos : 0 < x) (yPos : 0 < y)
        : 0 < x * y :=
  cases x refining xPos { | RationalRepresentative.make(n_x, d_x) =>
    cases y refining yPos { | RationalRepresentative.make(n_y, d_y) =>
      …use xPos (now refined to 0 < [n_x/d_x]) … } }
```

### `take x as <pattern> : T;` — statement-level intro with destructure

In a `{ … }` block body, `take x as <pattern> : T;` introduces a
Pi-binder of type T and immediately destructures it. Equivalent to
`take x : T; cases x { | <pattern> => <rest> };`. Dispatch is
type-directed: inductive T uses cases; quotient T uses the
quotient-cases path above.

```math
theorem Integer.triangle_inequality
        : (x y : Integer)
          → abs(x + y) ≤ abs(x) + abs(y) := {
  take x as IntegerRepresentative.make(a, b) : Integer;
  take y as IntegerRepresentative.make(c, d) : Integer;
  Integer.triangle_inequality_at_representatives(a, b, c, d)
}
```

### `suppose <P> as <pattern>;` — destructure on intro for hypotheses

Symmetric form for propositional intros. The pattern can be a bare
name (current behavior) or a tuple/constructor pattern (destructure
into named pieces).

```math
suppose ∃ (n : Natural). P(n) as ⟨witness, proof⟩;
-- equivalent to:
-- suppose ∃ (n : Natural). P(n) as h;
-- obtain ⟨witness, proof⟩ from h;
```

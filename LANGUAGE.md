# LANGUAGE.md — writing proofs in this library

This is a guide for people writing math proofs in this project's
language. It focuses on **how to maximize clarity** — which idioms read
as math, which ones leak CIC bureaucracy, and how to choose between
them. For the lower-level invariants (the kernel's reduction rules,
when the elaborator can't infer things), see `CLAUDE.md`.

The single overriding goal: **a proof should read like the math
a textbook would write**, with the kernel doing the typechecking. A
human should be able to scan a proof and follow the argument without
parsing CIC bureaucracy. Verbosity that aids comprehension is a
feature, not a cost.

## The shape of a proof

A proof body is one of three shapes:

**1. A direct term.** Most concise; right when the proof IS a single
named lemma or a constructor application.

```math
theorem Real.zero_less_one : Real.zero < Real.one :=
  Real.LessThan.from_rational(Rational.zero_less_one)
```

**2. A `calc` chain.** For equational/inequalitiy reasoning where each
intermediate form is named. Reads as a textbook equation chain.

```math
theorem Integer.subtract_swap (x y : Integer) : x - y = -(y - x) :=
  calc x - y
     = -(y - x)
```

**3. A `{ … }` block.** A sequence of statements (`claim`, `take`,
`obtain`, `let`, `cases`, `by_induction`, `calc`, `note`, etc.)
followed by a final expression. Reads as math prose with paragraphs.

```math
theorem Integer.triangle_inequality
        : (x y : Integer)
          → abs(x + y) ≤ abs(x) + abs(y) := {
  take x as IntegerRepresentative.make(a, b) : Integer;
  take y as IntegerRepresentative.make(c, d) : Integer;
  Integer.triangle_inequality_at_representatives(a, b, c, d)
}
```

Pick the shape that matches what the math looks like. A two-step
calculation is a calc. A multi-paragraph argument is a block. A
straight cite is a direct term.

## Names

- **No abbreviations in declared names.** `representative`, not `rep`.
  Local variables inside a proof can be `rep` — short names are fine
  when their scope is short.
- **Descriptive binder names.** `halvedEpsilonPositive`, not `hep`.
- **The convention `convention p : Natural with Natural.is_prime(p)`**
  (at the top of a file) means later `theorem`/`definition`
  declarations that mention `p` get `{p : Natural} {_ : is_prime(p)}`
  prepended implicitly. Useful for whole files about primes.

## Numbers, equality, and the calc kit

### Numeric literals over Peano constructors

Use `0`, `1`, `2` instead of `zero`, `successor(zero)`,
`successor(successor(zero))` everywhere — they're definitionally
equal, the kernel reduces them interchangeably, and the numeric form
reads as math. Same for `1 + n` over `successor(n)` in
expression positions.

The exception is pattern positions:

```math
cases n {
  | zero          => baseProof    -- bare constructor required
  | successor(k)  => stepProof(k)
}
```

And occasionally inside structural-reduction-sensitive proofs (see
`CLAUDE.md`'s "When `successor(n)` wins anyway").

### `=`, `≤`, `<`, `≥`, `>` in calc chains

`calc` accepts all five as step separators. The chain's overall
relation is the strongest one across steps: any `<` or `>` makes it
strict, otherwise `≤`/`≥` if present, otherwise `=`. Mixing forward
(`<`/`≤`) with backward (`>`/`≥`) is rejected; `=` is allowed in
either direction.

### `by lemma` in a `=` step infers congruence

If the `by` proof has type `Equality(T, a, b)` and the calc step's two
endpoints differ in a unique single position at `(a, b)`, the
elaborator auto-wraps with `Equality.congruence` and you don't have
to write the motive lambda. The user supplies the equation, the
elaborator finds the slot. (Same direction or symmetric.)

### `rewrite(eq)` and `rewrite(eq, term)`

Two forms. **1-arg in calc context**: `by rewrite(L)` for `L : a = b`
finds the unique structural occurrence of `a` on the calc step's LHS
and replaces it with `b`. **2-arg term-level**: `rewrite(eq, term)`
for `eq : a = b` and `term : P(a)` returns a term of type `P(b)`.
Replaces explicit `Equality.transport_proposition` everywhere outside
the few cases that need a manual motive.

### `ring` first, then explicit

`ring` (v2: polynomial normalization, ±1 coefficients) handles
essentially every commutative-ring identity you'd write by hand on
Natural, Integer, Rational, Real, or PAdic. Default for ring
equalities: `:= ring` or `(ring : LHS = RHS)` inside a `rewrite`.
Reach for explicit `add_commutative`/`add_associative`/`congruenceOf`
only after ring fails (coefficient outside ±1, missing axioms in
scope, etc.).

## Case analysis and induction

### `cases x { … }` — case split

Bare constructor patterns. The scrutinee must be a local-binder
variable (a parameter or let-binding).

```math
cases Integer.absolute_value_natural(x) {
  | zero          => …
  | successor(k)  => …
}
```

### `cases x with refinedEq { … }` — split with retained equation

Adds an equation `refinedEq : <scrutinee> = <constructor pattern>` to
each arm. Used when the goal mentions the scrutinee in a way the
constructor reduction alone won't expose.

### `cases x refining h1, h2 { … }` — refine in-scope hypotheses

Lifts the named binders into the recursor's motive so each arm sees
their types refined by the constructor match. Use when you have
hypotheses about `x` that need to update their shape per arm.

```math
cases x refining xPos { | RationalRepresentative.make(n, d) =>
  -- xPos : 0 < x has been refined to 0 < [(n, d)]
  …
}
```

Works on inductive and quotient scrutinees, with any number of
refining names.

### `by_induction on n with IH { … }`

Replaces pattern-match definitions for typical induction-on-Natural.
The `IH` is in scope in the `successor(k)` arm as a hypothesis about
`k`. Refines too: `by_induction on n with IH refining h1, h2 { … }`.

```math
theorem Natural.add_zero_right : (n : Natural) → n + 0 = n :=
  function (n : Natural) =>
    by_induction on n with IH {
      case zero:           reflexivity(Natural, 0)
      case successor(k):   congruenceOf(successor, IH)
    }
```

For strong recursion (you need IH for all `k < n`), use
`by_strong_induction on n with IH { … }`.

### `decide P { yes m => … | no n => … }` — classical case split

The canonical form for "P or not P" reasoning. Replaces both
`cases Logic.excluded_middle(P)` and the bisection-style
`cases Logic.classical_decidable(P) with eq { … }`. The elaborator's
motive search finds buried `classical_decidable(P)` occurrences (e.g.
inside `bisectionStepWithDec`) and abstracts them, so each arm proves
the ι-reduced shape automatically.

### Quotient destructure — pick a representative

For a quotient scrutinee (`x : Integer`, `x : Rational`, `x : Real`,
`x : PAdic(p, _)`), `cases x` lets you destructure as a
representative. Three accepted patterns:

```math
cases x { | rep_x => … }                                -- bind rep
cases x { | IntegerRepresentative.make(a, b) => … }      -- destructure rep
cases x { | Quotient.mk(IntegerRepresentative.make(a, b)) => … }  -- explicit
```

The middle form is the math-natural one and what to default to.

## Hypothesis intros and destructure

### `take x : T;` — introduce a Pi binder

Statement-level form. Wraps the rest of the block in
`function (x : T) => …`. Reads as "let x be of type T" / "take an
arbitrary x : T". Use it whenever the theorem signature is a `Pi`
type that needs intros.

### `take x as <pattern> : T;` — intro with immediate destructure

Type-directed dispatch: inductive T → `cases x`; quotient T →
quotient-cases via `Quotient.induct`. The pattern is the destructure
shape.

```math
take x as IntegerRepresentative.make(a, b) : Integer;
-- x is bound (a, b are too); the rest of the block proves the
-- goal at the destructured form.
```

### `suppose P as <name>;` — introduce a hypothesis

Symmetric form for proposition intros.

```math
suppose 0 < epsilon as epsilonPositive;
```

### `suppose P as <pattern>;` — intro and destructure

```math
suppose ∃ (n : Natural). Q(n) as ⟨witnessValue, witnessProof⟩;
```

### `obtain ⟨a, b⟩ from h;` — destructure an existing value

For an `h : ∃ x. P(x)` or `h : And(A, B)`, destructure into named
pieces. Also works with constructor patterns for any single-
constructor inductive, and with quotient patterns for a quotient
value (where it routes through `Quotient.induct`).

```math
obtain ⟨k, witnessEquation⟩ from Natural.subtraction_witness(a, b, h);
obtain IntegerRepresentative.make(a, b) from x;  -- x : Integer
```

### `choose N such that P(N);` — math-prose existential

```math
choose N such that converges_within_epsilon_of(s, N);
-- Sugar for: obtain ⟨N, _⟩ from someExists; claim P(N) by …
```

### `let x : T := V;` — local abbreviation

ζ-tracked: the kernel sees through `x` to `V` whenever needed
(`isDefinitionallyEqual`, the auto-prover's structural matchers, the
diff-bridge walker). Use freely for value abbreviations when one
expression appears 3+ times in a proof.

## Claims — sequence-of-claims style

When a proof has several distinct subgoals, write them as a sequence
of `claim` lines and assemble the result from the named claims:

```math
{
  claim epsilonHalvedPositive : 0 < halve(epsilon)
    by Rational.halve_positive(epsilon, epsilonPositive);
  claim sumWithinHalf : abs(s(m) - s(n)) < halve(epsilon)
    by sCauchy(halve(epsilon), epsilonHalvedPositive, m, n, mLarge, nLarge);
  -- assemble: …
}
```

The structure makes the argument legible. A reader can skim the claims
to see the shape before reading the inner proofs.

### Calc as a statement

`calc … as NAME;` and bare `calc …;` at statement position bind the
chain's result into local scope:

```math
calc (aInt * yPrime - qInt * bInt * yPrime)
   = (aInt - qInt * bInt) * yPrime
   = rInt * yPrime                            as factoredEqualsRYPrime;
-- factoredEqualsRYPrime is now in scope
```

Bare `calc …;` (no `as`) synthesizes an anonymous name and the
auto-prover finds the equation by type-match. Use `as NAME` only when
a later step textually references the name; the lint warns if you
use `as NAME` and never type NAME afterward.

### `note goal : T;` and `note <prop>;` — explicit assertions

`note goal : T;` asserts the current expected type IS T (kernel
defeq), continues the body with no semantic change. Reads as "we
need to show that …". Useful right after `take`s or after a `cases`
split to document the goal at a point where a reader benefits.

`note <prop>;` asserts that `<prop>` is closable by the auto-prover
at the current point, continues with no change. Reads as "note
that …" — a parenthetical aside for a fact the reader benefits from
seeing even if the surrounding proof would close without it.

## When the elaborator can't infer

### `Quotient.mk(rep)` short form

Needs an expected type of shape `Quotient(T, R)` from context. It
fails in: operand of unary `-`, binary `+`, `*`, `=`, `<`, `≤`; third
arg of `Equality.transport_proposition`; arguments of polymorphic
functions (`reflexivity`, `Equality.transitivity`, `congruenceOf`,
`Or.eliminate`, `Exists.eliminate`); inside `congruenceOf` lambdas
without an annotation.

**Trick:** ascribe the type. `(Quotient.mk(rep) : Rational)` recovers
the inference.

### `Quotient.induct(atRep, q)` — motive inferred

The motive is recovered by abstracting the scrutinee(s) in the
expected type. If the goal doesn't mention the scrutinee, the
constant-motive fallback kicks in. If the motive should have a
specific shape (e.g. threading hypotheses through `→`), supply it
explicitly OR use `cases ... refining` and let the elaborator
construct the chain.

### Explicit `_` placeholder

For most of the inference-bearing constructs (`Quotient.induct`,
`Quotient.induct_two`, etc.), you can write `_` in place of the
inferred argument when you want the call shape to be explicit:

```math
Quotient.induct(_, atRep, q)         -- same as Quotient.induct(atRep, q)
```

### `?` — goal-driven argument inference

A `?` in a positional argument asks the elaborator to fill that slot
by unifying the lemma's conclusion against the goal type and the
lemma's argument types against the supplied (non-`?`) args' types.

```math
-- Without `?` — every argument explicit:
claim oneEqualsTwoPlus : 1 = successor(successor(n))
  by Natural.successor_injective(1, successor(successor(n)),
                                  twoEqualsThreePlus);

-- With `?` — the two Natural args are recoverable from the goal:
claim oneEqualsTwoPlus : 1 = successor(successor(n))
  by Natural.successor_injective(?, ?, twoEqualsThreePlus);
```

`?` works wherever:
- The call is a known function (or `axiom`/`definition`) by name.
- The goal type and/or the supplied non-`?` args' types contain enough
  information to fix every `?` position by structural unification.

When the inference fails, the elaborator reports which positions
couldn't be resolved and shows the expected return type.

This is **strictly more powerful** than declaring args as implicit
`{a b : Natural}`: implicit args use only the supplied args' types,
while `?` uses the goal type as well. It's also opt-in per call site —
the lemma's declared form is unchanged.

## Opaque definitions and unfolds

`opaque definition Foo : … := …` hides `Foo`'s body from kernel
reduction. Downstream proofs must use **characterising lemmas** — one
per defining equation — to reason about `Foo`. `unfold Foo in <body>`
temporarily flips `Foo` transparent inside `<body>`; used in the
characterising lemmas themselves and the rare proof that genuinely
needs the unreduced view.

Used when proofs about a recursive function would get tangled by the
kernel's automatic reduction (e.g. `Natural.monus`, `Natural.power`).
Skip when proofs about the function are computational (e.g.
`Natural.distance` — opacity was tried and reverted).

## Common mistakes and how to avoid them

### Don't write nested `Equality.transitivity` — write `calc`

Nested `transitivity(A, transitivity(B, C))` encodes a chain in a
right-associated binary tree. A reader has to mentally flatten it.
Rewrite as a calc:

```math
-- Bad:
Equality.transitivity(eq1, Equality.transitivity(eq2, eq3))

-- Good:
calc lhs
   = mid1   by eq1
   = mid2   by eq2
   = rhs    by eq3
```

### Don't write `And.left(L, R, h)` for an `<` hypothesis

`x < y` unfolds to `And(LessOrEqual(x, y), Not(x = y))`. With `h : x
< y` and a goal needing `x ≤ y`, use `<Order>.LessThan.weaken(x, y,
h)` (one line) instead of `And.left(...)` (three to five).

### Don't write a Quotient lift's motive by hand if it's redundant

If you're calling `Quotient.induct_two(motive, atMake, x, y)` and
`motive` is just `λ p q. <goal>[x↦p, y↦q]`, drop it:

```math
Quotient.induct_two(atMake, x, y)
```

### Don't write a function-wrapping for "cases on expression"

```math
-- Awkward (forces the elaborator to type the lambda separately):
function (caseScrutinee : T) (eq : E = caseScrutinee) =>
  cases caseScrutinee { … : motive(caseScrutinee) }

-- Use `with`:
cases E with eq { | Pat => … }
```

### Don't write `Or.introduceLeft/Right` when `decide` would work

For "if P then … else …" reasoning, prefer `decide P { yes h => … |
no nh => … }` over `cases Logic.excluded_middle(P) { | Or.introduceLeft
=> … | Or.introduceRight => … }`.

### Don't keep a "claim by V" whose name is unused

The elaborator warns: switch to anonymous `claim <type> by V;` (the
auto-prover finds the equation by type), or to `note <type>;` if it's
purely for the reader.

### Don't keep a `by` annotation that the auto-prover would close

The verifier flags redundant `by` annotations. Drop them.

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

Layered: imports flow up, you can't import a layer above you. Each
module's files are organized basics → operations → laws → instances.

## When to step back from the language

If a proof is hard to write, the right reaction is almost always
**find the math-level reason it's hard**, not "fight the elaborator
harder". The current language has good idioms for most math moves:
- "Pick a representative" — `take x as <Constructor>(args) : T;`
- "By cases on …" — `cases E { … }`
- "By induction on n" — `by_induction on n with IH { … }`
- "WLOG assume …" — `decide P { yes h => … | no nh => … }` or
  cases-with-equality.
- "Suppose …" — `suppose <hypothesis> as <name>;`
- "Note that …" — `note <proposition>;`
- "Therefore …" — calc chains, claim sequences.

When the math has a "single move" that translates to bureaucratic
CIC, look for a sugar that exists. If none exists, **ask whether one
should**. The language is meant to grow.

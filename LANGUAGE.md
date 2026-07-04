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

**2. A relation chain (informally "calc").** For equational/inequalitiy
reasoning where each intermediate form is named. Reads as a textbook
equation chain.

```math
theorem Integer.subtract_swap (x y : Integer) : x - y = -(y - x) :=
  x - y
     = -(y - x)
```

**3. A `{ … }` block.** A sequence of statements (a bare stated
proposition, `take`, `choose`, `let`, `cases`, `by induction`, a
relation chain, `note`, etc.) followed by a final expression. Reads as
math prose with paragraphs.

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
calculation is a chain. A multi-paragraph argument is a block. A
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

## Numbers, equality, and the relation-chain kit

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

### `=`, `≤`, `<`, `≥`, `>` in relation chains

A chain accepts all five as step separators. The chain's overall
relation is the strongest one across steps: any `<` or `>` makes it
strict, otherwise `≤`/`≥` if present, otherwise `=`. Mixing forward
(`<`/`≤`) with backward (`>`/`≥`) is rejected; `=` is allowed in
either direction.

### `by lemma` in a `=` step infers congruence

If the `by` proof has type `Equality(T, a, b)` and the chain step's two
endpoints differ in a unique single position at `(a, b)`, the
elaborator auto-wraps with `Equality.congruence` and you don't have
to write the motive lambda. The user supplies the equation, the
elaborator finds the slot. (Same direction or symmetric.)

### `rewrite(eq)` and `rewrite(eq, term)`

Two forms. **1-arg in a chain step**: `by rewrite(L)` for `L : a = b`
finds the unique structural occurrence of `a` on the chain step's LHS
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

### Splitting with a retained equation: equation-shaped by-cases

When a proof needs the split equation on the page, state it in the
arm (the old `cases x with eq` form is retired):

```math
done by cases {
  case Natural.monus(d, n) = 0 as monusEq: …
  case Natural.monus(d, n) = successor(k) for some (k : Natural) as monusEq: …
}
```

Exhaustiveness discharges through the type's coverage lemma
(`<T>.cases_covered`, auto-generated; `Natural.zero_or_successor` /
`zero_or_one_plus` at the floor), and each arm's equation is an
ordinary stated hypothesis — addressable, citable, transported by the
prover.

`for some` takes a comma-separated binder list, so a multi-argument
constructor opens all its witnesses at once: `case x = pack(a, b) for
some a, b:` gives the arm the nested hypothesis `∃ a. ∃ b. x = pack(a,
b)`, with `a`, `b`, and the equation all in scope. Each un-annotated
binder's type is inferred by priority — an annotation `(a : T)`, else
the constructor's Pi-domain at that argument position, else the
equation's left-side type. A later binder may be annotated with a type
that mentions an earlier witness; repeating a name is a parse error.

### Hypotheses about the scrutinee refine automatically

A hypothesis whose type mentions the scrutinee is lifted into the
recursor's motive automatically, so each arm sees it refined by the
constructor match — no clause needed.

```math
cases x { | RationalRepresentative.make(n, d) =>
  -- an in-scope xPos : 0 < x is seen here as 0 < [(n, d)]
  …
}
```

Works on inductive and quotient scrutinees. For induction *loading* —
an IH that must quantify over extra binders ("induct on a, keeping b
arbitrary") — list them explicitly:
`by induction on a with IH generalizing b, c { … }`.

### `by induction on n with IH { … }`

Replaces pattern-match definitions for typical induction-on-Natural.
The `IH` is in scope in the recursive arm as a hypothesis about `k`.
Arms may state the constructor form as an equation (`case n = 0:` /
`case n = k + 1 for some k:`), and the header `with IH` may be dropped
when each recursive arm names its own hypothesis (`case n = k + 1,
with IH:`). Scrutinee-dependent hypotheses generalise automatically;
`generalizing b, c` loads the IH over extra binders.

```math
theorem Natural.add_zero_right (n : Natural) : n + 0 = n :=
  by induction on n with IH {
    case n = 0: done
    case n = k + 1 for some k: {
        k + 0 = k by IH;
        done
      }
  }
```

For strong recursion (you need IH for all `k < n`), use
`by strong induction on n with hypothesis IH;` (statement form — the
rest of the block is the body) or the braced
`by strong induction on n with hypothesis IH { … }`.

### `by cases { case P: … otherwise: … }` — classical case split

The canonical form for "P or not P" reasoning (the old `decide P {
yes/no }` construct is retired). `otherwise` is always last; its
hypothesis is the negation of the stated cases, and exhaustiveness is
excluded middle by construction. When a goal must REDUCE a value
defined by the same decision (`min(a, b)`, `List.filter`, a bisection
step), don't re-decide: cite the definition's characterizing
equations, which are one-liners over the generic conditional lemmas
`Logic.if_positive` / `Logic.if_negative`
(`min(a, b) = a  by Rational.minimum_eq_left; done by substitution`).

### `if P then a else b` — the value-level classical conditional

Branches a DEFINITION on any proposition (desugars to
`cases Logic.classical_decidable(P)`); this is the one surviving
value-level spelling. Reason about the result through
`Logic.if_positive` / `Logic.if_negative`, never by re-deciding.

### Collapsing Quotient-lifted ring laws (the "triple-helper" antipattern)

A common older idiom in this library: a ring law on a quotient
carrier (Integer, Rational, Real, PAdic) was proved by stacking three
or four helper theorems:

1. `Foo_at_representatives` — the Quotient.sound at the rep level.
2. `Foo_after_first_second` — `Quotient.induct` over the third arg with
   an explicit motive (uses `_at_representatives` at the leaf).
3. `Foo_after_first` — `Quotient.induct` over the second arg
   (uses `_after_first_second` at the leaf).
4. `Foo` (the main theorem) — `Quotient.induct` over the first arg
   (uses `_after_first` at the leaf).

This entire chain collapses to **one proof** with nested
`cases x { | Constructor.make(…) => … }` blocks:

```math
theorem Integer.add_commutative (x y : Integer)
        : x + y = y + x :=
  cases x { | IntegerRepresentative.make(a, b) =>
    cases y { | IntegerRepresentative.make(c, d) =>
      Quotient.sound(
          IntegerRepresentative.make(a + c, b + d),
          IntegerRepresentative.make(c + a, d + b),
          Integer.add_commutative_natural(a, b, c, d)) } }
```

The kernel's `Quotient.lift` β-reduces both sides at the leaf to the
representative form; `Quotient.sound` closes the equivalence using a
plain Natural-level kernel theorem. The motive-passing
`Quotient.induct` chain is unnecessary — `cases` does it implicitly.

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

### `take x REL E;` — combined take header (the analytic opener)

The analytic goal `∀ ε. ε > 0 → …` is a `Pi` whose codomain is an
implication, so opening it takes two intros: the binder and its
hypothesis. `take ε > 0;` does both in one line. It desugars EXACTLY
to the two-statement opener

```math
take ε;              -- binder type inferred from the goal's Π
suppose ε > 0;       -- anonymous hypothesis, picked up by type later
```

`REL` is one of `>`, `≥`, `<`, `≤`, `≠` (the `>`/`≥` forms reverse onto
`<`/`≤`, as any relation does). The hypothesis is left anonymous —
statement-addressable, so a later by-less / `by` / `substituting` step
consumes it by type. Exactly one binder: `take a, b > 0;` is a parse
error steering to separate `take` statements.

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

### `let ⟨a, b⟩ := E;` — destructure a data record

For genuine DATA (a record, a bundle, a single-constructor inductive
over values), the tuple pattern names the components flatly. Logic is
never destructured this way — `∃`/`∧` go through `choose` and the
conjunction-leg facts. (The old `obtain` construct is retired: it was
`choose` for logic and this let-pattern for data.)

### `choose w [such that P] [as h] [from E];` — ∃-elimination

The textbook "choose ε > 0 such that …". The property is stated on
the page and joins the context (conjunct-by-conjunct for ∧-chains);
`from` names the source (a hypothesis, an applied term, or a lemma
cited argument-free); without `from`, the most recent in-scope ∃ is
used. Witness lists flatten a nested ∃ in one step:

```math
choose k such that m = 2 * k;                        -- source: the in-scope `2 ∣ m`
choose m, n such that 1 ≤ m ∧ m = n from solutionExists;
```

### `let x : T := V;` — local abbreviation

ζ-tracked: the kernel sees through `x` to `V` whenever needed
(`isDefinitionallyEqual`, the auto-prover's structural matchers, the
diff-bridge walker). Use freely for value abbreviations when one
expression appears 3+ times in a proof.

## Stating facts — sequence-of-stated-facts style

When a proof has several distinct subgoals, write them as a sequence
of stated-fact lines and assemble the result from the named facts:

```math
{
  0 < halve(epsilon)
    by Rational.halve_positive(epsilon, epsilonPositive)
    as epsilonHalvedPositive;
  abs(s(m) - s(n)) < halve(epsilon)
    by sCauchy(halve(epsilon), epsilonHalvedPositive, m, n, mLarge, nLarge)
    as sumWithinHalf;
  -- assemble: …
}
```

The structure makes the argument legible. A reader can skim the facts
to see the shape before reading the inner proofs.

### `P by V, by definition of X[, Y];` — by-definition modifier

Sometimes the cited hint proves a fact whose type only matches the
stated proposition after a definition is unfolded (typically an opaque
one). The comma-joined modifier checks the proposition — and discharges
the hint — under the SAME unfold wrapper `suffices … by definition of X`
uses (the machinery is reused verbatim, not a second unfolding path):

```math
-- pointwiseLower(N) proves `B ≤ s(N)`; the stated fact reads it as
-- `-ε < …` with Real.LessOrEqual unfolded.
-ε < s(m) - b(m) by pointwiseLower(N), by definition of Real.LessOrEqual;
```

One or more comma-separated definition names may follow `of`. This is
distinct from the postfix `by V unfolding X`, which makes `X`
transparent only inside the hint proof, not for the proposition-vs-goal
match.

### A relation chain as a statement

`<chain> as NAME;` and bare `<chain>;` at statement position bind the
chain's result into local scope:

```math
(aInt * yPrime - qInt * bInt * yPrime)
   = (aInt - qInt * bInt) * yPrime
   = rInt * yPrime                            as factoredEqualsRYPrime;
-- factoredEqualsRYPrime is now in scope
```

Bare `<chain>;` (no `as`) synthesizes an anonymous name and the
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
explicitly, or rely on auto-generalize (`generalizing` for extra
binders) and let the elaborator construct the chain.

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
1 = successor(successor(n))
  by Natural.successor_injective(1, successor(successor(n)),
                                  twoEqualsThreePlus)
  as oneEqualsTwoPlus;

-- With `?` — the two Natural args are recoverable from the goal:
1 = successor(successor(n))
  by Natural.successor_injective(?, ?, twoEqualsThreePlus)
  as oneEqualsTwoPlus;
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

## Registrations

Top-level declarations that feed elaborator registries (all canonical:
a conflicting second registration is a declaration-time error, never a
search):

- `operator (sym) on (T1, T2) := F` — infix dispatch (`on (T)` for a
  postfix operator).
- `overload alias := F` — add `F` to the overload set `alias`.
- `coercion (S, T) := F` — canonical embedding `S ↪ T`.
- `instance N` — canonical structure instance (`N : IsGroup(T, …)`),
  bundle (`N : Ring`), or forgetful derivation, keyed by carrier.
- `congruence_under_binder F := L` — rewrite-under-binder lemma for
  chain steps whose endpoints differ inside a lambda under head `F`.
- `fold_operation (sym) on T := W` — register the operation behind
  `sym` on `T` as **fold-capable**, certified by
  `W : IsMonoid(T, operation, identity)`. The elaborator checks the
  witness's operation is exactly what the operator registry dispatches
  `sym` to on `(T, T)`. The registry feeds the fold binder form and
  the ellipsis notation for sums/products.

## The fold binder form

```
sum k from 0 to n of s(k)             -- Σ_{k=0}^{n} s(k)
product k from 1 to n of k            -- Π_{k=1}^{n} k
fold (+) k from m to n of s(k)        -- any registered operator
```

An ordinary term (legal anywhere a carrier element is), elaborating
through the `fold_operation` registry to
`Algebra.Fold(carrier, op, identity, λk. body, lo, count)`. The
carrier is the body's type; `(head-operator, carrier)` must be
registered or the form is an error naming the missing registration.

- **Range and count.** The range is inclusive `lo … hi`; the count is
  `(1 + hi) ∸ lo`, monus-free when `lo` is a literal `0` (count
  `1 + hi`) or `1` (count `hi`).
- **Half-open `E - 1`.** An upper bound *written* `E - 1` is half-open
  notation for `[lo, E)` with count `E ∸ lo`, so
  `sum k from 0 to n - 1 of s(k)` is the empty sum at `n = 0`.
- `sum`, `product`, `fold`, `to`, `of` remain ordinary identifiers
  everywhere else; only the `sum k from` / `fold (op) k from` shape is
  claimed. The body extends as far right as an expression can —
  parenthesise the whole form to continue an enclosing expression:
  `(sum k from 0 to n of s(k)) + 1`.
- The form does not coerce its carrier: where the context expects a
  different type, write the cast (or `Algebra.Fold`) explicitly.

## Ellipsis notation

```
1 + 2 + ... + n                                  -- Σ_{k=1}^{n} k
a(m) + a(m+1) + ... + a(n)                       -- symbolic bounds
a(0) + ... + a(n - 1)                            -- half-open: empty at n = 0
2 + 4 + ... + 2*n                                -- stride via the term function
1 * 2 * ... * n                                  -- products too
```

`t₁ op … op ... op g` is sugar for the fold binder form. The
**general term is the last term**; the recognizer reads the index and
term function by anti-unifying the last written prefix term against
`g` (the positions where they differ are the index), falling back to
evaluating `g` at 0 and 1 when the anchor is arithmetic rather than
structural (`2 + 4 + …`: the literal `2` is not literally `2·⟨_⟩`).
The written prefix is then verified term by term — a display that
does not match its general term is an error showing generated vs
written, and a display with several readings is an error naming all
of them; the explicit binder form is always the escape hatch.

- All terms must be under ONE operator (`1 + 2 - ... - n` is
  rejected), and `(op, carrier)` must be `fold_operation`-registered.
- `-` inside an ellipsis display is blackboard monus: it is verified
  by ground evaluation and desugars to `Natural.monus`
  (`1 + 3 + ... + (2*n - 1)` works; `-` still has no standalone
  Natural elaboration).
- **The prefix does not constrain the range** (§ degenerate ranges):
  `1 + 2 + ... + n` displays three terms but denotes the fold over
  `1 … n`, which at `n = 1` has one term and at `n = 0` is empty
  (the operation's identity).
- Ellipsis over relations (`a(1) ≤ ... ≤ a(n)`) and descending ranges
  are not in this version.

### Series relations

```
Real.power(2, 0) + Real.power(2, 1) + ... + Real.power(2, k) + ... = S
t₁ + t₂ + ... + g + ... = infinity
```

A trailing `+ ...` makes the display an **infinite series**, legal
only as one full side of an equality. The relation elaborates to a
convergence proposition on the partial folds —
`Real.SequenceConverges(λN. Σ_{first N terms}, S)`, definitionally
the library's `SeriesConverges`/`partialSum` spelling — or
`Real.TendsToInfinity(…)` when the other side is `infinity` (a
contextual keyword, never a term). This version: sums at Real, first
term at index 0 or 1, recognition by the structural mechanism (spell
the prefix so the index positions line up). Series in term position
and series inequalities are errors.

## Common mistakes and how to avoid them

### Don't write nested `Equality.transitivity` — write a relation chain

Nested `transitivity(A, transitivity(B, C))` encodes a chain in a
right-associated binary tree. A reader has to mentally flatten it.
Rewrite as a chain:

```math
-- Bad:
Equality.transitivity(eq1, Equality.transitivity(eq2, eq3))

-- Good:
lhs
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

-- Use the equation-shaped split:
done by cases {
  case E = 0 as eq: …
  case E = successor(k) for some (k : Natural) as eq: …
}
```

### Don't write `Or.introduceLeft/Right` when `by cases` would work

For "either P or not P" reasoning, prefer `by cases { case P: …
otherwise: … }` over `cases Logic.excluded_middle(P) {
| Or.introduceLeft => … | Or.introduceRight => … }`.

### Don't keep a named "stated fact by V" whose name is unused

The elaborator warns: switch to anonymous `<type> by V;` (the
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
- "By induction on n" — `by induction on n with IH { … }`
- "WLOG assume …" — `by cases { case P: … otherwise: … }` or
  cases-with-equality.
- "Suppose …" — `suppose <hypothesis> as <name>;`
- "Note that …" — `note <proposition>;`
- "Therefore …" — relation chains, sequences of stated facts.

When the math has a "single move" that translates to bureaucratic
CIC, look for a sugar that exists. If none exists, **ask whether one
should**. The language is meant to grow.

# LANGUAGE_VISION.md — the dream of a clean math-proof language

This document records what the language is *trying to become*. It's
separate from `LANGUAGE.md` (which describes today's idioms) because
the design isn't done and won't be for a while. The point of writing
it down: future sessions and collaborators can see the target, the
gaps, and the open questions — so the language can keep evolving
toward something coherent rather than accumulating ad-hoc sugars.

## The principle hiding underneath

> **A binder accepts a pattern, and the elaborator picks the
> eliminator from the type.**

Every form of "intro-and-destructure" in the language is a special
case of this. A mathematician writes:

- "Let n be a positive integer, say n = k + 1." — bind n, destructure
  as a successor.
- "Let q ∈ ℚ, say q = a/b." — bind q, destructure as a representative.
- "Let h : P ∧ Q, say h = (p, q)." — bind h, destructure as a pair.
- "Take a representative [(a, b)] of x." — quotient destructure.
- "By induction on n: ..." — bind n, case-split by constructor.
- "By cases on whether P holds: ..." — bind a decidability witness,
  case-split.

In CIC, each of these is a different elimination form with its own
ceremony — a motive, a Pi-binder telescope, a substitution. The
ceremony is bureaucracy. The math is a **single move**: "bind WITH
a pattern."

Patterns belong in binder positions. The elaborator should look at the
binder's type, find the right eliminator, and emit the right kernel
term. The user shouldn't have to know which eliminator.

## Where we are

Today, the language has many places where this principle has been
applied piecemeal. Each one removes a pile of CIC ceremony for one
specific intro-and-destructure shape.

| Construct | Pattern site | Eliminator picked |
|---|---|---|
| `cases x { \| Pat => … }` | scrutinee | `T_rec` |
| `cases x with eq { \| Pat => … }` | scrutinee + equation | convoy `T_rec` |
| `cases x refining h1, h2 { … }` | scrutinee + telescope | `T_rec` with motive lift |
| `cases x { \| Constructor(args) => … }` on a quotient | scrutinee | `Quotient.induct` |
| `by_induction on n with IH { case Pat: … }` | scrutinee | `Nat_rec` or supplied recursor |
| `by_strong_induction on n with IH { … }` | scrutinee | strong recursion |
| `decide P { yes h => …, no n => … }` | hypothesis | `Decidable_rec` (with motive search) |
| `obtain ⟨w, p⟩ from h` | existing existential/conjunction | `Sigma.elim` / `And.elim` |
| `let ⟨a, b⟩ := V` | RHS value | `Sigma.elim` |
| `take x as Pat : T;` | Pi-intro | type-directed dispatch |
| `suppose P as Pat;` | implication-intro | type-directed dispatch |
| `choose N such that Q(N);` | existential intro | `Sigma.elim` + claim |
| `theorem foo \| Pat₁, Pat₂ => …` (multi-pattern def) | arg | nested recursor with refinement |

That's a lot. Each was added to fight a specific bureaucracy. They
work. Proofs that used to take 40 lines of motive + cases + cases now
take 2-7 lines that read as one or two sentences of math.

## What this enables — concrete before/after

Here's the canonical case, `Integer.triangle_inequality`:

**Before:** 29 lines, three nested layers of motive + cases with
explicit type annotations on each cases block to re-state the goal.

```math
theorem Integer.triangle_inequality (x y : Integer)
        : abs(x + y) ≤ abs(x) + abs(y) :=
  Quotient.induct_two(
      function (p q : Integer) =>
          abs(p + q) ≤ abs(p) + abs(q),
      function (rep_p rep_q : IntegerRepresentative) =>
          (cases rep_p {
             | IntegerRepresentative.make(a, b) =>
                 (cases rep_q {
                    | IntegerRepresentative.make(c, d) =>
                        Integer.triangle_inequality_at_representatives(
                            a, b, c, d)
                  } : abs(mk(make(a, b)) + mk(rep_q))
                      ≤ abs(mk(make(a, b))) + abs(mk(rep_q)))
           } : abs(mk(rep_p) + mk(rep_q))
               ≤ abs(mk(rep_p)) + abs(mk(rep_q))),
      x, y)
```

**After:** 7 lines that read like the math proof.

```math
theorem Integer.triangle_inequality (x y : Integer)
        : abs(x + y) ≤ abs(x) + abs(y) :=
  cases x { | IntegerRepresentative.make(a, b) =>
    cases y { | IntegerRepresentative.make(c, d) =>
      Integer.triangle_inequality_at_representatives(a, b, c, d) } }
```

This is the proof a textbook would have:

> Take representatives x = [(a, b)] and y = [(c, d)]. The triangle
> inequality on Natural distance gives the result. □

The CIC has not disappeared — the elaborator emits the same kernel
term as before. What's gone is the **layer between the math and the
kernel that the user had to maintain by hand**. The elaborator
maintains it now.

## What's still aspirational

Many things still don't fit the pattern. Some are pain points
encountered while writing real proofs; some are design questions the
language hasn't answered yet.

### 1. `Quotient.exact` doesn't have a short form

When you have an equality `q1 = q2` between two `Quotient.mk` values
and want the underlying equivalence relation proof, the only API is
the 8-arg `Quotient.exact(T, R, R.reflexive, R.symmetric, R.transitive,
rep1, rep2, equationProof)`. Eleven call sites in the library use this
form. There's no shorter way to write it.

The cleanest fix would be: infer `T, R` from the equation type
(parallel to how `Quotient.mk` infers them), and look up `R.reflexive`/
`.symmetric`/`.transitive` via a type-class-like registry on `R`. Then
the call becomes `Quotient.exact(equationProof)`. Punch list items
#1 and #6 (`Rational.zero_not_equal_one`, `Real.zero_not_equal_one`)
would both shrink dramatically.

### 2. The `[a, b]` quotient pattern notation

Right now, the rep destructure pattern is the rep constructor name:
`IntegerRepresentative.make(a, b)`, `RationalRepresentative.make(n,
d)`. That's accurate but verbose. A mathematician writes "Let x =
[a, b]" — the brackets *are* the quotient-rep notation.

What if `[a, b]` parsed as a quotient-mk pattern, with the carrier
chosen by the binder's type? Then:

```math
take x as [a, b] : Integer;
take q as [n/d] : Rational;     -- the / is just sugar
```

This is purely surface syntax; the elaborator already handles the
desugaring. It's not done because the bracket might conflict with
other syntax in the future, and the naming convention to pick (`[…]`,
`⟦…⟧`, `<a, b>`, …) hasn't been decided. Worth doing once the right
notation is chosen.

### 3. Patterns in `let` and term-position binders

`let ⟨a, b⟩ := V;` works for tuple patterns. What about
constructor patterns?

```math
let IntegerRepresentative.make(a, b) := rep;
-- expected to bind a, b from the rep's constructor.
```

This would be the natural extension. Currently you have to write
`cases rep { | IntegerRepresentative.make(a, b) => <rest> }`, which
reads less directly. The let form would be a parser-level desugar.

### 4. The `_at_make` helper convention

A typical recurring pattern: prove the rep-level fact as a
`*_at_make` theorem (pattern-match definition over rep constructors),
then lift via `Quotient.induct[_two|_three](at_make, x, y, …)`. With
motive inference, the lift is a one-liner. But the user still has to
manually write the `_at_make` theorem.

What if there were sugar to inline the rep-level proof? Something
like:

```math
theorem Integer.triangle_inequality (x y : Integer)
        : abs(x + y) ≤ abs(x) + abs(y) :=
  by_representatives x as [a, b], y as [c, d] {
    -- here the goal is the rep-level fact:
    --   abs([a, b] + [c, d]) ≤ abs([a, b]) + abs([c, d])
    Integer.triangle_inequality_at_representatives(a, b, c, d)
  }
```

This is essentially the existing `cases x { | Pat => cases y { | Pat
=> body }}` but with a single keyword that reads more directly. Worth
doing once the bracket notation lands.

### 5. The motive when implications thread through

`Real.IsNonneg.add (x y : Real) (xNonneg : Real.IsNonneg(x))
(yNonneg : Real.IsNonneg(y)) : Real.IsNonneg(x + y)`. The natural
proof: take a representative of x and y, then `xNonneg` becomes
sequence-level eventually-nonneg, `yNonneg` similarly, and the
sequence-level fact gives it.

But the *naive* `cases x { … cases y { … }}` doesn't refine the
hypothesis types. You need `cases x refining xNonneg { … cases y
refining yNonneg { … }}`. The current language has this; it works.
But the user has to KNOW to write `refining`. The elaborator could
do better: detect that hypotheses in scope mention the scrutinee, and
suggest (or automatically add) the refining clause.

### 6. The block-syntax / term-syntax gap

Block syntax (`{ … }`) is for statement sequences. Term syntax is
for single expressions. Many sugars exist only on one side. For
example:
- `take x : T;` is statement-only.
- `function (x : T) => …` is term-only.

These are equivalent semantically, but the parser treats them
differently. Sometimes you want a `take` inside a `cases` arm, but
the arm is a term position, not a block. Forces you to wrap the arm
in `{ … }` to get block syntax.

Possibly: make statement-form sugars work uniformly in term
position by wrapping a single-statement-plus-final-expression as a
block.

### 7. Telescopes as first-class

When a definition has `(p : Natural) (primality : Natural.is_prime(p))`
threading through every operation, that's a **telescope** — a sequence
of bindings, some of which constrain earlier ones. PAdic operations
do this (currently explicit; planned migration to implicit).

A `telescope Prime { p : Natural; primality : Natural.is_prime(p); }`
declaration that could be reused across many definitions would
eliminate the boilerplate of repeating the same Pi prefix everywhere.
Convention does part of this; a first-class telescope might do more.

### 8. Multi-position diffs and the bridge limits

`rewrite(eq, term)` and the diff-bridge work when there's a single
position where two expressions differ. When there are two unrelated
positions (the `halve` moves between left and right operand of a
multiplication, for instance), the bridge bails. The user has to
expand to explicit `transport_proposition` with a hand-written motive.

A future bridge could handle multi-position diffs at least when each
diff has its own equation in scope (multi-equation transport). The
elaborator does this for `cases ... refining` but not for the
free-floating bridge.

## Pain points encountered in actual proofs

These are concrete things that have happened recently — not
hypothetical:

### "Pattern in a non-block position"

`function (rep) => congruenceOf(λr. mk(r), rep_level_eq)` — this is
a recurring shape. The lambda inside `congruenceOf` doesn't accept
pattern binders, so the user can't write `function (Constructor.make(a,
b)) => …`. They have to write the lambda binding the rep and then
`cases rep` inside it. Workable but verbose.

### "I want refining only on some arms"

`by_induction on n with IH refining h1, h2 { case zero: <h1 and h2
needed refined>; case successor: <only h1 needed> }`. The refining
clause forces the lift on EVERY arm. There's no per-arm refining.

### "Bare-name patterns shadow outer names"

`cases x { | rep_x => … }` introduces `rep_x` in the arm. If `rep_x`
was already in scope (a name collision), the inner `rep_x` shadows.
Sometimes this is intentional; sometimes it's a typo. The elaborator
doesn't warn.

### "The decide motive sometimes runs slow"

For very deeply nested goals where `classical_decidable(P)` is buried
under many δ-unfolds, the motive walker can be expensive. The recent
walker-memo + constant-motive fallback addresses the worst cases, but
on supremum.math the per-call cost was ~28 seconds before the fix.
Motive search is a quadratic worst case.

### "Universe inference fails in nested polymorphic calls"

Recurring on `Quotient.exact` and other deeply-polymorphic functions:
the inferred universe levels for nested calls don't unify the way the
user expects, leading to identical-printed-types errors. Workaround:
explicit `.{u, v}` annotations. The error messages are improving but
diagnosis is still painful.

### "I want to ascribe the result of a calc but the chain is mixed"

Mixed-relation calcs (`=`/`≤`/`<`) at statement position need the
explicit `claim NAME : TYPE by calc …;` form. All-`=` chains can use
`calc … as NAME;` directly. Worth unifying.

## The design questions still open

### Q1. How aggressive should patterns-in-binders go?

The current language supports patterns in `take`, `suppose`, `obtain`,
`cases`, `let` (tuple only). Should every binder position accept
patterns? Including `claim N : T by V;` where V has an unfolding
shape? Including function parameter declarations?

The risk: the language gets harder to learn because every binder has
many possible parses. The reward: math reads more directly.

### Q2. Should the elaborator infer destructure on FunctionApplication args?

Some proofs effectively destructure their argument as soon as they
get it: `function (rep : Constructor.make(a, b) <pattern>) => ...`.
This would parallel pattern-match definitions but in lambda position.

### Q3. Should `take`/`suppose`/`obtain` be unified?

`take x : T;` and `suppose T as x;` are syntactically symmetric.
`obtain Pat from h;` is similar but destructures an existing value.
A unified `take`/`as`/`from` family might be cleaner.

### Q4. Should we have a `WLOG` / `by symmetry` move?

A common mathematician's phrase: "Without loss of generality, assume
…". The proof then deals with the symmetric case. CIC doesn't have a
built-in for this; it has to be expressed as case-by-case proofs with
explicit symmetry arguments. A WLOG sugar would help, but the
semantics are subtle.

### Q5. How should errors point at math, not CIC?

When elaboration fails, the error message references kernel terms,
de Bruijn indices, or universe levels. A mathematician reading the
error would want it framed as "the proof you wrote doesn't establish
the goal you stated, because …". The elaborator has been improving on
this (better error frames, expected/actual types printed) but the gap
is still large.

## How to evolve the language

When you encounter a proof that reads as math bureaucracy:

1. **Identify the math move.** What single sentence would a textbook
   use to describe what this proof does?
2. **Count the CIC steps.** How many distinct kernel-level operations
   does the proof require?
3. **If math = 1 sentence, CIC = many steps, the bureaucracy is the
   bug.** Find a sugar that exists, OR design a new one.
4. **Test the design empirically.** A new sugar isn't done until you
   refactor several real proofs to use it and see how the language
   feels.

The patterns-in-binders work proves the model. Three new pieces of
sugar (motive inference, cases-on-quotient, take-as-pattern) plus
fixing one bug, and a punch list of 14+ proofs collapsed by ~70%
total. That's the kind of multiplier the language should aim for.

## A long horizon

If the language ever fully delivers the dream, a proof of, say, the
Cauchy-Schwarz inequality might look something like this:

```math
theorem cauchy_schwarz (n : Natural) (a b : Vector(Real, n))
        : (a • b)² ≤ (a • a) * (b • b) := {
  -- We argue by quadratic optimization on t.
  let f : Real → Real := λ t. (a + t·b) • (a + t·b);

  note f(t) = (a • a) + 2t(a • b) + t²(b • b);
  note f(t) ≥ 0 for all t  by inner_product_nonneg;

  -- A non-negative quadratic has nonpositive discriminant.
  apply nonneg_quadratic_discriminant to f;
  ring
}
```

The proof is short, every step names a math idea, none of the
ceremony is visible. The elaborator routes each move through the
appropriate kernel-level construction.

That's a long way off. But every piece of patterns-in-binders work
is one step in that direction.

# Tutorial

This is a gentle introduction to writing proofs in this system, aimed at a
mathematician who has not worked with a proof assistant before. You do not
need to know anything about the underlying logic (the Calculus of
Inductive Constructions, "CIC"); we explain the little that matters as we
go. The guiding idea is simple:

> **A proof should read like one you would write on paper.** You say *what*
> is true at each step; the machine works out *how* to check it.

Build your file with `make -j 16 library` from the project root.

## What a proof *is*, and why style matters

In CIC, a proof of a proposition is a *term*, and a theorem or lemma is —
quite literally — a function: you can apply it to arguments and it hands
you back a proof of its conclusion. So you *can* write an entire proof as
one big nested function call, and the kernel will happily check it.

The trouble is readability. Suppose `successor_injective` is the fact "if
`successor(a) = successor(b)` then `a = b`". Invoked as a function it looks
like:

```
Natural.successor_injective(a, b, equationProof)
```

This type-checks, but a reader cannot *see* what it produces (`a = b`)
without looking up the lemma's signature and mentally tracking the argument
order. With several arguments, or calls nested inside calls, the
*statement* being proved disappears into plumbing.

So this system nudges you toward a different style: **state the fact, and
just name the reason.** You can always be fully explicit about how a lemma
is used, but a proof usually reads better if you only mention the lemma's
name — `by <lemma>`, with no arguments, letting the system fill them in —
or if you skip the citation entirely and let the automatic prover find it:

```
claim a = b by Natural.successor_injective;
```

Now the line says exactly what is now true (`a = b`) and, parenthetically,
why. The rest of this tutorial is mostly about the constructs that let you
write in this "what, not how" style.

## A first theorem

A file is a module. It declares what it imports and then states theorems
and definitions. Every theorem has the shape `name (parameters) :
statement := proof`.

```
module Tutorial.intro

import Natural.basics
import Natural.arithmetic
import Equality.basics

-- `0 + n` reduces to `n` automatically (addition is defined by recursion
-- on its first argument), so to the kernel the goal `0 + n = n` is
-- *literally* `n = n` — true on the nose, with nothing to prove. `done`
-- says "the goal holds"; the automatic prover sees both sides are the
-- same term and accepts it.
theorem Tutorial.zero_add (n : Natural) : 0 + n = n :=
  done
```

Some equalities hold "on the nose" like this (the kernel reduces both
sides to the same thing); most do not and need a real argument. For any
identity in a **commutative ring** (`Integer`, `Rational`, `Real`, the
polynomial and algebra towers, …) the one-liner is the `ring` tactic, with
`field(h, …)` when you divide. (`Natural` is only a semiring, so there you
lean on the automatic prover and named lemmas, which we meet next.)

## The automatic prover, and `calc`

Most equational reasoning is a `calc` chain: a sequence of steps, each a
relation, that compose end to end. Relations may mix — `=` with `≤`, `<`,
`∣` — as long as they chain:

```
theorem Tutorial.chain (a b : Natural) : a + b ≤ b + a + 1 :=
  calc a + b
     = b + a          -- the automatic prover closes this (commutativity)
     ≤ b + a + 1      -- and this
```

A step with no annotation is handed to the **automatic prover**, a search
that tries to close the step from facts already in scope and a library of
basic lemmas. When it can manage on its own, say nothing — that is the
cleanest a proof gets.

When a step needs help, justify it by its *reason*. Here the first step
rewrites the left-hand side with the lemma
`Natural.add_successor : a + successor(b) = successor(a + b)`, and the
second step is left to the prover:

```
theorem Tutorial.add_successor_commute (a b : Natural)
        : a + successor(b) = successor(b + a) :=
  calc a + successor(b)
     = successor(a + b)   by Natural.add_successor
     = successor(b + a)   -- the automatic prover closes this (commutativity)
```

Notice the lemma is named with **no arguments**: `by Natural.add_successor`,
not `Natural.add_successor(a, b)`. The system infers the arguments from the
shape of the step. This is the heart of the preferred style — you cite the
operative fact, not the call.

The citation keyword is **`by <lemma>`**. Usually it means "the prover
needs this hint to close the step", but it is also right to keep a `by`
the prover doesn't strictly need when the lemma is illuminating (an
induction hypothesis, the key lemma) — the redundancy checker will flag
it, and keeping it anyway is a deliberate author's call. (An older
keyword `since` marked exactly those kept explanations; it has been
removed from the language.)

## Stating intermediate facts: `claim`

`claim P` asserts `P` and adds it to the context, where the automatic
prover and later steps can use it. By default the prover discharges it; a
`by` hint helps when needed:

```
theorem Tutorial.two_divides_six : 2 ∣ 6 := {
  note goal : ∃ (quotient : Natural). 6 = 2 * quotient;   -- this is what `2 ∣ 6` means
  claim sixIsTwoTimesThree : 6 = 2 * 3;                   -- the prover checks this
  witness 3 with sixIsTwoTimesThree
}
```

A few things to read off this example:

- The proof is a `{ … }` *block*: a sequence of statements ending in `;`,
  whose final (un-`;`-terminated) expression is the proof's result.
- **`note goal : T;` is a checked comment.** It asserts that the current
  goal is, by definition, `T` — here it spells out that `2 ∣ 6` unfolds to
  `∃ quotient. 6 = 2 * quotient`. The system verifies the two really are
  the same, then discards the line: it changes nothing and binds nothing,
  so you could delete it and the proof would still work. Its only job is to
  remind the reader (and you) what must actually be produced.
- **Name a claim only if you use the name.** Here we reference
  `sixIsTwoTimesThree` in the `witness`, so it earns a name. If you never
  refer to it, drop the name — write `claim 6 = 2 * 3;` — and the prover
  will still find the fact by its type. An unused name is just noise.
- `witness w with proof` proves an existential `∃ x. P(x)` by exhibiting
  the witness `w` and a proof of `P(w)`. Here the witness is the quotient
  `3` and the proof is `sixIsTwoTimesThree`. (`d ∣ n` is *defined* as
  `∃ q. n = d * q`, which is why a witness closes it.)

## Writing the proposition where a proof is expected

That example is more ceremony than it needs. **Anywhere the system expects
a *proof*, you may instead write the *proposition* it should prove, and the
automatic prover is dispatched to establish it.** It is the inline form of
a bare `claim`: you say *what* must hold, the machine works out *how*. So
the whole block above collapses to one line:

```
theorem Tutorial.two_divides_six : 2 ∣ 6 :=
  witness 3 with 6 = 2 * 3
```

The `6 = 2 * 3` sitting in the proof slot is not a proof term — it is the
proposition the witness obliges you to discharge, and the prover closes it.
This works in *every* proof-expecting position, not just `witness`: a
component of a tuple `⟨…, P⟩`, an argument you pass to a lemma, a `let`
value, even the whole body of a theorem (`theorem T : P := <P written out>`).

Two things to keep in mind:

- The proposition you write must be (definitionally) *the* obligation at
  that spot — you are restating what is needed, not substituting a
  different claim. An unrelated proposition fails loudly rather than being
  quietly "corrected".
- The prover still has to *succeed*. If the fact needs a real argument,
  you must supply one (a proof term, or a `claim … by <lemma>`). And when a
  fact is reused or genuinely illuminating, a *named* `claim` reads better
  than inlining it — the terse form is for the steps that are obvious once
  stated.

## Closing the goal

To close the current goal, write `done` or `okay`. They are precisely
`claim goal` — a claim whose statement is "the goal" (the type the context
expects). Like any claim they take an optional `by`:

```
  claim divisorPositive : 1 ≤ d by Natural.some_lemma;
  done
```

The word `goal` on its own just names the goal's type (handy in
`claim goal` or in a comment like `note goal : T`); it is not a standalone
closer.

## Using a hypothesis you already have

When a fact is sitting in your context — a parameter, a `claim`, an
induction hypothesis — you do *not* cite it with `by`; you simply let the
prover use it, or apply it by name if it is a function. Applying a *local*
hypothesis like `IH(k)` or `notEqual(proof)` is fine and reads well — it is
only *library lemmas* that we avoid invoking positionally.

## Existentials: `witness` and `choose`

We saw `witness` for *proving* an existential. To *use* one — to get at the
thing it claims exists — `choose` names the witness and (optionally) states the
property it satisfies:

```
  choose quotient such that a = d * quotient from dDividesA;   -- from a fact in scope
```

The `such that …` is a verified, in-place reminder of what `quotient` gives
you — better than making the reader unfold what `dDividesA` means. `from`
also takes a lemma, cited argument-free:

```
  choose quotient such that a = b + quotient from Natural.subtraction_witness;
```

Add `as <name>` to name the property for later citation, or leave it off and a
later by-less step picks it up. (`choose` is the ONLY spelling for `∃`/`∧`
elimination — the retired `obtain`'s tuple `⟨w, p⟩` exposed that connectives
happen to be encoded as tuples, which isn't how you think about them. The
tuple form `let ⟨a, b⟩ := …` survives for genuine data records.)

A context `A ∧ B` gives you both `A` and `B` as facts directly — no projecting
a pair — and `absurd(0 = successor(k))` lets you state a contradictory fact and
have it proved-then-contradicted.

## Induction

Recursion is written as `by induction`. The crucial payoff: the recursive
call becomes a *named hypothesis* `IH` in the successor case, so it reads as
"by the induction hypothesis" rather than as a function calling itself.

```
theorem Tutorial.add_zero (n : Natural) : n + 0 = n :=
  by induction on n with IH {
    case n = 0: done
    case n = k + 1 for some k: {
        k + 0 = k by IH;
        done
      }
  }
```

The arm states the constructor form as an equation on the inducted
variable (`for some k` is documentation — the pattern binds `k`); the
recursive arm restates the induction hypothesis and the goal closes
from it.

Here `IH` has type `k + 0 = k`, and `by IH` tells the reader the last
step rests on it. Two common extensions:

- **Hypotheses about the inducted variable just work** — a hypothesis
  whose type mentions the variable is generalised automatically, so each
  case sees it in the right shape and the IH quantifies over it.
- **`generalizing b, c`** — induction loading: list extra binders the IH
  should quantify over (`by induction on a with IH generalizing b { … }`
  reads "induct on a, keeping b arbitrary").
- **`by strong induction on n with hypothesis IH;`** — well-founded
  induction, where `IH` covers *every* `k < n`; the rest of the block is
  the induction body.

## Case analysis

`cases` splits a value built by constructors (a `Natural`, an `Or`, …):

```
  cases b {
    | zero => …
    | successor(m) => …
  }
```

Useful variants:

- **`cases e with eq { … }`** also gives you `eq : e = <pattern>` in each
  arm.
- **Hypotheses about the scrutinee just work** — a hypothesis whose type
  mentions `e` is generalised automatically, so each arm sees it refined
  to that arm's constructor form.
- **`cases by <lemma> { | C(args) => … }`** splits on a disjunction a lemma
  produces, inferring its arguments.
- **`by cases { case P: … otherwise: … }`** is the classical case-split
  on whether `P` holds; `if P then a else b` is its value-level sibling
  for *building data* (reason about the result via `Logic.if_positive` /
  `Logic.if_negative`).

## Introducing things, step by step

Inside a block you often build up the context before proving:

```
  take x : Natural;            -- peel off a ∀-bound variable
  suppose 1 ≤ x as positivity; -- assume a hypothesis (and name it)
  let m := x + 1;              -- a local abbreviation
```

## Proving a disjunction

To prove `A ∨ B`, get one of the disjuncts into your context and then
`done` — the prover does the "or-introduction" for you:

```
  claim 0 ≤ b by Natural.zero_least;
  done                                -- closes the goal `0 ≤ b ∨ …`
```

No need to mention `Or.introduceLeft` / `Or.introduceRight`.

## `note`: a checked comment

Sometimes you want to point something out to the reader without using it.
`note P;` asks the kernel to *verify* that `P` holds at this point — so the
comment cannot lie — but, unlike `claim`, it does **not** add `P` to the
context. It is pure documentation:

```
  note 1 ≤ successor(k);   -- observed, checked, but not bound
```

If a later step needs the fact, use `claim` (which binds), not `note`.

## A worked example

Putting the pieces together — "if `d` divides `a` and `d` divides `b`,
then `d` divides `a + b`":

```
theorem Tutorial.divides_add (d a b : Natural)
        (dDividesA : d ∣ a) (dDividesB : d ∣ b)
        : d ∣ (a + b) := {
  choose q1 such that a = d * q1 from dDividesA;
  choose q2 such that b = d * q2 from dDividesB;
  witness q1 + q2 with
    calc a + b
       = d * q1 + d * q2       -- using the two equations in context
       = d * (q1 + q2)         -- distributivity
}
```

Read it aloud: "write `a` and `b` as `d·q₁` and `d·q₂`; then `a + b = d·q₁ +
d·q₂ = d·(q₁+q₂)`, so `q₁+q₂` witnesses that `d` divides `a + b`." That is
the proof a mathematician would write — and every step is kernel-checked.

## Where to go next

- `docs/reference.md` — a catalogue of every construct.
- `docs/style.md` — the readability principles, distilled.
- `docs/library.md` — a map of what is already proved, by area.
- `docs/conventions/` — depth on `calc`, the algebra tactics, quotients,
  and more.
- `library/Test/` — a worked, checked example of essentially every
  construct.

# Tutorial

A 10-minute introduction to writing proofs. The goal of the language is
that a proof reads like a textbook, with a CIC kernel checking every step.
You write the mathematics; the auto-prover fills in the bureaucracy.

Build with `make -j 16 library` (or `make -j 16 tests`).

## A first theorem

A file is a module that imports what it needs and declares theorems and
definitions:

```
module Tutorial.intro

import Natural.basics
import Natural.arithmetic
import Equality.basics

-- Every theorem is `name (params) : statement := proof`.
-- The kernel reduces `0 + n` to `n`, so reflexivity closes the goal.
theorem Tutorial.zero_add (n : Natural) : 0 + n = n :=
  reflexivity(n)
```

For a **commutative-ring** identity (over `Integer`, `Rational`, `Real`,
the polynomial/algebra towers, …) the default proof is the `ring` tactic —
`field(h, …)` its counterpart when reciprocals appear. (`Natural` is a
semiring, not a ring, so there you lean on the auto-prover and named
lemmas instead.)

## Calculations

Most equational proofs are `calc` chains. Each line is a relation step;
adjacent steps compose (`=` with `=`, but also `≤`/`<`/`∣` mix in):

```
theorem Tutorial.example (a b : Natural) : a + b ≤ b + a + 1 :=
  calc a + b
     = b + a          -- by the auto-prover (commutativity)
     ≤ b + a + 1
```

A step with no annotation is discharged by the auto-prover. When it needs
help, justify the step by its *reason*, not the plumbing:

```
     = successor(a + predecessor)   by Natural.add_successor
```

Use `since <lemma>` instead of `by` when the reason is illuminating and
worth keeping for the reader even though the prover doesn't need it.

## Stating intermediate facts

`claim` introduces a fact into context; the auto-prover (or a `by`/`since`
hint) discharges it. Name it only if you reference the name later:

```
theorem Tutorial.two_divides_four : 2 ∣ 4 := {
  claim witnessEquation : 4 = 2 * 2;   -- auto-proved
  witness 2 with witnessEquation
}
```

`witness w with proof` proves an existential `∃ x. P(x)` by giving `w` and
a proof of `P(w)`. (`d ∣ n` unfolds to `∃ q. n = d * q`.)

## Closing the goal

`done` and `okay` are exactly `claim goal` — they close the current goal
(its type comes from the context). They take the same optional tail:

```
  claim p ∣ b by Natural.some_lemma;
  done                      -- the goal `(p ∣ a) ∨ (p ∣ b)`, by disjunction-intro
```

`goal` by itself is just the *name* of the goal type (used in `claim goal`,
`note goal : T`); it is not a standalone closer.

## Citing a lemma

Never apply a proof lemma to positional arguments. State the fact and cite
the lemma argument-free — the arguments are inferred from the goal and the
premises are discharged from context:

```
  -- NOT: Natural.successor_injective(a, b, proof)
  claim a = b by Natural.successor_injective;
```

## Induction

Recursion is `by_induction`, so the recursive call becomes a named local
hypothesis `IH` (apply it like `IH(args)` — that is not a lemma call):

```
theorem Tutorial.add_zero (n : Natural) : n + 0 = n :=
  by_induction on n with IH {
    case zero: reflexivity(0)
    case successor(k):
        calc successor(k) + 0
           = successor(k + 0)
           = successor(k)        since IH
  }
```

When a hypothesis's type mentions the variable you split on, add
`refining h` so it is generalised per case. For well-founded recursion use
`by_strong_induction on n with subject, IH { … }`.

## Case analysis and unpacking

```
  cases b {                       -- split a Natural / any inductive
    | zero => …
    | successor(m) => …
  }

  obtain ⟨q, equation⟩ from dividesProof;   -- destructure an ∃ / ∧
  obtain ⟨q, equation⟩ by Natural.some_lemma;  -- … from a lemma, args inferred

  suppose 1 ≤ b as positivity;    -- introduce a hypothesis as a step
  take x : Natural;               -- introduce a ∀-bound variable
```

To prove `A ∨ B`: establish one disjunct in context, then `done` (the
auto-prover does the introduction):

```
  claim 0 ≤ b by Natural.zero_least;
  done
```

## Where to go next

- `docs/reference.md` — every construct, catalogued.
- `docs/style.md` — how to make a proof read well (and what to avoid).
- `docs/conventions/` — depth on calc, algebra tactics, quotients, etc.

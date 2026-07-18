# Tutorial: writing a proof

This tutorial introduces the math-facing proof language. Its proof forms are
exercised by files in the clean manifest.

Before writing a proof, read the brief `README.md` in the relevant library
directory. It gives the public definitions, useful theorem names, and
abstraction rules for that area.

Build from the repository root:

```sh
make -j 16 library
```

## A module and a theorem

A source file begins with a module name and imports:

```math
module Tutorial.intro

import Logic.basics
import Equality.basics
import Natural.basics
import Natural.arithmetic
```

A theorem has parameters, a proposition, and a proof:

```math
theorem Tutorial.zero_add (n : ℕ) : 0 + n = n :=
  done
```

`done` asks the prover to close the current goal. Here the imported
arithmetic interface already knows the result.

## Relation chains

Write equality and order reasoning directly as a chain:

```math
theorem Tutorial.reassociate (a b c : ℕ)
        : (a + b) + c = a + (b + c) :=
  (a + b) + c
      = a + (b + c) by Natural.add_associative
```

The expression on each line is visible, while `by` names the reason for a
step that the automatic prover does not find itself. Do not apply a proof
theorem to positional arguments when the goal already determines them:

```math
a + (b + c) = (a + b) + c by Natural.add_associative
```

is preferred to a nested theorem call.

Chains may mix compatible relations:

```math
0 ≤ n
  < n + 1
```

The strongest relation in the chain is its result, so this establishes
`0 < n + 1`.

## Intermediate facts

Inside a proof block, state a proposition directly:

```math
theorem Tutorial.cancel (a b c : ℕ)
        (equality : a + c = b + c) : a = b := {
  a + c = b + c;
  done by Natural.add_cancel_right
}
```

The semicolon keeps the fact in scope. The prover can retrieve it by its
statement, so most facts do not need names.

Name a fact only when later text refers to that name:

```math
a + c
   = b + c
   = c + b
as rotatedEquality;
```

To transport a proposition across a named equality, write
`by substituting equalityName`.

## Introducing variables and hypotheses

For a universal or implication goal, introduce what the goal asks for:

```math
take x : X;
suppose P(x) as propertyOfX;
...
```

Use the name only if the proof refers to it explicitly. An anonymous
hypothesis remains available by its statement.

For a negation goal, suppose the statement and derive something impossible:

```math
theorem Tutorial.add_one_nonzero (n : ℕ) : ¬(n + 1 = 0) := {
  suppose n + 1 = 0;
  0 = n + 1
    = 1 + n;
  done
}
```

The final `done` sees the contradiction with the public Natural fact that
zero is not one plus a natural.

## Existentials

To prove an existential, provide a witness:

```math
witness n with P(n)
```

To use an existential, choose its witness:

```math
choose n such that P(n) from existsProof;
```

Together:

```math
theorem Tutorial.existential_round_trip
        (P : ℕ → Proposition)
        (existsProof : ∃ (n : ℕ). P(n))
        : ∃ (n : ℕ). P(n) := {
  choose n such that P(n) from existsProof;
  witness n with P(n)
}
```

Several nested witnesses can be opened or supplied on one line:

```math
choose m, n such that R(m, n) from existenceTheorem;
witness m with witness n with R(m, n)
```

## Natural numbers are arithmetic

Outside `library/Natural/`, do not use `zero`, `successor`,
`Natural.Raw`, or Natural constructor patterns. Use numerals, arithmetic,
and equation-shaped arms.

Induction:

```math
theorem Tutorial.add_zero (n : ℕ) : n + 0 = n :=
  by induction on n with IH {
    case n = 0: done
    case n = 1 + k for some k: {
      k + 0 = k;
      done
    }
  }
```

`IH` has the induction-hypothesis type for `k`. In this example the stated
fact `k + 0 = k` is found from that hypothesis automatically.

A non-recursive structural split:

```math
theorem Tutorial.zero_or_positive (n : ℕ) : n = 0 ∨ 1 ≤ n :=
  done by cases {
    case n = 0: done
    case n = 1 + k for some k: {
      1 ≤ 1 + k;
      done
    }
  }
```

The arm equation refines the goal automatically. Add `as equationName` to
an arm only when the equation itself is used later.

## Other inductive types

Proofs over exposed inductive types also use equation-shaped induction
arms:

```math
theorem Tutorial.append_empty (A : Type(0)) (xs : List(A))
        : List.append(xs, List.empty(A)) = xs :=
  by induction on xs with IH {
    case xs = List.empty: done
    case xs = List.prepend(head, tail) for some head, tail: {
      List.append(List.prepend(A, head, tail), List.empty(A))
         = List.prepend(A, head, List.append(tail, List.empty(A)))
         = List.prepend(A, head, tail) by substituting IH;
      done
    }
  }
```

The witness list after `for some` documents and binds the constructor
arguments; `IH` is the induction hypothesis for `tail`, applied here by
rewriting under the prepend. A recursive arm may name its own induction hypothesis:

```math
case xs = List.prepend(head, tail) for some head, tail, with tailIH: ...
```

Do not write a raw `cases value { | constructor => ... }` split. In a proof,
use equation-shaped `by cases` or `by induction`. For genuine data
destructuring, use the type’s public eliminator or its documented `let`/`take`
form.

## Splitting on propositions

For alternatives already expressed as propositions:

```math
done by cases {
  case P as proofOfP: ...
  case Q as proofOfQ: ...
}
```

For a classical split:

```math
done by cases {
  case x = 0: ...
  otherwise as xNonzero: ...
}
```

`otherwise` is the complement of the preceding cases and must be last.

When defining data by a condition, use:

```math
if P then valueWhenTrue else valueWhenFalse
```

Reason about it with `Logic.if_positive` and `Logic.if_negative`.

## Conjunctions and disjunctions

State the mathematical pieces and let `done` assemble them:

```math
A;
B;
done
```

To prove an existential, use `witness`. To use one, use `choose`. Avoid
exposing the tuple representation of logical connectives.

For a disjunction, state the true side and finish:

```math
A by reason;
done
```

## `note`, `done`, and `okay`

`done` and `okay` close the current goal. Both may take a reason:

```math
done by theoremName
```

`note P;` checks `P` but deliberately does not keep it in scope. Use it for
a machine-checked observation. If a later step needs `P`, state `P;`
instead.

## Algebra

Try the domain tactic before expanding an algebraic identity:

```math
theorem Tutorial.square_sum (x y : ℤ)
        : (x + y) * (x + y) = x*x + x*y + y*x + y*y :=
  ring
```

Use `field(nonzeroFacts...)` when division or reciprocals occur.

## What to read next

- `docs/reference.md` lists the supported surface forms.
- `docs/style.md` explains how clean library proofs are written.
- `library/<Area>/README.md` is the entry point for a mathematical area.
- `docs/conventions/` contains focused notes for advanced topics.

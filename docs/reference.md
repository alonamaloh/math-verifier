# Language reference

This is a compact catalogue of the supported math-facing syntax. For a
guided introduction, read `tutorial.md`.

## Files and declarations

```math
module Area.file
import Area.dependency

definition Name (x : T) : U := value
opaque definition Name (x : T) : U := value
theorem Name (x : T) : P := proof
automatic theorem Name (x : T) : P := proof
axiom Name : T
```

`automatic` declarations are available to the by-less prover. An opaque
definition reduces only when explicitly unfolded.

Parameters:

```math
(x : T)          -- explicit
{x : T}          -- implicit, inferred by unification
```

## Types and propositions

```math
Proposition
Type(0)
(x : T) → U
A → B
P ∧ Q
P ∨ Q
¬P
a ≠ b
∃ (x : T). P(x)
a = b
a ≤ b
a < b
a ∣ b
```

Prefer `a ≠ b` to `¬(a = b)`.

## Terms

```math
f(a, b)
(x : T) ↦ expression
let x : T := value in expression
if P then trueValue else falseValue
```

`?` in a function argument is a goal-driven unification hole:

```math
lemma(?, knownArgument)
```

It does not launch proof search.

A finite tuple `⟨e₀, …, eₙ₋₁⟩` builds a `RingVector(r, n)` when the expected
type fixes the coefficient carrier `r`; each entry is elaborated at that
carrier (so numerals and negatives need no ascription):

```math
⟨1, -2, 3⟩            -- : RingVector(Integer.commutative_ring_bundle, 3)
```

## Proof blocks

```math
{
  statement;
  statement;
  finalProof
}
```

A semicolon-terminated proposition is proved and retained in the local
context:

```math
P;
P by theoremName;
P as factName;
P by theoremName as factName;
```

A proof term may also be stated directly when its type is the fact to retain:

```math
existingProof;
```

Names are optional because facts can be found by their propositions.

## Relation chains

```math
first
   = second
   ≤ third by theoremName
   < fourth
```

Compatible `=`, `≤`, `<`, `≥`, and `>` steps may be mixed. The strongest
relation is the chain’s result. Named relations registered for chaining,
including `∣`, `⊆`, and `≈`, use the same form.

As a complete proof:

```math
theorem result : first = last :=
  first
     = middle
     = last
```

As a retained fact:

```math
first
   = middle
   = last;
```

Or named:

```math
first
   = middle
   = last
as equalityName;
```

Step modifiers:

```math
= next by theoremName
= next by substituting equalityName
= next by ring
```

## Closing a goal

```math
done
okay
done by theoremName
okay by theoremName
```

`goal` names the current goal type for forms such as `note goal : T`; it is
not a closer by itself.

## Introducing binders

```math
take x : T;
suppose P;
suppose P as hypothesisName;
```

Combined ordered binder:

```math
take x > 0;
```

Contradiction:

```math
suppose Not(goal) for contradiction;
```

Forward local reasoning:

```math
suppose P for proving Q { ... };
take x : T for proving Q { ... };
suffices Q by reduction;
```

## Existentials

Introduce:

```math
witness value with proof
witness first with witness second with proof
```

Eliminate:

```math
choose x such that P(x) from source;
choose x, y such that R(x, y) from source;
```

The source may be a hypothesis, an applied term, or an argument-free theorem
name whose premises are available in context.

## Conjunctions and disjunctions

To build a conjunction, establish its components and close:

```math
A;
B;
done
```

To use a conjunction, state or cite the needed component; conjunction legs
participate in context lookup.

To prove a disjunction, establish one side and close:

```math
A;
done
```

To eliminate alternatives:

```math
done by cases {
  case A as proofOfA: ...
  case B as proofOfB: ...
}
```

Classical complement:

```math
done by cases {
  case P: ...
  otherwise as notP: ...
}
```

`otherwise` must be last.

## Equation-shaped structural cases

For a Natural:

```math
done by cases {
  case n = 0: ...
  case n = 1 + k for some k: ...
}
```

For a multi-argument constructor:

```math
done by cases {
  case xs = List.empty: ...
  case xs = List.prepend(head, tail) for some head, tail: ...
}
```

Add `as equationName` when the arm uses the equation explicitly:

```math
case value = constructor(arguments) for some arguments as valueShape: ...
```

The arm goal and dependent hypotheses are refined by the equation.
Exhaustiveness is discharged through the type’s coverage theorem.

Raw `cases value { | ... }` syntax is not supported. `cases by theoremName
{ | ... }` remains available for splitting the inductive result supplied by
an argument-free theorem citation.

## Induction

Natural induction:

```math
by induction on n with IH {
  case n = 0: ...
  case n = 1 + k for some k: ...
}
```

Per-arm induction-hypothesis name:

```math
by induction on n {
  case n = 0: ...
  case n = 1 + k for some k, with stepIH: ...
}
```

Exposed inductive type:

```math
by induction on xs with IH {
  case xs = List.empty: ...
  case xs = List.prepend(head, tail) for some head, tail: ...
}
```

Generalize extra parameters:

```math
by induction on n with IH generalizing x, y { ... }
```

Explicit induction theorem:

```math
by induction on value using inductionTheorem with subject, IH { ... }
```

Strong induction on a Natural:

```math
by strong induction on n with hypothesis IH { ... }
```

Here `IH` covers every smaller natural.

## Bounded range check

Close a bounded-universal goal (leading quantified `n` with premises `a ≤ n`
and `n < b`) by kernel-checked enumeration of the half-open closed range
`[a, b)`. The endpoints must be integer literals, over `ℕ` or `ℤ`, and the
case count is capped (`MATH_FINITE_CHECK_MAX_CASES`):

```math
by finite_check n from 2 until 5      -- proves P(2), P(3), P(4)
by finite_check z from -2 until 3     -- over ℤ, crossing zero
```

Each case is closed independently; a failure names the exact value.

## Substitution and definitions

```math
P by substituting equalityName;
done by unfolding DefinitionName
suffices Q by definition of DefinitionName;
```

Use explicit unfolding only at the definition’s boundary. Consumers of an
opaque abstraction should use its characterizing theorems.

## Local bindings and destructuring

```math
let x : T := value;
set x := value;
let ⟨a, b⟩ := dataPair;
take value as publicPattern;
```

Use tuple destructuring for genuine data records, not for `∧` or `∃`.
Quotient-facing public destructuring is documented in
`conventions/quotients.md`.

## Tactics

```math
ring
field(nonzeroFact, ...)
linear_combination(expression)
group
monoid
module
disjunct(proof)
```

The applicable carrier structures and limitations are described in
`conventions/algebra-tactics.md`. On a commutative carrier `ring` normalises
the usual way; on a **non-commutative** carrier (e.g. the square-matrix ring)
it normalises to ordered words, keeps factor order, and declines `A * B =
B * A`.

`disjunct(proof)` injects a proof into the matching branch of a
right-associated disjunction. It is especially useful for generated finite
classifications: the elaborator emits the exact `Or` constructor path without
requiring a nested `Or.introduceRight(...)` term or invoking proof search.

## Citation and inference

`by theoremName` elaborates the theorem against the expected proposition,
infers data arguments, and discharges theorem premises from the local
context.

```math
resultingProposition by theoremName;
done by theoremName
```

Use a positional application only when an argument is mathematical data that
the goal cannot determine.

`recalling factName` temporarily supplies named facts to a citation:

```math
P by theoremName recalling factName;
```

## Checked observations

```math
note P;
note P by theoremName;
note goal : T;
```

`note` verifies but does not retain the proposition.

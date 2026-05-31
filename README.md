# math

A from-scratch dependent-type theorem prover, built to host a library of
formal mathematics whose proofs read like math — familiar to
mathematicians and easy for LLMs to write.

## What this is

- A **kernel** (CIC, ~Lean 4 shape): inductives, recursors, definitions,
  universe-polymorphic constants, propositional and large elimination
  rules, propositional extensionality.
- An **elaborator** that turns a small math-flavored surface language
  into kernel terms.
- A **library** of mathematics built on top, from logic and naturals
  through integers, rationals, reals, p-adics, polynomials, and the
  finite fields and complex numbers built from them.
- A **caching build system** (`make -j 16 library`) that verifies each
  source file independently and serializes the resulting environment to
  `build/library/.../*.mathv`. Warm rebuilds are sub-second.

The trusted base is the kernel. Everything else — the surface
language, the elaborator's auto-prover, the tactics — emits explicit
kernel terms that the kernel rechecks.

## Build

```
make -j 16 library     # verify all .math files in library/
./kernel               # unit tests (kernel + elaborator)
```

Always build with `-j 16`; the dependency graph is parallel.

## Lemma search

`./kernel search` finds library lemmas by goal shape:

```
./kernel search --goal "a + b = b + a"     # lemmas whose conclusion matches
./kernel search --mentions Natural.power   # lemmas mentioning these names
```

Failed proofs also surface candidate lemmas in their error output.

## Editor integration

Errors are printed in the canonical compiler format
`<file>:<line>:<column>: <kind> error: <message>` followed by an
indented breadcrumb stack with the local context and goal at each
frame, so any editor's problem-matcher / compilation-mode picks them up.

- `docs/editor/watch.md` — running the build in a tight loop with
  `fswatch` or `entr`.
- `docs/editor/vscode.md` — a `.vscode/tasks.json` recipe with a
  problem matcher that surfaces failures in the Problems panel.
- `docs/editor/emacs.md` — `compilation-mode` + a save-triggered
  rebuild via `dir-locals`.

## Layout

```
expression.hpp / level.hpp        kernel data
kernel.{cpp,hpp}                  type-check, WHNF, def-eq, inductives
lexer / parser / surface          surface language
elaborator.{cpp,hpp}              surface → kernel, tactics, sugar
lemma_search.{cpp,hpp}            goal-shape lemma index + `search` CLI
printer / serialize / hash        diagnostics, .mathv caching

CLAUDE.md                         project conventions and idioms
TODO.md                           planned work
HASH_USE_VS_LEAN.md               design note: subtree hashing vs Lean

library/
  axioms.math                     propext, function ext
  Logic/                          Equality, Quotient, ∃, ∧, ∨, Decidable, …
  Equality/basics.math            symmetry, transitivity, congruence
  Algebra/                        IsMonoid/IsGroup/IsRing/IsCommutativeRing/
                                  IsField, bundled structures, generic lemmas
  Set/                            Set(T), membership, subset
  Natural/                        Naturals through bezout, p-adic valuation
  Integer/                        Integers as Natural² quotient
  IntegerMod/                     ℤ/(n)
  Rational/                       Rationals as (Integer, ℕ⁺) quotient
  Real/                           Reals as Cauchy quotient of Rational
  PAdic/                          p-adics as p-adic-Cauchy quotient
  Polynomial/                     polynomials over a ring; division, gcd, Bezout
  RingModulo/                     generic quotient ring R/(ideal)
  ComplexNumber/                  ℂ = ℝ[x]/(x²+1)
  FiniteField/                    F_{p^k} = F_p[x]/(f) for irreducible f
  Lists/                          basic list machinery
  Test/                           small files exercising individual features
```

Imports flow up the dependency layers: a file in `Integer/` can import
`Natural/` and `Logic/`, but not `Rational/`.

## Current state of the library

- **Foundations:** propositional extensionality, function extensionality,
  Quotient kernel (`Quotient.mk` / `.sound` / `.lift` / `.induct` / `.exact`),
  classical `Decidable`, `Set`.
- **Algebra:** `IsMonoid`, `IsGroup`, `IsRing`, `IsCommutativeRing`,
  `IsField` predicates with bundled-structure carriers; generic lemmas
  (cancellation, inverse uniqueness, ring annihilation / negation,
  ring divisibility) usable at any carrier via instance inference.
- **Natural:** arithmetic, order, divisibility, Bezout, Euclidean
  algorithm, GCD, factorization, primes, p-adic valuation.
- **Integer:** commutative ring via the (a, b) representative quotient.
- **IntegerMod:** ℤ/(n) as a quotient; ring structure.
- **Rational:** field via (numerator : Integer, denominatorMinusOne : ℕ).
  Order; absolute value; halving; reciprocal; triangle inequality.
- **Real:** Cauchy sequences of Rationals; addition, multiplication,
  negation; order; **field instance**; completeness (suprema of
  bounded-above nonempty sets via bisection).
- **PAdic:** p-adic-Cauchy sequences of Rationals; full
  commutative-ring instance; honest p-adic absolute value; embedding.
- **Polynomial:** polynomials over a ring; degree, division with
  remainder, gcd / Bezout, irreducibility; `R[x]/(f)` is a field when
  `f` is irreducible over a field.
- **ComplexNumber:** ℂ = ℝ[x]/(x²+1) — commutative ring and field
  (x²+1 irreducible over ℝ), i² = −1, injective ℝ ↪ ℂ.
- **FiniteField:** F_{p^k} = F_p[x]/(f) is a field for irreducible f.

## Elaborator features at a glance

The patterns are documented in detail in `CLAUDE.md`. Highlights:

- **`ring` / `field` tactics.** `ring` normalises any commutative-ring
  identity (distributivity, AC-rearrangement, like-term collection at
  signed integer coefficients, cancellation, Integer literals) over any
  carrier with an `IsRing` instance — including an abstract bundled
  ring. `field(h₁, …)` extends it with reciprocal side-relations from
  nonzero hypotheses.
- **Calc with auto-prover.** `by <reason>` is optional on every calc
  step. When absent, the elaborator tries definitional equality →
  reflexivity, single-position diff resolved through a library-wide
  rewrite-lemma index → local-hypothesis match → `ring`-style
  rearrangement. `calc` chains mix `=`/`≤`/`<`/`≥`/`>` and pick the
  strongest relation. Lemma registration runs at theorem-declaration
  time and on `.mathv` load, so the index covers the library uniformly.
- **Subtree hashing.** Every `Expression` and `Level` carries a cached
  bottom-up structural hash; `structurallyEqual` uses it as an O(1)
  fast-reject, and a coarser spine-head hash drives the lemma-index
  bucket lookup (and the `search` CLI).
- **Quotient idioms.** `Quotient.mk(rep)` and friends infer their type
  and relation from context; `construction` names an intro form;
  `by_representatives x as ⟨a, b⟩, …` picks representatives in one line.
- **Instance inference.** `instance` registers a structure witness as
  canonical for its `(structure, carrier)` pair; generic lemmas with
  implicit structure/operation/instance arguments get them filled at
  concrete call sites (and from unique in-scope hypotheses for abstract
  carriers).
- **Statement-level proof sugar.** `claim`/`goal`/`obtain`/`choose`/
  `take`/`suppose`/`let`/`note`/`change` compose as math prose;
  `by_induction on n with IH`, `by_strong_induction on n with IH`, and
  `decide P { yes m => … | no n => … }` for case-splits.
- **`rewrite(lemma)`** in calc steps and **`rewrite(eq, term)`** at the
  term level; **`congruenceOf(F, eq)`** with diff-inferred congruence;
  **implicit arguments** `{x : T}`; **name-bound conventions**;
  **`opaque definition`** with `unfold … in …`.

## Design principles

These have been load-bearing decisions that show up everywhere:

- **Mathematician-friendly identifiers.** No sigil-marked or
  ALL_CAPS keywords; the math vocabulary belongs to the user. Tactic
  keywords are contextual where possible.
- **No abbreviations in identifiers.** `representative`, not `rep`,
  in declared names. Long fully-qualified names
  (`Rational.padic_absolute_value`) are searchable. Local-variable
  abbreviations are fine.
- **Coercions are explicit, never implicit.** Ascription `(x : T)`
  triggers a single registered embedding chain; anywhere else the
  user must write the conversion. Cascaded explicit casts are
  unbearable, but visible casts at one syntactic site localize the
  type change.
- **Embedding paths are canonical, not searched.** If two embeddings
  ever exist from source to target, the system rejects rather than
  picks one. The same one-per-pair stance governs the instance and
  coercion registries.
- **The trusted base is the kernel.** All elaborator features —
  auto-prover, tactics, sugar — emit explicit kernel terms that the
  kernel rechecks. AC-modulo reasoning, identity-lemma lookup, and
  the like never enter the trusted core.

## Where to go for more

- `CLAUDE.md` — the idiomatic patterns for writing proofs in this
  library, kept up to date for both humans and assistant sessions.
- `TODO.md` — planned work, in priority/dependency order.
- `HASH_USE_VS_LEAN.md` — design note pinning down where our
  subtree-hashing plan lines up with Lean's and where it diverges.
- `library/Test/` — small files that exercise individual elaborator
  features.
</content>
</invoke>

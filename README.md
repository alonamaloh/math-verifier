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
  through integers, rationals, reals, and p-adics.
- A **caching build system** (`make -j 16 library`) that verifies each
  source file independently and serializes the resulting environment to
  `build/library/.../*.mathv`. Warm rebuilds are sub-second; cold
  rebuild of the full library is ~4–5s.

The trusted base is the kernel. Everything else — the surface
language, the elaborator's auto-prover, the tactics — emits explicit
kernel terms that the kernel rechecks.

## Build

```
make -j 16 library     # verify all .math files in library/
./kernel               # unit tests (kernel + elaborator)
```

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
printer / serialize / hash        diagnostics, .mathv caching

CLAUDE.md                         project conventions and idioms
TODO.md                           planned work
HASH_USE_VS_LEAN.md               design note: subtree hashing vs Lean

library/
  axioms.math                     propext, function ext
  Logic/                          Equality, Quotient, ∃, ∧, ∨, …
  Equality/basics.math            symmetry, transitivity, congruence
  Algebra/                        IsMonoid, IsGroup, IsRing, IsCommutativeRing
  Natural/                        Naturals through bezout, p-adic valuation
  Integer/                        Integers as Natural² quotient
  Rational/                       Rationals as (Integer, ℕ⁺) quotient
  Real/                           Reals as Cauchy quotient of Rational
  PAdic/                          p-adics as p-adic-Cauchy quotient
  Lists/                          basic list machinery
  Test/                           small files exercising individual features
```

Imports flow up the dependency layers: a file in `Integer/` can import
`Natural/` and `Logic/`, but not `Rational/`.

## Current state of the library

- **Foundations:** propositional extensionality, function extensionality,
  Quotient kernel (`Quotient.mk` / `.sound` / `.lift` / `.induct` / `.exact`).
- **Natural:** arithmetic, order, divisibility, Bezout, Euclidean
  algorithm, GCD, factorization, primes, p-adic valuation.
- **Integer:** ring of integers via the (a, b) representative quotient.
  Commutative ring instance.
- **Rational:** field via (numerator : Integer, denominatorMinusOne : ℕ).
  Commutative ring instance; order; absolute value; halving;
  reciprocal; triangle inequality.
- **Real:** Cauchy sequences of Rationals; addition, multiplication,
  negation; basic order. Field instance is in progress.
- **PAdic:** p-adic-Cauchy sequences of Rationals; full
  commutative-ring instance; absolute value; embedding.

## Elaborator features at a glance

The patterns are documented in detail in `CLAUDE.md`. Highlights:

- **Calc with auto-prover.** `by <reason>` is optional on every calc
  step. When absent, the elaborator tries definitional equality →
  reflexivity, single-position diff resolved through a library-wide
  rewrite-lemma index (any `Π x₁…xₙ. LHS = RHS` lemma bucketed by
  the spine head of its sides, matched with a first-order matcher,
  emitted as a kernel-checked application with `Equality.symmetry`
  wrapped on for reverse direction) → local-hypothesis match, and
  finally a `ring`-style AC-rearrangement fallback. Lemma
  registration runs at theorem-declaration time and on `.mathv`
  load, so the index covers the whole library uniformly.
- **Subtree hashing.** Every `Expression` and `Level` carries a cached
  bottom-up structural hash; `structurallyEqual` uses it as an O(1)
  fast-reject. A coarser spine-head hash drives the calc
  auto-prover's lemma-index bucket lookup.
- **`Quotient.mk` short forms.** Type and relation inferred from
  context; only the representative is written.
- **Implicit arguments** `{x : T}` on `definition` / `theorem` / `axiom`.
- **Name-bound conventions.** `convention p : Natural with primality :
  Natural.is_prime(p)` at the file top auto-prepends implicit binders
  to every subsequent declaration mentioning `p`.
- **`rewrite(lemma)`** inside calc steps; **`by_induction on a with IH`**
  for math-style induction; **`obtain ⟨…⟩ from …`** for ∃-destructure;
  **`ring`** for pure-sum / pure-product rearrangement;
  **`congruenceOf(F, eq)`**; **`reflexivity`** without arguments in
  calc steps.

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
  picks one.
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

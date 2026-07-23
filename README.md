# math

A from-scratch dependent-type theorem prover, built to host a library of
formal mathematics whose proofs read like math — familiar to
mathematicians and easy for LLMs to write.

## What this is

- A **kernel** (CIC, ~Lean 4 shape): inductives, recursors, definitions,
  universe-polymorphic constants (non-cumulative, matching Lean 4's
  convention), propositional and large elimination rules, propositional
  extensionality.
- An **elaborator** that turns a small math-flavored surface language
  into kernel terms.
- A **library** of mathematics built on top, from logic and naturals
  through integers, rationals, reals, polynomials, and the finite
  fields and complex numbers built from them; a finite-dimensional
  **linear algebra** layer (matrices, determinants, rank–nullity,
  Cayley–Hamilton); and an in-progress **quadratic-forms development**
  driving toward the Fifteen Theorem.
- A **caching build system** (`make -j 16 library`) that verifies each
  source file independently and serializes the resulting environment to
  `build/library/.../*.mathv`. Warm rebuilds are sub-second.

The trusted base is the kernel. Everything else — the surface
language, the elaborator's auto-prover, the tactics — emits explicit
kernel terms that the kernel rechecks.

## Build

```
make -j 16 library     # verify all .math files in library/
make -j 16 tests       # also verify the Test/ feature files
make error-tests       # error-message regression suite
./kernel               # unit tests (kernel + elaborator)
```

Always build with `-j 16`; the dependency graph is parallel.

## Milestones: Freek's 100 theorems

The library tracks [Freek Wiedijk's "Formalizing 100 Theorems"
list](https://www.cs.ru.nl/~freek/100/) as a goal thread — 19 entries
verified so far, from the irrationality of √2 through the intermediate
value theorem, the non-denumerability of the continuum, and the
inequality of arithmetic and geometric means. The index of what's done
and where each theorem lives is **[docs/freek_100.md](docs/freek_100.md)**.

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
                                  IsField, bundled structures, generic lemmas,
                                  group homomorphisms / subgroups; matrices,
                                  determinant / adjugate, permutation sign,
                                  rank–nullity, Cayley–Hamilton, vector spaces;
                                  quadratic forms and the Fifteen Theorem effort
  Set/                            Set(T), membership, subset
  Natural/                        Naturals through bezout, p-adic valuation
  Integer/                        opaque ℤ as a Natural² quotient
  IntegerMod/                     ℤ/(n)
  Rational/                       opaque ℚ as a field of fractions over ℤ
  Real/                           Reals as Cauchy quotient of Rational
  Polynomial/                     polynomials over a ring; division, gcd, Bezout
  RingModulo/                     generic quotient ring R/(ideal)
  ComplexNumber/                  ℂ = ℝ[x]/(x²+1)
  FiniteField/                    F_{p^k} = F_p[x]/(f) for irreducible f
  GaussianInteger/                ℤ[i] = ℤ[x]/(x²+1); Euclidean; two squares
  Lists/                          polymorphic lists: products, permutations,
                                  ranges, filter, distinctness
  Test/                           small files exercising individual features
  ErrorTest/                      error-message regressions (`make error-tests`)
```

Imports flow up the dependency layers: a file in `Integer/` can import
`Natural/` and `Logic/`, but not `Rational/`.

## Current state of the library

- **Foundations:** propositional extensionality, function extensionality,
  Quotient kernel (`Quotient.mk` / `.sound` / `.lift` / `.induct` / `.exact`),
  classical `Decidable`, `Set`, and definite description (`Logic.the`:
  the unique object satisfying a uniquely-satisfied predicate), which
  underpins `Real.limit`, square roots, and `exp`.
- **Algebra:** `IsMonoid`, `IsGroup`, `IsRing`, `IsCommutativeRing`,
  `IsField` predicates with bundled-structure carriers; generic lemmas
  (cancellation, inverse uniqueness, ring annihilation / negation,
  ring divisibility) usable at any carrier via instance inference.
  Group theory on the bundled `Group`: homomorphisms (identity- and
  inverse-preservation, composition), subgroups, the kernel and image
  of a homomorphism, and injectivity ⟺ trivial kernel.
- **Linear algebra:** matrices over a commutative ring (the `Matrix.ring`
  bundle), matrix–vector and matrix–matrix products, transpose; the
  **determinant** via the permutation expansion, its multiplicativity and
  the **adjugate** / Cramer identities; permutations of a finite set with
  their **sign**; coordinate spaces, span, subspaces, and **rank–nullity**;
  and the **Cayley–Hamilton theorem**.
- **Quadratic forms & the Fifteen Theorem (in progress):** symmetric
  integer matrices, their quadratic forms, positive-definiteness,
  representation and universality, and Conway–Schneeberger *escalation*.
  Landed so far: the truant and escalation machinery; the complete
  deduplicated **rank-two and rank-three classifications**; a
  kernel-checked cover of **every rank-four escalator by 207 selected
  normal forms**; and the value-through-15 sweep of those forms. The
  final theorem is not yet proved — the remaining obligations are the
  universality of the selected forms and the **three-squares converse**
  (`n = x²+y²+z² ⇔ n ≠ 4ᵃ(8b+7)`), whose obstruction direction is proved
  and to which everything else is being reduced: the per-form universality
  proofs are conditional on it, and the ternary section-converses that
  gate them (so far `x²+y²+2z²`, `x²+2y²+2z²`, `x²+2y²+4z²`) reduce to it
  by elementary identities rather than independent genus theory. The
  escalation and universality certificates are **machine-generated by an
  untrusted search and rechecked in full by the kernel**. See
  `library/Algebra/fifteen-theorem.md` and `PLAN_15_THEOREM.md`.
- **Natural:** arithmetic, order, divisibility, Bezout, Euclidean
  algorithm, GCD, factorization, primes, p-adic valuation, factorial,
  Euler's totient; the fundamental theorem of arithmetic.
- **Integer:** commutative ring via the (a, b) representative quotient,
  now **opaque** — consumers go through the difference-of-naturals
  boundary; Euclidean division; sign / absolute value.
- **IntegerMod:** ℤ/(n) as a quotient; ring structure; **F_p is a field
  for prime p**; canonical representatives; the unit group of ℤ/n
  characterised by coprimality.
- **Rational:** an **opaque field of fractions** over ℤ — a quotient of
  (numerator : Integer, denominator : nonzero Integer), with consumers
  going through the fraction boundary. Order; absolute value; honest
  division; reciprocal; triangle inequality.
- **Real:** Cauchy sequences of Rationals — and a **fully proven
  complete-ordered-field interface** (field, total order compatible
  with + and ×, suprema of bounded-above nonempty sets, an
  order-embedded ℚ), after which downstream development never touches
  the quotient. A substantial **analysis layer** now sits on top:
  sequence limits and limit arithmetic, **Cauchy completeness**
  (every Cauchy sequence converges), continuity, the intermediate
  value theorem, a division-free **differential calculus** (constant /
  identity / sum / scale / negation / difference / product rules,
  continuity of differentiable maps, uniqueness of the derivative),
  square root as an honest function, the Cauchy–Schwarz inequality, and
  the **real exponential** `exp(x) = lim Σ xᵏ/k!` with `e`, `1 + x ≤
  exp(x)`, and `exp(x) > 0`.
- **Polynomial:** polynomials over a ring; degree, division with
  remainder, gcd / Bezout, irreducibility; `R[x]/(f)` is a field when
  `f` is irreducible over a field.
- **ComplexNumber:** ℂ = ℝ[x]/(x²+1) — commutative ring and field
  (x²+1 irreducible over ℝ), i² = −1, injective ℝ ↪ ℂ; real and
  imaginary coordinates with reconstruction `z = re + im·i`, the
  honest modulus `|z| = √(re² + im²)` with multiplicativity and the
  triangle inequality, **completeness** (every Cauchy sequence
  converges coordinate-wise), and the **complex exponential**
  `exp(z) = lim Σ zᵏ/k!`.
- **FiniteField:** F_{p^k} = F_p[x]/(f) is a field for irreducible f.
- **GaussianInteger:** ℤ[i] via the generic RingModulo; coordinates,
  norm, units, Euclidean structure.
- **Set:** finite-cardinality layer — equinumerosity, sizes, the sum
  and product rules, pigeonhole; Cantor's theorem and enumerability.

Headline theorems (Freek Wiedijk's "100 theorems" tally — nineteen so
far, indexed in [docs/freek_100.md](docs/freek_100.md)): irrationality
of √2 (#1), denumerability of ℚ (#3), Euler's totient theorem (#10),
infinitude of primes (#11), **Fermat's two-squares theorem** (#20, via
Wilson + descent in ℤ[i]), **non-denumerability of the continuum**
(#22), **divergence of the harmonic series** (#34), **the
arithmetic/geometric mean inequality** (#38), the binomial theorem
(#44), **Wilson's theorem with its converse** (#51), Cantor's theorem
(#63), the geometric series (#66), the Euclidean algorithm (#69), the
Cauchy–Schwarz inequality (#78), **the intermediate value theorem**
(#79), the fundamental theorem of arithmetic (#80), the sum of the
reciprocals of the triangular numbers (#42), and — from the linear-algebra
layer — **the Cayley–Hamilton theorem** (#49) and **Cramer's rule** (#97).

## Elaborator features at a glance

The conventions are documented in detail in `CLAUDE.md` and
`docs/conventions/` (and the surface catalogue in `docs/reference.md`).
Highlights:

- **`ring` / `field` tactics.** `ring` normalises any commutative-ring
  identity (distributivity, AC-rearrangement, like-term collection at
  signed integer coefficients, cancellation, numeric literals — Peano
  numerals fold on Natural, where `successor(e)` reads as `1 + e`) over
  any carrier with an `IsRing` instance — including an abstract bundled
  ring. On a **non-commutative** carrier (e.g. the square-matrix ring) an
  explicit `ring` normalises to ordered words, keeping factor order and
  refusing `A·B = B·A`. `field(h₁, …)` extends it with reciprocal
  side-relations from nonzero hypotheses, and `linear_combination(e)`
  closes a ring equality from a linear combination of equational
  hypotheses.
- **Finite and disjunction tactics.** `by finite_check n from a until b`
  closes a bounded-universal goal over `a ≤ n < b` by a kernel-checked
  enumeration of the closed range (capped, per-case). The auto-prover
  refutes a closed false ground disjunction (e.g. `¬(7 = 0 ∨ … ∨ 7 = 12)`)
  by certifying each leaf, and `by disjunct(proof)` injects a proof of one
  disjunct into a nested disjunction goal.
- **Expected-carrier propagation.** Once one operand of an operator or
  relation fixes the carrier, bare numerals and Natural variables in the
  same expression lift to it through the canonical coercion chain, so an
  Integer-valued comparison needs no `(… : ℤ)` on its literals. Finite
  vector literals `⟨e₀, …, eₙ₋₁⟩` build a `RingVector` at the
  expected coefficient carrier.
- **Relation chains with auto-prover.** A proof step is a bare stated
  relation; a run of them written `a = b = c … by <reason>` is a
  relation chain, mixing `=`/`≤`/`<`/`≥`/`>` (and preorders like `∣`/
  `⊆`) and picking the strongest relation. `by <reason>` is optional on
  every step: when absent, the elaborator tries definitional equality →
  reflexivity, single-position diff resolved through a library-wide
  rewrite-lemma index → local-hypothesis match → `ring`-style
  rearrangement. Lemma registration runs at theorem-declaration time and
  on `.mathv` load, so the index covers the library uniformly.
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
- **Argument-free citation.** Citing a lemma `by <Lemma>` (or naming a
  stated fact with `note P by <Lemma>`) infers every argument: data args
  from the goal, proof premises discharged from in-scope hypotheses (with
  back-inference for arguments that occur only in premises). This extends
  to Pi-typed goals (binders are introduced and the citation runs on the
  core goal) and to lemmas quantified over a predicate (`P(x)` conclusions
  recover `P` from the premises, unfolding folded definitions one δ-step
  at a time). Where no goal validates the choice, an ambiguous premise
  match is an error listing the candidates.
- **Statement-level proof sugar.** A bare stated proposition, `goal`/
  `choose`/`take`/`suppose`/`let`/`note`/`change` compose as math prose;
  `note P by <reason>` names a verified fact; `by_induction on n with IH`,
  `by_strong_induction on n with IH`, and `decide P { yes m => … | no n
  => … }` for case-splits.
- **Equation transport** through `… by substituting` and diff-inferred
  `by` steps in a relation chain; **implicit arguments** `{x : T}`;
  **name-bound conventions**; **`opaque definition`** with
  `unfold … in …`.

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

- `docs/tutorial.md` — a 10-minute, example-driven introduction to
  writing proofs; start here.
- `docs/reference.md` — a catalogue of every surface construct;
  `docs/style.md` and `docs/conventions/` — how to make a proof read
  well; `docs/library.md` — a map of `library/` by mathematical area.
- **`library/<Area>/README.md`** — the entry point for a library area
  (e.g. `library/Algebra/README.md`); read it before extending that area.
  `library/Algebra/fifteen-theorem.md` maps the quadratic-forms
  development, and `PLAN_15_THEOREM.md` is its stage-by-stage plan and
  authoritative progress tracker.
- `CLAUDE.md` — the always-apply project conventions (an index into
  `docs/conventions/`), kept up to date for both humans and assistant
  sessions.
- `docs/error_message_corpus.md` — the data-driven error-message
  improvement workflow (capture → diagnose → fix → regression).
- `TODO.md` — planned work, in priority/dependency order.
- `STRESS_PROBES.md` — a diagnostic roadmap of library extensions
  (analysis depth, geometry/topology, metatheory, abstract linear
  algebra, new quotients) chosen to load one layer — prover, surface
  language, or foundations — at a time and reveal where it bends.
- `PLAN_*.md` (repo root) — active and historical plans. The largest current
  effort is **`PLAN_15_THEOREM.md`** (the quadratic-forms / Fifteen Theorem
  development, with its own status ledger); `PLAN_LANGUAGE_IMPROVEMENT.md`
  tracks the surface-language direction (opaque-by-default + successor-free +
  cite-only prover).
- `LUX_PLAN.md` — the design note behind the planned higher-level proof
  surface (Lux).
- `HASH_USE_VS_LEAN.md` — design note pinning down where our
  subtree-hashing plan lines up with Lean's and where it diverges.
- `library/Test/` — small files that exercise individual elaborator
  features.
</content>
</invoke>

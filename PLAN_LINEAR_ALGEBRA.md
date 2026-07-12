# PLAN_LINEAR_ALGEBRA.md — finite-dimensional linear algebra (rank–nullity and det multiplicativity)

The two headline targets are **rank–nullity** (`dim ker T + dim im T = dim V`)
and **det(AB) = det(A)·det(B)**. They are chosen as *expressiveness probes*,
not for the mathematics: everything in the library so far lives over a fixed
carrier (ℤ, ℚ, ℝ, ℂ, a fixed group/ring/field, polynomials over a fixed base).
Linear algebra is the first branch that forces **families indexed by a count
that is itself proof data** (`NaturalsBelow(n) → V`) and **transport across a
proven `n = m`**. That is the one characteristic CIC pressure point we have
never tested. The primary deliverable of this branch is therefore *information*:
does the dependent-index / transport story stay ergonomic, or do proofs drown in
casts? Treat friction around `NaturalsBelow(n) ≃ NaturalsBelow(m)` as a finding
to record (in `STRESS_PROBES.md`), not just an obstacle to route around.

**On "finite-dimensional".** The vector-space *axioms are the standard,
unrestricted ones* and the `VectorSpace` structure is fully general — nothing in
the definitions is capped at finite dimension. "Finite-dimensional" governs only
(a) which *structure* carries a natural-number `dimension` and (b) which
*theorems* (the counting ones) are stated unconditionally. `IsBasis` is
index-generic and admits infinite bases (e.g. `{xⁿ}` for `F[x]`); see Stage D.

**On the axiom of choice.** This branch is built to make *turning AC on later
non-disruptive*, without adopting it now. Choice is **threaded as an explicit
`Proposition` hypothesis**, never added as a global axiom (see "Axiom-of-choice
architecture"). The finite-dimensional and countable-dimensional layers are
provably choice-free; only the general infinite-dimensional invariance/existence
results take a `(choice : AxiomOfChoice)` parameter. No step here may add an
axiom to the trusted base.

## Status ledger

Update this section before ending any session that works on the plan.

- **Stage 0 (decisions)** — 0.1/0.2 SETTLED by the Stage A landing
  (2026-07-11): `Field` = `CommutativeRing` + `Nontrivial` +
  `NonzeroInvertible` (predicates over the bundle, so `Field.make` reads
  as its content); universe check confirmed (`Field : Type(1)` carrying
  a `Type(1)` bundle is fine); reciprocal via `Logic.the` over
  `Field.inverse_unique`. 0.3 (two layers) and 0.4 (index bridge) are
  settled on paper, exercised by Stages B/D.
- **Stage A — DONE (2026-07-11).** `Algebra/field_bundle.math`: the
  `Field` record, projections, operation wrappers + operators
  (`+ - * ⁻¹`), `instance Field.is_ring`, the flattened law layer (the
  names `ring` demands), `Field.is_field`, `Field.inverse_unique`,
  `Field.reciprocal`, `Field.reciprocal_multiplies`. Instances:
  `Real.field` (`Real/field_bundle.math`), `Rational.field`
  (`Rational/field_bundle.math`, over the new
  `Rational/ring_bundle.math` — ℚ had no `Ring`/`CommutativeRing`
  bundle). A `FiniteField`/ℤp instance is deferred until a consumer
  wants it (IntegerMod lacks a `CommutativeRing` bundle; measure
  first). Elaborator support landed with it: `computeRingScheme`
  treats `Field.carrier(f)` like `CommutativeRing.carrier(c)` (sound —
  commutativity is a bundle field), `carrierProjectionField` recurses
  through the bundle layers (Field.make → CommutativeRing value → Ring
  value → carrier; also fixes the latent CommutativeRing-instance
  case), and the postfix-operator path saturates implicit-carrying
  dispatch functions with holes (`x⁻¹` over an abstract field).
  Acceptance: `Test/field_bundle_test.math` (ring-normalisation over
  abstract `Field.carrier`, bare instance axioms, by-less reciprocal
  cancellation, concrete-instance reduction). All five files in the
  clean manifest.
- **Stage B — DONE (2026-07-12).** `Algebra/vector_space.math`:
  `IsVectorSpace` (abelian group + the four scalar-action laws), the
  bundled `VectorSpace(f)` record INDEXED by its field (Type(1),
  parameterized inductive — the first in the library), projections,
  operations + operators (`+ - •`), `instance
  VectorSpace.is_abelian_group`, an `automatic` flattened law layer
  (no `ring` normaliser exists over a vector carrier, so the scan is
  what discharges bare vector arithmetic — six group laws + the four
  scale laws), and the `F`-over-itself instance
  (`Field.vector_space`). `Algebra/coordinate_space.math`: `Fⁿ` as
  `NaturalsBelow(n) → Field.carrier(f)` under pointwise operations —
  the first genuinely dependent-indexed carrier — with
  `CoordinateSpace.equal_of_pointwise` as the one extensionality
  bridge and every law a pointwise field fact closed by `ring`.
  FOUNDATIONAL PREREQUISITE LANDED WITH IT: **function extensionality
  is now a THEOREM** (`Function.extensionality`, Logic/functions.math)
  — derived from the quotient axioms + η (evaluate through the
  pointwise-equality quotient; the round trip computes back by lift-ι
  + η), no new axiom, honoring the no-axiom guardrail. Elaborator
  support: the `•` token (lexer/parser, multiplicative precedence);
  two-phase operator implicit recovery (a heterogeneous operator's
  left operand may not pin every implicit — `•` pins {f} from the
  scalar, the RIGHT operand's type against the second explicit domain
  pins {V}); `carrierProjectionField` peels implicit-carrying
  projections and reads through `VectorSpace.make` (parameter first,
  carrier second). Acceptance: `Test/vector_space_test.math`.
  PROBE FINDINGS (the branch's purpose): (1) the `by <lemma>` citation
  path does NOT ∀-intro a Pi goal before matching, so the ∀-shaped
  law legs need explicit binder lambdas around the pointwise bridge —
  a candidate follow-up for the citation machinery; (2) the leak
  taxonomy counts `equal_of_pointwise(<pointwise lambda>)` term calls
  as direct proof-lemma calls (same class as ComplexNumber's accepted
  `extensionallyEqual` applications) — `coordinate_space.math` is
  KEPT OUT of the clean manifest pending an owner style call (bless
  the pointwise-bridge application as data-like, or grow a surface
  form for it); `vector_space.math` is in the manifest.
  CLEAN_LEAK_BUDGET resynced 230→232 (field_bundle's two `Logic.the`
  proof-data tokens, the Real.reciprocal idiom — my Stage A gate ran
  before the manifest edit, so the +2 surfaced here).
- **Stage C — DONE (2026-07-12).** `Algebra/vector_space_lemmas.math`:
  the derived scale facts as `automatic` lemmas (no `ring` over vector
  carriers, so the scan is the normaliser): `zero_scale` (0·v = 0),
  `scale_zero` (a·0 = 0), `negate_one_scale` ((−1)·v = −v),
  `subtract_self`, `subtract_add_cancel`.
  `Algebra/subspace.math`: `IsSubspace` (zero + add/scale closure;
  negate-closure DERIVED via (−1)·v), accessor projections as
  proof-data `definition`s (the bundle-file pattern — keeps
  constructions leak-free), and the induced space on the subtype
  mirroring `subgroup_group`: ops inherit from V with closure
  membership proofs, every law reduces through
  `Subtype.equal_of_value_equal`, `Subspace.is_vector_space` assembles
  by argument-free `by Subspace.<law>` citations (the `Field.is_field`
  idiom), `Subspace.vector_space : VectorSpace(f)` bundles it. DESIGN
  CALL: `Subspace.carrier(V, subset, subspace)` is parameterized by
  the closure PROOF so the `+`/`•` operators recover it from the
  operand type (the PAdic `(p, primality)` recovery precedent) —
  subspace arithmetic reads `(x + y) + z`, no five-argument spellings.
  `Algebra/linear_map.math`: `IsLinearMap` (∧ of additivity +
  homogeneity), `LinearMap.additive`/`homogeneous` accessor
  definitions, preserves zero/negate/subtract, identity map + compose,
  `kernel`/`image` + both `*_is_subspace` (take/suppose/choose/witness
  shapes, no tuples), injective ⟺ trivial kernel via
  `Function.IsInjective` (reused from Logic/functions), and
  `Subspace.inclusion_is_linear`/`_is_injective`. Acceptance:
  `Test/linear_map_test.math`. TWO ELABORATOR GAPS fixed at the root
  (both in the Stage C commit): (1) the operator desugarer elaborated
  the RIGHT operand with the left's type as a hard expected type — a
  heterogeneous operator's right operand (`a • Subtype.value(x)`) got
  its implicits poisoned; the propagation is now a HINT with a
  bottom-up retry (elaboration + type inference share the retry).
  (2) The plain-call path inferred a declared implicit prefix only for
  EXACTLY-fully-applied calls, so a genuine partial application after
  the prefix (`Subspace.inclusion(V, subset, subspace)` leaving its
  function argument open) jammed V into the `{f}` slot; the guard is
  now `<=` (positional-with-implicits spellings are outside the
  window). PROBE FINDINGS: the conjunction-leg projection (`P by h`)
  does not δ-unfold a defined proposition (`by tLinear` fails with a
  `<unknown>`-head message — inbox entry filed); the robust idiom is
  accessor citations `by LinearMap.additive(tLinear)` at stated-leg
  expected types, then hypothesis application in chains. Accessor
  citations under a congruence wrapper mis-pin implicits (backward
  unification from the outer step equation wins over forward from the
  premise) — extract legs first there. Gates: library+tests,
  error-tests 54/0, export-check 2677, clean-check GREEN at budget 232
  (all three files manifest-added leak-free, re-run after the manifest
  edit), serial warning-site diff IDENTICAL (6 standing advisory
  sites both sides).
- **Stages D–H** — not started. Next: Stage D (span, independence,
  IsBasis — generic aggregation Stage 1 is landed, so unblocked).
  Note for D: bundled induced spaces of kernel/image
  (`Subspace.vector_space` applied to `kernel_is_subspace`) were left
  to consumers — construct them where Stage G needs dimensions.

## What is already in place (so this isn't re-litigated)

- **The finite-index type already exists.** `NaturalsBelow(n)`
  (`Set/finite.math`) is `Subtype(Natural, k ↦ k < n)` — our `Fin n` — with
  `.make` / `.value` / `.below` and value-extensionality
  (`NaturalsBelow.equal_of_value`). **Do not invent a new `Fin`.** Build finite
  bases and matrices as families over `NaturalsBelow`.
- **Counting / cardinality is a *relation*, not a `Cardinal` value.**
  `Equinumerous(A, B)` (`Set/equinumerous.math`) is a `Proposition` (an
  equivalence relation); `HasSize(X, n)` (`Set/finite.math`) is finite,
  `Natural`-valued. There is **no `Cardinal` type**, no cardinal *order* (`≼`),
  and (apparently) no Schröder–Bernstein yet. Design dimension around
  equinumerosity + `HasSize`, not around a cardinal object (Stage F).
- **Pigeonhole / size congruences.** `Set/finite_pigeonhole.math` and the
  `HasSize`/equinumerosity congruences in `Set/finite_sum.math` are what
  finite-dimensional invariance should reduce to.
- **The bundling pattern.** `Group` / `Ring` / `CommutativeRing`
  (`Algebra/*_bundle.math`) are single-constructor dependent records in
  `Type(1)` carrying carrier + ops + the `Is…` proof, with `cases g { … }`
  projections, flattened law projections (each `claim Is…(…) since X.is_X;
  done`), and `operator` declarations. Mirror this for `Field`, `VectorSpace`,
  and `FiniteDimensionalVectorSpace`.
- **The scalar-field predicate.** `IsField(carrier, add, zero, negate, multiply,
  one)` (`Algebra/field.math`) = `IsCommutativeRing ∧ zero ≠ one ∧ ∀ x ≠ 0. ∃ y.
  x·y = 1`. The inverse is **existential**, not a function (Stage 0.2). There is
  **no bundled `Field` record yet** — Stage A creates it.
- **Generic finite aggregation is in flight.** `docs/PLAN_GENERIC_AGGREGATION.md`
  introduces `Algebra.indexedAggregate(A, op, e, s, n)` with `bigSum`/`bigProduct`,
  backed by the `List.product` fold (`Lists/list.math`) and its
  permutation-invariance (`Lists/permutation.math`). **Linear combinations are
  `bigSum` over the vector abelian group**, so Stage D is downstream of that
  layer's Stage 1. Coordinate; do not roll a second fold.
- **Unique choice is already here.** `Logic.the` (definite description) is the
  *unique*-existence sibling of the choice axiom we are preparing for; the global
  AC axiom, if ever added, is literally `Logic.the` with the uniqueness
  requirement dropped. `Quotient.*` is available if a `Cardinal` type or the
  quotient route to rank–nullity is ever wanted.

## Axiom-of-choice architecture (prepare for AC without adopting it)

Goal: every choice-needing theorem is proven *today* as an honest conditional,
so "turning AC on" is later a one-axiom, purely additive change that invalidates
nothing.

- **`Logic/choice.math` — the gate.** Define choice as a `Proposition`
  (choice-function form):
  `AxiomOfChoice := ∀ (I : Type(0)) (A : I → Type(0)) (R : ∀ i. A(i) → Proposition).
  (∀ i. ∃ x. R(i, x)) → ∃ (f : ∀ i. A(i)). ∀ i. R(i, f(i))`.
  Prove, once and conditionally, the standard equivalences
  `AxiomOfChoice → Zorn` and `→ WellOrdering` (real but standard work). Keep it
  `Type(0)`-level for now; note that a universe-polymorphic restatement may be
  wanted when the algebra cluster (maximal ideals, algebraic closures) arrives.
  This file is **general infrastructure**, not linear-algebra-specific; LA is
  just its first customer.
- **Thread, never adopt.** A theorem that genuinely needs choice takes an
  explicit `(choice : AxiomOfChoice)` parameter and discharges its existentials
  through it (or through the derived `Zorn`). Theorems without the parameter are
  verifiably choice-free. Do **not** write `axiom Logic.choice`.
- **Confine choice to `Proposition` positions.** Use a threaded `choice` only to
  inhabit `Proposition`s, never to construct `Type`-level data you then compute
  on. The design already respects this: basis *existence* is a `∃` (a Prop), and
  the finite-dimensional bundle carries an *explicitly constructed* basis, never
  one pulled from choice. This keeps the eventual non-reducing axiom
  computationally irrelevant.
- **"Turn it on" later (do not write yet).** A future one-line
  `axiom Logic.choice : AxiomOfChoice` plus a thin file of unconditional
  restatements (feeding the axiom to discharge each `(choice : …)` hypothesis).
  Monotone and additive. We may also choose to leave everything conditional
  forever.

## Stage 0 — decisions to settle before writing structure

1. **Bundle a `Field`.** `Algebra/field_bundle.math`: a `Field` record =
   `CommutativeRing` + `zero ≠ one` + the inverse witness, mirroring
   `CommutativeRing.make`. `VectorSpace` is indexed by a `Field` so scalar
   multiplication recovers the scalar field from the operand type (the implicit
   recovery `RingModulo` uses for its modulus). Universe note: `Field : Type(1)`,
   and a `VectorSpace` carrying a `Field` *value* + a `Type(0)` carrier should
   still land in `Type(1)` — confirm before building on it.
2. **Reciprocal as a function.** The exchange step divides by a nonzero scalar,
   but `IsField` only gives `∃ y. x·y = 1`. The field inverse is **unique**, so
   derive a reciprocal *function* via `Logic.the` over that unique existence —
   stays inside LEM + unique choice, adds no axiom. Add `Field.reciprocal`
   (nonzero arg) and its characterizing lemma. Reach for nothing stronger than
   description here.
3. **Two structure layers, named distinctly.** The general `VectorSpace`
   (Stage B) is unrestricted. `FiniteDimensionalVectorSpace` (Stage 0.3 bundle)
   is a *separate, stronger* record layered over it — like `CommutativeRing` over
   `Ring` — additionally carrying `dimension : Natural`, a
   `basis : NaturalsBelow(dimension) → carrier`, and its `IsBasis` proof. Only
   this layer has a `dimension`; a bare `VectorSpace` has none (and shouldn't).
   Also prove the unbundled existence theorem "finitely generated ⟹ has a finite
   basis" (Stage E) — choice-free, keeps the bundled and unbundled views in sync.
4. **Linear-combination index shape.** `indexedAggregate` folds `s : Natural → A`
   over the first `n`. Pick one bridge to `NaturalsBelow`/`I`-indexed families and
   use it everywhere; record it in the aggregation plan so it is shared.

## Build order (each stage ends green under `make -j 16 library`)

- **Stage A — `Field` bundle + reciprocal.** Per Stage 0.1–0.2. Instances: ℝ, ℚ,
  a `FiniteField`. Flattened law projections + `Field.reciprocal` and
  `x ≠ 0 → x · reciprocal(x) = 1`.
- **Stage B — `VectorSpace` over a `Field` (general, unrestricted).**
  `Algebra/vector_space.math`: `IsVectorSpace(field, carrier, add, zero, negate,
  scale)` (abelian group on vectors + the four scalar-action laws), then the
  bundled `VectorSpace` record. Instances: the **standard space `Fⁿ`** as
  `NaturalsBelow(n) → F` (also the first real `NaturalsBelow`-indexed object),
  and `F` over itself. A `scale` operator with a symbol distinct from `·`.
- **Stage C — subspaces and linear maps.** `Subspace` (carrier predicate closed
  under `add`/`scale`, plus the induced `VectorSpace`), `LinearMap` (preserves
  `add` and `scale`; reuse the `Algebra/group_homomorphism.math` idiom), and
  `kernel`/`image` as subspaces.
- **Stage D — span, independence, finite generation; index-generic `IsBasis`.**
  Linear combinations via `bigSum` over the vector group (gated on
  `PLAN_GENERIC_AGGREGATION` Stage 1). Define over an **arbitrary index type
  `I`** (so infinite bases are first-class), with finiteness living in the
  combinations, not the basis:
  - `Spans(f : I → V) := ∀ v. ∃ k, ∃ (σ : NaturalsBelow(k) → I), ∃ c.
    v = bigSum(i ↦ scale(c(i), f(σ(i))))`.
  - `LinearlyIndependent(f : I → V) :=` for every **injective**
    `σ : NaturalsBelow(k) → I` and coefficients `c`,
    `bigSum(i ↦ scale(c(i), f(σ(i)))) = zero → ∀ i. c(i) = zero`.
  - `IsBasis(f) := LinearlyIndependent(f) ∧ Spans(f)`.
  Injective `NaturalsBelow(k) → I` selections keep this agnostic to decidable
  equality on `I` and reuse the `bigSum`/`NaturalsBelow` toolkit. `I = Natural`
  gives infinite bases; `I = NaturalsBelow(n)` is the finite case (identity
  selection).
- **Stage E — basis existence (finite) + Steinitz + `F[x]`.** `FinitelyGenerated`;
  the **exchange lemma** (independent ≤ spanning, swapping one vector at a time —
  where `Field.reciprocal` is used); **finitely generated ⟹ has a finite basis**
  by pruning a finite spanning set (choice-free). Define
  `FiniteDimensional(V) := ∃ n, ∃ (b : NaturalsBelow(n) → carrier), IsBasis(b)`.
  Worked **infinite-dimensional instance**: `F[x]` with `{xⁿ}` as a `Natural`-indexed
  basis — independence (a nonzero polynomial has a nonzero coefficient) and
  spanning (every polynomial is a finite combination of monomials) are both
  direct and choice-free. *Check the existing `Polynomial` representation first*:
  if polynomials are finite coefficient lists / finite support, spanning is
  near-definitional.
- **Stage F — dimension.** Define the **general relation**
  `SameDimension(V, W) := (a basis of V) Equinumerous (a basis of W)` — no
  `Cardinal` type needed. Then split invariance on choice:
  - *Finite-dimensional invariance (choice-free).* From the exchange lemma, any
    two `NaturalsBelow`-indexed bases of a fixed space are equinumerous, hence
    equal `HasSize` via the `Set/finite` congruences. Gives
    `dimension : FiniteDimensionalVectorSpace → Natural` and well-definedness.
    **This is the transport crux** — the size-equality is a propositional `n = m`
    you transport bundled data along; record how heavy it is.
  - *General invariance (AC-gated).* "All bases of an arbitrary `V` are
    equinumerous" is **not** a ZF theorem (Läuchli-style models give a space with
    bases of different cardinalities); the standard proof leaks choice in the
    cardinal arithmetic `κ·ℵ₀ = κ` and the uniform enumeration of finite
    supports. State it in `Algebra/dimension_general.math` threading
    `(choice : AxiomOfChoice)`. Note the free win: **countable-dimensional spaces
    (e.g. `F[x]`) get invariance choice-free** because the whole space is
    well-orderable — so `F[x]`'s basis is provably `Equinumerous(_, Natural)`
    (choice-free), and any basis is provably infinite (choice-free); only
    invariance for *non-well-orderable* spaces (Hamel basis of ℝ over ℚ) needs
    `choice`.
- **Stage G — rank–nullity (headline #1).** Finite-dimensional, choice-free.
  Route: extend a basis of `ker T` to a basis of `V` (Stage E exchange/extension);
  the `T`-images of the extension vectors form a basis of `im T`; count. Avoids
  `Quotient`. (Alternative: `V/ker T ≅ im T` via `Quotient` — also a fine probe;
  pick one, note why.)
- **Stage H — determinants (headline #2).** Matrices as `NaturalsBelow(m) →
  NaturalsBelow(n) → F`; matrix multiply via `bigSum`. Determinant as the signed
  sum over permutations of `NaturalsBelow(n)`. **Prerequisite to confirm first
  (Stage H0):** `Lists/permutation.math` has permutations and product-invariance,
  but the **sign / parity** of a permutation may be missing — if so, build it
  (inversions, or parity-of-transposition-count well-definedness). Then
  `det(AB) = det(A)·det(B)`. This is the Sₙ-flavored dependent-index probe,
  complementary to F/G's transport-heavy one.

## Choice-profile guardrails

- **No global axioms.** Everything is provable from the current base
  (LEM + unique choice/description + propext + quotients), with choice-needing
  results threading `(choice : AxiomOfChoice)` (above). If any step seems to want
  more than that hypothesis provides, stop and flag it — a finding, not a license.
- **Adopting AC stays safe.** Because you are already classical, AC adds
  choice-strength only (Diaconescu's LEM is already yours), and an axiom is
  logically monotone — it can only add theorems. The two real risks,
  computational opacity and silent erosion of the choice-free core, are both
  handled by threading + the "choice only in `Proposition` positions" rule: a
  proof can use choice only if it visibly takes the hypothesis, so the auto-prover
  cannot silently declassify a choice-free result.
- **Finite-dimensional / countable layers stay unconditional.** No `(choice : …)`
  parameter on anything finite-dimensional, on `F[x]`, or on rank–nullity and
  determinants.

## Diagnostic checkpoints (the actual point of the branch)

At the end of Stages F, G, and H, record in `STRESS_PROBES.md`: how much of each
proof was transport/cast bookkeeping around `NaturalsBelow(n)` vs. mathematical
content; whether any `cases`-on-expression / dependent-motive limitation
(cf. the `*_bundle` projection notes) bit; and whether dimension transport needed
elaborator help. If transport is painful, the fix is an elaborator/automation
improvement (a transport/`cast`-normalization helper, `PLAN_CAST_NORMALIZATION.md`),
**not** a proof hack — per CLAUDE.md "fix bugs, never work around them."

## Pointers

- Conventions: `docs/conventions/structures-and-inference.md` (bundles, implicit
  inference, instances, operators), `docs/conventions/proof-style.md` (math-like
  phrasing; raw-CIC tells to avoid — read before writing proofs),
  `docs/conventions/algebra-tactics.md` (`ring`/`field`).
- Models to imitate: `Algebra/group_bundle.math`,
  `Algebra/commutative_ring_bundle.math` (structure),
  `Algebra/first_isomorphism.math` (a counting/structure proof of comparable
  shape), `Set/finite.math` + `Set/equinumerous.math` +
  `Set/finite_pigeonhole.math` (the counting toolkit).
- Hard dependency: `docs/PLAN_GENERIC_AGGREGATION.md` (land its Stage 1 before
  Stage D). New general-infrastructure file: `Logic/choice.math`.
- Tracking: tick rows in `docs/freek_100.md`; map new modules in `docs/library.md`.

## Suggested order

`Logic/choice.math` (define the `AxiomOfChoice` Prop + Zorn/well-ordering
equivalences — independent of the rest; the finite core does not wait on it) →
A → B → C → D (after generic aggregation Stage 1) → E (incl. `F[x]`) → F
(finite-dimensional `dimension` choice-free; general invariance AC-gated) →
**G (rank–nullity)** → H0 (permutation sign, if needed) →
**H (det multiplicativity)**. Stages A–F are the real cost; G and H are
comparatively short once basis/dimension and matrix/permutation scaffolding stands.

## Appendix — matrix layer and the matrix ↔ linear-map bridge (off the critical path)

This records the type design for matrices and their relationship to linear maps.
**Neither headline theorem depends on the bridge** (see "Scope" below), so this is
its own module and must not gate Stage G or H.

**Three distinct objects.** Conflating them is what makes the topic feel murky:

```
LinearMap(V, W)   -- abstract structure: apply : V.carrier → W.carrier + preservation proofs
Matrix(K, m, n)   -- pure data:          NaturalsBelow(m) → NaturalsBelow(n) → K.carrier
multiplyMatrixVector(M, v)
                  -- concrete induced map on STANDARD spaces:
                  --   (NaturalsBelow(n) → K.carrier) → (NaturalsBelow(m) → K.carrier)
                  --   := i ↦ bigSum(j ↦ M(i)(j) · v(j))
```

A `Matrix` is scalars in a grid — no maps, no spaces, no proofs. A `LinearMap`
between arbitrary spaces is a third thing. A matrix is the *coordinate
representation* of a map, and "coordinate" means "relative to chosen bases".

**The unifying idea: an ordered finite basis of `V` *is* an isomorphism
`V ≅ Kⁿ`.** For `b : NaturalsBelow(n) → V.carrier`:

```
combine(b)     : (NaturalsBelow(n) → K.carrier) → V.carrier
               := c ↦ bigSum(i ↦ scale(c(i), b(i)))          -- coordinates ⟼ vector
coordinates(b) : V.carrier → (NaturalsBelow(n) → K.carrier)  -- its inverse (vector ⟼ coordinates)
```

`IsBasis(b)` says *exactly* that `combine(b)` is a bijection: `Spans` is
surjectivity, `LinearlyIndependent` is injectivity. So `(b, IsBasis b)` is a
linear isomorphism `StandardSpace(K, n) ≅ V`. **This is why the basis must be an
ordered family `NaturalsBelow(n) → V`, not a set/predicate** — a set could not
index matrix rows/columns; the ordered family is what makes matrices definable.
(Confirms the Stage D representation choice pays off here.)

**The bridge**, with `n = dim V`, `m = dim W`:

```
matrixOf(bV, bW, T) : Matrix(K, m, n)
   := i j ↦ coordinates(bW)( T.apply(bV(j)) )(i)      -- column j = coords of T(bV(j))
mapOf(bV, bW, M)    : LinearMap(V, W)
   := combine(bW) ∘ multiplyMatrixVector(M) ∘ coordinates(bV)
```

These are mutually inverse. The theorem that earns its keep — **composition
becomes multiplication** — is the entire content of "matrices model linear maps",
and is what *forces* the definition of matrix multiplication:

```
matrixOf(bV, bU, compose(S, T)) = multiplyMatrix(matrixOf(bW, bU, S), matrixOf(bV, bW, T))
```

**Transport friction (expected, and worth measuring).**
`multiplyMatrix : Matrix(K,m,n) → Matrix(K,n,p) → Matrix(K,m,p)` needs the inner
`n`s equal *definitionally*. Same variable ⟹ fine; one `dim V` and one `dim W`
for proven-equidimensional spaces ⟹ you transport across
`NaturalsBelow(dim V) ≃ NaturalsBelow(dim W)`, the branch's core stress point.
**Keep matrices indexed by literal `Natural` variables as long as possible and
specialize to `dim V` only at the boundary**, so casts stay at the edges rather
than smeared through proofs. Record the cost in `STRESS_PROBES.md`.

**Scope — off the critical path for both probes.**
- `det(AB) = det(A)·det(B)` lives entirely in `Matrix(K, n, n)` — pure scalar
  grids, no abstract spaces, no `matrixOf`.
- The Stage G rank–nullity route (extend a basis of `ker T`, push forward) is
  basis-level and abstract — it never forms a matrix.

So build the matrix layer as its own modules whenever convenient —
`Algebra/matrix.math` (concrete grid, `multiplyMatrixVector`, `multiplyMatrix`,
`determinant`) and `Algebra/matrix_representation.math` (the `matrixOf`/`mapOf`
bridge and the composition-becomes-multiplication theorem) — and **do not let it
gate G or H**.

**Deep version (later, optional).** `LinearMap(V, W)` carries a pointwise vector
space structure, and then `matrixOf`/`mapOf` upgrades from a bijection to a
*vector-space* isomorphism `Hom(V, W) ≅ Matrix(K, m, n) ≅ K^(m·n)`. That is the
satisfying statement to aim the representation module at, but it is strictly more
than the two probes require.


# PLAN_KERNEL.md — kernel soundness & capabilities roadmap

Distilled (2026-05-31) from the now-removed `PLAN.md`, keeping the
forward-looking soundness/capability items. The multi-tier *hardening* that
plan tracked is **complete**; this file preserves what remains.

## What is already done (hardening — historical record)

All landed (commit refs from the old `PLAN.md`, kept for traceability):
- **Tier 1 — defensive hardening**: arity checks in δ/ι/universe reductions;
  fuel on reducers + def-eq (`defaultFuel = 10000`); input validation at the
  `addAxiom`/`addDefinition`/`addInductive` boundary + an optional
  `kernelCheckInvariants` postcondition. (a6847ba)
- **Tier 2 — strict positivity** on inductive declarations
  (`isStrictlyPositive` / `checkConstructorStrictlyPositive`). (6f6b295)
- **Tier 3 — recursor & Prop machinery**: universe-polymorphic motive in
  auto-generated recursors (8202741); restricted elimination for non-empty
  Prop inductives, large elimination only for empty ones like `False`
  (260ec8a); proof-irrelevance × impredicativity boundary audit.
- **Tier 4.1 — property-based testing**: random well-typed expression
  generator; invariants for `whnf` idempotence, `isDefEq` reflexivity/
  symmetry, type preservation under reduction. (f703fd1)

Also closed since: **type-parameterized inductives** (`List(A)`,
`Polynomial(R)`, …) work end-to-end — declaration, recursor,
structural-recursion pattern-match definitions, and `by_induction`.

## Live item — 4.2 independent re-checker (revisit trigger now MET)

The old plan postponed a separate-codepath verifier "pending real-use
experience … revisit after the kernel sees non-test use." **That condition is
now satisfied**: the kernel has checked a substantial library — Naturals
through Integers, Rationals, Reals (Cauchy), p-adics, finite fields, and ℂ,
plus the generic `RingModulo` / polynomial division / Bézout tower. The
encoding has stabilized.

This was called out as "the biggest confidence multiplier." A second,
independently-written checker that re-verifies the serialized `.mathv` terms
(the kernel already round-trips them — see `serialize.cpp`) would catch a
whole class of single-implementation bugs the property tests cannot. Now is a
defensible time to invest. Companion: **4.3 export to an external checker**
(e.g. a known proof format) — higher cost, locks in an encoding; do only if a
strong external guarantee is wanted, and after 4.2.

### 4.3 feasibility — Lean export, and the cumulativity finding (2026-06)

A subagent divergence audit of our kernel against Lean 4's theory found our
type theory is a near-match (impredicative `Prop` via `imax`; β/η/δ/ι/ζ +
definitional proof irrelevance; auto-generated recursors with Lean's
argument order; the same Prop large-elimination restriction as a strict
subset of Lean's subsingleton rule; quotients with the identical
`lift∘mk ≡ f a` rule) with **one** place we are strictly *more permissive*
than Lean: **universe cumulativity**. Our `isSubtype` (`kernel.cpp` ~1591)
accepts `Sort m <: Sort n` for `m ≤ n` and covariant-Pi codomains; Lean is
non-cumulative (kernel def-eq requires `m = n`). Terms that typecheck *via*
cumulativity would be rejected by Lean.

**Measured** with a gated probe (`MATH_PROBE_CUMULATIVITY=1`, logs every
`isSubtype` Sort acceptance where `≤` holds but the levels are not equal —
the single point all cumulativity reliance, including Pi-covariance, bottoms
out at). Clean full rebuild → **only 7 strict-cumulativity acceptances, in 3
files**:
  - `Set/basics.math` ×1 (`Type(0) <: Type(1)`): `definition Set (T :
    Type(0)) : Type(1)` over-declares — `T → Proposition` actually inhabits
    `Type(0)`. One-line tighten to `: Type(0)` (verify downstream `Set`
    users don't then need `Type(1)`).
  - `Logic/constructor_totality.math` ×5 (`Prop <: Type(0)`): constructor-
    totality lemmas for the Prop-inductives (`And`/`Or`/`Exists`/
    `LessOrEqual`) where a `Proposition` flows into a `Type(0)` slot — e.g.
    `And.constructor_totality` passes `And(A,B) : Prop` as the `Type(0)`
    carrier of `Equality.{0}(…)`. The file header already documents this
    Prop/Type universe friction. In Lean each needs explicit handling
    (`ULift`, or restructuring so no Prop sits in a Type slot).
  - `Test/implicit_args_test.math` ×1 — a test, not library content.

**Conclusion:** cumulativity dependence is tiny and localized (6 real
library sites in 2 files), not pervasive — so a Lean export is essentially
unobstructed once those are made explicit. Other translation work is
mechanical (recursor name/shape remap `Foo_recursor`→`Foo.rec`; map our
`Quotient.*` to Lean's `Quot` *primitives*, not re-axiomatized; export
`opaque` defs as transparent `def` so characterising-lemma reflexivity
proofs check; `Internal.sorry`→`sorryAx`). The probe stays in the tree
(gated, zero-cost) to re-confirm the count drops to 0 as the sites are
fixed.

## Deferred kernel capabilities (open, in rough priority)

- **Indexed inductives** (`Vec A n`, where an index varies per constructor).
  *Parameters* that stay fixed across constructors are fully supported;
  proper indices were never re-tested and may still be open. Needed for
  length-indexed / dependently-typed data; not yet required by the math.
- **Direct recursion / a termination check.** The kernel has only recursors.
  *For users this is largely moot* — the elaborator's structural-recursion
  pattern-match definitions compile to recursors and are used pervasively
  (e.g. `Natural.monus`, `decides_equality`, the polynomial coefficient
  functions). A genuine kernel-level recursive `addDefinition` would need a
  structural-recursion / sized-types / `Acc` termination check; only worth it
  if a definition can't be expressed through the recursor.
- **Mutual induction.** Multiple inductives defined together. Real but niche;
  nothing in the current math needs it.
- **Performance — reduction caching / hash-consing.** The build is fast at the
  file-cache granularity, but in-kernel reduction has no memoization. This
  era's proofs (deep polynomial convolutions, Real-via-Cauchy positivity) are
  the heaviest so far and still verify comfortably, so "fine for our scale"
  still holds — but this is the item most likely to bite first if proof terms
  keep growing (e.g. a category-theory layer). `subtree_hash.hpp` exists as
  groundwork.
- **Full formal verification** (MetaCoq-style proof of the kernel). Months of
  work; the aspirational ceiling, not a near-term task.

## Suggested order if taken up

1. **4.2 independent re-checker** — the trigger has fired and it is the
   highest confidence-per-effort item.
2. Reduction caching, *if* a future layer (category theory) makes proof terms
   large enough to feel it — measure first.
3. Indexed inductives / mutual induction only when a concrete construction
   demands them.

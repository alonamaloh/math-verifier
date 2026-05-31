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

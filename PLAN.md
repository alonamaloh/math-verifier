# Plan: hardening the kernel toward soundness

**Status: complete.** All tiers landed; remaining items deferred with
reasons recorded below. Kept as a historical record. For the current
phase of work see `PLAN_F4_bezout.md`.

Tracking document for the multi-tier hardening work. Update the status
column as items land.

## Tier 1 — Defensive hardening

| # | Item | Status | Notes |
|---|---|---|---|
| 1.1 | Arity checks in internal reductions | **done** (a6847ba) | `substituteUniverseLevels`, δ-step, ι-step. Throw / refuse-to-reduce on mismatch. |
| 1.2 | Fuel parameter on reducers / equality | **done** (a6847ba) | `int fuel = defaultFuel (10000)` default. `weakHeadNormalForm` throws on exhaustion; `isDefinitionallyEqual` / `isSubtype` return false. |
| 1.3 | Input validation at API boundary + invariant-check flag | **done** | `validateName` checks every name supplied through `addAxiom` / `addDefinition` / `addInductive` (non-empty, no control chars, no leading '@'). `kernelCheckInvariants` flag toggles a kind-soundness postcondition on every successful `inferType`. Off by default; tests flip it on for a representative pass over the kernel's main behaviours. |

## Tier 2 — Strict positivity

| # | Item | Status | Notes |
|---|---|---|---|
| 2.1 | Strict-positivity check on inductive declarations | **done** (6f6b295) | `mentionsConstant`, `isStrictlyPositive`, `checkConstructorStrictlyPositive`. Rejects `Bad : Type 0 := mkBad : (Bad → Bool) → Bad`. |

## Tier 3 — Recursor and Prop machinery

| # | Item | Status | Notes |
|---|---|---|---|
| 3.1 | Universe-polymorphic motive in auto-generated recursors | **done** (8202741) | Recursor gains a fresh `motiveLevel` universe parameter; `buildRecursorType` takes a `LevelPointer` for the motive's codomain. Proof by induction now expressible. |
| 3.2 | Restricted elimination for Prop inductives | **done** (260ec8a) | Non-empty Prop inductives have motive fixed at Prop. Empty Prop inductives (`False`) still admit large elimination. |
| 3.3 | Proof-irrelevance × impredicativity audit | **done** (just now) | Boundary tests pin down what the kernel does and doesn't equate — predicates over types are NOT equated (type lives in Type 0), functions to proofs ARE (impredicativity collapses to Prop). |

## Tier 4 — Independent verification

| # | Item | Status | Notes |
|---|---|---|---|
| 4.1 | Property-based testing | **done** (f703fd1) | Random-expression generator over the arithmetic environment. Four invariants: `whnf` idempotence, `isDefEq` reflexivity, `isDefEq` symmetry, type preservation under reduction. ~250 well-typed cases per run (of 400 trials); deterministic seed for reproducibility. All four properties hold across all sampled cases. |
| 4.2 | Independent re-checker | postponed pending real-use experience | A separate-codepath verifier would be the biggest confidence multiplier, but pre-investing while the kernel is still evolving risks invalidating duplicated work in the alternative implementation. Revisit after the kernel sees non-test use. |
| 4.3 | Export to external checker | postponed (likely too hard right now) | Locks us into someone else's encoding before we know what we want to encode. Revisit if/when we want a billion-dollar guarantee. |

## Items deliberately deferred

- **Inductive parameters: NOW SUPPORTED (verified 2026-05-29).** Type-parameterized inductives like `MyList (A : Type(0))` work end to end — declaration, recursor, structural-recursion pattern-match definitions (`append`), and `by_induction` proofs (with qualified `case MyList.cons(a, rest):` labels) all verify. So `List(A)`, `Polynomial(R)`, etc. are expressible today; this item is closed. (Indices proper — `Vec A n` where the index varies per constructor — were not re-tested and may still be open; parameters that stay fixed across constructors are fine.)
- **Direct recursion in `addDefinition`.** Currently we don't allow it; recursion happens through recursors. Would need a termination check (structural recursion / sized types / `Acc`).
- **Mutual induction.** Multiple inductives defined together. Real but niche.
- **Performance.** No hash-consing, no reduction caching. Fine for our scale.
- **Full formal verification.** A MetaCoq-style proof of the kernel. Months of work.

## Suggested resume order

If picked up mid-session: complete Tier 1 first, then 2.1, then 3.1 → 3.2 → 3.3,
then 4.1. Each item is small enough to land in isolation; commits should be one
item per commit so the test suite grows alongside.

After Tier 1 + 2.1 + 3.1 + 4.1, I'd describe the kernel as "meaningfully
hardened" — the magic-string sentinels are gone, the most obvious soundness
gap (positivity) is closed, the recursor is properly polymorphic in the
motive, and property tests are guarding against regressions in zones the
hand-written tests don't cover. After 4.2 it gains a second pair of eyes.

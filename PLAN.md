# Plan: hardening the kernel toward soundness

Tracking document for the multi-tier hardening work. Update the status
column as items land.

## Tier 1 — Defensive hardening

| # | Item | Status | Notes |
|---|---|---|---|
| 1.1 | Arity checks in internal reductions | **done** (a6847ba) | `substituteUniverseLevels`, δ-step, ι-step. Throw / refuse-to-reduce on mismatch. |
| 1.2 | Fuel parameter on reducers / equality | **done** (a6847ba) | `int fuel = defaultFuel (10000)` default. `weakHeadNormalForm` throws on exhaustion; `isDefinitionallyEqual` / `isSubtype` return false. |
| 1.3 | Input validation at API boundary | deferred (low priority) | Origin-tag fix already closes the load-bearing case. |

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
| 4.1 | Property-based testing | not started | Small random-expression generator. Properties: `whnf` idempotence, `isDefEq` reflexivity/symmetry, type preservation under reduction. Failures get added back as regression tests. |
| 4.2 | Independent re-checker | not started | Separate file (`verifier.cpp`) with a deliberately different implementation: naive named binders, exhaustive substitution. Run after every successful `inferType` and assert agreement. Single biggest confidence multiplier remaining. |
| 4.3 | Export to external checker | not started | Serialise proof terms in a portable format readable by MetaCoq / Dedukti / equivalent. Cross-verify our claims against a system we didn't write. |

## Items deliberately deferred

- **Inductive parameters and indices.** `List A`, `Vec A n` aren't expressible yet. Substantial work (~500 LOC), affects the recursor builder, no urgent soundness implication at the current expressiveness level.
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

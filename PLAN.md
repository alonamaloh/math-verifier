# Plan: hardening the kernel toward soundness

Tracking document for the multi-tier hardening work. Update the status
column as items land.

## Tier 1 — Defensive hardening

| # | Item | Status | Notes |
|---|---|---|---|
| 1.1 | Arity checks in internal reductions | in progress | `substituteUniverseLevels`, δ-step in `weakHeadNormalForm`, ι-step constructor/recursor match. Throw on mismatch instead of indexing out of bounds. |
| 1.2 | Fuel parameter on reducers / equality | not started | Add `int fuel = 10000` default to `weakHeadNormalForm`, `isDefinitionallyEqual`, `isSubtype`. Decrement on each loop iteration and recursive call; throw or conservatively return false on exhaustion. |
| 1.3 | Input validation at API boundary | deferred (low priority) | Origin-tag fix already closes the load-bearing case. Could still add name-validation in `addAxiom`/`addDefinition`/`addInductive` as defense in depth. |

## Tier 2 — Strict positivity

| # | Item | Status | Notes |
|---|---|---|---|
| 2.1 | Strict-positivity check on inductive declarations | not started | In `addInductive`, for each constructor's argument types, verify the inductive name appears only in strictly-positive positions. Helpers: `mentionsConstant(expr, name)` and `isStrictlyPositive(expr, name)`. Reject `Bad : Type 0 := mkBad : (Bad → Bool) → Bad`. |

## Tier 3 — Recursor and Prop machinery

| # | Item | Status | Notes |
|---|---|---|---|
| 3.1 | Universe-polymorphic motive in auto-generated recursors | not started | Recursor declarations gain one extra universe parameter (call it `motiveLevel`). `buildRecursorType` uses `Sort (LevelParam motiveLevel)` for the motive's codomain. ι-step adds prefix-equality check on the universe args (constructor's args must match the inductive-prefix of the recursor's). |
| 3.2 | Restricted elimination for Prop inductives | not started | When the inductive's kind reduces to `Sort 0` (Prop), the auto-generated recursor must force the motive to land in Prop too — except for singleton inductives (zero or one constructor with all args in Prop). Implement after 3.1. |
| 3.3 | Proof-irrelevance × impredicativity audit | not started | Enumerate the cases where proof irrelevance fires. Add boundary tests at each (predicates vs proofs, η-expanded vs not, etc.). No new code expected — just analysis and tests. |

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

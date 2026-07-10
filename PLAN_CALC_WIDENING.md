# PLAN_CALC_WIDENING.md — honest `-`/`/` on ℕ + type-widening `calc` chains

Sits beside `PLAN_COERCIONS.md` and `PLAN_NATURAL_SEALING.md`. Written as a
design for a **dedicated future implementation session** (not started yet). The
Status ledger below is authoritative — read/update it each session.

## Status ledger

| Stage | Workstream | Status | Record |
|-------|------------|--------|--------|
| 0 | Honest `-`/`/` operators + `_preserves` prereqs | **DONE** (2026-07-10) | §A landed: `Integer/natural_subtraction.math` (ℕ`-`→ℤ + unary `-`→ℤ + the `subtract_from_difference` boundary lemma), `Rational/natural_division.math` (ℕ`/`→ℚ + `Rational.from_natural.nonzero_preserves`); the old floor division was renamed `Natural.floor_divide` to free the honest name. §B was already complete (ℕ→ℤ `_preserves` landed earlier; `make audit-coercions` clean on all three edges). Tests: `Test/honest_natural_arithmetic_test.math`. Unary `+` skipped (low value, per plan). |
| 1 | Carrier-raising `calc` fold | **DONE** (2026-07-10) | §C landed: `liftRelationProofAcrossCoercions` (statements.cpp, the §B relation companion of `applyCoercionChain`) + `raiseCarrier` in `elaborateCalc`'s pass 1 (lift recorded endpoints raw-cast + step proofs, clear/re-resolve relation names, carrier = running max). Also added the missing `Integer.LessThan.transitive_left/right`. Tests: `Test/calc_widening_test.math` (headline `a = b = c = d−1 < e` chain, ≤/< lifts, 2-edge ℕ→ℚ raise, triangular `n(n+1)/2` in ℚ). Full library+tests+error-tests green. Residual friction (pre-existing, noted for follow-up): `ring`/`field` don't cast-push operands (`cast(T*2)` ≠ atom `cast(T)*2`), and ℚ `field` needs the nonzero hypothesis in `¬(t = Rational.zero)` shape. |
| 2 | Data-driven relation registry + `∈`/preorder unification | **deferred** | §D: replace the hard-coded composition branch + merge `elaborateCalcPreorder` + add `∈` into one fold + two tables. The "small language" endgame. A separate, later session. |

**This session targets Stage 0 + Stage 1** (owner decision, 2026-07-10). Stage 2
is an explicit follow-on — do not start it in the same session.

---

## Context

We kept "bending over backwards" to avoid `-` and `/` between naturals — reindexing
`2n−1` to `2k+1`, using `Natural.monus` (an unfamiliar word), clearing denominators to
dodge `n(n+1)/2`. The owner's objection: this is unmathematical, and truncated
`4 − 5 = 0` is a proof-assistant convention, not real mathematics; a `-` that silently
truncates is *worse* than an honest `monus` because it lies.

Conclusion reached in discussion: **operations should return their result in the
smallest closure where they are total and honest.** So on ℕ:
- `a - b : Integer`  (total; `4 − 5 = −1`, no lie, no proof obligation)
- `a / b : Rational` (obligation `b ≠ 0`, discharged like every other `/`)
- unary `-` : Integer, (and, for uniformity, unary `+` : Integer)

This is deliberately *uncreative* — it is the ordinary mathematical semantics — and its
key virtue over a checked/partial ℕ subtraction is that **it hands `ring`/`field` back**:
once you are in ℤ/ℚ, `-`/`/` are genuine ring/field operations (a checked ℕ `-` is not a
semiring op, so `ring` would treat it as an opaque atom, exactly as it does `^`). It also
avoids the totality trap: a checked `-` makes `λk. 2k−1` ill-typed at `k=0`.

The consequence is that arithmetic **changes type mid-expression and mid-`calc`-chain**
(`a = b = c = d − 1 < e` starts in ℕ and finishes in ℤ). So the second half of this design
is a `calc` engine that lets a chain **widen** through the coercion tower ℕ ↪ ℤ ↪ ℚ ↪ ℝ ↪ ℂ.

### The right mental model (owner's, refined)

Not "compute one join type for the whole chain" — that framing collapses on heterogeneous
relations (`a = b ∈ S = X`, `a ∣ b = c`) where there is no common type to join to. Instead a
**left fold**: the accumulator is a *proof* of one relation `L R M` (left endpoint → current
middle). Each step `M′ R′ N` is folded in by **reconcile-then-combine**:

1. **Reconcile the middle.** If the step's left operand `M′` is the coercion-lift of the
   accumulator's right operand `M` (because `N` forced a higher type), lift the *whole
   accumulator proof* up that tower edge via a relation-preservation lemma, so its right
   endpoint becomes `M′`. Coercions only go up ⇒ the accumulator's type is a running maximum
   ⇒ never down-cast, no backtracking.
2. **Combine.** Apply a relation-composition rule to `(L R M′)·(M′ R′ N) → (L R″ N)`.

Two extensible registries fall out: **relation-composition** (`= · ≤ → ≤`, `≤ · < → <`,
`= · ∈ → ∈`, `∈ · = → ∈`, `∣ · ∣ → ∣`, …) and **coercion-preservation** (which relation
survives which tower edge; `=` via congruence always; `≤`/`<` via the `_preserves` lemmas;
`∣` survives ℕ→ℤ but **not** ℤ→ℚ). A missing entry is a *local, legible* error, never a
silent wrong answer. Coverage = registry coverage.

North star (the owner's "small language" framing — Stroustrup: *"within C++ there is a much
smaller and cleaner language struggling to get out"*): the endgame **replaces** the current
hard-coded 4-way composition branch *and* the separate preorder path *and* would absorb `∈`
into **one** data-driven fold + two tables. Fewer constructs, more expressible.

---

## What already exists (reuse, do not rebuild)

Grounded by exploration of `src/`:

- **The fold is already there.** `Elaborator::elaborateCalc` (`src/elaborator/calc.cpp:234-1584`)
  elaborates each step (pass 1, ~431-1203) then **left-folds** with an accumulator proof
  `running` + a `runningStrictness` enum (pass 2, 1404-1583). Backward `≥`/`>` chains are
  normalized to forward. `=` steps are upgraded to `≤` via `upgradeEqualityToLessOrEqual`
  (1339-1363, using `Equality.transport_proposition`).
- **Per-step coercion to the carrier already happens** — `combineOperands` → `applyCoercionChain`
  → `castPushToLeaves` at `calc.cpp:296-307` (leading term) and `456-474` (each RHS). **But the
  carrier is fixed by step 0 and only ever pulls a *lower* RHS up to it; it cannot rise when a
  step needs a *higher* type.** ← this is the core gap.
- **Relation-name resolution** `resolveLeqNames`/`resolveLtNames` (`calc.cpp:336-379`) via
  `Environment::lookupOperator` (`src/kernel/kernel.hpp:252-270`) → `R.reflexive`,
  `R.transitive`, `R.transitive_left/right`, `R.weaken`. Composition is the hard-coded 4-way
  branch at `calc.cpp:1505-1582`.
- **Preorder chains** (`∣`/`⊆`/`≈`) are a *separate* function `elaborateCalcPreorder`
  (`calc.cpp:9-232`) that does **no** coercion reconciliation. `∈` is **not** in the calc
  grammar (`CalcRelation` = {=,≤,<,≥,>}; `src/syntax/surface.hpp:389-395`).
- **Coercion tower + join** are built (PLAN_COERCIONS Tier 1): `combineOperands`
  (`src/elaborator/statements.cpp:647-710`), `applyCoercionChain` (638-645), the
  `coercionRegistry` (`kernel.hpp:162-168`) with edges ℕ→ℤ→ℚ→ℝ→ℂ transitively closed.
- **Operator return type = dispatch fn's codomain, no extra logic** (`elaborateOperatorDeclaration`,
  `src/elaborator/statements.cpp:385-467` — it validates *operands only*). **Precedent:**
  `operator (/) on (Integer, Integer) := Integer.divide` where
  `Integer.divide (a b : Integer)(h : b ≠ 0) : Rational` (`library/Rational/basics.math:165-170`).
- **The `/` nonzero obligation is already auto-discharged**: `dischargeTrailingSideConditions`
  (`src/elaborator/desugar_equality.cpp:737-792`) → auto-prover / `tryProveNonzero` /
  `tryProvePositive` (597-735), with a Natural base case `Natural.zero_lt_of_one_le` (659-682)
  and `automatic` lemmas `Real.two_is_nonzero`, `nonzero_of_positive`, etc.
- **Preservation-lemma slots + an audit tool**: convention `<coercionFn>.<Rel>_preserves`
  (source⇒target) / `_reflects` (target⇒source). `make audit-coercions`
  (`MATH_AUDIT_COERCION_PACKETS`, `src/elaborator/driver.cpp:274-305`) checks 11 canonical slots
  per edge. Congruence for `=` is automatic (generic `Equality.congruence`).

---

## The changes

### A. Operator definitions (small, additive — ℕ has no `-`/`/` today, so nothing breaks)

New library definitions + `operator` registrations (pattern copied from `Integer.divide`):
- `Natural.subtract (a b : Natural) : Integer := (a : Integer) - (b : Integer)`, then
  `operator (-) on (Natural, Natural) := Natural.subtract`.
- `Natural.divide (a b : Natural) (bNonzero : b ≠ 0) : Rational := (a : Rational) / (b : Rational)`
  (the inner `/` gets `(b:ℚ) ≠ 0` from `bNonzero` via `to_rational` zero-preservation), then
  `operator (/) on (Natural, Natural) := Natural.divide`.
- Unary `-` on ℕ: unary minus dispatches to `<T>.negate` (`src/elaborator/dispatch.cpp:1856-1864`).
  Define `Natural.negate (a : Natural) : Integer := Integer.negate((a : Integer))` so `-n : ℤ`.
  (Unary `+` : add a prefix `+` to the grammar only if the uniform rule is worth it —
  `Parser::parseUnary` `src/syntax/parser.cpp:3305-3319` currently has no unary `+`; low value.)
- Home for these: a small new file (e.g. `library/Natural/honest_arithmetic.math`) — note the
  layering: these definitions live *above* ℤ/ℚ in the import graph, so they belong wherever ℚ is
  already in scope, NOT in the foundational `Natural/` modules (where `a - b` should still not
  resolve). Confirm placement during implementation. Interacts with — but is independent of —
  `PLAN_NATURAL_SEALING.md`.

*Consequence to watch:* an expression that subtracts/divides naturals is now ℤ/ℚ-typed and
cannot be fed back into a ℕ-expecting position without a down-cast (honest — you left ℕ). Fold
term functions like `λk. 2k − 1 : ℕ → ℤ`; a fold summing them lands in ℤ. That is fine and
mathematician-faithful; the ellipsis/`sum` fold machinery is polymorphic over the carrier monoid.

### B. Prerequisite — complete the `_preserves` slots (for lifting *up*)

The fold lifts the accumulator **up** (source⇒target), so it needs `_preserves`, but some edges
only ship `_reflects` (target⇒source). Notably **ℕ→ℤ has `LessOrEqual_reflects`/`LessThan_reflects`
but no `_preserves`** (`library/Integer/order.math:138,156`). Run `make audit-coercions`, then add
the missing `<coercionFn>.{LessOrEqual,LessThan}_preserves` per edge (ℕ→ℤ, and verify ℤ→ℚ, ℚ→ℝ —
ℚ→ℝ already has them at `library/Real/embedding_order.math:44,62`). `=` needs nothing (congruence).
Also decide: lift multi-edge jumps by composing single-edge `_preserves`, or by the pre-chained
composites (`Real.from_natural.LessOrEqual_preserves`). Recommend: a tiny helper that walks the
`coercionRegistry` chain applying single-edge `_preserves` (mirrors `applyCoercionChain` but for
relation proofs), so no per-pair composite lemmas are needed.

### C. `calc` fold — let the carrier rise (the heart of the change)

In `elaborateCalc`'s fold (`calc.cpp`), make the carrier a *running* value, not a fixed one:
- When a step's endpoint type is **higher** than the current carrier (`combineOperands` reports
  the endpoint as the join and asks to coerce the *carrier* side up), **raise the carrier**: lift
  the accumulator proof `running` — and the fixed left endpoint + endpoint kernels used by later
  transitivity — up the tower via the §B relation-preservation helper, keyed on the current
  `runningStrictness` (`=`→congruence, `≤`/`<`→`_preserves`). Then re-resolve `resolveLeqNames`/
  `resolveLtNames` at the new carrier and continue.
- The existing "coerce lower RHS up to carrier" path (456-474) stays for the symmetric case.
- Net: the accumulator's carrier is a monotonic running max; each step reconciles upward.

This is a contained change to `calc.cpp` (the fold 1404-1583, the carrier setup 256-313, the
per-step reconciliation 456-474) plus the §B helper. It delivers all the arithmetic examples.

### D. (Stage 2, deferred) Unify into a data-driven relation fold

Replace the hard-coded 4-way composition branch **and** merge `elaborateCalcPreorder` into one
fold driven by a **relation-composition registry** (a `Trans`-style table: `(R, R′) → R″` + the
transitivity lemma name), and add `∈` (and any `⊆`/`≈`) as first-class relations with coercion
reconciliation. This is the "small language" endgame: one fold + two tables subsumes three code
paths. Bigger and riskier; a separate session, after Stage 1 is green.

---

## Files to modify (grounded)

- Library (Stage 0): new `library/Natural/honest_arithmetic.math` (placement TBD, above ℚ);
  add `_preserves` lemmas in `library/Integer/order.math` (and audit ℤ→ℚ in
  `library/Rational/archimedean.math`, ℚ→ℝ present in `library/Real/embedding_order.math`).
- `src/elaborator/calc.cpp` — Stage 1: carrier setup (256-313), per-step reconciliation
  (456-474), the fold + composition (1404-1583; `resolveLeqNames`/`resolveLtNames` 336-379).
  Stage 2: replace 1505-1582 with a registry; merge `elaborateCalcPreorder` (9-232).
- `src/elaborator/statements.cpp` — reuse `combineOperands`/`applyCoercionChain` (638-710); the
  §B relation-lift helper can live near them.
- `src/syntax/surface.hpp` (389-423) + `src/syntax/parser.cpp` `parseCalc` (4285-4355) — Stage 2
  only, to admit `∈` (and generalize the relation set).
- `docs/conventions/calc-and-rewrite.md` — document widening chains + the honest `-`/`/` typing.
- **Any `src/` change re-verifies the whole library** (the `.mathv` cache keys on the `kernel`
  binary): budget a full `make -j 16 library tests` per stage, always `ulimit -v` the kernel.

## Verification

1. **Micro (Stage 0):** a `Test/` file asserting `(2 - 3 : Integer) = -1`, `(1 / 2 : Rational)`
   type/value, `-(n:ℕ) : Integer`; `make audit-coercions` prints no "missing" for ℕ→ℤ/ℤ→ℚ/ℚ→ℝ
   `{LessOrEqual,LessThan}_preserves`.
2. **Widening chains (Stage 1):** `Test/` theorems — `a = b = c = d - 1 < e` (ℕ vars) closing at
   `(a:ℤ) < (e:ℤ)`; sum-of-odds in honest `2·n − 1` form; a `n(n+1)/2` triangular identity in ℚ.
   Confirm the manual-cast calc steps in `library/Real/harmonic_series.math:101` /
   `library/Real/density.math:119` still elaborate (regression), and ideally simplify.
3. **Heterogeneous (Stage 2, later):** `a = b ∈ S = X` ⟶ `a ∈ X`; `a ∣ b = c` ⟶ `a ∣ c`; a
   `∣` step meeting a `/`-widening must produce a clear "cannot lift `∣` across ℤ↪ℚ" error.
4. **Global:** full `make -j 16 library tests` green after every stage; existing calc regression
   tests (`library/Test/*calc*`, `series_relation_test`, `fold_binder_test`) unchanged.

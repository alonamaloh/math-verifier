# PLAN: Fingerprint-guided auto-prover (kill the blind ring searches)

Status: **Phase 0 + Phase 1 + Phase 2 DONE** (committed 2026-06-05). The
abstract-ring `ring` normaliser is complete: subtract-unfold → negation-push
→ distribute → identity-elim → AC-normalise → inverse-cancellation, all
proof-constructing over an abstract `Ring.carrier(s)`. Closes distributivity,
0/1 identities, and telescoping/inverse-cancellation goals; `Ring.add_four_
swap`, `Ring.difference_telescope`, `Ring.difference_add_distribute`
simplified to `:= ring`. The two follow-ups are DONE too: double-negation
(`Ring.negate_negate` + a `ringPushNegation` case) and sign-extraction
(`Ring.negate_multiply_left/right` + `ringExtractSigns`/`ringCombineProduct
Signs`/`ringApplyNegate`); `Ring.negate_difference` and `Ring.difference_
multiply_split` are now `:= ring` — every difference lemma in
`ring_difference.math` is a one-liner. **NEXT = Phase 3** (model-eval
fingerprint), then Phase 4 (commutativity witness in the ideal tower), then
clean the 9 concrete-carrier warn sites (deferred to last by request).
Phase 0
safety net (effort budget + expensive-step warning) is committed. Phase 1's
core win is committed: `proveAbstractRingAC` (`ring.cpp`) normalises +/·
rearrangements over an abstract `Ring.carrier(s)` and closes them directly,
**eliminating the 955,691-step worst case** (`principal_ideal_domain:153`).
It is wired additively into `tryAcRearrangement` (before `elaborateRing`), so
a non-match leaves the existing battery untouched. Approach taken vs. plan:
used **exact AC normal-form comparison** (`structurallyEqual` on the canonical
forms) rather than a hashed uint128 color — more precise, and the color is
only a perf optimisation for scale (not yet needed). The recursive-search
**gating** (§3.5b, Phase 1 step 5) was deliberately NOT done: the additive
route removed the headline thrash without the regression risk gating carries.
Remaining warn sites (9) are over concrete numeric carriers — hidden-
computation steps that want an explicit `by`, not AC rearrangements. NEXT:
Phase 2 (extend `ring`/`field` to abstract commutative rings; overlaps the
new normaliser — decide whether to unify) or address the 9 sites with `by`.

Picks up from a session that diagnosed why a handful of by-less proof steps
cost the auto-prover up to ~956,000 kernel reduction steps each. This
document is self-contained; read it cold and start at Phase 0.

Related code: `src/elaborator/{prover,calc,ring,diff_bridges,internal}.cpp/.hpp`,
`src/kernel/kernel.cpp/.hpp`. Related memory: `kernel_quirks` #17/#18/#19.

---

## 1. The problem (with measurements)

By-less calc steps (`calc … = … ` with no `by`) are closed by the
elaborator's auto-prover (`Elaborator::autoProveClaim` → `autoProveClaimTactics`,
`prover.cpp`). Over abstract / quotient algebra these steps quietly run an
**unbounded recursive search** and burn enormous kernel work for what a human
writes as one `by`.

Measured over the whole library (per outermost auto-prove call, in kernel
reduction steps; instrument: a temporary trace in the `BudgetGuard` /
`autoProveCalcStep`, plus `MATH_PROFILE_AUTOPROVER` / `MATH_TIME_TACTICS`):

- 2,283 auto-prove calls. median **145**, p90 **1.2K**, p99 **24K**, max **955,691**.
- Heavy tail: **10 sites > 50K**, 7 > 100K, 2 > 500K. Spread across the numeric
  tower (`Integer.sign`, `Rational.reciprocal_function`, `Natural.factorization`,
  `Natural.cancellation`, `PAdic.absolute_value`, …) and the algebra tower
  (`Algebra.principal_ideal_domain`).

**Root cause of the worst case** (`Algebra.principal_ideal_domain:153`, 956K steps):
the by-less step
```
calc (gInverse * x) * p + (gInverse * y) * a
   = gInverse * (x * p) + gInverse * (y * a)      -- this step
```
is **pure associativity** over an *abstract* ring `s : Ring`
(`s = PrincipalIdealDomain.ring(pid)`, carrier `Ring.carrier(s)`). The
`MATH_PROFILE_AUTOPROVER` per-claim row shows:

| tactic | ok | time |
|---|---|---|
| equalityBattery (reflexivity / diff / lemma-index / **ring**) | 0 | 11 ms |
| contextFactMatch (scans 66 candidate facts) | 0 | 207 ms |
| **contextEqualityBridge** | **1** | **16.6 s** |

So the closer is **`tryContextEqualityBridge`** (`prover.cpp:478`): it collects
every context equality — local hypotheses that are equations **plus library
lemmas matched against every `Application` subterm via `lemmaIndex_`
(`collectLibraryEqualitiesAt`)** — then for each candidate × both directions
**rewrites and recursively re-enters `autoProveClaim`**. That is a breadth ×
depth search tree; over an abstract bundle each candidate conversion is
expensive (bundle projections never reduce), so it thrashes. `symmetryFlip`
(the #2 cost overall) recurses the same way.

**Why `ring` can't save it** (empirically confirmed): `ring` (`ring.cpp`,
`elaborateRing`) is a *commutative-ring normalizer* keyed on the carrier's
**registered** structure (it builds `<carrier>.add/.multiply/...` names and
needs a commutative witness). It fires for concrete carriers (Integer/Rational/
Real) and the `CommutativeRing.carrier` operators, but **declines on the generic
`Ring.carrier(s)` projection** — even for pure associativity, and even when the
underlying ring is commutative — because the commutativity lives only in a
separate runtime fact (`IntegralDomain.commutative`), invisible to the static
tactic. Probe: `ring` fails on `(g*x)*p = g*(x*p)` over both an abstract `Ring`
*and* an abstract `CommutativeRing` when the carrier is written `Ring.carrier(…)`.

**Why "just disable the search" fails** (measured): running the whole library
with `MATH_DISABLE_CTX_EQ_BRIDGE=1` made `Natural/decide_divides.math` — *fast*
with the bridge on (~11.7K steps) — thrash for **12+ minutes**, because the step
the bridge was closing falls through to `symmetryFlip` (later in the battery,
also recursive) and the per-claim 1.2M budget doesn't catch it (cost spread over
many small claims). **Removing a blind search without a guided replacement just
relocates the thrash.**

---

## 2. What already exists in the tree (uncommitted at time of writing)

These are built and green (`make -j 16 tests` passes; library re-verifies with
no budget trips):

- **Hard effort budget** (from a prior subagent): a per-thread kernel
  reduction-step counter `kernelStepsSoFar()` (`kernel.cpp/.hpp`), snapshotted
  once per outermost auto-prove (`autoProveStepSnapshot_`); the prover's hot
  loops charge it (`autoProveSpend`) and **throw `AutoProverBudgetError`** at
  `autoProveBudgetLimit_` (default **1,200,000** steps; env `MATH_AUTOPROVE_BUDGET`,
  0 disables). The budget owner re-issues it as a clear "add `by`" error
  (`errors.cpp:throwAutoProveCalcStepBudgetExceeded`). Note: at 1.2M with a legit
  max of 956K this is only **1.25× headroom** — a backstop, not the fix.
- **Warning tier** (built this session): at the armed success return in
  `autoProveClaim` (`prover.cpp`), if a by-less step *closed* but spent
  `> MATH_AUTOPROVE_WARN` (default **50,000**) steps, emit
  `warning: <module>:<line>: expensive by-less proof step (N kernel-steps) — …
  add an explicit \`by <reason>\``. Non-fatal. Helper
  `autoProveWarnThresholdValue()` (anon namespace, `prover.cpp`). Produced a
  clean **10-site worklist** (see Appendix B).
- Pre-existing: `MATH_DISABLE_CTX_EQ_BRIDGE`, `MATH_PROFILE_AUTOPROVER`,
  `MATH_TIME_TACTICS`. And `ring`'s existing scalar fingerprint
  `evalRingMod` (mod the prime `2^64 − 59`) in `ring.cpp` —
  **this is the seed to generalize.**

Decision for Phase 0: commit the budget + warning as the safety net + visibility
layer, independent of the deeper work below.

---

## 3. The core idea: fingerprint coloring

Give every AST node a **color** (a fingerprint), computed **bottom-up**, that is
*invariant under the algebraic axioms we are allowed to use* and otherwise
*congruent*. Then:

- **Equality goal `L = R`**: if `color(L) ≠ color(R)` the cheap path declines
  (no expensive search); if equal it is a strong "these are equal — prove it
  directly" signal.
- **Congruence / multi-position goals** (`A ⊕ B = A' ⊕ B'`): child colors give
  the *correspondence* — prove `A = A'`, `B = B'` for the color-matched pairs,
  instead of blindly enumerating hypotheses and lemmas.

The color *replaces the blind search with a directed proof*, which is the only
way to remove `contextEqualityBridge`/`symmetryFlip` without regressions
(see §1).

### 3.1 How a color is computed (dispatch + congruent fallback)

Bottom-up over the term, dispatch on the head:

- **Recognized algebraic op at a recognized carrier** (e.g. `Ring.add`,
  `Ring.multiply` at `Ring.carrier(s)`): combine the children's colors per the
  op's declared axioms (see §3.2/§3.3).
- **Anything else** (arbitrary `f(args)`, bound/free variable, binder): an
  **opaque leaf** — `color = mix(hash(head_identity), color(arg₁), …)`, ordered.
  This is **congruence-respecting**: equal-colored children ⇒ equal-colored
  parent. So the coloring "sees through" non-ring context (`f(a+b)` and `f(b+a)`
  get the same color iff `a+b`, `b+a` do — which corresponds to a sound
  `Equality.congruence` step).

No top-level gating: every node gets a color; the color is only *informative*
where there is recognized algebraic structure. For a purely non-algebraic goal
the colors degrade to ordinary congruent/syntactic hashing (adds nothing, costs
nothing).

### 3.2 Combinator correctness — NEVER XOR

The combiner for a **commutative** op must be order-independent **and preserve
multiplicity**. XOR is addition in characteristic 2 (`x ⊕ x = 0`), so any subterm
of even multiplicity cancels: with XOR, `color(a+a) = color(b+b) = 0`, so
`a+a = b+b` *always* passes — fatal. Rule: **the combiner must live in large odd
characteristic.** Use a **modular sum of per-element avalanche-mixed colors**:
`color(⊕ xᵢ) = Σ mix(color(xᵢ)) (mod P)`, `P` a large odd prime (reuse
`2^64 − 59` or a 128-bit prime). The avalanche `mix` breaks the linearity that
would otherwise collide `{a,d}` with `{b,c}` when `color(a)+color(d) =
color(b)+color(c)`; residual collisions are ~`P⁻¹`, harmless for a fingerprint.
(Equivalently: when you *evaluate into a model* — §3.4 — just never pick a
characteristic-2 model.)

### 3.3 AC-normalization layer (exact, deterministic, highest ROI)

Bake associativity + (carrier-aware) commutativity + identities directly into
the color — sound *by construction*, no probability:

- **Associativity flattening**: collect the maximal connected subtree of one
  associative operator into a flat operand list, so all parenthesizations
  collapse.
- **Commutative op** (declared) → hash the operand **multiset** (avalanche-sum,
  §3.2). **Non-commutative op** → hash the operand **sequence** (ordered).
- **Identity absorption**: drop the identity element from the flattened list
  (`a+0 → a`, `a·1 → a`); `0`-annihilation (`a·0 → 0`).

**Carrier-aware axiom table** — key is `(operator-constant, carrier)`, default
**conservative = ordered/non-commutative** when unknown:
- `Ring.add` over any `Ring.carrier`: **associative + commutative** (the additive
  group of a ring is abelian — *unconditional*).
- `Ring.multiply` over `Ring.carrier`: **associative**; commutative **only** if
  the carrier is a `CommutativeRing.carrier(…)` (or a concrete commutative
  carrier: Integer/Rational/Real/IntegerMod/…).

**Key consequence (this is why AC-flatten is Phase 1, not the matrices):** the
worst measured case (`principal_ideal_domain:153`) is solved by this alone, over
a *general* `Ring`, with **no `·`-commutativity and no matrices** — because `+`
is AC and `·` is associative in *every* ring. Both summands flatten to
`·[g,x,p]` and `·[g,y,a]`; the two sides become the same `+`-multiset; the
16-second search becomes a hash compare.

### 3.4 Evaluate-into-a-model (probabilistic extension, for distributivity)

AC-flatten does **not** cover distributivity (`a·(b+c) = a·b + a·c`). For full
ring-theory power, *evaluate* the term into a model where all ring axioms hold:

- **Commutative ring** → scalars in `F_P` (`P` large odd prime) — this is exactly
  the existing `evalRingMod`, to be reused/extended.
- **General / non-commutative ring** → `M_n(F_P)` (n×n matrices over odd-char
  `F_P`). Leaves → random matrices (4 hashes per `2×2`, or one hash + 3
  avalanche-derived entries); ops → matrix `+`/`·`. Non-commutativity is honored
  (`a·b` vs `b·a` differ), so it won't wrongly suggest commutativity-only
  identities for a ring not known commutative.

This is a randomized polynomial-identity test (Schwartz–Zippel): sound reject
w.h.p., high-confidence accept. **Caveat:** `2×2` matrices satisfy the
Amitsur–Levitzki standard identity (degree 4) → small false-accept risk for
high-degree non-identities. Mitigate with a few independent random assignments,
or `n×n` for larger `n` (kills identities up to degree `2n`). Acceptance is only
a *hint*, so a rare false-accept costs proof effort, never soundness.

### 3.5 Two uses, two soundness levels (and the happy coincidence)

- **(a) Decision procedure** (the `ring` fix, extended to non-commutative):
  treating maximal non-algebraic subterms as opaque atoms, AC-normalization (and
  model evaluation) is **sound + complete for "provable from the declared axioms
  + congruence."** This is what *constructs* proofs for ring-shaped steps over
  abstract carriers — what today's `ring` can't do.
- **(b) Search guide / gate** (general prover): a **heuristic**, not an oracle —
  color *mismatch* is not a fully sound reject, because the congruent hash
  deliberately does **not** see definitional unfolding behind an opaque head
  (`f(a)` defeq `g` ⇒ different colors). Use it to prioritize/prune, and to
  **gate the blind searches**: color-certifies → run the cheap directed proof;
  color-mismatch and no `by` → decline and ask for `by`.
- **The coincidence that makes (b) principled:** the blind spot ("can't see
  equalities needing unfolding") is *exactly* the set of steps we already decided
  should carry an explicit `by` (the hidden-computation steps). So gating the
  by-less prover on the fingerprint is the behavior we want.

---

## 4. Implementation phases (by ROI / risk)

### Phase 0 — Land the safety net (low risk, immediate)
- Review the budget diff + the warning code in the working tree. `make -j 16
  kernel && make -j 16 tests`. Commit "auto-prover effort budget + expensive-step
  warning". (Optionally rebase the original subagent worktree branch
  `worktree-agent-…` away; the changes are already cherry-applied to the tree.)
- Add a regression test under `library/Test/` is **not** appropriate for a
  deliberately-failing repro; keep the `Bits.fold` repro in `scratch/` or
  document `MATH_AUTOPROVE_BUDGET=…` in the budget error.
- **Redundancy-checker synergy**: change `--check-redundant-by` so a `by` is
  flagged redundant only if removing it keeps the step **under the warn
  threshold** (cheap), not merely "still closes." Otherwise the checker tells you
  to delete the very `by`s that keep proofs fast. (Code: the redundant-`by`
  checks live near `autoProveCalcStep` in `calc.cpp`; measure
  `kernelStepsSoFar()` delta around the by-less attempt.)

### Phase 1 — AC-normalization coloring + deterministic AC normalizer (the win)
New file `src/elaborator/fingerprint.{hpp,cpp}` (or fold into `ring.cpp`):
1. `uint128 color(Expression, Context)` per §3.1–§3.3, with a memo cache keyed on
   the expression pointer/hash. Combiner = avalanche-sum (NOT XOR).
2. Axiom table `(constant, carrierClassifier) → {assoc, comm, identityElt}`;
   populate for `Ring.add/.multiply`, `CommutativeRing.*`, and concrete numeric
   carriers; conservative default. The carrier classifier inspects the operand
   type head (`Ring.carrier(...)` vs `CommutativeRing.carrier(...)` vs concrete).
3. A **proof-constructing AC normalizer**: normalize `L`, `R` to flattened
   canonical form; if equal, emit the proof via associativity/commutativity/
   identity rewrites + congruence. Works over abstract `Ring`/`CommutativeRing`
   carriers (the gap `ring` leaves).
4. Wire into `equalityBattery` (early, cheap): try the AC normalizer; if colors
   differ, return null fast (so the later recursive tactics are not even reached
   for AC-shaped goals).
5. **Gate the recursive searches**: only run `tryContextEqualityBridge` /
   `symmetryFlip` when the fingerprint does **not** already certify the goal AND
   (proposal) a `by`-ish budget is available; default to declining when no `by`
   and color says "not an axiom-equality." Re-measure `decide_divides` and the
   10-site worklist — they should close cheaply or surface as "add `by`."

### Phase 2 — Make `ring`/`field` work on abstract commutative rings
- **Increment 1 DONE** (committed 2026-06-05): surface `ring` now recognizes the
  abstract `Ring.carrier(s)` projection and routes to `proveAbstractRingAC` (the
  Phase 1 non-commutative AC normaliser). Previously `ring` keyed its fingerprint
  on non-existent `<carrier>.add/.multiply` names and wrongly declared such goals
  FALSE. Now it proves associativity / `+`-commutativity rearrangements over any
  ring and declines precisely otherwise. Multiplicative reassociation made
  optional (treat `·`-products as atoms when `Ring.multiply_associative` isn't yet
  in scope) so it works mid-bootstrap. `Ring.add_four_swap` simplified to `:= ring`.
  Unify decision: **kept Phase 1's `proveAbstractRingAC` as the single engine**;
  did NOT retrofit the v2 polynomial normaliser (its commutativity is pervasive —
  sorted monomial-signature map keys via `std::merge`/`std::sort`, `multiply_
  commutative` cited at many proof sites — too risky to parameterize).
- **Increment 2 DONE** — built route (a): extended `proveAbstractRingAC`'s engine
  into a full non-commutative ring normaliser, in committed sub-steps:
  - 2a `ringDistribute`/`expandRingProductOfSums`: products of sums → sums of
    products via `Ring.distributivity_left/right` (cross terms kept ordered).
  - 2b `ringSimplifyIdentities`: drop `0`/`1`, annihilate `·0`, `-0` (bottom-up,
    one law per node).
  - 2c `ringUnfoldSubtract` (defeq) + `ringPushNegation` (`negate_add_distribute`)
    + `ringCancelInverses` (permute pair to front via `proveProductEqualsSorted`,
    cancel with `add_negate_left/right`, drop `0` with `zero_add`).
  Pipeline: unfold-subtract → push-negation → distribute → simplify-identities →
  AC-normalise → cancel-inverses, each stage proof-chained; every stage gated on
  its laws being in scope (graceful mid-bootstrap). `buildBinaryOpCongruence` /
  `buildLeftAssocFoldLambda` are the shared proof helpers.
  - **Not done (small follow-ups):** double-negation `negate(negate x)=x`
    (`Group.inverse_involution`, needs the additive-group projection) and
    sign-extraction `negate(x)·y = negate(x·y)` (would close
    `difference_multiply_split`). Full COMMUTATIVE power over a *secretly*
    commutative `Ring.carrier(s)` still needs Phase 4 (source the witness).

### Phase 3 — Evaluate-into-a-model fingerprint (distributivity, non-commutative)
- Generalize `evalRingMod` (scalar, commutative) and add `M_n(F_P)` evaluation
  (§3.4): leaf→matrix hashing, matrix arithmetic mod odd `P`, independent
  assignments for confidence. Use as the stronger PIT where AC-flatten is
  insufficient (distributivity), primarily as a **guide** (§3.5b) since it's
  probabilistic; the constructed proof for distributivity steps comes from the
  ring normalizer or an explicit `by`.

### Phase 4 — Expose `CommutativeRing` in the factorization/ideal tower
- The ideal/PID/factorization layer works over `Ring.carrier(s : Ring)` though it
  is *entirely commutative* (`IntegralDomain` = commutative ring + …). To let the
  normalizer fire there, either (a) add `PrincipalIdealDomain.commutativeRing` /
  work over `CommutativeRing.carrier`, or (b) restate `Ring.IsIdeal`/
  `GeneratesIdeal`/`pairIdeal`/PID over `CommutativeRing` (the `Ring`-level
  generality — left ideals in possibly non-commutative rings, e.g. `M_n`, the
  canonical non-commutative example — is unused). Then the 10-site algebra
  rearrangements close via cheap `ring`.

---

## 5. Soundness checklist
- Every evaluation model is **odd characteristic** (never GF(2)/XOR).
- The axiom table is **conservative**: unknown `(op, carrier)` ⇒ ordered /
  non-commutative (lose matches, never assert a false one).
- Coloring is **congruence-respecting** (equal children ⇒ equal parent).
- Decision-procedure use (Phase 1/2): equal color ⇒ a *constructible* proof from
  declared axioms (don't trust the color — build and type-check the term).
- Guide use (Phase 3): treat as heuristic; never hard-reject a step purely on
  color mismatch unless we are explicitly enforcing "needs `by`."

## 6. Open decisions (resolve next session)
- Color width (64 vs 128 bit) and modulus (reuse `2^64−59`?).
- Matrix size `n` vs the Amitsur–Levitzki false-accept tradeoff; how many
  independent assignments.
- Unify the Phase-1 AC normalizer with the Phase-2 `ring` extension, or keep
  separate.
- How hard to gate the recursive searches (decline-by-default when no `by`, vs
  tiny budget). Re-run the `MATH_DISABLE_CTX_EQ_BRIDGE` experiment *with* the
  fingerprint normalizer in place to confirm no `decide_divides`-style regression.
- Warn threshold (50K now) and whether to eventually turn the warn into a hard
  decline.

## 7. Test plan
- The 10-site worklist (Appendix B): each should close cheaply (cost ≪ 50K) or
  surface a clean "add `by`".
- `Natural/decide_divides.math`: must NOT regress (the canary).
- `library/` + `make tests` fully green; `MATH_AUTOPROVE_WARN` count → 0 (or only
  intentional `by`-less computations).
- A `Test/` file exercising: assoc-only over abstract `Ring`; AC over abstract
  `CommutativeRing`; distributivity over a concrete ring; a non-identity that
  must be *rejected* (e.g. `a*b = b*a` over a plain `Ring`).

---

## Appendix A — env vars / knobs (current)
- `MATH_AUTOPROVE_BUDGET=N` — hard effort cap in kernel steps (0 disables; default 1.2M).
- `MATH_AUTOPROVE_WARN=N` — warn threshold (0 disables; default 50K).
- `MATH_DISABLE_CTX_EQ_BRIDGE=1` — turn off the recursive context-equality search.
- `MATH_PROFILE_AUTOPROVER=1` — per-claim TSV rows: `file:line, goal_head,
  goal_size, winner, tactic, ok, us, cand`.
- `MATH_TIME_TACTICS=1` — per-module per-strategy timing summary.

## Appendix B — the 10-site expensive worklist (warn @ 50K, kernel-steps)
```
Algebra.principal_ideal_domain:153      955691   (pure assoc over abstract Ring; closed by contextEqualityBridge)
Integer.sign:140                        603510
Rational.reciprocal_function:448        452307
Natural.factorization:47                247996
Natural.factorization:35                 94625
PAdic.absolute_value:534                 67919
Rational.order_multiplication:452        66308
PAdic.absolute_value:178                 65969
Natural.prime_divides_product:71         63776
Natural.prime_divides_product:56         61539
```
(`Algebra.factorization_list` had a ~367K step in an earlier sweep but does NOT
warn — it was an expensive *failed/abandoned* attempt, correctly not flagged; the
warning fires only when an expensive by-less step actually *closes*.)

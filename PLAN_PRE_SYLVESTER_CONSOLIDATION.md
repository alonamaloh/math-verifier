# Pre-Sylvester consolidation pass

> **Why now.** S1.F3 (Sylvester) forces submatrix/minor machinery — the most
> index-heavy work in the whole 15-theorem plan — and S1.B2 is entry-level
> inequality work. Both dive below the `matrix_vector` interface into
> `NaturalsBelow` index land, where an external review of the Stage-0 corpus
> identified recurring language taxes. This pass fixes the tax structure
> BEFORE that code gets written. Source: review of
> `determinant_multiplicative.math`, `permutation_transposition_sign.math`,
> `matrix_vector.math`, `determinant_transpose.math`, and the new S1 files.

> **2026-07-18 revision (in-repo, after grep-verifying every claim — all
> held).** Trims and riders: T4 demoted to a probe folded into T1 (the sweep
> of verified files is retroactive value only; new code just needs to know
> whether `Permutation.apply` elaborates first-class). T1 gains the
> wrapper-head defeq friction from the S1 build as probe (d). T2 gains the
> head-constant dispatch caution + the `Integer.one_multiply_left`
> disposition (delete, don't relocate). T5 gains the `applyVector_zero` /
> nonzero-preservation / positive-definiteness-isometry riders. T6
> recommendation recorded: defer; a scoped variant exists if partial benefit
> is wanted sooner. Session budget: T1(+T4 probes)+T3+T5 ≈ one session;
> T2 ≈ one–two sessions.

## How to use this sheet

- Work the tasks IN ORDER; each task is its own commit (or small commit
  series). Re-verify the affected build surface after each task and note
  wall-clock in the ledger entry — no silent perf regressions.
- **Time box: this pass is probes, registrations, and known sweep patterns
  only.** If any task hits a genuine surprise, write a QUIRK.md entry
  (symptom / hypothesis / attempts / workaround), mark the task `[B]` here,
  and move on. Do not investigate in this pass.
- **Do not rewrite verified Stage-0 proof bodies cosmetically.** New
  machinery is for code not yet written (Sylvester onward). Old files are
  touched only where a task's acceptance test explicitly says so, or where
  a lemma is being relocated.
- Every claim below about the current state of the library should be
  re-verified with a grep before acting on it — the review was external and
  the tree moves fast.
- Status boxes: `[ ]` TODO · `[~]` WIP · `[B]` BLOCKED · `[x]` DONE.
  Append a dated ledger note under each task when it closes.

---

## T1 `[ ]` (S) Probe: `let`-bound FUNCTION subterms in relation chains

**The question.** Scalar `let`s work in chains (see
`Real/arithmetic_geometric_mean.math` — `firstSum`, `secondSum` are
`let`-bound and cited in chain steps). The determinant corpus never
`let`-binds the recurring six-line summand LAMBDAS — e.g.
`Matrix.phi_inner_sum` (`Algebra/determinant_multiplicative.math:147`)
spells its summand ~8 times, 89 lines for one factor-extraction. Is that a
missed idiom or a matcher limitation?

**The probe.** In a scratch `library/Test/` module, restate a small analogue
of `phi_inner_sum`:

```
let summand : Permutation(n) → CommutativeRing.carrier(r) :=
    (sigma : Permutation(n)) ↦ ... ;
CommutativeRing.sumOver(summand, Permutation.allPermutations(n)) = ...
    by CommutativeRing.sumOver_scale_left ...
```

Test specifically: (a) does a chain step cite `sumOver_scale_left` /
`sumOver_congruence` against the `let`-bound name; (b) does
`sumOver_congruence(pointwise := ...)` unify when the goal mentions
`summand` but the lemma's conclusion mentions the applied lambda; (c) does
the diff matcher bridge a step where one side uses the name and the other
the literal lambda; (d) the wrapper-head friction hit live in the S1 build
(992a4fc3): a chain opening at `Matrix.quadraticForm(…)` could not cite
`applyVector_multiply` under it — diff-inference does not δ-unfold the
chain HEAD to find the congruence site, and needed an explicit defeq step
down to the `innerProduct` spelling first. Reproduce minimally; it is the
same matcher surface, so the conventions note or QUIRK entry should cover
(a)–(d) together; (e) folded in from old T4: does `Permutation.apply`
elaborate as a first-class `Permutation(n) → (NaturalsBelow(n) →
NaturalsBelow(n))` value where the corpus writes the eta-expanded double
lambda (`determinant_multiplicative.math:241–243` is the reference site)?
Probe ONLY — no sweep of verified files (their value is retroactive; what
matters is that Sylvester-era code may write the direct form).

**Branch on outcome.**
- Works → add a "name your summands" rule to `docs/conventions/` (chains
  section) with the probe as the worked example. Delete the scratch module.
- Fails → QUIRK.md entry with the exact failure mode. This is the seed of a
  dedicated elaborator session; do NOT fix it now.

**Acceptance:** either the conventions entry or the QUIRK entry exists;
probe module deleted; nothing else changed.

---

## T2 `[ ]` (M) ★ NaturalsBelow order — the Sylvester gate

**The tax.** `NaturalsBelow` (`Set/finite.math:27`) has only
`value`/`make`/`below`. Every index comparison in the library is spelled
`NaturalsBelow.value(i) < NaturalsBelow.value(j)` — the ~640-line
`permutation_transposition_sign.math` pays this 2–4 times per line.
Sylvester's leading-principal-minor work will be wall-to-wall index
comparisons; it must not be written in this style.

**Steps.**
1. Verify the gap library-wide first: grep for any existing
   `operator (<) on (NaturalsBelow` or order definitions on the type.
2. Define `i < j` and `i ≤ j` on `NaturalsBelow(n)` as value comparisons,
   registered via `operator`, placed next to the family (in
   `Set/finite.math` or a sibling `Set/finite_order.math`). Prefer a
   definitionally transparent definition so existing `Natural.*` order
   lemmas cite through it; if the elaborator needs explicit bridges, add
   `automatic` transport lemmas in both directions (the `automatic`
   pattern is already used at `Set/finite.math:45`, and the S1
   sign-discharge audit is the template for which spellings discharge
   sites want). **Caution:** operator dispatch and calc-carrier detection
   key on head constants, and this puts a second `<` next to ℕ's — the
   Natural order foundation (opaque `<` / transparent `≤`,
   `order_foundation_lux`) is the precedent for which shape survives
   dispatch; check it before choosing transparency.
3. Relocate the stray general lemmas the sign files accumulated so nobody
   re-proves them: `Natural.lt_or_gt_of_ne`, `Natural.lt_asymmetric`
   (`permutation_sign.math:29,38`), `Natural.ne_of_lt`
   (`permutation_transposition_sign.math:280`),
   `NaturalsBelow.ne_of_value_ne` (`permutation_sign.math:431`),
   `Equality.ne_symmetric` (`permutation_transposition_sign.math:122`),
   `Product.eta` (`permutation_sign.math:228`)
   — each to its family's home file, as PURE MOVES (no spelling
   modernization inside the moved lemmas), mechanical import fix-ups only.
   Exception: `Integer.one_multiply_left` (`permutation_sign.math:160`) is
   literally `:= ring` — routine computation. Delete it and leave its call
   sites bare (post-cast-absorption they likely close without it); relocate
   only if a site genuinely still needs the name.
4. OPTIONAL PROBE, do not force: can `NaturalsBelow.value` register as a
   coercion `NaturalsBelow(n) → ℕ` under the argument-position coercion
   machinery? The source type is DEPENDENT (indexed by `n`), which the
   ℕ→ℤ→ℚ→ℝ→ℂ chain never exercises. If the machinery rejects dependent
   sources, record that in the ledger and stop — the order operators alone
   remove most of the tax. Check PLAN_COERCIONS.md for the registration
   pattern before probing.

**Acceptance:** a `library/Test/` module where, for `i j k :
NaturalsBelow(n)`: `i < j; j < k; i < k by Natural.lt_transitive` (or the
bridged equivalent) closes; a swap side condition that previously needed
spelled-out values discharges; full library re-verifies. Old files NOT
rewritten.

---

## T3 `[ ]` (S) ≠-symmetry in premise discharge

**The tax.** Side-condition discharge does not try symmetry of `≠`, so
proofs carry two-line flips — `value(a) ≠ value(j) by Natural.ne_of_lt;
value(j) ≠ value(a) by Equality.ne_symmetric;` — three times in one
110-line excerpt of `pairOrient_swap_adjacent_other` alone
(`permutation_transposition_sign.math:333–339, 367–370`).

**Step.** Register the symmetric spelling as an `automatic` bridge exactly
the way the S1 sign-discharge fills did (0-anchored-weaken precedent:
lemmas that "never register" in the index get a bridging twin). Gate it the
same way those were gated so no search widening occurs.

**Acceptance:** a probe claim needing `y ≠ x` with only `x ≠ y` in context
discharges silently; the sign-discharge probe corpus still discharges;
re-verify green.

---

## T4 `[x]` (—) MERGED INTO T1 (2026-07-18 revision)

Demoted from sweep to probe (e) under T1: the sweep's value was entirely
retroactive polish of verified files, which this pass's own ground rules
deprioritize. What Sylvester-era code needs is only the probe answer —
whether `Permutation.apply` elaborates first-class at the double-lambda
sites. A `Permutation(n) → (NaturalsBelow(n) → NaturalsBelow(n))` coercion
has the same dependent-source caveat as T2.4 — same probe-then-stop rule.

---

## T5 `[ ]` (S) S1 riders from the review (do before F3)

1. **`Matrix.quadraticForm_scale`:** `Q(c • x) = c² · Q(A, x)` in
   `Algebra/quadratic_form.math`. Check first whether
   `Matrix.applyVector_scale` exists in `matrix_vector.math`
   (`innerProduct_scale_left` does, at :179; grep 2026-07-18 confirms
   `applyVector_scale` is missing); add it. Both are
   short chains in the existing interface vocabulary. Consumers: the
   S1.F2 ℤ⟺ℚ agreement, S1.B1, S1.B2.
   **Riders (2026-07-18), same file-visit, same size:**
   `Matrix.applyVector_zero` (`A · 0 = 0`), "an invertible action
   preserves nonzero" (`U invertible → x ≠ 0 → U·x ≠ 0`, via
   `x = V·(U·x)` and `applyVector_multiply`/`applyVector_identity`), and
   their consumer `Matrix.isometric_positive_definite` — the S1 loose end
   that positive-definiteness is an isometry invariant
   (`integer_quadratic_form.math`).
2. **Record the owner decision on S1.F2** in PLAN_15_THEOREM.md: the
   ℤ-vector statement is CONFIRMED as the primitive. Add to the item note:
   *"ℚ agreement = denominator-clearing via `quadraticForm_scale`. The ℝ
   statement is a Sylvester corollary at its first consumer (S2.R2 /
   S3.T1) — do NOT attempt via density: positivity on a dense set yields
   only semi-definiteness in the limit; the gap needs
   rational-kernel-of-PSD or the Sylvester route."*
3. **Signature clutter — probe-then-adopt, NOT adopt-then-discover.** Pick
   a candidate abbreviation for `Matrix(Integer.commutative_ring_bundle,
   n, n)`, but an alias `definition` risks the same head-constant gotchas
   as T2: `*`/`ᵀ`/`·` dispatch and citation matching key on `Matrix` as
   the head, and binders typed at the alias may not unfold at dispatch
   time. Probe ONE theorem end-to-end (state at the alias, prove, cite
   from a consumer file) before putting it in any signature. If it fights,
   fall back to lexer-level notation (the ℤ/ℕ pattern) or drop the item —
   a wordy-but-working signature beats a short one that breaks citations.
   Document whatever survives as a conventions note. No elaborator changes.

---

## T6 `[ ]` (L, GATED — needs owner go/no-go) Lists/Logic implicit-argument modernization

`List.map (A B : Type(0)) ...` (`Lists/map.math:15`) and siblings
(`List.Distinct`, `List.Permutation`, `Function.IsInjective`, ...) predate
the implicit-argument style `Algebra/` uses, so every call site pays
explicit type arguments — an estimated 15–20% of the tokens in the
enumeration/sign/transpose files. The fix is the established sweep pattern
(the ∸ sweep at f62c7ff9 covered ~490 sites): change the signatures,
mechanical call-site fix-ups, per-file commits, full re-verify per file.
Large but bounded, and it only grows with each stage. **Do not start
without an explicit owner go** — it is the one task in this pass big
enough to eat the time box.

**Recommendation (2026-07-18): defer out of this pass.** If partial
benefit is wanted sooner, the scoped variant is: only the modules the
Sylvester work will import heavily (`Lists/map`, `Lists/list`,
`Set/finite`, `Logic.functions`) — roughly a quarter of the sites for
most of the new-code benefit. Whenever it does run, the ∈-sweep recipe
applies (parallel Sonnet subagents, per-file verify; Sonnet floor, never
Haiku).

---

## Non-goals for this pass (recorded so they don't creep in)

- **Auto-lifted congruence for under-binder rewriting.** The one item with
  real design questions. File it as its own plan entry (PLAN_ERGONOMICS.md
  or a new sheet) with this acceptance test recorded now: *restate
  `Matrix.phi_inner_sum` in ≤ 20 lines with every displayed statement
  still an honest, locally-checkable equation.* Build it early in S1
  against Sylvester's live need, not speculatively here.
- **Import re-export / manifest mechanism.** Real, growing, not urgent;
  design work, not a registration.
- **Cosmetic re-sweeps of verified Stage-0 files** with the new T2/T3
  machinery. Their value is entirely in unwritten code.

## Wiring

Any new gate or ratchet introduced by this pass must run as part of
`make library` (or the standard check target) — the 07-18 ratchet audit
(e6826cb7) showed off-path gates drift unseen.

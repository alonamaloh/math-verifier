# PLAN_LANGUAGE_IMPROVEMENT.md — the declarative endgame

This plan distills a design review of the surface language (July 2026)
into concrete workstreams. It is now the **single forward plan for the
language**: it absorbs `PLAN_LUX_TRANSITION.md` (the 2026-06 transition
plan, largely landed — see the lineage section at the end) and
`PLAN_INTERFACE_IMPLEMENTATION.md` (the 2026-06-21 sealed-structures
design, now Part D). The organizing principle, stated once:

> **Every block in the language announces or concludes with an explicit
> proposition.** A proof is a sequence of stated facts; the elaborator's
> job is to verify each stated fact and to silently discharge the facts
> a mathematician wouldn't bother to state. Nothing is ever proved that
> isn't on the page — but plumbing that carries no mathematical content
> should never be on the page either.

The plan has four parts: (A) the statement language — collapsing the
construct zoo into a small core; (B) the auto-prover — a tiered,
deterministic discharge engine that eliminates breadcrumb claims without
reintroducing global theorem search; (C) supporting work — lints,
diagnostics, documentation, migration; (D) interface and implementation
— module-level abstraction barriers so a type's construction is a sealed
detail behind an axiomatic interface.

Workstreams are ordered by leverage. Within each item: motivation,
design, implementation notes, and open decisions. Anything marked
**DECIDE** needs a human call before implementation.

---

## Status ledger

Implementation spans many sessions. **Every session that works on this
plan updates this table before it ends** (status + commits); deeper
findings go into the owning section as a dated note. Steps refer to
the suggested order at the end of the plan.

| Step | Workstream | Status | Record |
|------|------------|--------|--------|
| 1 | B5 classifier (instrument hinted claims/calc steps) | **done** | 2026-07-02; `MATH_CLASSIFY_HINTS` + `scripts/hint_classification_report.py`; findings in B5 (64.6% absorbable of 5807 sites) |
| 2 | B1–B3 tier skeleton, context index, cast tier | **B1/B2 done; B3 scoped (forensics next)** | tier-4 sign index v1 (21b1cb4) + v1.1 IsNonneg/alternatives/form-bridges: closes-today 36.2%→42.3% (+352 sites). B3 cast retry landed (test-proven; yield compounds with future families). Per-key vectors landed. **B3-proper audit (2026-07-02 night): the tier3-cast bucket (445) is DIFFUSE — 170 sites are hand-built `<term>` proofs, top named lemma 14 sites, shapes mostly cast-bearing EQUALITIES (Integer to_integer/absolute_value chains), not order judgments. No quick prototype exists; it needs the full morphism-packet + norm_cast design. DECIDED (delegated, 2026-07-02): convention-named lemma discovery — no new syntax; missing-slot warnings make it auditable; a packet clause only if discovery proves too magic.** **B1 stage-1a memo tried and REVERTED (73ae506): A/B showed zero effect — the 2026-06-27 perf session already satisfied tier-0's speed rationale (derivative ~4.9s, continuity ~1.3s, full re-verify 25.5s wall today). B1's remaining value = the A2 statement-address spine + derived-fact blackboard, not speed.** **Zeroness DECIDED by measurement (2026-07-02 night): post-breadcrumb-sweep, the classifier shows the `= 0` slice at single-digit sites (the sweeps consumed it) — no dedicated judgment family; the equality battery suffices. Post-sweep bucket sizes (3868 hinted sites, down from 5807): tier3-cast 465, B4-order-step 308, tier2-ground 268, tier4-sign 189 — B4 is now the largest well-specified target.** A2 spine: stage 1 landed (see row 5). **B3 scoping sharpened (2026-07-03, classifier re-run at the post-flip tree: 3872 hinted sites, closes-today 981/25.3%, tier3-cast 412, tier3+4-sign-cast 74, tier2-ground 242, B4-order-step 98):** the tier3-cast bucket's shapes are already LEAF-cast (`to_integer x * to_integer y = |z| * to_integer w` — atoms under single casts), so castPushToLeaves (which EXISTS, proof-carrying, gated on the `<hop>.<op>_preserves` convention — cast_normal.cpp) is NOT the missing piece for them; the yield is in cast REFLECTION/lowering (`ι a = ι b ⟸ a = b`, order twins) + CONTEXT-FACT cast normalization so goal and hypotheses meet at one placement. Staged design for the fresh-context build: B3.1 equality tier (push both sides + injective lowering when both sides are same-hop casts, then battery retry on the lowered goal); B3.2 order transport (normalize/lower endpoints, feed B4); B3.3 context-fact normalization; B3.4 packet audit warnings at coercion registration (slots: zero/one/add/multiply/subtract/LessOrEqual/LessThan preserves + reflects/injective; naming today is INCONSISTENT — Rational.to_real.LessOrEqual_preserves vs Real.from_natural_add_preserves — the owner wants uniform names, see embedding_order_lemmas_uniform_naming memory; adopt `<hop>.<op>_preserves`/`<hop>.<op>_reflects` and sweep). Measure each stage against the classifier baseline above (log at scratchpad classify_before.log, regenerate with MATH_CLASSIFY_HINTS=1 make library + scripts/hint_classification_report.py). |
| 3 | A1 keyword-free claims/calc | **stage 1 landed** | Stage 1 (2026-07-03, 3b3126e): bare `P;` / `P by V;` / `P as NAME;` at statement position = a claim (desugars onto the claim wrapper — shared elaboration/unused-tracking/errors); bare proof terms state their type; blocks may end by restating the goal (the final-expression `E}` / `E;}` shapes keep their exact old meaning, so data-valued blocks are untouched). Activation bug found+dodged: the claim branch's dead done/okay wrapping path mis-binds de Bruijn when a `done by X` before `}` becomes a binding (goal-sentinel proposition passes the non-null check) — done/okay stay excluded from the statement loop; that latent path is still dead and should be deleted or fixed when the migration touches it. PARITY LANDED (post-26bc0be): the bare-statement by-tail routes through parseStructuredClaimTail — by-cases/by-substituting/by-induction/unfolding all work on bare statements; the MIGRATION SWEEP is now unblocked. **PILOT DONE (535d5e23): library/Integer keyword-free — 100 claim sites across 14 files, 3 subagents + batch build; found+fixed a real chain-probe bug (bare `k = 0 ∨ …` mis-parsed as a chain — detection now requires a full-chain speculative parse with ≥2 steps ending at a statement boundary) and the truncated-library-depends.mk-after-parse-error gotcha. LEAVE-LIST TAXONOMY for the full sweep: terminal `claim by cases {…}` (no proposition — keep or redesign per A4); semicolon-less claims in EXPRESSION position (`:= claim P by X claim by cases {…}` bodies — spec decision needed, likely braces+statements); claim-last-before-} (bare `P;}` means final-expression — keep claim or end with done). **LIBRARY-WIDE SWEEP DONE (owner-approved 2026-07-03, commits e22f001a..0e841e42+tail): ~4400 claim/calc statement sites converted across Natural, Rational, Real, ComplexNumber, IntegerMod, Algebra, Lists, Set, Polynomial, GaussianInteger, Integer, Logic, RingModulo — 6 waves of 4-5 subagents (Sonnet fine for these, owner request: use Sonnet for mechanical batches), full clean validation per wave, zero-to-two fixups per wave. REMAINING keyword population (the keep-list, pending A4/A5 and the expression-position story): terminal `claim by cases {…}` heads; claims/calcs in EXPRESSION position (`:= calc` bodies, `↦`/`=>` arm bodies, parenthesized args, `witness … with (calc …)`, semicolon-less `:= claim P by X claim by cases` chains); claim-last-before-`}` (bare `P;}` = final-expression); Leave-rule (f) RETIRED (25b59f65): equality claims route lambda hints through tryUnderBinderStep exactly like calc = steps — the two forced calc keywords went bare. KEYWORD REMOVAL from the parser stays gated on: A4 (case-analysis redesign kills terminal `claim by cases`), the expression-position chain story, and rule-f. Owner also asked for a CIC-leak sweep (pattern matching, Or.introduceLeft, …) — planned as the post-A4 follow-up sweep.** Connectives note (ba0943d, since REMOVED entirely by owner call 9bc0c46): `then`/`hence`/`therefore` parse as noise words before bare statements (contextual, operand-start lookahead guards the if-then-else sugar; no recency-hint plumbing needed — the fact scan is already most-recent-first). Chains LANDED (127e890): a relation chain at statement position is a calc with no anchor word — rewound additive-level speculation detects the shape, the existing calc statement branch handles it via parseCalc(consumeCalcKeyword=false); single relations keep the claim route; mixed chains + per-step by + as-naming + connectives compose. REFERENCE-TARGET GAP LIST (checked against the idealized form 2026-07-03): bare-by statements ✓, from-form ✓, connectives ✓, chains ✓, choose-without-from ✓; still missing (a) STATEMENT-FORM structural steps (A3/A4/A5 territory; the induction HEADER is settled — owner-designed `by_strong_induction on m with hypothesis no_smaller_solution` LANDED (contextual word marks the IH, subject defaults to shadowing the inducted variable; verbose `with <subject>, <ih>` stays for non-variable `on` targets) — what remains is the braces-to-flat-statement transformation), (b) whole-body `by lemma` plumbing — Or.self collapse LANDED (0944d67) + the literal `:= by <lemma>` body spelling LANDED (4e70823: after `:=` a by-headed body desugars to the goal-restating claim) — **two_divides_root now verifies in its EXACT idealized spelling**; REMAINING: goal-side intro + ∃-flattening for the ¬∃ shape (sqrt_two_irrational := by no_double_square), (c) the acceptance form's `contradiction with <fact>` must be rewritten to the owner's done-idiom (terminal skipped by DECIDE), (d) prover strength on the bare `hence n*n = 2*(k*k)` ring-cancellation step. **Idealized no_double_square PROBED end-to-end (2026-07-03, scratchpad ideal_probe.math): parses and elaborates through the chain/from/hence forms; first failure is the FIRST contradiction block's `done`** — the chain binds `subject = 0` but False needs the transported absurdity. Probe-driven fixes for next session: (i) end reductio chains AT the absurdity (`then 1 ≤ subject = 2 * 0 = 0;` binds `1 ≤ 0`, and the Not-peeled pool + premise discharge should close False via not_less_or_equal_successor_zero — verify); (ii) mark `Natural.lt_irreflexive` automatic (the second block binds `s*s < s*s`; Real's twin is automatic, Natural's is not — [[reductio_done_idiom]] alignment, cheap); (iii) the second block's chain steps (s*s ≤ n*n from s ≤ n via mono index; n*n < 2*(n*n) needs 1 ≤ n*n) may need by-hints — measure which close bare; (iv) ∃-FLATTENING DESIGN (the remaining whole-body-by piece, for sqrt_two_irrational := by no_double_square): in the by-hint path only, depth-bounded — goal WHNF-Pi ⇒ λ-intro + recurse; else eliminate a context Exists via verbose `Exists.eliminate.{u}(A, P, G, λ x hp. body, h)` and recurse with x, hp in scope; CLOSED-in/CLOSED-out convention throughout (internal.hpp ~476), delicate de Bruijn — fresh context required. **Probe iteration 2 (2026-07-03, same session): fixes (i)+(ii) LANDED AND VERIFIED** — chains-to-the-absurdity close the first reductio (`then 1 ≤ subject = 2 * 0 = 0; done` works via the Not-peeled pool), and Natural.lt_irreflexive is automatic (8fadcd3). The probe now verifies THROUGH both reductio blocks and the descended equation; the two remaining stoppers, precisely: (α) the single-position diff walker in the claim-by/coercion transport recurses PAST the rewrite point when both sides share a head (fact `s*s ≤ n*n` vs target `2*(n*n) ≤ n*n`: multiply-vs-multiply descends to a two-position diff and declines, though `equation : s*s = 2*(n*n)` rewrites the whole operand in one step) — fix: also try each whole mismatching subtree as ONE rewrite leaf against in-scope equalities before recursing; interim spelling is `claim … by substituting equation`; also from-with-STATED-PROPOSITION facts skip transport entirely (bridgeCitedFact path) — same fix location; (β) `¬(a ≤ b) → b < a` does NOT exist at Natural (the old proof case-split on compare_strict instead) — add `Natural.lt_of_not_le` to order.math (via trichotomy), then the final `done by no_smaller_solution` premise-discharge chain can derive `n < subject` from the second reductio's fact. Probe file: scratchpad ideal_probe.math (copy into Test/ when it goes green as the acceptance test). **GREEN (2026-07-03, 2475868): Test/no_double_square_idealized.math LANDS as the acceptance test** — both stoppers closed same session (α FIXED (post-2475868): findUniqueDiffPair is a bottom-up coarsening walk — a node whose children carry multiple distinct diffs is itself the diff; whole-subtree rewrites transport (probe green); previously-found pairs unchanged; β: Natural.lt_of_not_le moved to its honest home in Natural/order.math via trichotomy — it existed BURIED in Polynomial/bezout.math, duplicate deleted, bezout's prover-found use now hits the canonical one). Deviations from the plan text, each owner-sanctioned or queued: done-idiom reductio endings (owner DECIDE), by_strong_induction braces (statement-form steps pending, A3-A5), the substituting step (α), and two derivation steps carry `by` hints the idealized text leaves bare (lt_of_not_le, successor_less_or_equal_multiply — prover-strength residual). Lux-gate remainder: sqrt_two_irrational := by no_double_square needs the ∃-flattening; then the gate question goes to the owner. **∃-flattening step 2 LANDED (7c1cf78): citePiGoalByIntroduction WHNF-peels (¬ goals intro their supposition) + citeCoreGoalWithExistsFlattening (direct attempt, else eliminate an introduced Exists binder into witnesses via verbose Exists.eliminate, recurse; depth-bounded, by-hint only). Feature-tested GREEN: single ∃, ∃+∧, nested ∃. LAST GAP (rung 3): nested ∃ WITH a ∧ under the inner one — the premise back-inference (completeCitationFromBindings pass (a), induction.cpp ~1514) meets the whole conjunction as ONE eliminated fact `h1 : (λn. And(1≤m', And(1≤n, eq)))(w1)` and cannot pin both witnesses: it scans BINDER TYPES only (no ∧-leg decomposition there) and its first-match commit has no backtracking. Fix directions to evaluate with instrumentation, fresh session: (i) decompose conjunction legs of context facts in pass (a) (mirror collectLocalBinderFacts), and/or (ii) unique-match-first premise ordering (collect all candidate facts per premise; commit only unique matches each round; ambiguous ones only when no progress). Suspicious detail worth checking first: WHY rung 2 (single ∃+∧, same conjunction-as-one-fact shape) PASSES — find which pass discharges its legs before assuming (i) is needed.** **RESOLVED SAME SESSION (33a9ca8): And-typed binders now DECOMPOSE in the flattening scan (two lambda binders applied to the And.left/And.right projections, alternating with the Exists eliminations) — rung 3 AND the ∃-inside-∧ variant both close, and **Natural.sqrt_two_irrational IS NOW THE IDEALIZED ONE-LINER `by Natural.no_double_square`**. ALL THREE reference-target theorems verify with their whole-proof citations. THE LUX GATE QUESTION IS NOW THE OWNER'S: the remaining textual deltas between the acceptance test and the plan's idealized form are (1) statement-form by_strong_induction (A3-A5, braces remain), (2) the owner-sanctioned done-idiom reductio endings, (3) one `by substituting equation` step (diff-walker fix queued), (4) two prover-strength `by` hints. Whether that clears the 'idealized form' bar — and triggers the Lux rename — is an owner call. **OWNER WEIGHED IN (2026-07-03): the library file itself must carry the ideal form — the cases-on-compare_strict pattern match and the positional inductionHypothesis(...) call were the remaining anti-patterns. DONE (3ee9222): Natural/sqrt_two_irrational.math now holds the idealized no_double_square (reductio + `hence n < subject by Natural.lt_of_not_le` + argument-free `done by no_smaller_solution`); Natural.compare import dropped; the Test duplicate deleted (the library file IS the acceptance form).** Remaining textual deltas from the plan's exact reference text (updated after 2d0260c): statement-form by_strong_induction (A3-A5), done-idiom endings (owner-sanctioned), the two-hop squaring chain (`s*s ≤ s*n = n*s ≤ n*n` — the one-step `s*s ≤ n*n` needs two-operand mono composition in B4), and two substantive `by` hints (lt_of_not_le, lt_multiply_of_two_le). GONE since the owner's successor/claim feedback: the successor spellings (lt_multiply_of_two_le, `<`-stated + automatic, ABSORBED successor_less_or_equal_multiply; factorization + prime_factorization_unique restated in `<`), the lone `by substituting` step and the 1 ≤ 2 / 1 ≤ n*n seeds (the single reductio chain ends at the absurdity and everything else discharges bare). ALSO fixed at source: writeCacheFile is atomic now (temp+rename — an interrupted parallel build left truncated .mathv files that poisoned incremental builds with 'short read').** **Owner nitpick round 2 (2026-07-03, 38aea21): the A7 `from`-form is REMOVED by owner verdict (plain `P by fact` already transports — distinction without a difference); `then`/`hence`/`therefore` are REMOVED ENTIRELY (9bc0c46 — owner call: the parser tolerance too; the A1 connectives design bullet is dead); breadcrumbs left the page via two additive prover changes (two-pass premise back-inference: historical greedy first, unique-match-first on failure; search-free ground-premise lookup under the scan against premise-free automatic facts — Natural.one_le_two is the first, the stop-gap pattern for [[arithmetic_decision_tactic_idea]]); two_divides_root renamed two_divides_of_two_divides_square. STILL OWED from the nitpick list: (a) k² notation LANDED (27fbfbb: postfix ² token, parse-time desugar to `E * E` — downstream systems see plain multiplication; sqrt file restated; printing-side superscript compression = existing printer work item); (b) `done by no_smaller_solution(n, k)` — positional-data-args mapping LANDED in recoverClaimHint (data args fill non-Prop slots in order, premises become holes) but BLOCKED on a deeper gap: explicit-hole citations of LOCAL-BINDER facts don't premise-discharge (probe: scratchpad positional_probe.math, `by L(a, ?, c, ?)` fails with premises stated in context) — RESOLVED (26bc0be): the hole dispatch only knew GLOBAL heads; a local-binder branch routes to the same solver, and the positional form works end-to-end — the sqrt descent closes with `done by no_smaller_solution(n, k)`; **∧-leg premise discharge LANDED meanwhile (e563c45): the back-inference's hypothesis scan decomposes conjunction binders into legs (projection proof terms, worklist) in the unique-match-first retry pass only — additive; grouped hypotheses (bothPositive-style) and unpacked-existential bodies now discharge citation premises without restating legs;** (c) the mathematician-invisible rearrangement `2*(n*n) = (2k)(2k) = 2*(2k²)` still needs one chain on the page — absorbing it = ring-normalize-then-cancel prover composition (the cancellation tier).** THEN the migration sweep, which ANSWERS the keep-vs-remove DECIDE. |
| 4 | B4 order automation in calc | **v1 DONE** | Landed 2026-07-02 night: monotonicity index (same-head order conclusions, bare-binder order premises = structural-descent admission, registerAlgebraicShape funnel, per-key ordered alternatives) + tryMonotonicityRecursion after the sign tactic at both prover hooks. v1.1 same night: two-sided keys (lhs-head-or-star, rhs-head-or-star) admit one-sided (x < x+e), constant-sided (negate(x) < 0), and mixed-head (triangle inequality) rules; sign-shaped premises follow the sign-index admission. Measured total: closes-today 463→743 (+280 sites, 12.0%→19.2%), B4 bucket 308→118; wall at baseline both steps. Residue (118): suspects are cross-relation weakening (le rule at lt goal), reflexive-leaf premises (a ≤ a), multi-position diffs needing two premises on the same head, and casts (tier-3 territory). The Natural strict add-monotonicity gap is CLOSED (add_left/right_strict_monotone, automatic; nested strict steps close by-less). |
| 5 | A2 statement addressability + A7 `contradiction` kit | **A2 stage 1 + transport done; A7 done** | A2 stage 1 (2026-07-02 night): propositions in FUNCTION position and as `choose` sources address in-scope facts — desugared onto `given(...)`, which already implements the A2 semantics verbatim (defeq match, loud ambiguity naming both facts, anonymous facts participate). Discovery: A2's expected-type half already existed as the bare-proposition-as-proof coercion, so stage 1 closes the no-expected-type positions. By-cases transport LANDED (2026-07-02 night): given()'s failed defeq scan retries each binder through tryDiffBridgeViaContextEquality (the coercion path's existing single-position equation bridge) — a cases-with-eq arm addresses P(pattern) and the outer P(scrutinee) transports silently, same ambiguity rule. v1 scope: single-position diffs, equation must be in scope (cases … with eq); multi-occurrence motives and auto-synthesized equations stay `refining` territory. A7 DECIDED (delegated, 2026-07-02): skip the `contradiction` terminal (redundant with the owner-built done-closes-absurdity idiom); the `from <fact>: <instance>` restatement form is the A7 piece to build when reached. `by`-position survey largely covered by context-discharge. **A7 `from <fact>: <instance>` LANDED (2026-07-03, 4120b7d):** proof-block statement `from h: P [as NAME];` — source fact named first, transformed statement on the page; thin parser sugar onto the claim wrapper with the fact as by-hint (a probe showed `claim P by h` ALREADY transports across context equalities via the A2 bridge, so no new elaboration path). Feature test Test/from_instance_test.math; reference.md row. With the contradiction terminal skipped by owner decision, A7's delegated scope is COMPLETE; the remaining A7 bullets (by-lemma whole-body plumbing, let-in-definition-bodies, module-local open, piecewise) stay future work. |
| 6 | A3/A4/A5 construct distillation | **A4 `decide` deletion DONE; A3 exits DONE; A5 DONE** | **A3 (2026-07-04): one `for` grammar for both suppose exits** — `suppose P for proving Q { … }` replaces `to prove Q` (migration error; one real use, the feature test), and the ∀-analog `take x : T for proving Q { … }` landed (unrolls through the same wrapper — a lambda over the data binder gives the Pi statement in context; feature tests in suppose_modifiers_test). Still open from A3: the block-length announcement lint, `suffices … by definition of X` (the unfold-header idiom it replaces now survives only in Test files — low value). **A5 (2026-07-04, in flight): multi-witness choose landed** (`choose m, n such that P [from S]` — the n-ary tuple pattern flattens nested ∃/∧; feature test choose_multi_test; the lemma+such-that disambiguation path rejects witness lists with a claim-first pointer), **the `representative` pattern landed** (`take x as representative(a, b) : Integer` / `cases x { | representative(a, b) => … }` — quotient-cases routes a constructor pattern named `representative` through the tuple path, so the carrier's constructor name leaves the page; take_with_pattern_test updated), and the **obtain→choose sweep is DONE (484cac50): `obtain` is RETIRED** (parser migration error; ~194 sites / 60+ files converted — choose for ∃/∧ with the property stated inline, `let ⟨⟩ :=` for genuine data, bare `as`-restatements for named conjunction legs, plain deletion for pure-∧ destructures of in-scope hypotheses; obtain_* tests renamed/repurposed; ErrorTest obtain_retired; docs rewritten across LANGUAGE.md/reference/tutorial/proof-style/quotients). Wave findings: (α) a by-less calc that rewrote through a leg the OLD tuple named works only if the equality's spelling matches the goal's — the anonymous ∧-leg keeps the LEMMA's spelling (e.g. IntegralDomain.ring(d) vs the let-alias s), and tryContextEqualityBridge matches occurrences structurally; remedy = restate the equation bare at the working spelling (principal_ideal_domain, 2 sites) — a candidate for ζ-tolerant occurrence matching later; (β) choose's unused-name warnings caught 6 sweep-introduced dead names, settled. A5 is COMPLETE (multi-witness choose, representative pattern, obtain retired, `choose` the sole logic eliminator). | 2026-07-04: **`decide` is deleted from the proof surface** (parser throws a migration error steering to `by cases`/`if`; `decide` stays a contextual keyword for qualified names like Natural.decide). The two-phase recipe finished in one session: (1) QUARANTINE — generic `Logic.if_positive.{u}`/`if_negative.{u}` in Natural/classical_decidable.math (`(if P then a else b : T) = a/b`; the file joined scripts/foundational_layer.txt — it IS the classical-decidability machinery) proved with the `if` spelling itself; every refinement-class definition then publishes one-liner characterizing equations (`by Logic.if_positive`) — the citation matcher unfolds min/filter/bisectionStep through their WithDec helpers and matches the conditional shape. Rational/minimum (pilot, now one-liners), Lists/filter (filter_prepend_positive/negative), Real/supremum (bisectionStep_eq_of_[not_]upper_bound + the FOUR endpoint recurrences bisectionLeft/Right_successor_of_[not_]upper_bound — all invariant proofs reason through them). (2) SWEEP — ~40 proof-side sites across Polynomial/ComplexNumber/Real/Algebra/Lists/Natural/Rational converted to `case P: … otherwise: …` (5 Sonnet agents + orchestrator; wave-level build as verification per the June workflow). Value-level definitions keep `if P then a else b` (the sole surviving spelling; docs updated: LANGUAGE.md, reference.md, tutorial.md, proof-style.md). Substitution-rule fallout: 2 arms got SIMPLER (degree_product `case i = m: done`, bezout speaks zero directly). ELABORATOR FIXES flushed out by the sweep (commit d823bd43): (α) both structured-claim-arm CLONE sites (substituteSurfaceName, rewriteRecursiveCalls) dropped isOtherwise/witnessName/witnessType — any otherwise-arm under a `let`/`set` or in a recursive definition became a stated arm with a null proposition and SEGFAULTED; clones now copy fully + a loud internal error replaced the null deref; (β) `P by substituting <Lemma>` now discharges the lemma's Prop premises via the budget-capped bare prover (mirrors citation premise discharge — needed for premised characterizing equations); (γ) the endpoint-instance scan falls back to CONTEXT-FACT statements when the goal carries no instance (hypothesis-transport claims state the rewritten form). Tests: decide_test/decide_recursion_pi_test → if_split_test/if_recursion_pi_test (given(P) addresses the anonymous branch hypotheses); ErrorTests decide_retired + if_missing_classical_decidable; 37/37 green, library + both ratchets green (manifest floor stays 204). A3/A5/induction-as-by-cases still open. |
| 7 | A6 `eventually` | **core DONE (binder form + goal scope + lemma set)** | 2026-07-04: library substrate + binder form. `Natural.Eventually(P) := ∃N. ∀m ≥ N. P(m)` (Natural/eventually.math) with the elaborator-facing lemma set: `Eventually.and` (∧-closure via maximum — the invisible-threshold combinator), `Eventually.monotone` (pointwise weakening), `of_always`, `past` (re-threshold past any later index). Surface: `eventually (m). P(m)` parses as an ordinary proposition (contextual `eventually`, claimed by the `(name).` lookahead shape only — the word stays usable as an identifier); rule (iii) came free (`choose N such that ∀m. N ≤ m → P(m) from h` opens the threshold — Eventually is transparent, WHNF exposes the ∃). Feature test eventually_test (states/combines/weakens/choose); reference.md row. **Rule (ii) LANDED same day: `eventually (m): { … }` in goal position** — new SurfaceEventuallyScope (parser lookahead `eventually (name):`, distinct from the binder form's `.`; all four surface walkers extended — substituteSurfaceName also gained the missing SurfaceByStrongInduction case while at it); the elaborator collects every in-scope `Natural.Eventually(Pᵢ)` fact (STATED-spelling head match — WHNF would δ-unfold the transparent definition past recognition, the day's recurring lesson), folds them with `Eventually.and` (combined predicate mirrors the lemma's conclusion shape exactly, applications unreduced, so the chain typechecks structurally), and closes with `Eventually.monotone` handing the body `m` + the combined hypothesis (∧-legs decompose for the prover); zero eventual facts degrades to `of_always`. Tests: scope combining two hypotheses, derivation body, always case — thresholds never on the page. REMAINING: the Real-ε bridge (SequenceConverges/IsCauchy restated through Eventually or bridging lemmas — then the LessOrEqual_of_pointwise_lower acceptance target); `for sufficiently large m:` prose sugar; index generalization beyond Natural if ever needed. |
| 8 | C1–C6 (continuous; C4 with each construct) | **in progress** | C1 elaborator side done 2026-07-02 (cb21629). **since→by sweep + breadcrumb deletion DONE for the clean manifest** (2026-07-03). Sweep: 8d1783c (`kernel rewrite --since-to-by`, the lexer-driven C6 rewriter) + 3f23ee7 (1820 sites / 124 files). Docs/skill retaught post-C1 (1176f93). Breadcrumb pass: --check-redundant-by flagged 1133 sites in 117 files; 5 parallel-agent batches (631e253, 88ce001, a6b7332, 85cc493, abaea54) deleted ~1050 routine hints, kept ~70 deliberately (IH, split/partition equations, archimedean/IVT/Bezout-class citations; zero performance-restores needed), settled the unused-name cascade, and fixed the 4 pre-existing claim-by-calc leaks that had clean-check failing at 208/205 → **manifest floor now 204, budget resynced, library+tests+both ratchets green**. **Library-wide since→by sweep + breadcrumb pass DONE (2026-07-02 afternoon session).** Sweep: 0e6232e (1065 sites / 68 files via the rewriter; Test/since_test.math deliberately reverted — it exercises the synonym until the keyword dies). Breadcrumb pass: 83 files / ~1080 flags in 6 parallel-agent batches (a19e07c, 02d0ee5, 324b932, 3043739, 2aa4822, e00dd2e) — ~890 routine hints deleted, ~190 deliberate keeps (IH, split equations, the-citation-IS-the-idea, symmetric twins), cascades settled, full clean rebuild + both ratchets + error-tests 22/22 green. **C6/C1 COMPLETE (2026-07-02 evening, 643fa1f): the `since` keyword is deleted** — lexer token, three parse sites, the explanation-flag fields and classifier plumbing, the one-shot rewriter tool, since_test.math, docs. `since` is now an ordinary identifier. Prerequisite fix landed first (fde6bb5): the redundancy checker leaked backwardChainingDepth_ on budget-tripped premise-discharge probes, silently disabling discharge past the cap mid-file; RAII'd, and trigonometric_bounds' formerly unreachable tail then got its breadcrumb pass (2fa6bc8, via a Sonnet 5 agent). Operational notes: (α) agents on files sharing an import cone CANNOT re-verify mid-batch — a sibling's edit stales the shared build/ cache (freshness is mtime-based even when the iface is byte-identical); the batch-level `make` is the verification step, and agents must check for the "stale cache" message TEXT (exit 0, evades warning greps); (β) CHECKER BUG to fix: `--check-redundant-by` hard-errors on an argument-free `done by Natural.LessOrEqual.transitive` that plain verify accepts (probe path loses context-discharge), aborting the scan mid-file — trigonometric_bounds past ~line 584 never got scanned; (γ) subagent session limits can kill a whole batch instantly — check for near-zero token counts and redo inline |
| 9 | D: sealed structures (Phase 0 ℝ prototype first) | **DONE through the flip campaign (residuals: visibility lint, universe-polymorphic obligations)** | D3a implementation design banked (iface-derivation refinement, 5 stages); stage 1 landed 2026-07-02 night: interface/implementation module kinds + interface-body forms (type/constant/theorem-signature as tagged axioms) parse via contextual words, implementation modules build inertly, interface modules rejected with a stage-2 pointer (3 ErrorTests). Stage 2 LANDED same night: obligation check (defeq against the loaded implementation, loud mismatch errors) + sealed-cache emission (abstract entries as bodyless Axioms, obligations as stripped opaque theorems, implementation dropped from the dependency list; cache v11 carries implementsName, cross-validated). Stage 3 (Makefile edge) came FREE — the interface imports its implementation, so the existing dep scan orders the build. Toy counter triple + sealing ErrorTest prove the acceptance property end-to-end. **Stage-5 scoping finding (2026-07-02 night, MEASURED): the hand-listed interface does not scale to ℝ.** Consumers spell 159 distinct Real.* names, but the PROVER reaches Real lemmas invisibly (automatic lemmas + the rewrite/sign/monotonicity indexes), so a curated theorem list breaks by-less proofs unpredictably; the honest closure is "all theorems" — and the Real subtree has 386 theorems (23 automatic) + 78 definitions, so listing them by hand is unmaintainable churn (every new Real lemma would edit the interface). **DECIDED (owner 2026-07-02): hard opacity KEPT — the AliasBridgeScope softening is REVERTED (the interface-module cache boundary is the sealing mechanism; the alias-defeq bridge is moot for consumers). Remaining decisions delegated to Claude; stage-5 step A LANDED (825e303): `export theorems of M1, M2, …` — Prop-typed declarations of listed modules re-emit sealed with `automatic` preserved (sealed automatic lemmas keep powering by-less steps — the consumer test proves it); listed modules AND the implementation drop from the dependency list (content copied, edges would leak). Design rule surfaced: the interface must itself import every module its exported statements reference (the vocabulary can't ride the dropped construction edges) — D6's closure discipline made mechanical. NOTE for step B: Prop-VALUED DEFINITIONS (SequenceConverges etc.) do NOT bulk-export (their Pi-into-Prop types don't pass the levelAsConstant check — same lazy-level behavior that keeps .iface from stripping their bodies today; fragile, worth a deliberate predicate eventually) — they need explicit interface treatment (transparent re-export or constants + intro/elim lemmas). Step B LANDED (dc3540c): Real.cauchy roll-up (38 modules; IVT/uncountable/showcases outside) + Real.interface (type Real, 21 constants, bulk export of all 38) + a consumer test working ENTIRELY through the sealed view — exported citation, sealed-automatic by-less step, and the fold binder over the sealed carrier. Two structural findings: (α) wiring CANNOT be re-declared in the interface source (collides with the loaded construction) — it is copied mechanically from the dropped modules' caches, filtered to sealing-surviving names; (β) boundary lemmas must live in their OWN module at the construction's top (imported only by the roll-up): fold_as_partialSum is a definitional identity, and indexing it inside series.math perturbed matcher-unfolding searches downstream (exponential_addition broke; `construction` is also a reserved word — the roll-up is Real.cauchy per the D3 sketch). **Flip-campaign bill item 1 FIXED (2026-07-03, commit 9a3b6e8): Not-conclusion lemmas now join the unprompted pool.** Root cause (profiled with MATH_PROFILE_AUTOPROVER, not guessed): the construction path never applied Real.LessThan.irreflexive either — the actual winner on `(c : Real)(h : c < c) : False := done` was `local binder h (∧-right)`: Real.LessThan is transparently `LessOrEqual ∧ Not(=)`, so collectLocalBinderFacts WHNF-decomposed h and the `Not(c = c)` leg applied to reflexivity closed False; sealing removed that transparency and nothing replaced it. The pool itself had a blind spot on BOTH paths: the anyDepthMatches prefilter peels the candidate's Pi chain STRUCTURALLY, so a `Not(P)` conclusion (an Application, not a Pi) never reached its definitional False — automatic negation lemmas were invisible to False goals everywhere. Fix: the peel treats a Not-headed cursor as one more premise with conclusion False (structural, no WHNF — the loop runs per declaration per goal); the application side already WHNF-peels Not (autoFillHintForClaimCore), so admission was all that was missing. Repro pair now closes both ways; the done-idiom's documented mental model (contradictions end via the automatic irreflexive lemma) is now literally true, sealed or unsealed. Full clean validation green at the known-warning baseline. Residual lesson for the flip bill: any other unprompted closing that leans on Prop-definition transparency (∧-leg decomposition of `<`-like definitions, negation application) fails through the seal the same way — watch for the class during cone flips; the remedy is an automatic boundary lemma or a prover-visible peel like this one. **Owner-requested review of the stage-5 work + fixes (2026-07-03, commit 26dcfa1): the bulk export had NO closure discipline** — it re-emitted every Prop-typed statement including rep-level lemmas quantifying over construction internals, writing DANGLING references into the sealed cache (repro was: `Real.ContinuousAt` unknown-identifier through the seal; 48 dangling names total). Fixed at the seal step: (1) export pruning — a candidate emits only if every constant its statement mentions is sealed/fellow-export/reachable-via-kept-imports (fixpoint; unspellable statements skipped with a per-module `sealing note`, 72 rep-level statements today — grep the interface build's stderr for the current list); (2) a closure-validation backstop turning any remaining dangling reference into a loud build error naming the vocabulary + stating theorem; (3) obligations seal under the interface-STATED spelling (public contract; guards reduced-spelling re-entry) via CheckedInterfaceObligation{name, role, statedType}, and preserve the implementation's automatic flag (was hardcoded false — an explicitly-listed automatic obligation would silently stop powering by-less steps); (4) wiring copy errors loudly on an unreadable dropped cache (was silent wiring loss). Real.interface grew the public analysis vocabulary (constants: ContinuousAt, HasDerivativeAt, SequenceConvergent, limit, SeriesConverges, IsUpperBound/IsBoundedAbove/IsSupremum, square_root, e, exponentialTerm, midpoint, minimum, partialProduct; imports: Set.basics, Natural.maximum/factorial/binomial, Rational.power). Consumer test pins a continuity citation + the unprompted sealed done-idiom. Rest of the reviewed arc (stage-1 parser, stage-2 obligation check, hard-opacity revert, A2 by-cases transport, Natural strict monotonicity pair) is sound. NOTE for cone flips: the skipped rep-level statements are invisible to interface consumers BY DESIGN — a flip that needs one signals a construction-side proof leaking rep detail, not a missing export. **FLIP CAMPAIGN, showcase wave (2026-07-03, commits 87ebb60+b61f626): ALL FIVE Real showcase cones flipped sealed with ZERO proof edits** — uncountable (#22), triangular_series (#42), cauchy_schwarz (#78), harmonic_series (#34), arithmetic_geometric_mean (#38). The load-bearing mechanism is the NEW `export definitions D1, D2, …` clause (transparent re-export): the uncountable flip-measure showed the real bill is Prop/data-definition transparency — proofs intro/eliminate the bodies of honest public definitions (take-y-suppose-mem on sequence_range/IsUpperBound, the IsSupremum ∧-decomposition, `Real.one ≡ to_real(one)`, `a−b ≡ a+(−b)`) and NONE of that survives constants-only sealing, while the bodies are pure public vocabulary anyway. Real.interface now: 8 true quotient-level constants (add, multiply, negate, absolute_value, IsNonneg, to_real, square_root + type Real) and ~29 transparent definitions (zero/one/subtract, LessOrEqual/LessThan, divide/reciprocal, power/partialSum/partialProduct, midpoint/minimum, exponential family, ε-δ family incl. TendsToInfinity, ContinuousAt/ContinuousOn/HasDerivativeAt, supremum family, sequence_range); intermediate_value joined the roll-up + export list. The transparent layer is closure-validated (type AND body; construction-internal mention = loud error). D7's transparent-vs-sealed calls are hereby made: transparent iff the body is quotient-free. Also fixed: the wiring-copy filter now tests CONSUMER-VISIBILITY (sealed ∪ reachable-via-kept-imports), not sealed-ness — the sealed-only filter silently dropped the Natural→Real coercion chain (kept-layer links). Bill classes CONFIRMED EMPTY for these cones after the transparent layer: no numeral/cast issues, no prover-parity issues, no boundary-lemma gaps. REMAINING consumers: the ComplexNumber cone (32 files, next), and the Test/ files that deliberately exercise the construction (stay). **FLIP CAMPAIGN COMPLETE (2026-07-03, aee8cf8): the ComplexNumber cone (32 files) flipped with ZERO proof edits** — 538 construction-import lines collapsed to 32 `import Real.interface` lines (3 parallel subagents, Edit-tool recipe, one batch build as verification). Only interface change demanded: the three structure witnesses (Real.ring, add_is_monoid, multiply_is_monoid) moved constants→transparent (consumers project bundle fields: `Ring.carrier(Real.ring)` must reduce to `Real` for `Polynomial(Real,…)` sites). **EVERY Real consumer in the library now works through the sealed view**; construction modules load only in the interface build. The D7 bill FEARED (curated-list breakage, boundary-lemma churn, numeral/cast noise, ε-δ intro/elim surface) collapsed to: ONE transparent-definitions clause + the right transparent/constant split (quotient-free body ⇔ transparent). Total flip cost across all 37 consumer files: zero proof edits, 2 new elaborator features (export definitions, visibility-based wiring filter), ~30 interface-file lines. D stage-5 is functionally DONE; still open when needed: the visibility lint (D6), universe-polymorphic obligations, the `sealing note` skip list as a rep-leak worklist (~60 statements after the transparent layer). Pathfinder flip on Test/block_autoclose_test REVERTED (wrong choice — that file TESTS unprompted closing; also 1-file cones must flip wholesale anyway since mixed sealed/construction import paths collide same-named declarations). REMAINING for the full migration: flip consumers (ComplexNumber/Polynomial/Set cones + the showcase theorems) onto `import Real.interface` and measure the real bill — expected: boundary-lemma gaps for every defeq consumers lean on (the partialSum precedent), numeral/cast elaboration over the abstract carrier, and the Prop-valued definitions (SequenceConverges consumers that unfold ε-δ bodies CANNOT through the seal — they need the intro/elim lemma surface or must stay construction-side). Original call: BUILD the bulk clause — `export theorems of Real.basics, Real.addition, …` — re-emitting all Prop-typed declarations of the listed construction modules (sealed) so the interface file lists only the abstract type/constants, the operator wiring, and heavily-referenced transparent data definitions (Real.partialSum, Real.exponentialCoefficient, Real.zero/one — the top consumer references — each needing a transparent-vs-sealed-with-boundary-lemmas call per D7).** The obligation-check and sealing machinery (stages 1-3) is ready either way; the toy triple stays the acceptance test. Also still pending: the visibility lint and universe-polymorphic obligations when needed. Phase-0 flip-measure-revert 2026-07-02 (7-file bill; the Real quotient-alias elaborator gap = Phase 1's first item); interface = closure-not-minimality, LUB canonical + Cauchy exported (D7). **Gap investigation (2026-07-02 evening, reproduced + located, fix pending):** repro = flip `library/Real/basics.math:58` to `opaque definition`, `rm -rf build/library && make -k`; the (b) failures ("function expects `Quotient.{0} CauchyRationalSequence CauchyEquivalent`, argument is `Real`" in limits/continuity/derivative) mean an IMPORTED lemma's stored type carries the reduced carrier spelling. Mechanism: `engageOpaqueQuotientAlias` (desugar_eliminators.cpp:463) flips the alias Transparent "for the rest of this declaration" (restored by `OpacityRestoreScope`, internal.hpp:926); inside that window a home-file declaration's STORED interface type gets normalized/inferred with the alias unfolded, baking `Quotient(...)` into the cache that consumers then can't defeq back to opaque `Real`. Integer/Rational don't show it because their home files were built to the boundary discipline. MINIMIZED (2026-07-02 late, probe bisection on a clean flip build): the (b) failure is the interaction **compound statement × `choose`** — division is a red herring. Failing reproducer (theorem in a fresh file with limits.math's imports, under the flip): statement `Real.SequenceConverges((n : Natural) ↦ s(n) + t(n), sLimit + tLimit)`, proof `(ε : Real) (εPositive : ε > 0) ↦ { choose sThreshold as sClose from sConverges(ε, εPositive); sorry }` → "function expects Quotient.{0} CauchyRationalSequence CauchyEquivalent, argument is Real" anchored at the ε-lambda. The SAME choose with a simple statement passes; the SAME compound statement with claim-only body passes; `ε / 2` and the lambda-vs-unfolded-SequenceConverges check pass everywhere. So the reduced spelling is manufactured during the choose's Exists-elimination motive assembly when the surrounding goal carries the compound spelling — chase the motive/type-argument construction in the choose path of desugar_eliminators.cpp under the flip. SHARPENED: the message is a KERNEL TypeError (Application: argument type does not match Pi domain) on re-checking the assembled eliminator — so the choose path deep-normalizes the goal/motive (unfolding the TRANSPARENT Real.add into its Quotient.lift2 body, exposing reduced-typed parameter positions) and the result cannot re-check under opaque Real. Fix direction: the motive must be used as written (WHNF-only, opacity-respecting) — find the over-eager normalize in the choose/Exists-elim assembly; grep candidates: normalize/deepReduce calls between goal capture and Exists.eliminate assembly. **FIXED (387969f):** the real root cause was one level deeper — `isHardOpaqueConstant` returned true unconditionally, so the kernel's opacity-tolerant bridges were DEAD CODE; stored home-file constructions (Real.add's Quotient.lift body applied to Real-typed args, legal under the declaration-time engagement) then failed any consumer re-check. Fix = quotient-type aliases are soft-opaque, gated by AliasBridgeScope armed ONLY around inferType's application check (unscoped costed +26% wall + a budget blow-up in trig_bounds; scoped is at baseline). TypeError now carries the offending terms (the diagnostic that cracked it). Phase-0 bill re-measured: 7 files → 1 site (addition.math:228, (a)-class home reconciliation). OWNER REVIEW FLAG: this deliberately softens Integer/Rational/Real-class TYPE aliases at type-checking defeq — the value-definition hard-opacity predictability guarantee is untouched, but it is a reopening of the hard-for-all decision at one decision point. Also still true: the culprit definition (Real.SequenceConverges, convergence.math:56) is PLAIN — no short form, no engagement in its own declaration — so the reduced spelling enters either consumer-side (an engagement earlier in limits.math leaking past its OpacityRestoreScope) or via poisoned WHNF/defeq caches across the flip (the Makefile checker-tests note documents that disease class); instrument the consumer check at limits.math:75 under the flip first. Then either (i) close the engagement window before the declaration's type is stored, or (ii) re-alias the stored type (fold `Quotient(T,R)` back to the alias) at interface-write time — (ii) also fixes any OTHER leak source. Then re-measure the Phase-0 bill (should shrink to the (a) home-file reconciliations) |
| 10 | A8: Fold library → binder form → recognizer → series | **done** (all six steps, 2026-07-02 night) | steps 1a (42e9865) + 1b (0cb6791) done. **Step 1c mostly done (2026-07-03, 6001927 + ba48edd):** (i) `indexedAggregate` re-homed as the definitional `start = 0` instance of `Algebra.Fold` (its lemma set unchanged, so partialSum/partialProduct re-homed for free; the bridge theorem is now `done`). Fallout was small but split in two: one consumer failed the incremental build, six more only surfaced on the forced FULL rebuild — proofs leaning on the old ground-index defeq (`s(0+0)` vs `s(0)` after the Fold recursion's `f(start + c)`); all now route through `partialSum_add_one`/`one_add`/ground index equations. **Lesson: after re-defining a shared definition, validate with a full rebuild, not the incremental one — byte-identical intermediate interfaces mask transitive defeq reliance.** (ii) The `fold_operation (sym) on T := W` registry landed (W : IsMonoid certificate, operator-registry consistency check, reject-on-ambiguity, cache-serialized format v10, replay proven by the duplicate ErrorTest); Natural +/* registered in Algebra.aggregation; LANGUAGE.md/reference.md updated per C4. **Step 1c COMPLETE (2026-07-02, ec205d6 + e880592):** (iii) `Ring.Sum` retired onto the Fold: `Ring.Sum(r, f, n) := Fold(carrier, Ring.add, Ring.zero(r), f, 0, 1 + n)`, making `Real.partialSum_eq_ring_sum` (the off-by-one bridge) definitional. ring_summation.math re-proved through the Fold set — new `Ring.Sum.base` (Σ≤0 = f(0)) and `Ring.Sum.successor` (constructor-form peel) replace the lost defeq; `Algebra.Fold_rebase` (range rebase `Fold(f, 1+start, c) = Fold(f∘(1+·), start, c)`, pure index arithmetic) added to the Fold characterizing set for shift_one_plus. Fallout was small: 4 consumer files, all ground-index sites (Polynomial/commutative extensional_range+reverse base cases, multiply_laws shift_multiply zero case, ComplexNumber defining_polynomial+irreducible coefficientOf_multiply at k∈{0,1}); variable-k peels stayed by-less — the prover absorbs them through the new lemma set by search. FINDINGS: (α) citation matching works Fold-headed but NOT indexedAggregate-headed on a Ring.Sum goal (whnf exposes Fold; the lemma-side indexedAggregate doesn't unfold — cite `Algebra.Fold_*` from Sum contexts, or use term-level named-gap application à la finite_products); (β) `Fold_pointwise`-style conditional premises (`start ≤ j → …`) don't discharge from an unconditional context fact — claim the instantiated premise first; (γ) the incremental build again masked 2 of the 4 consumer breaks (ComplexNumber pair) — full rebuild caught them. (iv) `fold_operation` +/* registered for Integer/Rational/Real in their instances.math files (IsMonoid witnesses already lived there); ErrorTest fold_operation_duplicate_real proves instances-file registrations replay (22/22). **Step 2 DONE (2026-07-02 evening, ed4f510): the explicit binder form** — `sum k from LO to HI of BODY` / `product …` / `fold (op) k from … to … of …`, contextual identifiers (lookahead-claimed, `product` stays a variable name), inclusive count `(1+HI) ∸ LO` monus-free at literal LO ∈ {0,1}, half-open `E − 1` per design; carrier from the body's type through the registry. IMPLEMENTATION FINDING: the registry's `identityName` is a head-constant name only — composite identities (Natural's `1` = successor(zero)) have no one-name spelling, so the binder form re-reads the identity as a core expression from the witness TYPE and assembles the `Algebra.Fold` application in core (v1 does not coerce the carrier; explicit cast is the escape hatch). Feature test fold_binder_test + ErrorTest fold_binder_unregistered. **Step 3 DONE (ccf7273): peel-last closes by-less** — the "rewrite index" is the existing automatic-lemma index; `Fold_add_one`/`Fold_zero` are now `automatic` (Fold_one keeps its premise, stays cited), and the §12 acceptance shape verifies at Natural (times-two form) with every step by-less or IH; no perf regression on the full rebuild. **Step 4 DONE (3c0def5): the ellipsis recognizer** — `t₁ op … op ... op g` per §3 (surface anti-unification with consistent-pair anchors + the 0/1 probe; prefix verified by defeq/ground evaluation; verification failure falls through to the probe; root-divergent single-prefix identity readings compete with probe readings and overlap is the §9 ambiguity error). The 'tier-2 evaluator' need resolved recognition-side only: a SURFACE blackboard evaluator (numerals, + * − ^, monus semantics for −) plus a core evaluator (constructors + add/multiply/monus) — truth-only, no proof terms, so the prover-side `Fold(λk.k,1,3) = 6` gap remains (harmless; noted in fold_binder_test). `−` in displays = blackboard monus, desugared to Natural.monus. Full §3.3 corpus + §12 triangular acceptance in-notation as feature tests; §9 errors 1/3/4 as ErrorTests (2 subsumed by 3's message, 5 shared with the binder form). **Characterizing-equation tier added same evening (budget-capped bare-prover probe, truth-only): the geometric corpus row passes — §3.3 corpus fully covered. Step 5 (§8 printing) DONE same evening: the kernel printer compresses successor-chains to digit numerals (global readability win; one ErrorTest expectation updated) and renders faithful Folds in ellipsis form (gates: body mentions index, op is +/*, (lo,count) invertible; half-open/symbolic-monus counts stay explicit — the `E − 1` display has no core term to substitute; residual if wanted). **Step 6 DONE — A8 COMPLETE (all six steps + §3.3 corpus + §9 suite).** Series relations land per §6 v1 (sums at Real, lo ∈ {0,1}, mechanism-1 recognition, SequenceConverges/TendsToInfinity targets, contextual `infinity`, term-position/inequality errors); the desugared partial folds are definitionally the library's partialSum spelling, so notation and library hypotheses interchange. Ambiguity errors now suggest the one-more-term workaround (owner-approved). v2 doors left open per plan: extended-reals series, relations-ellipsis, descending ranges, half-open printing. Post-landing fix: prefix flattening judges mixed operators per PRECEDENCE GROUP — a multiplicative leaf inside an additive chain is legal (1*0 + 2*1 + ... resolves uniquely; the single-prefix form is the two-start probe ambiguity, ErrorTest-covered).** |

---

## Part A — the statement language

### A1. Keyword-free claims and calc (drop `claim` and `calc`)

**Motivation.** In this language every stated proposition is verified,
so the `claim` keyword adds no information. A textbook proof is
literally a sequence of stated propositions; the keyword is filler.
Similarly, a sequence of relations *is* a calc chain — blackboard
notation needs no announcement.

**Design.**
- A bare statement `P;` at statement position: elaborate the
  expression, inspect its type `T`.
  - If the expression **is a proposition** (its type is a sort of
    Prop): hand `P` to the auto-prover; on success add `P` to the
    local context.
  - If the expression **is a proof** (`T : Prop`): add `T` to the
    local context directly.
  - Anything else (e.g. an under-applied lemma of Π type): error,
    phrased as a failed claim, not as a raw elaboration error (see C2).
- A relation chain `a R₁ b R₂ c … ;` (inline or with the current
  multi-line calc layout, minus the `calc` keyword): each adjacent pair
  is a step closed by the auto-prover or by an attached `since`/`by`;
  the outer relation between the endpoints (strongest relation in the
  chain, current calc rules) enters the local context. A single
  relation is a one-step chain — `claim` and `calc` genuinely merge
  into one construct.
- **Block endings.** A block may end by restating the goal (or
  something the prover bridges to it). This is the "therefore, P. ∎"
  ending; it also makes `done` unnecessary in the common case. Keep
  `done` as a synonym for "the goal, restated" during migration.
- **Rhetorical connectives as noise words.** `then`, `hence`,
  `therefore`, `note that` parse before any bare statement and are
  semantically identical to it, except: connectives that imply
  consequence (`then`, `hence`, `therefore`) hint the prover to try
  the most recently established facts first. This gives proofs the
  rhythm of prose at zero semantic cost, and gives LLMs harmless
  places to put connective tissue they emit anyway.
- **Keep `suppose` mandatory.** Assumption is the one speech act that
  genuinely differs from assertion. Never infer it.

**Implementation notes.**
- The proposition-vs-proof dispatch is type-directed and decidable;
  the subtlety is error messaging (C2).
- `calc … as NAME` survives as `<chain> as NAME;` for the rare case a
  later step references the name textually; the lint for unused names
  stays.

**DECIDED-BY-DEFERRAL (owner, 2026-07-02):** the question of whether
`claim`/`calc` stay parse-accepted is answered by the migration
itself. Current expectation: they add no value and are removed
outright once the sweep is done. If specific proofs read worse
without them, revisit then — with the evidence in hand — and keep one
or both. Do not relitigate before the migration.

---

### A2. Statement-addressable hypotheses (names become optional)

**Motivation.** Mathematicians refer to facts by restating them ("but
m ≥ 1"), not by identifier. LLMs are good at restating propositions
and bad at inventing and consistently reusing spellings like
`mGeqNs`. Once facts can be referenced by statement, most binder
names, `as NAME` clauses, and re-derivation claims disappear.

**Design.**
- Anywhere a proof term/hypothesis is expected, a proposition in that
  position means "the in-scope fact with this statement" — matched up
  to defeq (and, after A6, up to cast normalization).
- **Ambiguity is an error.** If two distinct hypotheses match, reject
  loudly and ask for a name — mirroring the canonical-embeddings
  principle (never silently pick).
- Names remain available and are pure documentation.
- Inside `by cases` branches (A4): referencing an outer fact by name
  or statement silently transports it along the branch's case
  equation (this replaces `refining`).

**Implementation notes.** The local-hypothesis matcher in the calc
auto-prover is most of the lookup; subtree hashes give O(1) candidate
filtering. Defeq-equality of statements must use the existing kernel
defeq, not syntactic equality.

---

### A3. `suppose … for proving / for contradiction` — hypothetical reasoning

**Motivation.** "Suppose for contradiction" is negation introduction;
"to show Q, suppose P" is implication introduction. Both are distinct
speech acts from case analysis, and both should announce their exit
before the reader enters the block.

**Design.** One grammar: `suppose P for <exit> { … }`.
- `suppose P for contradiction { … }`: block must reach
  `contradiction` / `False`. Establishes `¬P`. If `¬P` closes or
  prover-bridges to the current goal (e.g. via trichotomy: goal
  `n < m`, supposition `m ≤ n`), the block is the whole proof;
  otherwise `¬P` enters the context and the proof continues. Note the
  bridge is where classical double-negation elimination silently
  enters — acceptable in this library, but the elaborator should know
  it's doing it.
  The `for contradiction` marker is **mandatory** (a block that turns
  out to be a reductio only at its last line is a bait-and-switch, and
  the marker enables the precise error "supposition was to be refuted,
  but block concludes P").
- `suppose P for proving Q { … }`: block proves Q under P; establishes
  `P → Q` in context (or closes the goal if it bridges). The
  `for proving Q` clause is **optional** — with A1's restate-the-goal
  ending, `suppose P { …; Q }` is already unambiguous — but when
  present it is checked against the block's conclusion, and it pins
  the expected type from the first line (better bridging, better
  errors). Lint: suggest adding the announcement when a block exceeds
  a length threshold.
- **`take` analog:** `take x : T for proving Q(x) { … }` establishes
  `∀x. Q(x)`. If `suppose` gets exit annotations and `take` doesn't,
  someone will trip on the asymmetry. The combined header "let x be
  arbitrary with P(x); we show Q(x)" is the two-statement sequence
  `take x : T; suppose P(x) for proving Q(x) { … }`.
- **One hypothesis per `suppose`.** Resist `suppose P, Q for proving R`
  (ambiguous between `P → Q → R` and `P ∧ Q → R`); nest instead.
- **Relation to `suffices`:** keep both, keep them crisp. `suffices P
  by <justification of P → goal>` changes the goal (backward);
  `suppose … for proving` never changes the goal, it only adds a fact
  (forward). Also add `suffices … by definition of X` to replace the
  `unfold X in (lambda …)` proof-header idiom.

---

### A4. `by cases` — the only case analysis in proofs

**Motivation.** The current zoo (`cases` with patterns, `cases … with
eq`, `cases … refining`, `decide`, proof-side if-then-else,
single-constructor `cases`) does four different jobs. Sorted
semantically: propositional split, structural split, destructuring,
and case-knowledge propagation. Structural split is a special case of
propositional split ("n is zero or a successor" *is* a proposition);
destructuring isn't case analysis at all (one branch); propagation
should be automatic, not syntax.

**Design.** The favored form generalizes to be the *only* form:

```
prove <fact> by cases {
  case <prop1>: <proof of fact under prop1>
  case <prop2>: <proof of fact under prop2>
}
```

- Proves `<fact>` in every branch, discharges exhaustiveness
  (`prop1 ∨ prop2 ∨ …`) via the auto-prover, adds `<fact>` to context.
  With A1, `prove <fact>` can be just the bare fact followed by
  `by cases`.
- **`otherwise:`** clause for the complement of the other cases —
  makes exhaustiveness trivially `P ∨ ¬P` and **deletes `decide`
  entirely**. *(Finding, 2026-07-03 night: the deletion needs a
  re-classification. The 47 library sites split into: 1 value-level
  (`List.filter`'s definition — stays, it produces data);
  proof-side WITHOUT scrutinee refinement (the goal doesn't mention
  the decision term — convert mechanically to `case P: … otherwise:`);
  and proof-side WITH scrutinee refinement — the goal mentions a
  `decide`-defined value (`min(a,b) ≤ a`), and the construct's case
  split ι-reduces the embedded `classical_decidable(P)` term, which a
  propositional `by cases` split CANNOT do: from `h : P` one cannot
  rewrite the Type-valued `classical_decidable(P)` to `yes(h)` without
  proof irrelevance. Those sites need per-function CHARACTERIZING
  LEMMAS first (`minimum_eq_left_of_le : a ≤ b → min(a,b) = a`, filter
  unfold lemmas, …) — the same boundary discipline opaque definitions
  use. Full site-by-site classification table is in the 2026-07-03
  session transcript; the refinement-free subset is the mechanical
  batch, the refinement subset is proof-engineering per definition.
  PILOT VALIDATED (37ffdc14): Rational/minimum — minimum_eq_left/
  minimum_eq_right as the quarantine boundary, the three order
  theorems converted to case/otherwise splits through the
  equations. DONE 2026-07-04: the quarantine moved one level deeper —
  generic Logic.if_positive/if_negative prove every characterizing
  equation as a one-liner — and the full sweep + parser retirement
  landed; see the ledger row 6 record.)*
- **Structural cases with witness binders:**
  `case n = successor(k) for some k: …`. The elaborator recognizes
  constructor-coverage shapes and emits the recursor. Per-inductive
  coverage lemmas (`Natural.cases_covered : ∀n. n = 0 ∨ ∃k. n =
  successor(k)`) are auto-generated at inductive-declaration time so
  exhaustiveness stays out of the trusted base.
- **Substitution rule (load-bearing):** when a case proposition is a
  constructor equation, the elaborator *substitutes* it into the goal
  and into any referenced hypotheses — not merely makes it available —
  so the kernel can ι-reduce. This is what lets `refining` and
  `cases … with eq` be deleted rather than kept as escape hatches. It
  must be reliable, not best-effort, or users will fall back to raw
  recursors.
- Exhaustiveness obligations should almost always discharge silently
  (totality/trichotomy lemmas live in the Part-B rule index); when
  they don't, the error must name the gap: "cases not shown
  exhaustive: missing m = n".
- **Induction as a variant, not a fifth construct:**

```
by induction on n {
  case n = 0: …
  case n = successor(k) for some k, with IH : P(k): …
}
```

  Same clause syntax plus a recursion permit; strong induction changes
  what IH quantifies over. Replaces `by_induction`/
  `by_strong_induction` blocks (keep the old spelling as sugar if the
  migration is heavy). The induction variable keeps its name — no
  `subject` renaming.
- **Lint (both directions):** a `cases` branch consisting solely of a
  contradiction should be a `suppose … for contradiction` folded into
  the other branch; a refuted supposition never used afterward is a
  vestigial detour.

**A4 progress (2026-07-03, 9b1b593b): `otherwise:` LANDED.** Last-arm
only (parser-enforced); hypothesis = ¬(∨ of stated cases), optional
`as h`; exhaustiveness = excluded middle BY CONSTRUCTION (elaborator
builds the EM split + injection map — no prover obligation, cannot
fail to cover). `case P:` clause spelling was already parse-accepted
(A2-era); reference.md now documents it as primary with `in (P):`
legacy. Landed alongside: a LATENT Let-lift bug the tests flushed out
(liftBoundVariables skipped Let nodes → stale indices under ζ-lets
lifted by one binder; bit any ≥3-arm by-cases whose later arms
carried claim wrappers referencing outer binders). REMAINING A4 (structural witness clause LANDED 33f3d949: `case n = k + 1
for some k [as eq]:` — ∃-hypothesis opened on the spot via one
Exists.eliminate, witness type inferred from the equation's left
endpoint or annotated `for some (k : T)`, single binder v1;
Natural.zero_or_add_one marked automatic as Natural's coverage lemma;
feature test + reference row): SUBSTITUTION RULE LANDED for witness arms (4c36aacb: the arm's goal
gets the variable substituted by the constructor form and the proof
transports back automatically — ι-reduction works, computed facts
state bare; deterministic, applies whenever the equation's left side
is a plain local variable and the goal mentions it; plain `case x = c:` arms FLIPPED too
(348e6dec) — library fallout was exactly two arms, both of which got
SIMPLER; referenced-hypothesis substitution remains open (context
facts still bridge via `by substitution`); zero_or_one_plus added as the automatic
1+k coverage lemma). coverage-lemma AUTO-GENERATION at
inductive-declaration time is still open (sketch below now partially
superseded — parser — after the arm proposition, accept `for some
<name>[, <name>…]` (names optionally `(k : T)`-annotated), store
witnessBinders on the arm; elaborator — the arm's disjunct becomes
the ∃-nest `∃k. equation` with unannotated binder types INFERRED as
the type of the equation's LHS (elaborate the surface `=`'s left side
without k; error asks for an annotation if the proposition isn't a
surface equality); arm body elaborates under extendedBinders + [k:T,
eq-hypothesis] and buildArmLambda wraps it in Exists.eliminate(T,
predicate, goal, λ k eqHyp. body, disjunctHypothesis); exhaustiveness
stays the normal prover path against existing coverage lemmas
(zero_or_add_one etc.) until per-inductive auto-generation lands), the SUBSTITUTION rule for constructor
equations (must be reliable, kills `refining`/`cases…with eq`),
induction as a by-cases variant, `decide` deletion (needs the
substitution rule + otherwise), and the both-directions lint.
The `in (P):`→`case P:` migration is DONE (d3b3655e) and the spelling
is RETIRED from the parser (post-348e6dec) with a migration-grade
error; the retirement caught 3 multi-line stragglers + 5 Test files.

**Settled: clause keyword is `case P:`, with `otherwise:` for the
complement.** (Decided July 2026; do not relitigate.) Rationale:
(1) "Case 1: m ≤ n" is the literal textbook idiom — `case` is read
correctly on first sight by mathematicians and LLMs, `in` has no
prose antecedent; (2) `case …: / case …: / otherwise:` self-labels
when skimming a long proof, and with A1 removing most keywords the
survivors carry more structural-signaling load; (3) the colon can
terminate the proposition, so no mandatory parentheses — arms with
binders stay clean (`case n = successor(k) for some k:`);
(4) consistency with the existing `by_induction` arm syntax
(`case zero:`), which matters once induction is unified as a `by
cases` variant. `case` is contextual — only recognized at
statement-head inside a `by cases` / `by induction` block — so it
needs no global reservation and cannot collide with identifiers.
The older `in (P):` experiments should be migrated, not kept as a
synonym.

**Interface interplay (Part D):** over a sealed `Natural` (D4) the
structural clause is spelled `case n = k + 1 for some k:` and routes
through the *exported* induction/coverage principle, never the
constructor; the auto-generated coverage lemmas of this section become
interface obligations. Same clause grammar, one more reason the
recursor-emission must be principle-driven rather than
constructor-driven.

---

### A5. `obtain` / `take … as` — destructuring, unified

**Motivation.** `obtain`, `choose N as h from e`, `choose N such that
P(N)`, and single-constructor/quotient `cases` all destructure. Three
overlapping spellings plus one masquerading case-analysis.

**Design (DECIDED 2026-07-02: the surviving keyword is `choose`).**
The original objection was never to a keyword — it was to `⟨w, p⟩`
angle-bracket patterns revealing that `∃`/`∧` are tuples under the
hood. The unified construct states the property as a proposition, so
both spellings were acceptable; `choose … such that` wins on prose
("choose ε > 0 such that …" is the textbook idiom for the dominant
use, existential instantiation) and on migration cost (the library
already speaks it; `obtain` is a residue). The consciously accepted
cost: the intro/elim pair is asymmetric (`witness E with P`
introduces, `choose w such that P` eliminates).

- One construct for LOGIC: `choose <witnesses> such that <property>
  [as <name>] [from <fact-or-name>];` — witness names first, property
  stated inline (and thereafter statement-addressable per A2), source
  inferred by type-match against in-scope facts when `from` is
  omitted. Example: `choose k such that m = 2 * k;` (source: the
  in-scope `2 ∣ m`). After A2, `as <name>` is pure documentation.
- Witness lists flatten **nested ∃/∧ in one step**:
  `choose m, n such that 1 ≤ m ∧ 1 ≤ n ∧ m*m = 2*(n*n) from
  solutionExists;`. Conjunctions added to context are also registered
  conjunct-by-conjunct (already implemented — keep).
- **The Prop/data boundary, made explicit:** `choose` is for `∃`/`∧`
  elimination only. A genuine data record IS honestly tuple-shaped,
  so pattern binders (`let ⟨a, b⟩ := r;`, `take x as ⟨a, b⟩`) remain
  the right destructuring there — revealing real structure leaks
  nothing false. The angle-bracket ban is a ban on spelling LOGIC as
  tuples, not on destructuring data.
- Quotient representatives get the mathematical name:
  `take x as representative (a, b);` — replacing constructor-spelled
  `cases x { | Representative.make(a,b) => … }` for the
  single-"branch" use. `by_representatives` and quotient `cases`
  forms route here.
- `obtain` parses as a linted synonym for one sweep, then is removed.

---

### A6. First-class `eventually` quantifier

**Motivation.** Every limit argument currently pays the
N₁/N₂/maximum(N₁,N₂)/re-derive-N≤m tax by hand. This is the
highest-leverage single addition for Real, PAdic, ComplexNumber — a
lightweight, hardcoded fragment of filters; the general theory is not
needed.

**Design.**
- `eventually (m). P(m)` ≡ `∃N. ∀m ≥ N. P(m)`; a first-class binder
  form the elaborator understands.
- Elaboration rules: (i) closed under ∧ — combining k eventual
  hypotheses takes max of thresholds invisibly; (ii) goal position:
  `eventually (m): { … }` / `eventually (m): <calc>` proves an
  eventual goal from eventual hypotheses, entering a scope where each
  eventual hypothesis is usable at the bound variable `m`;
  (iii) hypothesis position: `choose N such that eventually (m). Q(m)
  from h;` when the threshold itself is needed.
- Monotone: `eventually P` + `∀m. P(m) → Q(m)` (or a prover-bridgeable
  gap) gives `eventually Q`.
- Library side: define the predicate in `Real/sequence.math` (or a
  new `Logic/eventually.math` generic over an ordered index), prove
  the ∧-closure and monotonicity lemmas the elaborator emits.
- Sugar worth considering after the core lands:
  `for sufficiently large m: …` as a prose spelling of the goal form.

---

### A7. Small statement forms

- **`contradiction` terminal.** Bare `contradiction` closes any goal
  when in-scope facts are jointly absurd, via a small refutation kit:
  `x < x`, `successor(k) ≤ k`, `P` with `¬P`, constructor
  disjointness, `0 = successor(_)`, plus one round of the Part-B
  linear tier. `contradiction with <fact>` names the clashing fact
  for the reader (statement-addressable per A2). Deletes the
  "restate absurdity, then `done`" pattern.
- **`from <fact>: <instance>;`** — restate a hypothesis after
  substituting in-scope equations into it; the elaborator checks the
  stated form is reachable by rewriting. Replaces most
  `by substituting` incantations with the transformed statement
  itself on the page.
- **`by <lemma>` as a whole proof body** — the prover does the
  logical plumbing between the goal and the lemma's form: intros,
  ∃/∧ flattening, `Or.self`, argument discharge from context. Pure
  logic-shuffling with no mathematical content should never be on the
  page. (`sqrt_two_irrational := by no_double_square`.)
- **Hypothesis discharge at call sites.** When applying a lemma or an
  IH, arguments whose types are propositions already in scope (up to
  defeq / cast-normalization) are filled automatically;
  `no_smaller_solution(n, k)` supplies `n < m`, `1 ≤ n`, `1 ≤ k` from
  context. This generalizes `?` from goal-driven to context-driven.
  *Gap found and FIXED same day (2026-07-02):* citation
  premise-discharge used to scan LOCAL hypotheses only — `by
  pointwiseEqual` couldn't discharge `start ≤ start + c` even though
  `Natural.less_or_equal_add_right` is automatic. Now both discharge
  paths (`completeCitationFromBindings` step (c) and
  `inferCallWithHoles` step 5b) fall back to a budget-capped bare
  prover for fully-determined Proposition premises, gated off the
  speculative context scan (which both bounds cost and breaks the
  prover→scan→citation recursion). Feature test:
  `Test/citation_automatic_discharge_test.math`; the scaffolding
  claim in `Fold_pointwise` is gone.
- **`let` in definition bodies + module-local `open`.** Definitions
  like `bisectionStepWithDec` repeat 4-line subexpressions; allow
  `let` in definition bodies and a file-scoped
  `open Real.BisectionInterval` so a file about X can write
  `left(state)`.
- **Piecewise definitions only.** Pattern matching and if-then-else
  survive exclusively in definitions (computation), never in proofs.
  Optionally adopt piecewise syntax (`… if P(x)` / `… otherwise`) so
  definitions share the case vocabulary without sharing machinery.

---

### A8. Ellipsis notation for folds and series

(Contributed 2026-07-02; specified to implementation depth.) The
one-sentence summary: **the general term is the definition; the
prefix terms are verification.** Everything else follows from taking
that sentence seriously.

#### 1. Motivation

Mathematicians write `1 + 2 + ... + n = n(n+1)/2`, not
`Fold(+, identity, 1, n, λk. k) = n(n+1)/2`. Blackboard ellipsis is
normally too ambiguous to formalize (`2, 4, 8, ...` — powers of two or
even numbers?), but a small discipline removes the ambiguity entirely:
the term after the ellipsis, written with an explicit variable, IS the
general term; the concrete terms before the ellipsis exist only so a
reader (and the elaborator) can confirm they instantiate it. Under
that rule the notation is not a heuristic — it is a deterministic
surface form for an ordinary fold, and it can appear in statements,
in calc chains, in goals, and in printed output.

A trailing ellipsis extends the notation to infinite series
(`1/2 + 1/4 + ... + 1/2^n + ...` — the limit of the partial folds).
This is a genuine semantic extension, not sugar, and is treated
separately in §6.

#### 2. Surface syntax

##### 2.1 Finite folds

```
<t₁> <op> <t₂> [<op> <t₃>] <op> ... <op> <general>
```

- `<op>` is one binary operation, the same at every position,
  drawn from the registered fold-capable operations (§4). Mixed
  operators in one ellipsis expression are a parse error.
- `<t₁> … <tₖ>` are the **prefix terms**: concrete expressions, at
  least one, typically two or three. They contain no occurrence of
  the index variable.
- `...` is a literal token (also accept the Unicode ellipsis `…`).
- `<general>` is the **general term**: an expression containing at
  least one variable that does not occur in the prefix terms. It is
  the anchor of the whole notation.

Examples that must parse and elaborate:

```
1 + 2 + ... + n
1 + 2 + 3 + ... + n
2 + 4 + ... + 2 * n
1 + 3 + 5 + ... + (2 * n - 1)
1 * 2 * ... * n                       -- factorial as a fold
f(1) + f(2) + ... + f(n)
1/1 + 1/2 + ... + 1/n                 -- general term 1/n, index n itself
a(0) + a(1) + ... + a(n)              -- starting index 0
x + x^2 + ... + x^n                   -- index in the exponent
```

##### 2.2 Infinite series (trailing ellipsis)

```
<t₁> <op> <t₂> <op> ... <op> <general> <op> ...
```

Same shape, with a final `<op> ...` after the general term. See §6
for the (restricted) contexts where this form is legal.

##### 2.3 The explicit form

The ellipsis form is sugar over an explicit surface form, which must
exist independently — as the escape hatch when inference fails or is
ambiguous, and as the documented meaning of the sugar:

```
sum k from 1 to n of f(k)
product k from 1 to n of f(k)
fold (<op>) k from i₀ to n of f(k)      -- general registered op
```

(Exact keyword spelling is a surface decision for the implementer to
propose; the requirement is that an explicit binder form exists, is
documented in LANGUAGE.md, and that the ellipsis form is defined by
translation into it.)

#### 3. Recognition and elaboration algorithm

(DECIDED 2026-07-02, replacing the earlier fresh-variable/probe
draft after working the example corpus of §3.3.) Two complementary
mechanisms, both deterministic, tried in order:

**Mechanism 1 — anti-unification (structural anchors, symbolic
bounds).** Match the LAST prefix term `tₖ` against the general term
`g` (it is the term most likely to share `g`'s shape). The positions
where they differ must all hold one consistent pair
(`⟨value at tₖ⟩`, `⟨value at g⟩`) =: (jₖ, hi); the term function `f`
is `g` with those positions abstracted; `lo := jₖ − (k−1)` (numeral
arithmetic, k small). Then verify the earlier prefix terms downward:
`t_{k−1} ≡ f(lo + k − 2)`, …, `t₁ ≡ f(lo)`, each by defeq → tier-2
ground evaluation → **one pass of registered characterizing
equations** (the rewrite index; bounded and index-driven, not search
— this is what lets `x ≡ x^1` and `1 ≡ x^0` verify against opaque
`power`). This mechanism is the one-metavariable case of
`matchAgainstPattern` and handles symbolic bounds
(`a(m) + a(m+1) + … + a(n)` → lo = m), shared-parameter indices
(`binomial(n,0) + … + binomial(n,n)` — no fresh variable exists),
and ground ranges (`1 + 2 + … + 10`).

**Mechanism 2 — the 0/1 evaluation probe (arithmetic anchors).**
When anti-unification fails structurally (`2 + 4 + … + 2*n`: the
numeral `2` is not literally `2*⟨_⟩`), abstract `g` over its fresh
variable and test `f(0) ≡ t₁` and `f(1) ≡ t₁` by ground evaluation,
verifying the rest of the prefix for whichever start matches.
Starting indices beyond {0, 1} are not probed in v1.

**Ambiguity is a loud error** at every stage, per the house rule:
two consistent (lo, hi) readings, or both probe starts matching
(possible with a single prefix term: `0 + … + k*(k−1)` matches
lo = 0 and lo = 1), name every surviving candidate and point at the
explicit binder form. Zero candidates: "general term does not
generate the prefix", showing the nearest-miss `f(lo), f(lo+1)`
against the written terms.

**Upper bounds and the half-open rule.** The written general term is
the last term, so the range is inclusive lo..hi with **count
`(1 + hi) ∸ lo`** — monus, whose clamping gives exactly the right
empty range when a symbolic lo exceeds hi. One special case, decided:
an upper bound of the syntactic shape `E − 1` is **half-open
notation** — range [lo, E), count `E ∸ lo` — so that
`a(0) + a(1) + … + a(n-1)` denotes the empty sum at `n = 0` (the
naive inclusive reading gives count 1 there: `1 + (0∸1) ∸ 0 = 1`,
which is wrong). Literal lo ∈ {0, 1} yields monus-free counts
(`1 + n` and `n`); symbolic lo keeps the monus in the count slot
only, and peel lemmas surface `lo ≤ hi` side conditions exactly
where the mathematics needs them.

##### 3.1 Upper bound, precisely

The written general term is the fold's **last term**, so the fold's
range is `v = i₀ … V` where `V` is the value of the index variable as
it appears free in the surrounding statement. Concretely: in
`1 + 2 + ... + n`, the index variable is `n` itself and the range is
`1 … n`. In `1 + 3 + ... + (2*m - 1)`, the index variable is `m`, the
range is `1 … m`, and the term function is `λm. 2m − 1` — note the
**stride comes for free**: no stride-inference machinery exists or is
needed, because anchoring on the general term makes "odd numbers" a
term function over a unit-step index. Implementers must NOT add
consecutive-difference stride guessing; it reintroduces exactly the
ambiguity this design eliminates.

##### 3.2 Degenerate ranges

The displayed prefix does not constrain the range. `1 + 2 + ... + n`
shows three terms but denotes `Fold(+, id, 1, n)`, which is
meaningful at `n = 1` (one term) and `n = 0` (empty fold = the
operation's identity, so `0`, and the identity `0 = 0·1/2` still
holds). Document this in LANGUAGE.md — it occasionally surprises —
and make the pretty-printer's behavior at small symbolic ranges
consistent (§8).

##### 3.3 Example corpus (the seed for the feature-test file)

| expression | mechanism | reading |
|---|---|---|
| `1 + 2 + ... + n` | anti-unify (`1` vs `n`) | lo 1, hi n, f = id |
| `a(0) + a(1) + ... + a(n)` | anti-unify | lo 0, hi n |
| `a(m) + a(m+1) + ... + a(n)` | anti-unify | symbolic lo = m; count `(1+n) ∸ m`, empty when m > n for free |
| `a(0) + ... + a(n-1)` | anti-unify + half-open rule | count n; empty at n = 0 |
| `2 + 4 + ... + 2*n` | probe (f(1) = 2) | lo 1, hi n |
| `1 + 3 + 5 + ... + (2*n - 1)` | probe (monus ground-evaluates) | lo 1, hi n |
| `1/1 + 1/2 + ... + 1/n` | anti-unify (`1/1` vs `1/n`) | the written `1/1` is what makes the shape visible — the discipline matches practice |
| `x + x^2 + ... + x^n` | anti-unify on `x^2`, verify `x ≡ x^1` via characterizing equation | lo 1, hi n |
| `binomial(n,0) + ... + binomial(n,n)` | anti-unify (no fresh variable exists) | lo 0, hi n, f = λv. binomial(n,v) — the binomial-theorem display |
| `1 + 2 + ... + 10` | anti-unify | ground range; harmless, allowed |
| `a(1,1) + ... + a(n,n)` | anti-unify, consistent pair at both positions | the diagonal, λv. a(v,v) |
| `n + (n-1) + ... + 1` | — | rejected in v1 by the downward verification (t₁ ≠ f(lo)); see §10 for the future-work door |

#### 4. Elaboration target and library work

The ground-truth form is a single generic fold over a registered
operation:

- **DECIDED (2026-07-02): `Fold(op, identity, f, i₀, count)` — lower
  bound plus COUNT, recursion on the count.** This is the only
  convention with no monus and no side conditions in the definition
  or the characterizing lemmas (peel-last
  `Fold(f, i₀, 1+c) = Fold(f, i₀, c) op f(i₀+c)`, peel-first
  `Fold(f, i₀, 1+c) = f(i₀) op Fold(f, 1+i₀, c)`, empty
  `Fold(f, i₀, 0) = identity` — all unconditional), while keeping
  `i₀` as DATA in the term, which makes the §8 printer trivial
  (read i₀ and count off the term) instead of pattern-extracting
  offsets from a lambda body. The display semantics stay inclusive
  `f(i₀) op … op f(hi)`; the count is the kernel spelling only.
  Rejected alternatives, for the record: a two-ended inclusive
  primitive (monus or `i₀ ≤ N` guards infect every lemma, and the
  half-open rule of §3 has no home — it gets `a(0)+…+a(n-1)` wrong
  at n = 0); offset-in-the-term-function over the existing
  count-only fold (works, but buries i₀ in a lambda the printer
  must reverse-engineer forever); Ring.Sum's inclusive-from-f(0)
  form (cannot represent the empty range at all — it is the problem,
  not a candidate). `Algebra.indexedAggregate` becomes the `i₀ = 0`
  instance; `Real.partialSum`/`partialProduct` re-home mechanically;
  `Ring.Sum(f, n)` retires as `Fold(f, 0, 1 + n)`, turning the
  off-by-one bridge lemma into a definition.
- **Fold-capable operation registry.** An operation qualifies by
  registering (op, identity, associativity proof). `+` and `*` on
  each numeric carrier register at instance-declaration time.
  Registration without an identity/associativity certificate is an
  error. Two registrations for the same operator symbol on the same
  carrier: declaration-time error (canonical, never searched).

  *Step-1c design note (2026-07-02).* The certificate is exactly
  `IsMonoid(carrier, op, identity)` (Algebra/monoid.math — assoc +
  both identity laws, precisely what the Fold lemma set consumes as
  per-lemma hypotheses today). Surface form mirrors the `operator`
  declaration, since the key is the same (symbol, carrier) shape:
  `fold_operation (+) on Real := Real.add_is_monoid;` where the RHS
  names a proof of `IsMonoid(Real, Real.add, Real.zero)`. Elaborator
  checks at declaration time: (1) the RHS type is IsMonoid applied to
  (carrier, op, identity); (2) the symbol resolves to that same `op`
  on that carrier in the operator registry; (3) the (symbol, carrier)
  key is unregistered (reject-on-ambiguity, like the instance
  registries). Stored as `foldOperationRegistry : (symbol, carrier) →
  {operationName, identityName, monoidWitnessName}` on Environment,
  serialized in the cache like `instanceRegistrations`. Consumers are
  steps 2–4 (binder form, rewrite-index registration, recognizer);
  step 1c itself validates via declaration-time error tests + a
  Test/ feature file exercising registration for +/* on the numeric
  carriers.
- **Characterizing lemmas, registered in the rewrite index** — this
  is what makes the notation usable in proofs rather than merely
  pretty in statements:
  - `Fold(op, f, i₀, i₀) = f(i₀)` (singleton)
  - `Fold(op, f, i₀, N+1) = Fold(op, f, i₀, N) op f(N+1)` (peel last)
  - `Fold(op, f, i₀, N) = f(i₀) op Fold(op, f, i₀+1, N)` (peel first)
  - `Fold(op, f, i₀, i₀−1) = identity` (empty range, however ranges
    are represented)
  - index-shift / split-range lemmas as needed by the library.

  With these in the index, the calc step every induction proof needs
  closes by-less. **Acceptance test** (must verify with no `since` on
  the first step):

  ```
  1 + 2 + ... + (n + 1)
     = (1 + 2 + ... + n) + (n + 1)
     = n * (n + 1) / 2 + (n + 1)        -- IH, statement-addressable
     = (n + 1) * (n + 2) / 2            -- ring
  ```

  The proof reads in the same notation as the statement. That is the
  whole payoff; if this calc needs annotations, the feature has
  failed its purpose.

#### 5. Where the notation may appear

Finite ellipsis folds are ordinary terms: legal in theorem
statements, definitions, calc steps, `suppose` headers, anywhere a
term of the carrier type is legal. They are pure sugar — no
proposition is generated by the notation itself beyond the shape
verification at elaboration time (which is a compile-time check, not
a proof obligation).

#### 6. Trailing ellipsis: infinite series

A trailing `<op> ...` changes the meaning from a value to a **limit
of partial folds**, and limits are partial — `1/2 + 1/4 + ... +
1/2^n + ...` has a value; `1 + 1/2 + ... + 1/n + ...` does not. To
keep partiality out of the term language, version 1 restricts the
form:

**Rule: an infinite-series expression is legal only as one full side
of a relation, and the whole relation elaborates as a proposition.**

- `t₁ op … op g op ... = S` elaborates to
  `ConvergesTo(λN. Fold(op, f, i₀, N), S)`.
- `t₁ op … op g op ... = infinity` elaborates to
  `TendsToInfinity(λN. Fold(op, f, i₀, N))`.
  `infinity` (and `∞`) is a **contextual keyword** legal only in this
  position; it is never a term of Real, and using it elsewhere is a
  parse error with a message saying so.
- Both target predicates are library definitions on sequences
  (`Real/sequence.math` has the substrate; `eventually` from A6 is
  the natural vocabulary for their definitions).
- Consequences of the restriction, stated so the implementer doesn't
  "fix" them: `(1/2 + 1/4 + ...) + 1` is illegal in v1 (no series in
  term position); `... = S` with `S` itself a series is illegal
  (one side only); inequalities `t₁ + ... + g + ... ≤ B` are
  **rejected in v1** (DECIDED 2026-07-02 — see the v2 note below for
  why the question largely evaporates later).

**Deferred (v2) — and the extended-reals direction (owner,
2026-07-02).** The v2 design should be built on a two-point
completion ℝ̄ = ℝ ∪ {−∞, +∞} (order and limits only — ℝ̄ is not a
ring; `ring`/`field` never touch it; ±∞ case splits are A4 `by
cases` + tier-4 food). What it buys, precisely:
- **One limit predicate instead of two.** `ConvergesTo` and
  `TendsToInfinity` unify into convergence in ℝ̄'s order topology;
  `… = infinity` stops being a keyword hack and becomes an ordinary
  equation inside the predicate (`infinity` is just a term of ℝ̄).
- **On the monotone/nonneg fragment the totality questions
  evaporate**, exactly as hoped: a series with eventually-nonneg
  terms ALWAYS has a value in [0, +∞] (monotone convergence), so
  nonneg series can eventually be a TOTAL function into [0, ∞] —
  term position legal with NO convergence side conditions on that
  fragment (the measure-theory move; cf. mathlib's ℝ≥0∞ experience,
  where this totalization is what makes series automation pleasant).
  The signed case then routes through absolute convergence. On this
  fragment the candidate inequality readings (∀N over partial sums /
  limit ≤ B / limsup ≤ B) all coincide — which is why deciding the
  v1 reading would have been wasted work. Note this needs only
  ADDITION and sup on [0, ∞], both total without any convention.
- **ℝ̄ arithmetic stays PARTIAL (owner, 2026-07-02).** No `0·∞ = 0`
  convention — it is as unmathematical as `1/0 = 0`, which this
  library already refuses. Undefined combinations (`∞ − ∞`, `0·∞`,
  `∞ + (−∞)`) carry proof obligations that the operation makes
  sense, in the same spirit as honest division's nonzero
  obligations — and dischargeable by the same machinery: a tier-4
  `IsFinite`-style judgment family mirrors the structural `nonzero`
  tactic, so the obligations stay off the page in the common cases.
  Accepted cost, stated honestly: more side conditions than the
  convention route (mathlib chose totality for a reason), but the
  house already made this trade for `/` and built the discharge
  machinery that makes it pleasant; consistency wins.
- **What does NOT evaporate:** oscillating series
  (`1 − 1 + 1 − …`) have no limit even in ℝ̄, so a single total
  "value of any series" remains impossible — defining it as limsup
  would make `1 − 1 + 1 − … = 1` a true equation, which is worse
  than partiality. Hence the trailing-ellipsis form stays a
  RELATION-position proposition in v2 too; what changes is that the
  predicate is one, the ±∞ equations are honest, and the nonneg
  fragment gets total term-position sums.
- Implied library ladder: ℝ̄ with order + the ℝ ↪ ℝ̄ embedding
  packet (B3), limsup/liminf (independently wanted for analysis),
  the unified limit predicate, then [0,∞]-valued total sums.
  Convergence side conditions for the general signed term-position
  case stay a tier-4 judgment family
  (`(ConvergesTo, power)` geometric rules etc.) as previously
  sketched. Do not build any of this in v1.

#### 7. Interaction with the rest of the plan

- **Tier-2 dependency.** Steps 3–4 of the recognition algorithm are
  ground evaluation — precisely Part B's tier 2. Implement B1/B2's
  evaluation tier before this feature; the shape check then costs
  nearly nothing and shares its code.
- **Rewrite index (B2/B4).** The characterizing lemmas of §4 register
  exactly like any other rewrite/monotonicity lemma. No new index
  machinery.
- **Keyword-free calc (A1).** Ellipsis terms inside relation chains
  must parse unambiguously: the chain separators are the relations
  (`=`, `≤`, …) and the ellipsis operator is arithmetic (`+`, `*`),
  so there is no grammar conflict, but add parser tests for an
  ellipsis fold as a calc endpoint on both sides.
- **Statement-addressable facts (A2).** A fact stated with ellipsis
  notation and the same fact stated with explicit `Fold` must be the
  same fact for context lookup — guaranteed if the sugar desugars at
  parse/elaboration time and hashing happens on kernel terms (it
  does).
- **`--explain` / errors (C2).** Every error from §3 must show the
  candidate term function and the evaluated prefix side by side.

#### 8. Printing (round-trip)

Goals, errors, and `--explain` output involving `Fold` should print
in ellipsis form whenever a faithful rendering exists — users write
in this notation and must not debug in another one. Printing rule:
render `Fold(op, λv. g, i₀, N)` as `g[v↦i₀] op g[v↦i₀+1] op ... op
g[v↦N]` with the first two terms ground-evaluated for display, i.e.
`1 + 2 + ... + n`, provided the evaluated prefix terms are small
literals; otherwise fall back to the explicit binder form. Never
print a prefix the recognizer of §3 would not re-accept
(round-trip property: parse(print(e)) elaborates to e). Add a
round-trip test over the library's fold expressions.

#### 9. Errors (all must exist, with these shapes)

1. Mixed operators: "ellipsis requires a single operation; found `+`
   and `*`".
2. No index candidate: "general term contains no variable absent
   from the prefix; write the explicit form".
3. Prefix mismatch: "general term `2*k` with start `k = 1` generates
   `2, 4, 6, ...` but the prefix is `2, 4, 7`" — show generated vs
   written.
4. Ambiguity: "ambiguous between index `m` (start 1) and index `j`
   (start 0); write the explicit form" — list every surviving
   candidate.
5. Unregistered operation: "`⊕` is not registered as fold-capable;
   register (op, identity, associativity) or use explicit recursion".
6. Series in term position (v1): "an infinite series may only appear
   as one side of a relation".
7. `infinity` outside a series relation: "'infinity' is only legal as
   the right-hand side of a series relation".

#### 10. Non-goals for v1 (do not build)

- Stride inference from consecutive differences (§3.1 — the general
  term already carries the stride).
- Series in term position; algebra on series expressions (§6, v2).
- Double/nested ellipses (`(1+..+n) * (1+..+m)` is fine — two
  independent folds — but `a(1,1) + ... + a(n,m)` matrix-style is
  out).
- Ellipsis over **relations** (`a(1) ≤ a(2) ≤ ... ≤ a(n)` as sugar
  for a monotonicity ∀). This is a genuinely good future feature and
  composes with B4, but it elaborates to a ∀-statement, not a fold —
  a separate plan item, not a rider on this one.
- **Descending ranges — not in v1, door explicitly open (owner,
  2026-07-02).** The motivating display is the polynomial:
  `a(n)*x^n + ... + a(1)*x^1 + a(0)*x^0`, and the harder textbook
  form `a(n)*x^n + ... + a(1)*x + a(0)`, whose trailing terms only
  match the general term through characterizing equations
  (`x^1 = x`, `a(0)*x^0 = a(0)` via power_one/power_zero/multiply
  laws) — i.e. the same normalization-assisted verification §3
  already uses, pointed at the tail instead of the head. Note the
  kernel form doesn't care about direction (a descending display is
  `λj. f(hi ∸ j)` reindexing — recognizer/printer work only), so
  nothing decided now forecloses it. In v1, reject with a clear
  message; the §3 downward verification already rejects it
  automatically (t₁ ≠ f(lo)).

#### 11. Suggested implementation order

**Groundwork survey (2026-07-02).** The generic fold largely EXISTS:
`Algebra.indexedAggregate(A, op, identity, s, n)` (aggregation.math:32)
is carrier-generic with loose `(op, identity, laws)` arguments, and
`Real.partialSum`/`partialProduct` are already thin instances of it;
`Ring.Sum` (ring_summation.math:19) is a second, bundled fold with an
INCOMPATIBLE range convention (inclusive `0..n` vs count-based `k<n`;
bridge lemma `Real.partialSum_eq_ring_sum` carries the off-by-one).
Step-1 work is therefore: (a) unify on one convention with a genuine
`i₀` lower bound (no existing fold has one); (b) add the missing named
characterizing lemmas — singleton and peel-first exist only on
`Ring.Sum` (`Ring.Sum.shift`), empty-range is definitional-but-unnamed
everywhere; peel-last (`_add_one`) and split exist on all three;
(c) build the fold-capability registry on the `instance` precedent
(`instance CommutativeRing.is_ring`, keyed by carrier — see
commutative_ring_algebra.math:69) — no `(op, identity, associativity)`
registry exists today, laws travel as per-lemma hypotheses;
`congruence_under_binder Ring.Sum := Ring.Sum.extensional`
(ring_summation.math:64) is the precedent for registering fold lemmas
into elaborator machinery. ~19 files consume partialSum/Product, ~15
consume Ring.Sum — the re-expression sweep is real but bounded.

1. Generic `Fold` + operation registry + characterizing lemmas in the
   library; re-express `partialSum`/`partialProduct`/`aggregation`
   over it. (Pure library work; independently valuable.)
2. Explicit binder form (`sum k from … to … of …`) in the surface
   language, elaborating to `Fold`.
3. Register characterizing lemmas in the rewrite index; make the §4
   acceptance calc close by-less **using the explicit form**.
4. Ellipsis recognizer (§3) desugaring to the explicit form; error
   suite of §9.
5. Printer round-trip (§8).
6. Trailing-ellipsis series relations (§6 v1).

Each step lands with LANGUAGE.md/reference.md updates and a
`library/Test/` feature file, per C4.

#### 12. Acceptance criteria

- `theorem Natural.triangular_sum : (n : Natural) → 1 + 2 + ... + n =
  n * (n + 1) / 2` states, and its induction proof's peel-last calc
  step closes with no `since` (§4).
- `1 * 2 * ... * n` proves equal to `factorial(n)` by induction with
  the same by-less peel step.
- `1/1 + 1/2 + ... + 1/n + ... = infinity` states and elaborates to
  `TendsToInfinity` of the harmonic partial sums (proving it is
  library work, not part of this feature's acceptance — and the
  library already proves harmonic divergence, so the existing theorem
  can be restated in the new notation as the test).
- Every error in §9 is exercised by an `ErrorTest/` file.
- Round-trip test passes over all fold expressions in the library.

---

## Part B — the auto-prover: tiered, deterministic discharge

**Constraint (hard-won):** global search over imported theorems was
removed for performance. Do not reintroduce it under another name.
The replacement insight: breadcrumb claims fall into a few *judgment
families*, each with a deterministic, syntax-directed procedure linear
in the term. Search appears only in the last, budgeted tier.

### B1. Tier architecture

Cheapest first, strict budgets, first success wins:

| Tier | Procedure | Cost |
|------|-----------|------|
| 0 | Context lookup (stated + derived facts; conjunct index) | O(1) via hash-indexed context |
| 1 | Defeq / reflexivity | existing |
| 2 | Ground evaluation (literal comparisons, arithmetic) | linear |
| 3 | Cast normalization (B3), then retry 0–2 | linear |
| 4 | Sign/judgment recursion (B2) | linear, no backtracking |
| 5 | Single-position-diff rewrite index (existing) — **extended to order relations** (B4) | existing |
| 6 | Budgeted linear-arithmetic combiner over context facts | metered |

- **No separate memo cache — derived facts enter the local context.**
  Side conditions repeat constantly (`0 ≤ secondSum` should be proved
  once), but a dedicated cache would be a shadow context with its own
  scope stack and hash index. Instead: every fact the prover
  discharges is recorded as an **anonymous fact in the local
  context**, and the **hash index over the context is a general
  feature** — the same structure serves A2 statement-addressable
  references, tier-0 lookup, conjunct-splitting, and reuse of
  discharged side conditions. One blackboard; stated and derived
  facts live on it identically; scope safety is inherited from the
  context's existing block discipline for free.
  - **Insertion depth — one rule:** a derived fact is inserted at the
    level of the deepest local binder/hypothesis its proof term
    references. **Closed goals are the degenerate case, not an
    exception:** a proof with no local dependencies falls through
    every block and the theorem's parameters to the enclosing
    environment — the same place declared theorems live — so tier-2
    facts like `Rational.zero < Rational.one` persist file-wide, and
    `.mathv` persistence is just the environment's existing
    serialization applying to one more entry. ("Closed" means closed
    over *locals*; references to global constants are satisfied at
    the environment level by construction, and `.mathv` is per-file
    with its imports, so persistence stays coherent.)
  - **Staging:** the full dependency-depth scan is not
    launch-blocking. Ship with two insertion levels — current depth,
    or environment when the proof is locally closed (the scan that
    finds nothing, trivially cheap) — and generalize to exact-depth
    insertion later if profiling shows sibling-branch re-derivation
    matters. Re-derivation is cheap anyway: tiers 0–4 are linear and
    deterministic. Same rule throughout, implemented at increasing
    resolution.
  - **Dedup:** never insert a derived fact whose statement is
    hash-equal to an existing context entry, so derived facts cannot
    create A2 ambiguity. (For Props, proof irrelevance would make a
    duplicate harmless anyway; not inserting is cleaner.)
  - **Visibility:** the context now holds facts the user never
    wrote. Everything that prints context — error breadcrumbs,
    `--explain`, the goal-state printer — must tag derived facts and
    fold them by default, or failing proofs drown in `0 ≤ …` trivia
    that was never on the page.
  - **Representation note:** hash lookup must respect binder depth —
    with de Bruijn indices, equal hashes at coincidentally equal
    depths can denote different statements. Keying within the
    context's scope structure (a per-level map, not one flat map)
    handles this implicitly; alternatively hash a level/free-variable
    rendering.
- Tiers 0–4 are deterministic and linear — the latency cliff of
  global search structurally cannot recur. Tier 6 is the only genuine
  search and it is metered.

**Tier-0 implementation staging (design note, 2026-07-02).** The
obstacle: `localBinders` is a plain `std::vector<LocalBinder>` passed
by value/reference through every elaboration path — there is no
single push/pop chokepoint to hang an incremental index on, and
`collectLocalBinderFacts` (prover.cpp) currently rebuilds the fact
list, WHNF-decomposing every conjunction hypothesis, on EVERY
auto-prover call (the measured dominant cost in ε-δ files). Staged
plan that avoids an elaborator-wide refactor:
1. **Memoized fact collection, keyed by binder-prefix hash.** Compute
   a running order-sensitive hash of the binder types; cache
   decomposed fact lists per (depth, prefix-hash). Binder vectors
   grow monotonically within a block, so a cache hit on a prefix
   reuses its facts and decomposes only the new binders. Pure
   retrofit inside `collectLocalBinderFacts`; no caller changes.
2. **Statement-hash lookup map on top** of the cached fact list
   (statement hash → fact), giving O(1) tier-0 lookup — and this
   same map IS the A2 statement-address structure and the
   derived-fact blackboard's spine (one structure, three consumers,
   as designed above). Respect the de Bruijn depth caveat: key
   within the per-depth cache, not one flat map.
3. **Push/pop discipline (RAII context object) only if profiling
   still demands it** after 1–2 — i.e., only if hashing the binder
   vector itself shows up hot. Do not start with the invasive
   refactor.

*Correction (2026-07-02, A/B-measured):* stage 1 was implemented and
REVERTED — it has zero effect, because the 2026-06-27 perf session
(context memoization + fused binder opening, see the
`verification_perf_autoprover_scan` memory) already removed the
scan's hot cost; the fact-list rebuild itself is cheap. So tier-0's
PERF motivation is already satisfied; what remains valuable here is
stage 2 — the statement-hash lookup structure — justified as the A2
statement-address spine and the derived-fact blackboard, not as an
optimization. Build it when A2 lands, not before.

### B2. The judgment-rule index (tier 4)

- Generalize the rewrite-lemma index: at declaration time (and
  `.mathv` load), lemmas whose conclusion has shape `0 ≤ f(…)`,
  `0 < f(…)`, `f(…) ≠ 0`, `IsNonneg(f(…))`, etc. self-register in a
  bucket keyed by **(judgment, head symbol of subject)**.
- Discharge is recursion on the goal's subject term: at each node,
  dispatch by head symbol to the (single) registered rule, recurse on
  its premises. Lean's `positivity` design; one pass, no backtracking.
- **Admission criterion (the load-bearing constraint):** a lemma
  registers as a rule only if each premise's subject is a **proper
  subterm** of the conclusion's subject. This guarantees structural
  descent — a procedure, not a search. Lemmas failing the criterion
  keep their explicit `since`, and each such survivor is a diagnostic
  pointing at a lemma worth restating in dischargeable form.
- **Conflicts are declaration-time errors:** two rules for the same
  (judgment, head) pair → reject, mirroring the two-embeddings-reject
  principle. Dispatch stays choice-free.
- Also index totality/trichotomy lemmas (`a ≤ b ∨ b < a`, constructor
  coverage) under a coverage judgment — this is what makes A4's
  exhaustiveness obligations discharge silently.

**v1 landed (2026-07-02, commit 21b1cb4).** Judgments: `0 ≤ f(…)`,
`0 < f(…)`, `f(…) ≠ 0` over Constant-headed or numeral subjects;
registration hooks `registerAlgebraicShape` (so seeding and fresh
declarations share one funnel); admission = sign-judgment premises on
bare lemma binders; conflicts first-wins-and-counted (the
declaration-time error waits for a library duplicate cleanup); tactic
sits after `localFactExactMatch`; `MATH_SIGN_INDEX_DEBUG` traces rule
firings. Feature test: depth-3 recursion through an opaque wrapper.
Measured day-one yield (classifier, library-only): closes-today
36.2% → 39.1% (+180 sites); tier-4 sign 312 → 263, sign-cast
217 → 147. The residue decomposes as: (a) ~90 sites of
IsNonneg-form plumbing (`IsNonneg_of_LessOrEqual_zero` and kin) —
extend the judgment vocabulary to unary predicates and route across
the bridge lemmas; (b) the sign-cast bucket, blocked on tier 3
(subjects carrying non-numeral casts don't match rules stated on the
bare carrier); (c) `f(…) = 0` zeroness equalities (the classifier
counts them sign-shaped; a `zero` judgment family would take them);
(d) whatever the conflict counter is masking — audit it.

### B3. Cast normalization (tier 3)

- Each registered canonical embedding carries a **morphism packet**:
  preservation lemmas for `0`, `1`, `+`, `*`, `≤`, `<` (and
  reflection where true). Declaring an embedding without its packet
  is a warning; the packet slots are named so the elaborator finds
  them without search.
- A `norm_cast`-style pass rewrites goals/hypotheses to canonical cast
  placement; afterwards other tiers operate as if casts weren't
  there. Canonicity of embeddings ⇒ no choice points ⇒ deterministic.
- This alone collapses chains like
  `IsNonneg((m : Rational)) → 0 ≤ (m : Rational) → (0:Real) ≤ (m:Real)`
  to nothing.

### B4. Order automation at parity with equality (tier 5 extension)

- Index monotonicity lemmas (`Π…, a ≤ b → f(…a…) ≤ f(…b…)`) by head
  symbol exactly as rewrite lemmas are indexed; single-position-diff
  `≤`/`<` calc steps then close by-less, the way `=` steps already do.
- Result: in analysis files, `since Rational.add_preserves_LessThan`
  and kin disappear from calc chains; `since` survives only where it
  carries mathematical content — which is the explicitness philosophy,
  not a compromise of it.

### B5. Explainability and regression safety

- `--explain` mode: for any silently discharged obligation, print the
  tier and rules that fired. Failure messages name the gap in the
  recursion: "couldn't establish 0 ≤ firstSum: no (0 ≤ ·, partialSum)
  rule registered" / "premise 0 ≤ s(k) unresolved".
- **Materializer** (inverse of the redundancy lint): a tool that
  rewrites a file inserting the explicit `since` clauses the prover
  found, so a proof can be pinned down against future prover changes.
  With more elaborator search, proof-maintenance brittleness is the
  real risk (never soundness — everything still emits kernel-checked
  terms); the materializer is the mitigation.
- **Validation before building:** instrument the current library's
  `claim … since` lines and classify by absorbing tier. Expectation
  from review: tiers 2–4 absorb well over half, dominated by
  partialSum/power/abs sign lemmas and to_real transport. Build this
  classifier first; it prioritizes everything else in Part B.

**Findings (2026-07-02 — the classifier ran over the full library).**
Instrument: `MATH_CLASSIFY_HINTS=1` (hooks at the hinted-claim and
hinted-calc-step elaboration sites; shape features + a budget-capped
speculative by-less re-proof), aggregated by
`scripts/hint_classification_report.py`. **5807 hinted sites**
(2811 `since` / 2996 `by`; 3387 claims / 2420 calc steps), bucketed
first-match-wins:

| bucket | sites | share | dominated by |
|---|---|---|---|
| closes-today (budget-capped bare re-proof succeeds) | 2101 | 36.2% | inline terms, `LessThan.weaken`, `IsNonneg` bridges, bare `IH` |
| B4 order calc step | 305 | 5.3% | `add_preserves_LessOrEqual/LessThan` family, `multiply_by_nonneg`, `triangle_inequality` |
| tier 2 ground | 345 | 5.9% | `two_positive`, `zero_less_one`, `to_real.positive_preserves`, `False` |
| tiers 3+4 sign-through-casts | 217 | 3.7% | `divide_positive`, `absolute_value_nonneg`, `factorial_cast_positive` |
| tier 4 sign | 312 | 5.4% | `IsNonneg` bridges/`IsNonneg.multiply`, `modulus_nonneg`, `square_IsNonneg` |
| tier 3 cast | 473 | 8.1% | cast-bearing equalities/existentials, `sign_split` |
| **absorbable total** | **3753** | **64.6%** | |
| unabsorbed | 2054 | 35.4% | inline sub-proof terms (586), `IH` citations, abstract-ring plumbing, `le_through_max_*` |

Reading, against the expectations above:
- **The tier-2–4 + B4 prediction is confirmed in composition**: the
  sign/cast buckets are dominated by exactly the predicted families
  (divide/abs/factorial-cast positivity, `to_real` transport), and
  the B4 bucket is almost entirely `add_preserves_*` monotonicity —
  but their combined share is ~23%, not "over half". The bulk
  absorber is **closes-today at 36%**: hints today's prover already
  discharges near-instantly. Under C1's role split those become
  lint-removable citations wholesale — so C1 + the lint, not new
  tiers, deletes the single biggest slice.
- **The unabsorbed third decomposes on sight**: inline `<term>`
  sub-proofs (the hint IS the proof — correctly on the page), `IH`
  citations (A2 statement-addressability's target), abstract-carrier
  associativity/commutativity plumbing (`ring`'s domain, invisible to
  head-symbol indexes), and `Natural.le_through_max_*` threshold
  juggling (A6 `eventually`'s target, 28 sites in this bucket alone).
- **Caveats**: buckets are shape-classified upper bounds (tier 4's
  yield depends on B2 rule coverage); generic-relation calc steps
  (`∣`/`⊆`) are labeled `=` by the instrument; `closes-today` uses
  the 1000-step redundancy budget, so slower-but-provable sites land
  in other buckets.
- **Priority confirmed with one amendment**: B3+B2 first (1002
  sign/cast sites), then B4 (305 steps, a dozen lemma families to
  index), then the tier-2 evaluator (345). The amendment: schedule
  the C1 `since`-role decision early, because the closes-today slice
  (2101) is gated on it, not on any tier.

---

## Part C — supporting work

### C1. Synonym reduction

One canonical spelling per intent; others parse-accepted + linted
during migration, then removed.

**DECIDED (2026-07-02): `by` and `since` unify on `by`.** With
`automatic` scoping the silent prover is boring by construction
(standard tactics over local + `automatic` facts, `--explain` as the
accountability backstop), so "kept explanation, exempt from the
redundancy lint" no longer earns a keyword. `since` becomes a linted
synonym for one sweep, then dies; `byIsExplanation` /
`stepProofIsExplanation` and the redundancy exemption are deleted
from the elaborator. The citation-vs-sub-proof distinction the old
proposal wanted is already carried by the hint's SHAPE (identifier vs
`{ … }` block) — the lint can differentiate without a second keyword.
A reader-load-bearing redundant justification migrates to a stated
fact (A1) or to `note P [by V];`, the designated verified comment.
Consequence to schedule deliberately: un-exempting the former `since`
sites makes `--check-redundant-by` flag the whole closes-today bucket
(~42% of hinted sites) — that IS the C6 breadcrumb-deletion
work-list, scoped per the clean manifest.

Remaining pairs: `obtain`/`choose`/`take as` (→ A5, decided);
`take` vs raw `↦` lambdas at proof top level (→ `take`; lambdas only
in terms); `decide` (→ deleted by A4 `otherwise`); `done` (→
restate-the-goal, A1); the `done by substituting X unfolding Y`
sub-language (→ A7 `from`, `suffices by definition of`).

### C2. Error messages for the keyword-free world

- Bare-statement failures always phrase as "couldn't establish:
  ⟨stated proposition⟩ — nearest registered rules / candidate lemmas:
  …", regardless of whether the failure was elaboration, dispatch, or
  a missing premise. A typo that flips proposition↔proof-term must
  not surface as a raw type error.
- Ambiguous statement-address (A2): list the matching hypotheses,
  ask for a name.
- `suppose … for proving Q` mismatch: "block concludes P, announced Q".
- Exhaustiveness gap (A4): name the missing case.

### C3. Lemma discovery for LLMs

Expose the rule/lemma indexes as a CLI: given a goal (or a file
position), print candidate lemmas with signatures, ranked by the same
head-symbol match the prover uses. LLMs iterate extremely well against
this + the existing breadcrumbed error format; they iterate poorly
when discovery requires grepping.

### C4. Documentation as the single source of truth

`LANGUAGE.md` must be **complete** — it currently omits `since`,
`witness`, `given`, `done`, the `substituting/unfolding` grammar. For
LLM writability, completeness of the one in-context spec beats
elegance. After each Part-A construct lands: update `LANGUAGE.md`,
`docs/reference.md`, `docs/tutorial.md` in the same commit; add
`library/Test/` feature files per construct.

### C5. Structure-parameter consistency

`Algebra/group_lemmas.math` mixes explicit five-parameter headers
(`right_inverse_unique`) with implicit ones (`cancel_left`) in the
same file. Whichever convention wins (implicits + `convention`
headers, or bundled structures), the inconsistency is worse than
either choice. Sweep the Algebra layer to one convention; explicit
carrier/op/identity/inverse/proof call sites are a raw-CIC tell.

### C6. Migration mechanics

(The load-bearing lessons here are inherited from the Lux transition,
which executed a sweep of this shape in June 2026.)

- **The cost model: touch the bulk exactly once.** The analysis bulk
  (`Real/` + `ComplexNumber/`, ~40% of the library) must be migrated in
  ONE coordinated pass after the constructs are settled on smaller
  layers — sweeping construct-by-construct re-touches the same proof
  bodies repeatedly, and each extra touch re-derives the same reasoning
  in a changing syntax. Corollary: land the A-constructs first, sweep
  second.
- **Strictly bottom-up by dependency layer**, `make -j 16 tests` green
  after each coherent group, one reviewable commit per group:
  Natural/Integer/IntegerMod → Rational → Lists/Set → Polynomial →
  Real/ComplexNumber/GaussianInteger. The June sweep confirmed no file
  is a self-contained migration — interface changes cascade both down
  (structural matchers in consumers) and up (lemmas stated in the old
  form) — so partial-layer migrations strand consumers.
- **The mechanical/semantic split.** Syntax mapping (`claim P since L;`
  → `P since L;`; `decide P { yes h => A | no h => B }` → `by cases {
  case P: A otherwise: B }`; numeral rewrites; tuple sugar) absorbs
  ~60–70% of per-file churn and is safe to automate because the kernel
  re-checks every rewrite — a wrong transform fails to verify, the
  safety net is exact. The semantic residue (choosing minimal citation
  sets, characterising lemmas, restructuring term-position helpers) is
  human/LLM work under any strategy. Breadcrumb-claim deletion is
  driven by the B5 classifier.
- **The rewriter is the elaborator, not a text script.** Ad-hoc
  sed/perl passes over `.math` files are banned (they make a mess);
  mechanical rewrites ride the parser/elaborator, which is also the
  only thing that can respect nesting, comments, and layout.
- The redundancy tooling becomes the style enforcer in the
  keyword-free world: distinguish "unused and unenlightening"
  (delete) from "unused but reader-load-bearing" (keep; the old
  `note`) — operationally, whatever the author keeps after a
  `--check-redundant` pass.
- Editor/highlighting: with keywords gone, layout and punctuation
  carry structure; update the editor recipes so statements,
  justifications, and block structure are visually loud.

---

## Part D — interface and implementation (sealed structures)

(Absorbs `PLAN_INTERFACE_IMPLEMENTATION.md`, 2026-06-21, and the
opacity workstream of the Lux transition. The discipline is the
disciplined-C++ one: consumers compile against a header; the
translation unit is never seen.)

### D1. Goal and principle

Give the library true **abstraction barriers**: a type and its
operations are presented to consumers as an *axiomatic interface* — a
fixed set of operations and proven properties — while the construction
lives behind a seal the rest of the library cannot see through.

- Consumers see ℝ the way Spivak presents it — a complete ordered field
  with a ℚ ↪ ℝ embedding — and nothing else. Swapping the Cauchy
  construction for Dedekind cuts must be invisible to every consumer.
- Consumers see `Natural` through `0`/`1`/`+`/`*`/`<`/induction and a
  lemma collection from which anything they need is provable;
  **`successor` is not exported at all.** The implementation file uses
  it heavily — that is its job.

**Sealed, proven, not assumed.** The interface's "axioms" are theorems
*proved about the construction*, then sealed. The interface costs zero
trust: it hides representation and proofs; it admits nothing. This is
strictly better than an axiomatic foundation — the ergonomics of
axioms with the soundness of a construction.

### D2. Where we already are

The library has been converging on this by convention; Part D makes it
a checkable artifact. Already in place: `opaque definition` +
characterising lemmas (`docs/conventions/opaque.md`); Integer and
Rational as opaque quotients behind `difference_equal` /
`fraction_equal` boundaries; algebraic bundles as the semantic version
(an abstract `Ring` consumer can only use the axioms); and the
`successor`-outside-`Natural/` campaign as a lint-enforced prototype of
exactly this barrier. Two opacity spikes measured the retrofit cost
(sealing `Natural.LessThan`: 3 files broke; sealing `Natural.multiply`:
8 home-file unfolds + 2 downstream files) — every break a mechanical
defeq-exploit fix, none structural. **Transform, do not greenfield.**

What's missing: (a) sealing the *carrier type itself* (so the quotient
cannot be unfolded or `by_representatives`-ed), (b) bundling a whole
interface — type + operations + obligations — as one importable unit
with real operators rather than bundle-projection noise, (c)
kernel-level rather than lint-level enforcement.

### D3. Surface design

Two module kinds plus a sealing relation. The interface module declares
the public view — abstract `type`, abstract operation `constant`s,
operator wiring, optionally transparent derived definitions, and
theorem *signatures* (the obligations):

```
interface module Real
  type Real
  constant Real.zero : Real
  constant Real.add  : Real → Real → Real
  constant Real.LessOrEqual : Real → Real → Proposition
  constant Rational.to_real : Rational → Real
  operator (+) on (Real, Real) := Real.add
  …
  definition Real.LessThan (x y : Real) := Real.LessOrEqual(x, y) ∧ x ≠ y
  definition Real.IsSupremum (S : Set(Real)) (s : Real) := …

  theorem Real.is_ordered_field : IsOrderedField(Real, …)
  theorem Real.complete : ∀ (S : Set(Real)). Real.IsNonempty(S) →
            Real.HasUpperBound(S) → ∃ (s : Real). Real.IsSupremum(S, s)
  theorem Rational.to_real.preserves_add : …    -- the hom + order + injectivity packet
```

What the interface exports is decided by CLOSURE over consumer needs,
not minimality (see the D7 decision): theorems consumers genuinely
reach for (density, Archimedean, Cauchy completeness) may be exported
alongside the core even though they are derivable, because they are
proved either way and buildability is the criterion. Whole-theorem
consumers like IVT stay outside. The acceptance test (D6) is
accordingly closure — no consumer needs anything off the list — which
is what the Phase-0 spike measured.

The implementation module provides the opaque construction and
discharges every obligation:

```
implementation module Real.cauchy implements Real
  definition Real := Quotient(CauchyRationalSequence, CauchyEquivalent)
  definition Real.add := …
  theorem Real.is_ordered_field := <proof using representatives>
  theorem Real.complete := <the Cauchy-completeness proof>
```

`implements` is checked at module load: every interface constant/type
has a matching definition of definitionally-equal type; every theorem
signature has a matching proof; the set is complete. Downstream,
`import Real` sees only the interface view — bodies sealed (no
δ-reduction), carrier never unfolding to the quotient. The
implementation module is not on the ordinary import path.

#### D3a. Phase-1 implementation design (2026-07-02 night survey)

The `.mathv.iface` machinery is already ~90% of the sealing semantics:
it strips proof bodies and opaque-definition bodies to bodyless axioms,
zeroes source-dependent fields, and consumers load interfaces
transitively (never proof-carrying caches). Phase 1 therefore builds as
a REFINEMENT of the iface derivation, not a new subsystem:

- An `implementation module Y implements X` is an ordinary module plus
  the recorded relation.
- Processing `interface module X` = load Y's cache, run the OBLIGATION
  CHECK (every interface `type`/`constant`/theorem signature has a
  matching Y-declaration with definitionally-equal type; the set is
  complete), then derive X's cache from Y's by FILTERING to the listed
  names and FORCING opacity on listed value definitions (listed
  transparent `definition`s keep bodies; unlisted names remain present
  but unadvertised — a visibility lint can tighten this later).
- `import X` then resolves to the interface cache exactly like any
  module import; no new load path.
- BUILD EDGE: the interface file must name its implementation for the
  Makefile to know the dependency without scanning — proposed spelling
  `interface module X ... implemented by Y` (cross-validated against
  Y's `implements X`). OWNER MAY VETO the dual declaration; the
  alternative is a build-system mapping file.
- Staging: (1) parser + surface for both module kinds and the
  interface-body statement forms (`type N`, `constant N : T`, theorem
  signatures without `:=`); (2) the obligation check + sealed-cache
  derivation in main.cpp; (3) the Makefile rule; (4) a TOY interface
  feature test (counter over Natural) where the consumer must FAIL to
  see the construction defeq — the sealing acceptance; (5) migrate the
  ℝ prototype (the measured 1-site bill).

### D4. Eliminator export — the Natural interface

ℝ has no eliminator problem (nothing eliminates a real). `Natural` is
the opposite: **induction IS the interface.** The interface exports an
induction principle stated without the constructor; the implementation
discharges it with the raw recursor:

```
interface module Natural
  type Natural
  constant Natural.zero : Natural
  constant Natural.add  : Natural → Natural → Natural
  -- NB: successor is NOT exported. Naturals are built from 0, 1, +.

  theorem Natural.induction
        : ∀ (P : Natural → Proposition).
            P(0) → (∀ (k : Natural). P(k) → P(k + 1)) → ∀ (n : Natural). P(n)
```

`by induction on n { case n = 0: … case n = k + 1 for some k, with
IH : P(k): … }` (A4's unified clause syntax) desugars to the exported
principle; `| successor(k) =>` patterns disappear from user space. This
is the deep resolution of the successor-confinement campaign: the lint
barrier becomes a kernel barrier, and the one construct the lint could
never remove — constructor patterns — is removed by the eliminator
export. Recursive *definitions* in user space ride the numeral-pattern
recursion (`0` / `1 + n` patterns, already landed) re-based on the
exported recursor.

Semantics: **module-scoped opacity** (a body transparent inside its
implementation module, opaque everywhere else — a small generalization
of the existing per-definition flag) plus the obligation check (reusing
the ordinary theorem-signature match). No kernel-soundness change; the
kernel still checks every proof in full.

### D5. Enforcement: the kernel seal retires the lints

The leak/successor linters are advisory; a sealed type is enforced by
the kernel — a consumer *cannot* δ-unfold ℝ to the quotient even by
accident. Once a type is sealed, its lint retires. **Interim ratchet
(until then):** re-arm the leak-report baseline after each migration
group and wire a no-increase check into `make check` — carrier
constructors outside the owning module, non-opaque definitions outside
the foundational allowlist, opacity piercings: the number only goes
down.

### D6. Phased plan

- **Phase 0 — sealed-ℝ prototype with today's machinery (no language
  change).** Make the carrier and operations opaque outside their
  defining files, route consumers through the field/order/completeness
  theorems, and re-verify the whole IVT cone (`intermediate_value.math`
  + imports) using only the interface: no `by_representatives`/`cases`
  on a Real, no `CauchyRationalSequence` reached through ℝ. Files that
  break enumerate exactly the missing boundary lemmas — that list is
  the deliverable, and it sizes Phase 1 before any syntax is built.
  *Survey result (2026-07-02): the boundary already holds by
  convention.* Every construction-piercing site sits inside Real/'s
  own ~20 construction/boundary files (22 Real-destructures across 11
  of them; 72 `CauchyRationalSequence.make` sites); the other 24
  Real/ files, the IVT cone, exponential, and all of ComplexNumber/
  contain ZERO construction vocabulary. So Phase 0 needs no consumer
  rewrites — the risk surface is only whatever consumers currently
  get from transparent δ-reduction rather than stated theorems, which
  the opacity flip will enumerate directly.
  *Spike result (2026-07-02: flipped `Real` to `opaque definition`,
  keep-going build, then reverted).* **7 files fail, everything else —
  including all of ComplexNumber/ — verifies.** Two failure shapes:
  (a) construction files (`addition`, `embedding_order`, `field`,
  `triangular_series`-adjacent): declared type says `Real` /
  `Rational.to_real(…)`, the proof's inferred type spells the reduced
  `Quotient.class_of(…)` form — home-file reconciliation, the
  mechanical `unfolding`/boundary-lemma bill;
  (b) consumers (`continuity`, `derivative`, `limits`): "the function
  expects `Quotient.{0} CauchyRationalSequence CauchyEquivalent` but
  this argument is `Real`" — an imported interface type carries the
  REDUCED spelling, i.e. the opaque-quotient-alias machinery that
  already serves Integer/Rational does not engage for `Real`'s alias
  in the interface-normalization path. (b) is an ELABORATOR gap, not
  proof debt, and is the concrete first work item of Phase 1; fix it
  and the Phase-0 bill shrinks to the handful of home-file
  reconciliations in (a). Cost measured: bounded and small, matching
  the `Natural.multiply` spike precedent.
- **Phase 1 — language support** (`interface module` /
  `implementation module … implements`, scoped opacity, obligation
  check, export view); migrate the ℝ prototype onto it.
- **Phase 2 — eliminator export**, then seal `Integer` (already an
  opaque quotient; modest eliminator needs).
- **Phase 3 — `Natural`** (D4): the hardest and last, where this part
  and the successor campaign converge. Prep work already queued:
  sealing `Natural.multiply`/`factorial` behind characterising lemmas
  (reference implementation exists on the field-of-fractions branch).
- **Phase 4 — the rest**: ℂ on a sealed ℝ, finite fields, polynomials.

### D7. Costs, risks, open questions

- **Loss of defeq.** Every ι/δ-reduction consumers lean on becomes a
  propositional boundary lemma — the same bill Integer/Rational already
  paid, just larger. Phase 0 measures it; the mitigation is a generous,
  well-named boundary-lemma set published *with* the interface.
- **Numerals.** `0`/`1`/`2`/`k + 1` for sealed types must elaborate via
  interface constants, not constructors, and `ring`/`field` must still
  see numerals. Note the Part-B interaction: over a sealed `Natural`,
  tier-2 ground evaluation cannot ι-reduce — it must be lemma-emitting.
- **Tactics over sealed carriers.** `ring`/`field` already work over
  abstract bundles, so the path exists; verify they fire through the
  interface axioms.
- **Interface minimality vs convenience — DECIDED (owner,
  2026-07-02): buildability wins.** Nothing is ever assumed — every
  interface entry is proved from the construction — so the question
  was only which proved statements to export. The criterion is "easy
  to build on top of," not axiomatic purity: the interface is the
  CLOSURE of what consumers actually need (operationally: the
  headline theorems the construction files already export — exactly
  what the Phase-0 spike validated), not a minimal axiom set.
  Concretely for completeness: **LUB (Spivak's form) is the
  canonical completeness statement, and Cauchy completeness is
  exported alongside it** — both proofs already exist
  (supremum.math, cauchy_complete.math), so this costs nothing
  today; the eventual nicety is re-deriving Cauchy completeness over
  the interface rather than the construction (cauchy_complete.math
  is already construction-vocabulary-free, so this is nearly true
  now). A future alternative implementation discharges LUB and
  derives Cauchy via the (then-generic) equivalence. The minimal
  core (ordered field + LUB + embedding packet) remains identified
  — not as the export boundary, but as the statement of the
  categoricity theorem below. Extension discipline unchanged:
  extend the interface and discharge the new obligation, never
  bypass it.
- **Uniqueness.** A complete ordered field is unique up to unique
  isomorphism; stating (eventually proving) categoricity makes "swap
  the construction" a theorem rather than a hope.

### D8. Integration with Parts A–C

- **A4:** structural-case exhaustiveness lemmas are interface
  obligations; clause syntax `case n = k + 1 for some k:` routes
  through the exported principle (note in A4).
- **B1/B2:** interface theorems are the natural `automatic` set —
  stated in dischargeable (proper-subterm-premise) form they feed the
  tier-4 judgment index directly; implementation internals are never
  automatic. An interface style rule: prefer stating obligations in
  rule-admissible form.
- **B3:** the embedding hom/order packet in an interface (`to_real.
  preserves_*`) IS the morphism packet cast normalization consumes —
  one declaration serves both.
- **C6:** interface conversion of a layer and its syntax migration are
  the same touch — schedule them together so the bulk is still touched
  once.

---

## Suggested order of implementation

1. **B5 classifier** (instrument existing `claim … since` lines) — it
   sizes and prioritizes everything in Part B. Cheap.
2. **B1–B3** (tier skeleton + memoization; sign index; cast
   normalization) — kills the breadcrumb-claim complaint at its root.
3. **A1** (keyword-free claims/calc) — the biggest visible change;
   depends on B for the bare statements to actually discharge.
4. **B4** (order automation in calc) — transforms the analysis files.
5. **A2 + A7-contradiction** — statement addressability and the
   `contradiction` terminal; large readability gain, moderate cost.
6. **A3 + A4 + A5** (suppose-for / by-cases / obtain) — the construct
   distillation; includes deleting `decide`, `refining`, `with eq`.
7. **A6** (`eventually`) — library + elaborator; unblocks rewriting
   Real/PAdic/ComplexNumber proofs at a fraction of current length.
8. **C1–C6** interleaved throughout; C4 with every landed construct.
9. **Part D** runs as a second track: **Phase 0 (sealed-ℝ prototype)
   is library-only and can start immediately** — its
   missing-boundary-lemma list is cheap information, like the B5
   classifier. The `Natural.multiply`/`factorial` sealing (Phase-3
   prep) likewise. Language support (D Phases 1–2) waits for A4 so the
   eliminator export and the unified `by cases` land as one design;
   Phase 3 (`Natural`) comes after the A-construct sweep so the bulk
   is touched once (C6 cost model).
10. **A8** (ellipsis folds/series): its steps 1–3 (generic `Fold` +
    registry + characterizing lemmas, explicit binder form) are
    independently valuable and can start any time; the ellipsis
    recognizer waits for the tier-2 evaluator (step 2 above), and the
    series relations (§6) wait for A6 (step 7).

## Reference target

`sqrt_two_irrational.math` after steps 1–6 (the agreed idealized form —
keep this in the repo as the acceptance test for the migration):

```
theorem Natural.two_divides_root (m : Natural) (squareEven : 2 ∣ m * m)
        : 2 ∣ m :=
  by Natural.prime_divides_product

theorem Natural.no_double_square (m n : Natural)
        (mPositive : 1 ≤ m) (nPositive : 1 ≤ n)
        : m * m ≠ 2 * (n * n) := {
  by_strong_induction on m with no_smaller_solution;
  suppose m * m = 2 * (n * n) as equation;

  2 ∣ m  by Natural.two_divides_root;
  choose k such that m = 2 * k;

  suppose k = 0 for contradiction {
    then m = 2 * 0 = 0;
    contradiction with 1 ≤ m
  };
  hence 1 ≤ k;

  from equation: (2 * k) * (2 * k) = 2 * (n * n);
  hence n * n = 2 * (k * k);

  suppose m ≤ n for contradiction {
    then m * m ≤ n * n < 2 * (n * n) = m * m;
    contradiction
  };

  contradiction with no_smaller_solution(n, k)
}

theorem Natural.sqrt_two_irrational
        : ¬ ∃ (m n : Natural). 1 ≤ m ∧ 1 ≤ n ∧ m * m = 2 * (n * n) :=
  by Natural.no_double_square
```

And the analytic acceptance test, `LessOrEqual_of_pointwise_lower`
(currently ~50 lines), after step 7:

```
theorem Real.LessOrEqual_of_pointwise_lower
        (s : Natural → Rational) (sIsCauchy : IsCauchy(s))
        (B : Real)
        (pointwiseLower : ∀ (n : Natural). B ≤ (s(n) : Real))
        : B ≤ Real.limit(s, sIsCauchy) := {
  take B as representative (b, bIsCauchy);
  suffices ∀ ε > 0. eventually (m). -ε < s(m) - b(m)
      by definition of Real.LessOrEqual;
  take ε > 0;

  choose N such that eventually (m). abs(s(m) - s(N)) < ε/2
      from sIsCauchy;
  eventually (m). -ε/2 < s(N) - b(m)
      by pointwiseLower(N), by definition of Real.LessOrEqual;

  eventually (m):
    -ε = -ε/2 + -ε/2
       < (s(m) - s(N)) + -ε/2
       ≤ (s(m) - s(N)) + (s(N) - b(m))
       = s(m) - b(m)
}
```

Principles that must survive every step: the trusted base is the
kernel (every construct and every tier emits kernel-rechecked terms);
embeddings and dispatch rules are canonical, never searched; ambiguity
is always a loud error, never a silent pick; and nothing appears on
the page that a mathematician wouldn't write — in either direction.

---

## Review pins (2026-07-02 code-check)

A read of the current elaborator/parser against this plan confirmed
its factual claims and produced these amendments; treat them as part
of the design:

1. **A4:** keep `refining` / `cases … with eq` parse-accepted until
   the substitution rule survives the full migration (~85 uses).
   Substitution into arbitrary hypothesis types has historically hit
   opacity walls; delete the escape hatches only after the general
   rule is proven on the whole library.
2. **A2 × B1:** dedup is hash-based but statement-matching is
   defeq-based, so a user-stated fact and a silently derived one can
   both match. Rule: statement-addressing prefers user-stated facts;
   ambiguity errors fire only on ties among user-stated ones.
3. **B1:** derived environment-level facts never export across the
   file boundary — whether a file verifies must not depend on what
   side conditions another file's proofs happened to derive.
4. **A1:** rhetorical connectives may affect which proof is found and
   how fast, never *whether* one is found. Pin this as an invariant or
   the "noise word" story is false.
5. **B2 boundary rule, explicit:** fact *search* is scoped by
   `automatic`; syntactic *indexes* may be global (precedent: the
   rewrite index already seeds from every imported equality lemma).
6. **Tier 6** must respect the unary-coefficient ceiling of the ring
   normaliser (proof size O(Σ|coefficient|)) — meter it accordingly,
   or gate on the symbolic-coefficient rewrite.
7. **A7:** `decide` disappears from the proof surface; the value-level
   machinery underneath `if … then … else` in definitions survives.
8. **DECIDED (owner, 2026-07-02):** both convention questions are
   settled — `by`/`since` unify on `by` (C1), and the destructuring
   construct keeps `choose … such that` with `obtain` retired (A5).
   See those sections for the rationale and consequences.

---

## Lineage, document map, and the Lux rename

**Folded into this plan and deleted** (git history is the record):

- `PLAN_LUX_TRANSITION.md` (2026-06) — the transition executed and
  merged to main 2026-06-19. Landed and recorded there: the induction
  keystone, the opacity spikes (→ D2's "transform, do not greenfield"),
  the cite-only validation (superseded by the `automatic`-tier model
  Part B builds on), the baby library, the bottom-up sweep discipline
  (→ C6). Its `1 + n`-keystone framing was reframed 2026-06-22 into
  "confine the constructor asymmetry to the `Natural/` floor" — whose
  final form is D4's kernel seal.
- `PLAN_INTERFACE_IMPLEMENTATION.md` (2026-06-21) — now Part D,
  updated with the A4/B/C6 integration points.

`LUX_PLAN.md` (the old destination spec) is already gone; this
document is the destination spec. Still-current companions:
`LANGUAGE.md` (the as-is idiom reference — C4's completeness target),
`PLAN_KERNEL.md`, `PLAN_COERCIONS.md`, `PLAN_CAST_NORMALIZATION.md`
(B3's precursor), `PLAN_AUTOPROVER_FINGERPRINT.md` /
`PLAN_READABILITY.md` / `PLAN_LESS_CIC_STYLE.md` (shipped-infrastructure
records).

**The rename.** The language becomes **Lux** when the reference target
above verifies in its idealized form (end of step 6) — the moment the
surface actually looks like the new language. Renaming earlier would
brand transitional syntax and force a second identity migration; at
the gate, docs, error messages, and editor recipes migrate once.

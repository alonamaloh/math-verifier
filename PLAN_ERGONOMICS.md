# PLAN_ERGONOMICS.md — removing surprises for the mathematician

The overriding goal of this project is that a mathematician writes proofs
the natural way and the kernel does the checking. Every place where two
*mathematically equal* spellings are treated differently by the language,
elaborator, tactics, or lemma library is a **surprise** — the user has to
learn an implementation detail they shouldn't need to know. This document
is the single prioritized driver for eliminating those surprises. It is a
consolidation, not a replacement: each item points at the plan / memory /
`QUIRK.md` entry that holds the detail.

Guiding principle (owner, 2026-07-15):

> Sealing `Natural` was meant to hide implementation details from a user
> who doesn't need them. A tactic that works on `1 + n` but not `n + 1`,
> or on `0 + a` but not `a + 0`, re-exposes exactly what sealing was meant
> to hide. That non-uniformity is **intolerable** — collect every instance
> and fix the class, don't paper over each site.

## How to read this

Each friction has: **Symptom** (what the user sees), **Root cause**,
**Fix direction**, **Priority**, and **Detail** (where the deep notes live).
Priorities: **P0** flagship / user-flagged intolerable · **P1** frequent,
class-wide · **P2** real but localized · **P3** nice-to-have.

Related living docs this consolidates from (do not duplicate — extend):
`PLAN_CAST_NORMALIZATION.md` (mixed-type cast association),
`PLAN_LANGUAGE_IMPROVEMENT.md` (statement language + tiered auto-prover),
`TODO.md` / `docs/TODO.md` (idea backlogs),
`docs/error_message_inbox.md` + `docs/error_message_corpus.md` (error triage),
`QUIRK.md` (elaborator quirks with repros), and the memory notes
`one_plus_vs_plus_one_asymmetry`, `numeral_let_ring_elaborator_gaps`,
`successor_elimination`, `coercion_join_project`.

---

## F1 · Natural additive-form uniformity — `n+1` vs `1+n` vs `successor n` vs numerals  ·  **P0 (flagship)**

**Symptom.** These four spell the same number but are not interchangeable in
matching / argument positions:
- `less_or_equal_add_left(1, d) : 1 ≤ d + 1` is **rejected** where `1 ≤ 1 + d`
  is expected ("argument has the wrong type … expects `1 ≤ 1 + dPred` but is
  `1 ≤ dPred + 1`"), though they differ only by `add_commutative` (2026-07-15,
  brick-6b distance induction).
- Citing a `successor`-stated lemma against a `1 + n` goal (or vice versa)
  fails to unify / infer args; the fix has been per-lemma `1 +`-form wrapper
  lemmas.
- Closed numerals ≥ 2 (`2`, `4`) match in `=` goals (ring bridges `2 ↔ 1+1`)
  but not in non-`=` matching / citations.

**Root cause.** `Natural.add` is `opaque` and structurally recurses on its
**first** argument, so only `1 + n` WHNF-bridges to `successor n` (via the
`automatic` `Natural.one_add`). `n + 1`, commuted forms, and numerals ≥ 2 are
propositionally equal (automatic lemmas / `ring`) but **not defeq** — and
argument checks / `matchAgainstPattern` compare by defeq + structural match,
which the automatic lemmas do not feed.

**Already landed (partial):** `Natural.induction_on_plus_one` exists;
`Natural.add_one` is `automatic`; the auto-prover bridges both forms in `=`
GOALS; `{0,1}` numeral canonicalization (`asNumeralLiteral`) works in the
matcher. **The remaining gap is the matcher / argument-coercion layer.**

**Fix direction.** Give the matcher and the argument-coercion path a
**Natural additive normal form**: canonicalize any Natural expression built
from `+`, `successor`, `0`, `1`, and closed numerals to an ordered
(atom-multiset, constant-offset) form before structural comparison — the same
move `asNumeralLiteral` makes for `{0,1}`, generalized. Then `n+1`, `1+n`,
`successor n`, `2 = 1+1` all unify, and a lemma result differing by such an
identity coerces into an argument slot. Scope it to Natural-headed terms and
props (`=`/`≤`/`<`), gated for cost. This retires the per-lemma wrapper idiom
and the "which form does induction present" tax. Cross-check the normal form
against `PLAN_CAST_NORMALIZATION.md`'s leaf-cast form so they compose.

**Detail.** `one_plus_vs_plus_one_asymmetry` (root cause + landed fixes),
`numeral_let_ring_elaborator_gaps` item 3 (numerals ≥ 2), `successor_elimination`.

### F1 — Investigation findings (2026-07-15)

**Architectural constraint (the finding that shapes everything).** The failure
in the brick-6b case (`less_or_equal_add_left(1, d) : 1 ≤ d+1` rejected where
`1 ≤ 1+d` is expected) is the KERNEL throwing `Application: argument type does
not match Pi domain` (`src/elaborator/internal.hpp:624`), i.e.
`isDefinitionallyEqual` (`src/kernel/kernel.cpp:2106`) returns false because
`Natural.add` is opaque and `d+1` / `1+d` are not defeq. **The kernel must not
learn arithmetic** — it is the trusted checker; teaching it `add_commutative`
would either bloat trust or require an axiom. Therefore **every F1 fix is an
elaborator-level auto-transport: detect the additive mismatch, SYNTHESIZE a
proof of the rearrangement equality, and insert a transport so the term the
kernel sees is genuinely well-typed.** No kernel change; trust is preserved and
the built proof is still kernel-checked.

**Two separable surfaces, both in the elaborator:**

1. **Argument / expected-type coercion** — `coerceToExpectedTypeViaDiff`
   (`src/elaborator/coercion.cpp:59`), called on every function argument at
   `src/elaborator/dispatch.cpp:1423`. It already runs a family of transport
   strategies ((a) equality-goal diff-wrap, (b) `tryDiffBridgeViaContextEquality`,
   (c) double-negation, (d) bare-proposition). My case fell through all four
   (expected head is `LessOrEqual`, no context equality, not structurally
   equal) and hit the kernel reject. **Add strategy (e): Natural additive
   rearrangement.** Prefilter: expected and actual are the same Natural
   relation head (`Equality`/`LessOrEqual`/`LessThan` over Natural) with
   corresponding sides that share an additive normal form but differ
   syntactically. Action: for each differing side synthesize the equality
   (`side_actual = side_expected`) and diff-bridge the term across it — reusing
   the strategy-(b) transport with a *synthesized* equality instead of a
   context hypothesis.

2. **Citation matching** — `matchAgainstPattern`
   (`src/elaborator/diff_bridges.cpp:1036`), whose top already canonicalizes
   `{0,1}` numerals via `asNumeralLiteral` (`diff_bridges.cpp:918`) and peels
   `successor`/`NaturalLiteral`. **Generalize that canonicalization to a full
   Natural additive normal form** so `by <successor- or n+1-stated lemma>`
   matches a `1+n` goal. This only WIDENS matches; the elaborator then builds
   the application and surface (1) inserts any needed transport, so the two
   compose and the kernel still re-checks.

**The normal form.** Canonicalize a Natural expression over `+`, `successor`,
`0`, `1`, and closed numerals to `(sorted multiset of atoms, constant offset)`.
Two expressions are "additively equal" iff identical normal forms. Terminating
(finite atom sort), closed under the automatic bridges (`one_add`, `add_one`,
`add_commutative`, `add_associative`). Define it compatibly with
`PLAN_CAST_NORMALIZATION.md`'s leaf-cast form (leaf-cast first, then additive)
so mixed-type expressions compose.

**Proof synthesis is already callable.** `elaborateRing(localBinders,
expectedType, line, col)` (`src/elaborator/ring.cpp:702`) returns a proof term
for a stated equality goal, and its carrier detection already recognizes
`Natural` (`ring.cpp:173`: Natural literals + `successor`) and closes additive
AC. So strategy (e) synthesizes `side_actual = side_expected` by building that
equality goal and calling `elaborateRing` (or the lighter `proveAbstractRingAC`,
`ring.cpp:2179`). No new prover needed — only the detection + transport wiring.

**Risk assessment.**
- *Soundness*: none. Elaborator builds a real transport; kernel re-checks. No
  kernel/defeq change.
- *Performance*: `coerceToExpectedTypeViaDiff` is ~1 ms/call and already
  prefiltered; strategy (e) needs an equally cheap prefilter (both types are
  Natural-relation-headed AND at least one side contains `+`/`successor`)
  before any inferType/normal-form work. `matchAgainstPattern` runs hot — the
  normal-form escape must be O(size) and only attempted when the plain
  structural match has already failed at that node.
- *Termination*: normal form is a terminating sort/merge; `elaborateRing` is
  bounded.
- *Surface fidelity*: the transport is invisible (a wrapper), exactly like the
  existing registry/diff coercions — the user's source is unchanged.
- *Interaction*: coordinate the atom ordering with cast-normalization so a
  mixed `1 + x + n` and `1 + n + x` also unify (that is `PLAN_CAST_NORMALIZATION`
  territory; the Natural normal form is its homogeneous special case).

**Recommended implementation order.**
- **Step 1 (self-contained, high-value): strategy (e) in
  `coerceToExpectedTypeViaDiff`.** ✅ **DONE 2026-07-15.** This is exactly the
  brick-6b failure, is testable in isolation (a `library/ErrorTest`- or
  feature-style regression: `lemma(1, d)` of type `1 ≤ d+1` used where
  `1 ≤ 1+d` is expected), and reuses `elaborateRing` + the diff-bridge.
  Landed as strategy (e) "Natural additive rearrangement": prefilter (expected
  is a Natural relation head `=`/`≤`/`<` with a `+`/`successor`) → diff-walk →
  `synthesizeNaturalEquality` (builds `diffInferred = diffExpected`, calls
  `elaborateRing`) → the strategy-(b) transport, now factored into the shared
  `buildDiffBridgeTransport(resolveEquality)` engine so context-equality and
  ring-synthesis reuse one motive-masking transport. Handles both directions,
  associativity, numeral-2 (`ring` folds `2 = 1+1`), and the `<` head. Wrong
  forms still rejected loudly (`ring` declines → nullptr → kernel reject).
  Regression: `library/Test/natural_additive_rearrangement_test.math`.
  library+tests+export-check green, axiom inventory unchanged (3080 decls).
  Wrapper-lemma-removal sweep deferred: the `1 +`-form wrappers are mostly a
  *citation* idiom, so they clear with Step 2, not the argument path.
- **Step 2: additive normal form in `matchAgainstPattern`.** ⚠️
  **INVESTIGATED 2026-07-15 — mostly NOT NEEDED; one narrow residual, deferred.**
  Empirically, the `matchAgainstPattern` / `by`-citation path **already
  bridges every constructible F1 additive form**: order goals (`1 ≤ 1 + d`
  cited against `1 ≤ k + 1`), `=` goals, commute both directions,
  associativity, numeral-2, and even a metavar occurring *solely* inside the
  additive node (`1 ≤ n + 1` cited against `1 ≤ 1 + k`) — the auto-prover's
  goal-driven citation + order/ring bridging carries them. So the planned
  additive-normal-form change to that hot matcher would be **speculative
  complexity with no observed benefit** (could not construct a failing
  matchAgainstPattern case). NOT done.
  - **The one genuine residual** is a *different* unifier: implicit-argument
    inference of a bare implicit-leading identifier used as a direct function
    argument (`impl_bound {n} : 1 ≤ n + 1` passed where `1 ≤ 1 + k` is
    expected) fails. Root: `unifyConstructorParameters`
    (`src/elaborator/unification.cpp:81`) misassigns `n := 1` positionally on
    the `Natural.add` node, AND the dispatch adopt-gate
    (`dispatch.cpp:561`) demands strict defeq. This is **F2-flavoured**
    (provable-not-defeq arg coercion across implicit inference), constructed-
    only (no library instance found).
  - **A fix was attempted and reverted**: a Natural-additive-normal-form
    branch in `unifyConstructorParameters` (+ a `coerceToExpectedTypeViaDiff`
    bridge in the dispatch gate) solved the isolated case but **regressed
    `library/Integer/embedding.math`'s difference-boundary inference** — the
    additive branch perturbs metavar bindings in load-bearing citation
    inference. Flagged as friction: a safe fix needs a surgical approach that
    only overrides positional binding when it would *demonstrably* misbind
    (or handles the coercion purely at the dispatch layer without touching the
    shared unifier), not a blanket additive escape in the hot path.
- **Step 3: fold numerals ≥ 2** into the same normal form (F4b), and re-check
  the mixed-type cases against `PLAN_CAST_NORMALIZATION`. Argument-slot
  numerals ≥ 2 are **already covered by Step 1** (`ring` folds `a + 2 ↔ 2 + a`
  in strategy (e)); citation-path numerals ≥ 2 also already bridge (verified,
  same as Step 2). Remaining Step-3 scope is thin.

---

## F2 · Argument / citation coercion across a provable-not-defeq identity  ·  **P1**

**Symptom.** The general form of F1 beyond Natural: passing a lemma result
whose type is *provably* but not *definitionally* equal to the expected
argument type fails at the argument check, with no attempt to bridge. Also:
`done by <Lemma>` cannot discharge a premise that holds by a registered
`instance` rather than an in-scope hypothesis (`Ring.zero_multiply` etc. need
an explicit `claim IsRing(…)`).

**Root cause.** Argument elaboration checks defeq only; citation
premise-discharge consults in-scope hypotheses only.

**Fix direction.** (a) When an argument's type mismatches by a same-relation
Natural/ring identity, attempt a cost-gated coercion (reuse the F1 normalizer
/ registry-coercion path — `numeral_let_ring` item 4 extends
`coerceToExpectedTypeViaRegistry` to more positions). (b) Have citation
premise-discharge also consult registered `instance`s (`numeral_let_ring`
item 5) — collapses the derived-ring-law boilerplate.

**Progress.** ✅ **Implicit-leading + named-argument coercion — DONE 2026-07-15.**
Strategy (e) (F1's Natural additive-rearrangement transport) now fires on the
explicit trailing arguments of an **implicit-leading** call (through
`inferLeadingArguments`), for both positional and `name := value` arguments —
so `consume_bound(h)` / `consume_bound(bound := h)` with `consume_bound {n d}
(bound : successor(n) ≤ d)` and `h : 1 + n ≤ d` now bridge, matching the plain
positional path. Root cause was a WHNF of the expected domain in the trailing-arg
path (`inference.cpp:629`) δ-unfolding `≤` (`< ∨ =`) into an `Or`, defeating
strategy (e)'s relation-head prefilter; fixed by trying the un-reduced domain
first, WHNF as fallback. Regression:
`library/Test/implicit_leading_argument_coercion_test.math`. **Remaining F2:**
the general provable-not-defeq coercion beyond Natural relations, and (b) the
`instance`-premise discharge.

**Detail.** `numeral_let_ring_elaborator_gaps` items 4 & 5, `coercion_join_project`.

---

## F3 · `substituting` / calc rewrite direction  ·  **P1**  ·  ✅ ALREADY WORKS

**Status (verified 2026-07-15).** The symptoms below no longer reproduce: a
calc step `A = B by <direct-lemma>` where the lemma proves `B = A` closes, a
bare-name citation flips (args inferred from the flipped conclusion), and
`substituting eq` rewrites in the reverse orientation. The symmetry machinery
now covers direct-lemma calls, not just named hypotheses. Regression:
`library/Test/calc_symmetry_and_numeral_leaf_test.math`. Kept for history.

**Symptom.** `substituting eq` only rewrites `eq`'s LHS→RHS **in the goal**.
To use it the other way, or against a hypothesis, you must restate the
equation flipped and name it. A calc step `A = B by <direct-lemma>` where the
lemma proves `B = A` **fails** — direct lemma calls are not tried symmetric,
though a *named hypothesis* flips fine. Repeated tax this session (brick 6b):
every "combine two sub-chains at a shared value" needed name-and-flip.

**Root cause.** `substituting` is single-orientation; calc `by <lemma>`
matches the step relation without trying symmetry for direct lemma calls
(the corpus notes symmetry *is* tried for `Not`-wrapped equalities — so the
machinery exists, just not on this path).

**Fix direction.** (a) `substituting eq` tries both orientations (and,
behind a flag or by target, rewrites a named hypothesis). (b) calc `by
<lemma>` tries the symmetric conclusion for `=` steps uniformly, matching the
already-forgiving named-hyp behavior.

**Detail.** `docs/conventions/calc-and-rewrite.md`; brick-6b session notes.

---

## F4 · `ring` reach: opaque subterms, numerals ≥ 2, diff-leaf  ·  **P2**

**Status (verified 2026-07-15).** (a) ✅ already works — `(2*2)^m = 4^m` closes
by-less (ground arithmetic decides `2*2 = 4`, then congruence); regression in
`library/Test/calc_symmetry_and_numeral_leaf_test.math`. (b) numerals ≥ 2 in
argument slots are covered by F1 Step 1. (c) is an error-message item (→ F9).

**Symptom.** (a) A by-less `=` step whose two sides differ only inside a
closed-numeral leaf (`power(2*2,m) = power(4,m)`) is not closed — the diff
already isolates the leaf but discharges it with local hyps only, not ring.
(b) Numerals ≥ 2 don't canonicalize in the matcher (shared with F1).
(c) `ring` legitimately can't prove `sum = value(b)` when `value(b)` is an
opaque variable a *hypothesis* equates to that sum — expected, but the error
should point at "use the hypothesis" rather than just "ring failed".

**Fix direction.** Cost-gated `ring` at the `structuralDiff` leaf
(`numeral_let_ring` item 1); the F1 numeral normal form covers (b); (c) is an
error-message improvement (→ F9).

**Detail.** `numeral_let_ring_elaborator_gaps` items 1 & 3.

---

## F5 · Implicit-argument inference under expected-type ascription  ·  **P2**

**Symptom.** `NaturalsBelow.below(x)` (with `x : NB(k)`) mis-infers its
implicit `n` as `1+k` when the expected type is a `value(inclusion(k,x)) < k`
ascription, clashing with `x`. The mathematically trivial "this bound is just
`below(x)`, since `value(inclusion(k,x))` is definitionally `value(x)`" does
not go through; you must derive the bound at the `n=k` spelling separately.
(2026-07-15, brick-6a.)

**Root cause.** The expected type's `NaturalsBelow.value` carries implicit
`n = 1+k`, and unification propagates that into `below`'s implicit before
reducing `value(inclusion(k,x))` to `value(x)`.

**Fix direction.** Reduce definitional projections (`value(make …)`,
`value(inclusion …)`) before / during implicit resolution, or prefer the
argument's own type over the expected type's propagated implicits. Needs a
minimal repro in `QUIRK.md` and an elaborator investigation.

**Detail.** `QUIRK.md` (to be added), brick-6a session notes.

---

## F6 · Auto-prover can't cheaply bridge two sub-chains at a shared value  ·  **P2**

**Symptom.** After proving `LHS = v` and `RHS = v` where `v` is a small value
but `LHS`/`RHS` mention expensive opaque unfolds (`compose`, `swap`), a
trailing `done` either warns "expensive by-less proof step (~½M kernel-steps)"
or gives up; you must name both chains and write an explicit combining calc.
(2026-07-15, brick-6b conjugation identity, four times.)

**Root cause.** `done`'s search re-derives the bridge by unfolding the
expensive endpoints instead of noticing both were just shown equal to a
common named term.

**Fix direction.** When the context contains `A = v` and `B = v` (or the two
most recent facts share an endpoint), close `A = B` by transitivity through
`v` *before* attempting definitional search.

**Detail.** `QUIRK.md` (to be added), brick-6b session notes.

---

## F7 · `if P then a else b` discards the witness  ·  **P3**

**Symptom.** A branch of `if`/`decide` cannot use `P` (the witness is bound to
`_`), so proof-carrying uses fall back to `Natural.compare_strict` or explicit
`decide`. Owner idea: inject the witness as an anonymous context fact (and a
named `if P as h then …` cousin).

**Detail.** `numeral_let_ring_elaborator_gaps` item 6.

---

## F8 · Long structural case trees are boilerplate-heavy  ·  **P3**

**Symptom.** Deciding an index against a few landmarks (e.g. `i ∈ {a, b,
other}`, then the same for `j`) is a hand-written 3×3 `by cases` nest
(brick-6b `pairOrient_swap_adjacent_other`, `swap_conjugate_by_swap`).
Mathematically it's "case on where each index sits"; the surface cost is high.

**Fix direction.** Explore a multi-way `cases i against a, b` sugar, or a
tactic that splits a finite type by named landmarks. Speculative; measure
whether it recurs before building.

---

## F9 · Error-message quality  ·  **P1 (parallel track)**

The triage pipeline already exists: `scripts/record_error.sh` →
`docs/error_message_inbox.md` → promote to `docs/error_message_corpus.md`
(5-axis rubric) → `library/ErrorTest/` regression. Work items:
- Sweep open corpus entries; re-score against the current build (several may
  already be stale-fixed, per the 2026-06-29 sweep pattern).
  - DONE (2026-07-15): the "`by_induction` 1+n mixed `case zero:`/`case
    step(k):`" message (inbox) is already fixed — `induction.cpp` now names
    the offending clause and suggests the `zero`→`base` / `successor`→`step`
    rename. Stale inbox entry; leave the note as a data point.
- Specific low-scorers to improve, captured while working:
  - "auto-prover gave up after exhausting its effort budget" — should name the
    likely missing bridge, not just suggest raising the budget.
  - F1's argument-mismatch message is *clear* but could add "these differ by
    `add_commutative` — the forms are not definitionally equal" when both
    sides are Natural-arithmetic. **OBVIATED (2026-07-15) — do NOT ship this.**
    Empirically, strategy (e) additive-rearrangement coercion now rescues
    EVERY genuinely-equal Natural additive spelling that reaches an argument
    slot: positional, theorem-body, return position, and named-arg-when-the-
    other-args-are-pinned all verify (tested `1+k`↔`k+1` in each). The only
    mismatches that still reach the kernel "wrong type" message on Natural
    relations are (a) genuine INEQUALITIES (`k+1` vs `k+2`) and (b) an
    argument mis-inference (`k` bound to `1`, giving `1+1 ≤ n` vs `1+k ≤ n`) —
    for BOTH, an "these differ by `add_commutative`" note would MISLEAD (it
    would send the user to bridge two forms that are not in fact equal). A
    prototype note was written and reverted for exactly this reason. The F1
    coercion work subsumed this message item.
  - Head-mismatch citation leaked `<unknown>` for a `∀`/`→` goal —
    **DONE (2026-07-15, corpus #23):** `inference.cpp` now describes a
    non-constant goal/conclusion head by shape ("a `∀`/`→` statement")
    instead of the internal placeholder. Regression
    `library/ErrorTest/citation_goal_head_pi.math`.
  - F4(c): "ring failed" on `sum = <opaque var>` should suggest the equating
    hypothesis.

---

## Recommended session order

1. **F1 (Natural additive normal form in the matcher)** — P0, user-flagged,
   highest surprise-per-encounter, and it subsumes F4(b) and part of F2.
   Biggest single uniformity win; retires the wrapper-lemma idiom.
2. **F2 (provable-not-defeq argument coercion + instance premise discharge)**
   — builds directly on F1's normalizer; kills a second class.
3. **F3 (substituting/calc symmetry)** — small, frequent, self-contained.
4. **F9 (error-message sweep)** — run as a parallel/interleaved track; cheap
   per item, compounding.
5. **F5, F6** — need minimal repros in `QUIRK.md` first, then targeted fixes.
6. **F4(a), F7, F8** — opportunistic; F8 only if it recurs.

Each landed item: delete it here (or mark DONE with the commit), add a
`library/ErrorTest/` or feature regression, and update the memory note it
came from.

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

**Detail.** `numeral_let_ring_elaborator_gaps` items 4 & 5, `coercion_join_project`.

---

## F3 · `substituting` / calc rewrite direction  ·  **P1**

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
- Specific low-scorers to improve, captured while working:
  - "auto-prover gave up after exhausting its effort budget" — should name the
    likely missing bridge, not just suggest raising the budget.
  - F1's argument-mismatch message is *clear* but could add "these differ by
    `add_commutative` — the forms are not definitionally equal" when both
    sides are Natural-arithmetic.
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

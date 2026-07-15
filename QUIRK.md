# Elaborator quirks worth investigating

Working notes for things that look like bugs / surprises in the
elaborator. The goal is to come back to these in a dedicated session
once we have more context. Each entry: symptom, root cause hypothesis,
attempted fixes, and the workaround the library currently uses.

Catalogued and prioritized in `PLAN_ERGONOMICS.md`; the repros live here.

## Q1 — implicit `n` mis-inferred under an expected-type ascription (F5)

**Symptom.** With `x : NaturalsBelow(k)`, the trivial bound
`NaturalsBelow.value(inclusion(k, x)) < k` is `NaturalsBelow.below(x)` (since
`value(inclusion(k, x))` is definitionally `value(x)`), but writing
`let p : NaturalsBelow.value(NaturalsBelow.inclusion(k, x)) < k :=
NaturalsBelow.below(x)` (or passing it to an argument slot of that type)
fails: "the function expects `NaturalsBelow k` but this argument is …",
because `NaturalsBelow.below` is elaborated with implicit `n := 1 + k`.

**Root cause hypothesis.** The expected type mentions `NaturalsBelow.value`
whose implicit `n` is `1 + k` (its argument `inclusion(k, x) : NB(1+k)`).
Unifying the expected type against `below`'s return `value(element) < n`
propagates `n := 1 + k` and `element := inclusion(k, x)` before the elaborator
reduces `value(inclusion(k, x))` to `value(x)` — so it never tries `n := k,
element := x`.

**Attempts.** None yet — flagged during brick-6a, worked around.

**Workaround.** Derive the bound at the `n = k` spelling on its own line
(`NaturalsBelow.value(x) < k by NaturalsBelow.below`) and route the downstream
term through `NaturalsBelow.make(NaturalsBelow.value(x), …)` instead of
`value(inclusion(k, x))`.

## Q2 — `done` re-derives an expensive bridge instead of using a shared value (F6)

**Symptom.** Two calc chains establish `A = v` and `B = v` for a small `v`,
where `A` and `B` mention `Permutation.compose` / `Permutation.swap`. A
trailing `done` (to prove the per-index goal `A = B`) either emits
"expensive by-less proof step (~½M kernel-steps)" or exhausts the auto-prover
budget, even though `A = v` and `B = v` are both in context.

**Root cause hypothesis.** `done`'s search tries to reconcile `A` and `B` by
unfolding the opaque/expensive endpoints (`compose`, `swap`) rather than
noticing both were just shown equal to the common named term `v` and closing
by transitivity through it.

**Attempts.** None yet — flagged during brick-6b (`swap_conjugate_by_swap`,
four per-index leaves).

**Workaround.** Name both chains (`… as lhsEq`, `… as rhsEq`) and write an
explicit combining calc `A = v by lhsEq = B by rhsEq` (the named-hyp flip that
F3 also wants).

## How to use this file

When a new quirk shows up that's worth a dedicated session, add an
entry with the four sections (symptom, hypothesis, attempts,
workaround). Don't fix in the same session that found the quirk
unless the fix is genuinely localised — otherwise the investigation
sprawls.

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

## Q3 — citation bridging does not δ-unfold a wrapper HEAD on the goal side

**Symptom.** A chain step (or claim) whose left endpoint is a wrapper
definition — `Matrix.quadraticForm(Mᵀ * A * M, x)`, which δ-unfolds to
`RingVector.innerProduct(x, (Mᵀ * A * M) · x)` — cannot cite the lemma
that rewrites UNDER the wrapped spelling:

    Matrix.quadraticForm(Mᵀ * A * M, x)
       = RingVector.innerProduct(x, (Mᵀ * A) · (M · x))   by Matrix.applyVector_multiply

fails with "the conclusion shape fits, but an argument could not be
inferred from the goal or a premise discharged from context" (single-step
form; the multi-step calc form failed with "justification proves a
different relation"). Hit live twice: S1 build 992a4fc3
(`quadraticForm_pullback`) and the T1 probe repro (2026-07-18).

**Root cause hypothesis.** The citation matcher's endpoint reduction
handles the RELATION endpoints, but diff-inferred congruence compares the
two sides structurally BEFORE δ-unfolding the head constant of the goal's
LHS — `quadraticForm` vs `innerProduct` never align, so the congruence
site (`innerProduct`'s second argument) is never found, and match-and-
unify against the lemma's conclusion is attempted at the wrong altitude
("shape fits" = the applyVector equation matched somewhere, but the
enclosing congruence could not be assembled).

**Attempts.** None in-pass (T1 is probe-only by design).

**Workaround.** Open the chain with an explicit defeq step down to the
unfolded spelling, then cite:

    Matrix.quadraticForm(Mᵀ * A * M, x)
       = RingVector.innerProduct(x, (Mᵀ * A * M) · x)         -- defeq, by-less
       = RingVector.innerProduct(x, (Mᵀ * A) · (M · x))       by Matrix.applyVector_multiply

Arguably good pedagogy at a definition's FIRST unfolding, but it taxes
every wrapper-headed chain; the fix (δ-unfold candidate heads before
diff-matching, symmetric to the ζ-unfold the chain endpoints already get)
is elaborator work for a dedicated session.

## Q4 — a universe-polymorphic `automatic` theorem never fires

**Symptom.** `automatic theorem Equality.not_equal_symmetric {A : Type} …`
verifies fine but the discharge never uses it: the failed-claim candidate
listing shows it with `(A : Type _auto_u_0)` and no "needs import" note —
in scope, shape-matched, yet not applied. Changing the binder to
`{A : Type(0)}` makes the same lemma fire silently (T3, 2026-07-18).

**Root cause hypothesis.** The automatic-lemma index stores/matches at a
concrete universe; an unresolved `_auto_u_0` level variable in the key
fails unification with the goal's concrete level (or the registration is
skipped for polymorphic entries). No diagnostic distinguishes "not
automatic" from "automatic but universe-blocked".

**Attempts.** Monomorphizing to `Type(0)` — works; adopted.

**Workaround / rule.** Declare `automatic` lemmas MONOMORPHIC (`Type(0)`
carriers) until the index learns levels. Fix candidates: unify levels in
the automatic index, or at least warn when an `automatic` declaration is
universe-polymorphic (it silently degrades to citation-only today).

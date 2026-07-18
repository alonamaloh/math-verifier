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

**Audit 2026-07-18.** Full-library scan of every `automatic` declaration
(259: 258 `:=`-form + `And.right`'s pattern-match form) for bare-`Type`
binders: **none polymorphic — no registration is silently dead.** The
exposure is confined to future declarations until the index fix lands;
the rule above is the guard.

## Q5 — `ring` atomizes definition applications: `(a • x)(k)` never reduces

**Symptom.** In a goal like `A(i, k) * (a • x)(k) = a * (A(i, k) * x(k))`
(where `(a • x)(k)` β/δ-reduces to `a * x(k)`), `ring` fails with "the two
sides do not agree mod 2^61 − 1 … the identity is FALSE" — it treats the
unreduced application `(a • x)(k)` as an opaque atom, so the polynomial
fingerprints genuinely differ. The identity is true; the report of
falsity is an artifact of the atomization. Hit in
`Matrix.applyVector_scale` (T5.1, 2026-07-18). Sylvester's inequality
work will produce this shape constantly (index applications of scaled /
added vector definitions).

**Root cause hypothesis.** `ring`'s atom collection normalizes numerals
and ζ-unfolds `let`s but does not β/δ-reduce a definition applied to
arguments before deciding atomhood — same family of blindness as Q3
(matcher/diff-congruence) and the T5.3 registry head checks: subsystems
compare heads without reducing first.

**Attempts.** None (found mid-T5; workaround adopted).

**Workaround.** Either state the pointwise fact at the already-reduced
spelling, or close the step with `done by substituting
<operative-lemma>` (the auto-prover's rewrite search DOES see through
the application — it closed the same goal that `ring` refused). The
misleading "identity is FALSE" wording deserves a caveat when any
non-variable application was atomized.

## Q6 — `by substituting <quantified-lemma>` under an aggregation head picks the registered congruence and dies

**Symptom.** A chain step rewriting INSIDE `CommutativeRing.productOver`/
`sumOver` via a quantified lemma —
`… = productOver(term, prepend(top, map(incl, E))) by substituting
NaturalsBelow.enumerate_one_plus`, or a reindex via `by substituting
CommutativeRing.productOver_map` — fails with
"claim `(@_hole_2_CommutativeRing.productOver_congruence i) =
(@_hole_3_…)`: no in-scope hypothesis matches …": the diff bridge
commits to the REGISTERED congruence lemma for the aggregation head
(`productOver_congruence`, which congruences the TERM function pointwise)
even when the diff is in the LIST argument (or both), leaving its two
term-function holes unfillable. Hit twice in
`Matrix.determinant_bordered_top_row` (2026-07-18).

**Root cause hypothesis.** The rewrite justification path prefers the
lemma-index congruence entry keyed on the outer head constant over plain
positional congruence `f(x) → f(x')`; for `productOver` the registered
entry only covers the term-function slot.

**Attempts.** None in-session (worked around).

**Workaround.** Pre-state the rewrite as a GROUND named fact
(`X = Y by <quantified-lemma> as name;` — goal-driven citation handles
the instance fine), then `by substituting name` in the chain. The same
failure did not occur for scalar-position rewrites (`from_integer` arg,
matrix-entry args), which bridge by plain congruence.

## Q7 — `substituting` and lemma-instance search do not ζ-unfold `let`-spelled goal terms

**Symptom.** `… by substituting Permutation.pairOrient_extend_row` fails
with "no instance of its left- or right-hand side occurs in the goal"
when the goal spells the instance through chain-local `let`s
(`map(ambientPair, E)` for the lemma's literal lambda): the occurrence
check is syntactic and does not ζ-unfold. Chain ENDPOINTS do get
ζ-unfolded (whole-equation conclusion matches against `let`-spelled
endpoints work); the occurrence search inside `substituting` does not.
Hit in `Permutation.pairOrient_extend_block` (2026-07-18).

**Workaround.** Insert an explicit by-less defeq chain step that
re-spells the `let`-abbreviated term literally, then substitute. (Same
family as Q3/Q5: subsystems compare terms without reducing first.)

## Q8 — two small elaborator gaps hit while building sign_extend

- **Implicit under `Set`-typed slot:** `List.filter(Permutation.indexPairBelow, …)`
  fails to instantiate `indexPairBelow`'s implicit `{n}` when the filter's
  element type is still a metavariable at that argument's elaboration
  ("expects Set(Pair …) but argument is (n : Natural) → …") — the
  deferred-second-pass fix (T6 (b)) does not fire when the expected type
  is the `Set` wrapper. Workaround: ascribe the predicate
  `(Permutation.indexPairBelow : Pair(…) → Proposition)`.
- **`witness` in a disjunct position:** with goal `(∃ …) ∨ P`, an arm
  proof `witness v with done` errors ("anonymous tuple: 'Or' has 2
  constructors") — the disjunction-injection coercion is not tried for
  the `witness` form. Workaround: state the existential as a bare fact
  (`∃ …. P by { witness v with done };`) and close with `done`.

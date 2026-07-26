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

## Q9 — CLOSED 2026-07-19: under-binder congruence (`by ((x) ↦ …)`) fell through when the changed slot's head is a compound application

**Symptom.** A chain `=` step between two `CommutativeRing.sumOver` calls whose
lambdas differ pointwise, justified by the under-binder pointwise-lambda form,
fails with "bare `claim` / `done` needs an expected type from context" pointing
into the lambda body — the congruence path silently fell through and the lambda
was elaborated with no expected type. Trigger: the differing slot's root is an
application whose HEAD is itself a compound application — a matrix-product
entry `(B * Matrix.inclusionMatrix(r, sel))(p, j)` rewritten to `B(p, sel(j))`,
or a definition application `Matrix.borderElimination(B)(k, l)` rewritten to
`Matrix.identity(r, 1 + m)(k, l)`. The same step with a VARIABLE-headed slot
(`C(i, j)` → `D(i, j)`, or `u(j)` → `v(j)` inside a product) fires fine, as
does a whole-body swap where both bodies share a `*` root
(`Test/name_your_summands_test.math`).

**Repro.** Same import set as `Algebra/matrix_submatrix.math`:

```math
theorem Test.probe_entries {r : CommutativeRing} {m : ℕ}
        (B : Matrix(r, 1 + m, 1 + m)) (i : NaturalsBelow(m))
        : CommutativeRing.sumOver(
              (j : NaturalsBelow(m)) ↦
                  (B * Matrix.inclusionMatrix(r, NaturalsBelow.inclusion(m)))(NaturalsBelow.inclusion(m, i), j),
              NaturalsBelow.enumerate(m))
          = CommutativeRing.sumOver(
              (j : NaturalsBelow(m)) ↦ B(NaturalsBelow.inclusion(m, i), NaturalsBelow.inclusion(m, j)),
              NaturalsBelow.enumerate(m)) :=
  CommutativeRing.sumOver(…f…) = CommutativeRing.sumOver(…g…)
      by ((j : NaturalsBelow(m)) ↦ { done by Matrix.multiply_inclusionMatrix_entry })
-- fails; the identical statement closed via a stated ∀ + argument-free
-- `by CommutativeRing.sumOver_congruence` passes (probe F).
```

**Root cause hypothesis.** The single-binder-diff detection walks the two
lambda bodies in structural lockstep looking for the diff position; when the
differing subterm's function position is itself an `Application` on one side
and a variable (or different-arity spine) on the other, the walk keeps
descending into the spines and lands on a function-level "diff" (e.g.
`Matrix.multiply(…, B, J)` vs `B` as functions), so the assembled pointwise
obligation doesn't match the author's lambda and the path falls through —
another member of the "compare heads without reducing/aligning first"
family (Q3/Q5/Q7).

**Attempts.** Bisected 2026-07-18 with five probes (variable slots, product
slots, compound-head slots, classical route); only compound-head slots fail.

**Workaround (retired).** State the pointwise fact as a named/anonymous ∀ and
close the chain step with argument-free `by CommutativeRing.sumOver_congruence`
(the classical form; was used at five sites in `Algebra/schur_complement.math`).

**Fix (2026-07-19).** The root cause was NOT the diff walk (the top-level
single-slot diff detection was fine): `tryUnderBinderStep` instantiates the
congruence lemma's pointwise premise `∀ x. term(x) = termPrime(x)` with the
two LITERAL lambdas, so the user's proof elaborated against β-REDEX endpoints
`((j) ↦ …)(x)`. A variable-headed slot survives (the auto-prover closes
through the redex); a compound-head slot's cited entry lemma
(`done by Matrix.multiply_inclusionMatrix_entry`) can't match the redex
spelling, the ElaborateError was swallowed, and the path fell through to the
misreport. Two changes in `tryUnderBinderStep`: (1) the pointwise expected
type is β-contracted (`betaNormalizeForDisplay` — pure β, no δ) before the
proof elaborates; (2) mismatched endpoint HEADS get up-to-8 head δβ-steps to
align (`RingVector.extend(y)(top)` vs a literal `sumOver` — Q3 family), so
wrapper-headed endpoints accept the lambda form too. Error quality: a lambda
proof on a calc `=` step now surfaces the recognizer's own reason when it
declines (a lambda has no other reading there), and a lambda hint on an
equality CLAIM appends the reason as a note to the inner error. Locks:
`Test/under_binder_compound_head_test.math`,
`ErrorTest/under_binder_fall_through`, `ErrorTest/under_binder_claim_note`.
All five `schur_complement.math` classical-form sites converted to the
honest lambda form.

## How to use this file

When a new quirk shows up that's worth a dedicated session, add an
entry with the four sections (symptom, hypothesis, attempts,
workaround). Don't fix in the same session that found the quirk
unless the fix is genuinely localised — otherwise the investigation
sprawls.

## Q3 — CLOSED 2026-07-18: citation bridging now δ-unfolds a wrapper HEAD on the goal side

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

**Fix (2026-07-18).** `tryApplyBareLemmaToDiff`'s descent loop gained a
δ-retry on its give-up path: when neither structural equality nor the
defeq tie-break can localise the diff at a level, the sides are re-examined
after `unfoldHeadConstantOneStep` — ONE δβ-step at a time (a full WHNF blew
past the lemma's altitude down to `List.product` internals under a binder),
preferring the single unfold that aligns the two sides' heads, budget 8.
Covers both the single-step claim form and the multi-step calc form (both
route through `tryApplyBareLemmaToDiff`); the applied-lemma walk
(`tryDiffApplyUserProof`) already had its own WHNF retry. Locks:
`Test/reduce_before_compare_test.math` (`Probe.q3_*`). The
`quadraticForm_scale` chain now cites `applyVector_scale` straight from
the wrapper-headed endpoint; `quadraticForm_pullback` keeps its explicit
first unfolding as pedagogy.

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

## Q5 — CLOSED 2026-07-18: `ring` now δβ-reduces definition applications like `(a • x)(k)`

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

**Fix (2026-07-18).** `ringDeltaExposeAtom`: before atomizing, each of the
three atomization sites — the Z/p fast-fail (`evalRingMod`), the polynomial
normaliser (`normaliseToRingPolynomial`), and the proof builder
(`proveEqualsCanonical`, with a reflexivity defeq-bridge stitching
`expression = exposed`) — tries up to 8 head β-contractions / one-step
δ-unfolds and re-dispatches iff the exposed form is a recognised ring shape
(operation at the carrier, or embedded literal); otherwise the ORIGINAL
spelling stays the atom, so atom identity is unchanged for genuinely opaque
terms. `Matrix.applyVector_scale`'s pointwise fact is back to bare `ring`.
The diagnostic is also softened: when the fingerprints differ AND a
transparent-definition-headed application was atomized, the verdict says
"may be an atomization artifact" instead of the flat FALSE (locked by
`ErrorTest/ring_atomized_application_verdict`). Locks:
`Test/reduce_before_compare_test.math` (`Probe.q5_*`).

## Q6 — CLOSED 2026-07-18: not reproducible at HEAD; workaround sites converted and locked

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

**Closure (2026-07-18).** Could NOT be reproduced at HEAD, with the
pre-fix kernel, in any tested shape: both live
`determinant_bordered_top_row` sites accept the direct quantified
citations (`by substituting NaturalsBelow.enumerate_one_plus`,
`by substituting CommutativeRing.productOver_map`) with the ground facts
DELETED, and fresh probes covering list-argument rewrite, bare-`by` diff
path, whole-application reindex, and reindex-under-a-product all pass.
The failure was presumably an artifact of a mid-construction step shape
that the final file no longer contains; the "registered congruence
hijack" hypothesis did not survive testing. Workaround ground facts
removed from `determinant_bordered.math` and `permutation_sign_extend.math`;
the shapes are locked in `Test/reduce_before_compare_test.math`
(`Probe.q6_*`). If it resurfaces, refile with the failing file FROZEN in
a branch so the exact step shape is preserved.

## Q7 — CLOSED 2026-07-18 (fixed): `substituting` now scans a ζ-unfolded goal form

**Symptom.** `… by substituting Permutation.pairOrient_extend_row` fails
with "no instance of its left- or right-hand side occurs in the goal"
when the goal spells the instance through chain-local `let`s
(`map(ambientPair, E)` for the lemma's literal lambda): the occurrence
check is syntactic and does not ζ-unfold. Chain ENDPOINTS do get
ζ-unfolded (whole-equation conclusion matches against `let`-spelled
endpoints work); the occurrence search inside `substituting` does not.
Hit in `Permutation.pairOrient_extend_block` (2026-07-18).

**Workaround (retired).** Insert an explicit by-less defeq chain step that
re-spells the `let`-abbreviated term literally, then substitute. (Same
family as Q3/Q5: subsystems compare terms without reducing first.)

**Closure (2026-07-18).** Two parts.

The ORIGINALLY-FILED sites turned out not to reproduce at HEAD even
pre-fix: `pairOrient_extend_block` verifies with the explicit re-spell
step DELETED, and `sign_extend` accepts `by substituting
NaturalsBelow.enumerate_one_plus` inline with the `enumerationSplits`
ground fact removed (both converted; locked in
`Test/reduce_before_compare_test.math`, `Probe.q7_let_spelled_chain`).

But the REAL failure mode surfaced in the `phi_inner_sum` acceptance
build: when the lemma's instance is visible ONLY through the `let`s
(`aFactor * bTerm(sigma)` where BOTH factors are `let`-names — nothing
in the goal spells the `productOver … * productOver …` instance
literally), `by substituting CommutativeRing.productOver_multiply` died
with the filed "no instance … occurs in the goal" error. FIXED:
`elaborateClaimBySubstitution` and
`collectQuantifiedSubstitutionCandidates` now also search a ζ-unfolded
goal form (`zetaUnfoldLetBinders` + a deep-WHNF pass to contract the
β-redexes it creates), so `let`-spelled goals are searched at their
literal spelling too. Lock: `Test/name_your_summands_test.math` — the
under-binder pointwise chain cites `productOver_multiply` against a
fully `let`-spelled goal.

## Q8 — elaborator gaps around leading-implicit / unapplied-fact arguments

- **FIXED 2026-07-19 — unapplied ∀-fact in an explicit proposition slot:**
  `NaturalsBelow.embed(Natural.less_or_equal_add_right, element)` failed
  ("expects n ≤ n + p but argument is (a b : ℕ) → a ≤ a + b") while the
  same lemma passed unapplied to `NaturalsBelow.make`'s proof slot works.
  Root cause: `make`'s implicits resolve BACKWARD (from the expected
  return type) before its proof slot elaborates, so the slot's domain is
  concrete and the by-name citation path fires; `embed`'s `{k n}` resolve
  from the LATER `element` argument, so the bound slot elaborated under a
  metavariable domain and took the lemma bottom-up (a Pi type that fits
  nothing). Fix: `inferLeadingArguments` now DEFERS a bare-identifier
  argument that is an unapplied ∀-fact (universal over data, Proposition
  conclusion — `factIsUniversalOverData`) to the second pass, exactly
  like bare implicit-leading operations (T6 (b)); the second pass
  elaborates it against the by-then-concrete domain. Lock:
  `Test/unapplied_fact_argument_test.math`.

- **OPEN (sharpened 2026-07-19) — partial application with an unpinnable
  leading implicit in a stated proposition:**
  `Function.IsInjective(NaturalsBelow.shift(n));` fails with "could not
  infer all leading arguments of 'NaturalsBelow.shift': position 0 is
  unassigned" — `shift {p : ℕ} (n : ℕ)`'s `{p}` occurs nowhere else in
  the claim, so the claim TEXT genuinely underdetermines it (this is NOT
  a compare-without-reducing bug: `IsInjective`'s `?A → ?B` unifies fine,
  it just pins nothing). Any fix must complete elaboration WITH an
  unresolved metavariable and then ∀-GENERALIZE it at the statement
  boundary (auto-bound implicits, Lean-style): the claim would record
  `∀ {p}. IsInjective(shift(n))`, which the S2 ∀-instantiation machinery
  already consumes downstream, and a theorem signature would grow a fresh
  implicit binder. That is a core-inference redesign (a mode where
  `inferLeadingArguments` emits a fresh generalizable free variable
  instead of throwing, plus quantification at claim/theorem-statement
  elaboration), not a matcher alignment — deliberately NOT forced in the
  2026-07-19 matcher session. Workaround stands: double-paren ascription
  `Function.IsInjective((NaturalsBelow.shift(n) : NaturalsBelow(p) →
  NaturalsBelow(n + p)))` — 4 sites in `Algebra/matrix_direct_sum.math`.

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

## Q10 — OPEN (attempted + withdrawn 2026-07-19): flex-headed application pattern vs a δ-defined constant when the head is already solved

**Symptom.** In `unifyConstructorParameters`, a pattern `?select(?q)`
whose head metavariable is ALREADY assigned (pinned by an earlier
position — e.g. citing `multiply_inclusionMatrix_transpose_entry_selected`,
where `inclusionMatrix(?select)` pins `?select := shift(1)` before the
index position is reached) silently returns without matching, so `?q`
is never pinned from a target constant like `NaturalsBelow.secondOfTwo`
whose δ-body is `shift(1, top(0))`. Constant-vs-constant head mismatches
δ-align (batch-3 item 2 / the Q3 family); flex-with-solved-head does not.

**Impact today: LOW.** The batch-3 wrapper-head fix
(`unfoldHeadConstantOneStep` re-applies spine args past a value body)
plus defeq validation of the instantiated conclusion carries every live
site — the index hole is pinned from the conclusion's other side, and
the final check accepts the defeq spelling. The gap only bites when the
flex-applied hole occurs NOWHERE else in the conclusion.

**Attempt (withdrawn).** Substituting the solved head and re-running the
node as a rigid match (so the target-side δ-loop fires) is the natural
fix, and it closed the rank_two sites — but it REGRESSED
`Algebra/function_enumeration.math`'s `CommutativeRing.productOfSums_distributes`:
inside a ∀-goal citation, the substituted-head recursion (patterns under
`productOver` lambdas, Miller-solved heads re-entering as lambdas)
poisoned the hole ladder into its bare-lemma fallback ("the `by` hint
citation does not prove this goal", hint typed as the unapplied Π chain
under a stray leading binder). A retry needs either (a) tentative
assignment (unify into a scratch map, commit only if the whole
conclusion then validates), or (b) a guard excluding lambda-valued
solved heads / binder-depth > 0. Lock to build first: a citation whose
flex-applied hole appears only under the solved head
(`Test/citation_delta_alignment_test.math`'s second probe is the
end-to-end shape; it currently passes through the citation ladder's
other rungs).

## Q11 — CLOSED 2026-07-25: chain endpoints at a BUNDLE carrier didn't lift numerals

**Symptom.** Inside a relation chain whose carrier is a concrete bundle's
carrier — `CommutativeRing.carrier(Integer.commutative_ring_bundle)`, the
type of every `Matrix.quadraticForm` value — a step endpoint written with
bare numerals (`= 0 * 0 + 2 * (0 * 0) + 5 * (0 * 0)`) stayed at Natural.
The step was then ill-typed, and the failure surfaced as a citation
mismatch printing two spellings that look identical (`2 * (y * y)` vs
`(Natural.to_integer 2) * (y * y)`) — recipe (d)/(h) of the fifteen-theorem
memory, which cost two sessions' worth of ascription noise
(`(0 : ℤ) * 0 + (2 : ℤ) * …`) and explicit-argument citations.

**Root cause.** `calc.cpp`'s endpoint reconciliation asked
`combineOperands(nextHead, carrierTypeName, …)` with RAW head names. A
bundle projection's raw head is `CommutativeRing.carrier`, which the
coercion registry knows nothing about, so no join was found and the
endpoint was left alone. The `=`-desugaring path (dispatch.cpp) already
handled this by retrying over `carrierHeadCandidates`; the chain path
never got the same treatment.

**Fix.** `Elaborator::combineOperandTypes(leftType, rightType)` —
`combineOperands` keyed on the TYPES, raw heads first and normalized
carrier candidates second — now backs both chain sites (the leading-term
probe and each step's endpoint). Lock:
`Test/chain_numeral_bundle_carrier_test.math`; the whole
`Algebra/critical_value_minimality` + `Algebra/diagonal_forms` pair is now
written with bare numerals (114 ascriptions deleted).

## Q12 — CLOSED 2026-07-25: a `let`-spelled goal blocked citation argument inference

**Symptom.** `let extended := Matrix.diagonalExtension(A, c); …
Matrix.IsSymmetric(extended) by Matrix.diagonalExtension_symmetric` failed
with "could not infer hole(s) at position 3" — the goal's let name hides
the structure the conclusion pattern reads `A` and `c` off. Every such
site had to spell the arguments by name.

**Root cause.** `autoFillHintForClaim` retries ζ-unfolded, but the HOLE
SOLVER (`inferCallWithHoles` Step 2) had no ζ rung: its ladder was raw →
WHNF-both → equality-endpoint reduction → class-equality relaxation.

**Fix.** A final ζ rung in Step 2 (fallback-only; the produced term is
still checked against the ORIGINAL goal, so a ζ step cannot admit a wrong
proof). Lock: `Test/natural_spelling_test.math`'s
`citation_through_a_let`, and the `let block` / `let zero` spelling of
`Matrix.diagonalQuaternaryForm_one_two_five_five_isometric_representative`.

## Q13 — CLOSED 2026-07-25: a premise argument couldn't be a citation of its own

**Symptom.** `Lemma(premise := Other(x := 1, value := done))` failed with
`@_hole_N` goals: `Other`'s data parameters come from `Lemma`'s, which were
still unsolved when the argument was elaborated. Fixing it meant passing
`Lemma`'s data parameters by hand (`A := …, v := …`) even though the goal
determines them — 18 lines of that in the minimality file alone.

**Root cause, two halves.** (a) A `by <application>` hint is deliberately
elaborated with NO expected type first (so a partial application can peel
its Pi chain), so the outer lemma's parameters are unsolved holes; the
inner citation then has nothing to infer from. (b) The failure inside that
speculative attempt was an `AutoProverBudgetError`, which is deliberately
NOT an `ElaborateError` so its rich message survives speculative catches —
so it escaped the recovery instead of falling back.

**Fix.** `autoProveClaim` now declines a goal that still mentions an
unsolved call hole (`containsUnsolvedCallHoleFreeVar`) — no tactic can
assign metavariables, so the search was pure waste — and `recoverClaimHint`
re-elaborates an argument-bearing citation WITH the goal as the expected
type. Lock: `Test/natural_spelling_test.math`'s
`nested_citation_takes_its_data_from_the_goal`.

## Q14 — CLOSED 2026-07-25: `linear_combination` treated a bare numeral coefficient as an atom

**Symptom.** `linear_combination((2 * b + c + 7 * shear) * hypothesis)`
reported "the identity is FALSE as a polynomial" — sending the author after
a mathematical error that does not exist. Ascribing every numeral
(`((2 : ℤ) * b + …)`) fixed it. The docs warned about the top-level
coefficient only, not nested ones.

**Root cause.** The combination tree elaborates each leaf WITHOUT an
expected type (a leaf may be a hypothesis, i.e. a proof), so a bare numeral
landed at Natural; the normaliser then treated the Natural literal as an
opaque ATOM and the combination denoted a different polynomial.

**Fix.** A scalar leaf is lifted to the goal's carrier through the coercion
registry — exactly what the ascription did. Lock:
`Test/natural_spelling_test.math`'s
`linear_combination_bare_numeral_coefficient`.

**Q13 addendum (same day).** The first fix (goal as expected type for a
named-argument citation) was not enough on its own: with a ∀-shaped goal the
conclusion pattern is OVER-APPLIED — the lemma's own conclusion binders
(`∀ (u : ℕ)`, and each premise arrow of the conclusion) are consumed as
argument positions, so the pattern no longer matches the ∀-goal and NOTHING is
pinned. `citePiGoalByIntroduction` then retries at the introduced inner goal
and does pin the data parameters — but a parameter that only a CONTEXT
hypothesis determines (`v` in `¬(u = v)`, matched against the introduced
`¬(u = 1)`) is pinned by the context discharge, which runs AFTER argument
elaboration. Hence part (b): defer an argument whose first elaboration fails
against a hole-bearing domain, and retry it after the discharge. Deferring
UNCONDITIONALLY (on the domain's shape rather than on a failure) regresses
`Polynomial.ExtensionallyEqual.transitive`, whose `Equality.transitivity(?, ?,
?, first, second)` pins its holes precisely BY elaborating those arguments —
forward inference is the reason the domain-shape test is the wrong gate.

## Q15 — PERF, PARTLY CLOSED 2026-07-25: the context-fact scan ζ-unfolded the same terms 40,000 times

**Symptom.** `Algebra/rank_four_exceptional_truants` takes ~10 minutes to
verify, of which ONE theorem (`Matrix.oddC4R2C7_not_represents_ten`) is 413 s.

**Measured.** `contextFactMatch` 84% of the module, ~1.1 s per invocation; the
temporary `zetaRetry:*` buckets showed **174 s in ζ-unfolding alone** over
40,169 calls — the same goal (and the same context-fact types) re-expanded
once per candidate.

**Fixed.** `zetaUnfoldLetBindersCached` memoizes the unfold on (term address,
let-stack fingerprint). Theorem 413→255 s, module ~615→261 s, no proof
changes. Do NOT "fix" it by skipping the ζ retry inside the scan: that is
faster still but breaks `Matrix.weightedD5S0R0C5_represents_below_fifteen`,
whose `let A := …` witness rows need ζ inside the scan.

**Still open.** `contextFactMatch` remains 141 s at 349 ms/invocation there —
the candidate walk over a context that grows to dozens of facts inside nested
`by cases` arms. Levers, in order of expected value: a cheap structural
prefilter before the full matcher; explicit `by` on the proof's bare claims;
a ground fast path in `ring` (the generated tables carry ~23k `by ring` calls
on CLOSED ground equations, and `ring` runs the full AC normaliser on each
while the ground-relation tier already builds a compact certificate).

**Q15 addendum — a NEGATIVE result worth keeping (2026-07-25).** The obvious
reading of the scan census is that the unprompted IMPORT tier is the problem:
on a failing scan the pool averages 158 candidates, of which ~123 are
automatic imports. Gating that tier on the goal's head constant (the 2-level
fingerprint the scorer already computes, checked against BOTH the written and
the WHNF'd goal so an aliased conclusion is not dropped) removes ~78% of the
candidates — and made the heaviest proof **SLOWER**: 255 s → 293 s, 283 s with
the headless-goal guard. Two lessons. Candidate COUNT is not candidate COST:
an import is a small closed statement that fails fast, while a local fact
carries the proof's own `let`-spelled type and is expensive to match. And a
prune that removes an EARLY winner makes the scan fail and the prover fall
through to costlier tactics — so pruning must be justified by measured time,
never by pool composition. The gate survives behind `MATH_SCAN_HEAD_GATE=1`,
default OFF, as a probe for other module shapes.

**Q15 addendum 2 — the local-window census and its (small) payoff, 2026-07-25.**
Owner asked whether the unprompted scan should read only the last few local
facts, and whether "every same-module declaration is automatic" was misguided.
Census (`MATH_LOG_SCAN=1`, 503 scans over five proof-heavy modules —
rank_four_exceptional_truants, sylvester, escalator_tree, Real/continuity,
critical_value_minimality):

| outcome | count |
|---|---|
| nothing won (full walk) | 255 (51%) |
| won by a SAME-MODULE declaration | 151 (30%) |
| won by an automatic import | 71 (14%) |
| won by a LOCAL fact | 26 (5%) |

Pool on a failing scan: 158 candidates — 25 local, 11 same-module, 123 import.
Local wins by distance back in the stack: 21 at 0, two at 1, two at 2, one at 7.

Timings on `Matrix.oddC4R2C7_not_represents_ten` (255 s after the ζ memo):
window 4 as a hard PRUNE 233 s (−8.4%); window 1 as a prune 231 s (−9.6%);
window 4 as a DEFERRAL (far locals moved behind the library tier — no
semantic change) 254 s (nothing). The deferral buys nothing because the far
locals are reached almost exclusively in the 51% of scans that FAIL, and a
deferral still tries everything there.

Conclusions. (a) The same-module tier is the CHEAPEST per win in the system —
30% of wins for 7% of the pool — and the feared blow-up in big generated
modules does not happen: `rank_four_weighted_diagonal_d5_generated` (425
theorems) runs ZERO scans, because every generated row is an explicit
citation. Keep it. (b) A local window is worth ≤10%, and 4-vs-1 is 1% — so
the window size is a STYLE decision (how far may a proof reach silently?),
not a performance one. The mechanism is in the tree behind
`MATH_SCAN_LOCAL_WINDOW=N` (default 0 = off) as a deferral, with a warning
naming the distant fact and asking for a `by`. (c) The cost is concentrated
in the few PLAUSIBLE candidates that pass the head test and get a deep
matching attempt (~10 ms each), not in the pool size — which is why the ζ
memo (making each attempt cheaper) was worth 38% and every pool-trimming
idea measured here was worth ~0 or negative.

## Q16 — pointers into `FRICTION_PLANE_LAYER0.md` (2026-07-25)

The Plane/Layer-0 session kept its findings in that file, in this format.
Four of its entries meet work recorded here; noting the joins so neither
side re-derives them.

- **its I8** (lemma search ranks by fewest remaining hypotheses, so
  inequality goals return nonsense) is the one place the Q15 SHAPE
  FINGERPRINT belongs without reservation: `kernel search` emits a
  suggestion list, not a proof step, so the winner-loss that blocks the
  fingerprint as a prover filter cannot bite there. Measured discrimination
  on real scans: 86–93% of candidates separated, 91% of the DEEP attempts.
  Rank by shape compatibility first, hypothesis count second.
- **its E2** (`ring` treats `Plane.Vector.first(u + v)` as an opaque atom)
  looks like Q5's mechanism not reaching far enough rather than a new gap:
  `Plane.Vector.first` is a plain `definition` (`Product.first(vector)`),
  and Q5 taught `ring` to δβ-expose definition applications. Check that
  before designing around it.
- **its E4** (a ONE-step relation in proof position reads as a proposition,
  a multi-step chain reads as a proof) is the same parser seam as the
  `witness E with <one-step chain>` trap fixed at the message level on
  2026-07-25 (ErrorTest/witness_one_step_chain). One seam, two symptoms.
- **its I1** (the sign battery cannot parse `e ≤ 0`, only `0 ≤ e`) is index
  work in `lemma_index.cpp` adjacent to Q15's territory: `parseSignJudgment`
  computes an index KEY, so admitting `e ≤ 0` also needs the form bridge
  `e ≤ 0 ⟼ 0 ≤ -e` before any existing rule matches.

Its section I otherwise reads as missing LIBRARY rather than a missing
tactic: I3 (add two inequalities — the most frequent friction in that
batch) is one absent lemma, I2 is one absent `automatic` tag on
`Real.LessOrEqual.negate` (its strict twin has one), I5 is two absent
strict counterparts, and I6 is an API split (`Real.IsNonneg.multiply`
exists, a `≤`-stated `Real.multiply_nonneg` does not). I4 is the genuine
linear-arithmetic decision procedure.

## Q17 — `^`'s LEFT operand never sees an expected type, not even a direct ascription (2026-07-26)

Found while checking whether the coercion improvements let the analysis
files drop their numeral ascriptions. They mostly cannot, and this is
why.

**Symptom.** The named form coerces; the infix form does not.

```math
theorem NamedForm (m : ℕ) (x : ℝ) : Real.power(2, m) * x = Real.power(2, m) * x := ring   -- verifies
theorem InfixForm (m : ℕ) (x : ℝ) : 2 ^ m * x = 2 ^ m * x := ring                          -- parse-time decline
```

```
elaborate error: operator '^' is not supported for operand type 'Natural';
supported: +, *, ≤, <, ∣ on Natural; +, *, - on Integer; ∧, ∨ on Proposition
```

**What is actually happening.** The bare `2` is elaborated bottom-up,
lands at Natural, and `^` is then looked up for Natural — where it is
not registered. The expected type (ℝ, from the goal, the chain carrier,
or a sibling operand) is never consulted for the LEFT operand. This is
the documented "RIGHT operands only; left bottom-up" limit, but `^` is
where it bites hardest, because a Natural exponent makes the left
operand the *only* thing that can carry the carrier.

**Not fixed by an ascription on the enclosing expression.** Measured,
all at goal `… * x` with `x : ℝ`:

| spelling | verdict |
| --- | --- |
| `(2 : ℝ) ^ m` | works — ascription on the immediate base |
| `(2 * 2 : ℝ) ^ m` | works — ascription on the immediate base, compound is fine |
| `(2 ^ m : ℝ)` | **fails** — ascription outside the `^` does not reach the base |
| `(2 ^ m * 2 ^ m : ℝ)` | **fails** |
| `((2 : ℝ) ^ m * 2 ^ m)` | **fails** — an already-Real SIBLING does not help either |

So the only spelling that works is one ascription per `^`, on its base.
That is what `Real/arithmetic_geometric_mean.math` carries: 16 of its 20
numeral ascriptions are `(2 : ℝ) ^ …` and every one is load-bearing.

**Message quality.** The error blames the operator ("`^` is not
supported for operand type Natural") when the real story is "the left
operand was defaulted to Natural before the expected type was
consulted". It sends the reader looking for a missing `^` registration
on Natural rather than at the coercion. The supported-operators list it
prints is accurate and useless here.

**Fix direction.** Give the left operand the same expected-type pass the
right operand already gets, at least when the bottom-up elaboration
lands on a carrier where the operator is unregistered — that case is
unambiguous, since there is nothing to be ambiguous with. Failing that,
say so in the message.

**Related but distinct — the two spellings are not term-identical.**
`(2 * 2 : ℝ)` and `(2 : ℝ) * (2 : ℝ)` are provably equal (`ring` closes
it) but do not interchange in a chain step whose justification matches
on structure: swapping the base of `((2 : ℝ) * (2 : ℝ)) ^ m` for
`(2 * 2 : ℝ) ^ m` in `Real.means_inequality_double` breaks step 12.
Worth knowing before any bulk re-spelling of ascriptions.

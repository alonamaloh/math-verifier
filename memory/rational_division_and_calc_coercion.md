---
name: rational_division_and_calc_coercion
description: Rational `/` operator, calc-endpoint tower-coercion elaborator fix, and the redundant-cast checker's known false positives
metadata:
  type: project
---

Work from 2026-06-24/25 cleaning Real/continuity.math + Real/derivative.math.

**Calc-endpoint tower coercion (elaborator fix, commit f46a992).** A `calc`
endpoint written as a bare lower-tower term (e.g. a Rational in a Real chain)
was NOT coerced up to the carrier: passing `carrierType` as the expected type
does not trigger the registry-tower coercion — only ascriptions
(dispatch.cpp) and operator operands (`combineOperands`) do. So `… ≤ q`
against a Real carrier built a heterogeneous relation and the endpoint needed
an explicit `(q : Real)` ascription just to typecheck. Fixed in the order
engine of `src/elaborator/calc.cpp` (the `elaborateCalc` loop, NOT
`elaborateCalcPreorder` which handles only `∣`/`⊆`): lift the endpoint via
`combineOperands` + `castPushToLeaves`. Regression test in
`library/Test/coercion_join_test.math`.

**Redundant-cast checker (`MATH_CHECK_REDUNDANT_CASTS=1`) caveats.** It is a
*candidate generator*, not a guarantee. Trust it for standalone claims/binders
(a structural-equality probe makes those safe). Do NOT trust it for: (a) calc
SUBJECT casts like `calc (Rational.zero : Real)` — carrier-setters, forced;
(b) before the f46a992 fix, calc `≤`/`<` endpoints (it flagged them via
cross-step attribution but dropping broke elaboration). After the fix, calc
endpoints ARE droppable. Always re-verify a drop.

**Rational `/` operator (library/Rational/division.math).** `a / b :=
a · reciprocal_function(b)`, denominator-nonzero a side condition the `/`
operator leaves to the auto-prover (mirrors Integer.divide). Key trick for
writing `a / b` SUGAR in lemma *statements* despite no definitional proof
irrelevance: keep the `bNonzero` hypothesis in scope so the `/` hole resolves
to that BOUND VARIABLE — a unifiable slot the citation matcher binds to
whatever proof a use site carries. A *compound* proof (`nonzero_of_positive(b,
bPositive)`) baked in instead would NOT match across sites. For `/2`, the hole
resolves to the global `two_is_nonzero` (same constant everywhere). Lemmas:
`divide_cancel` (b·(a/b)=a), `divide_positive`, `divide_two_doubled`,
`two_positive`, `two_is_nonzero`. `divide_positive`'s `0 < 2` premise must be a
LOCAL claim (`since two_positive`) — `since`-premise discharge searches local
context, not global lemmas.

**`(X : Rational) : Real` double-cast.** The inner `: Rational` is a no-op when
X is already Rational — write `(X : Real)`. But the OUTER `: Real` is
load-bearing at `to_real.multiply_preserves`/`add_preserves` bridge steps: it
keeps the product as `to_real(a·b)` (ascription doesn't push to leaves),
whereas a bare endpoint rides up via the f46a992 fix which DOES push to leaves
(`to_real(a)·to_real(b)`), making the preservation step a no-op. So that outer
cast is genuinely forced.

**`/` now exists for Rational, Real, and Complex.** `Rational/division.math`
(total reciprocal_function), `Real/division.math` (partial Real.reciprocal +
divide_positive via reciprocal_positive, a classical sign case-split),
`ComplexNumber/division.math` (reciprocal-by-`Logic.the` from is_field, mirroring
Real/field; ℂ's 0/1 spelled `RingModulo.{zero,one}(Real.polynomial_commutative_ring,
Complex.definingPolynomial)`). All use the bNonzero-hypothesis-as-slot trick.
Each concrete type registers its own `operator (/)`; there is NO generic field
`/` (IsField keeps inverse propositional, and operator sugar dispatches per
type head anyway). To add reciprocal-by-description for a new field: prove
inverse_unique (ring) + reciprocal_exists (from is_field), then
`reciprocal := Logic.the(...)`; the shared `since reciprocal_exists` citation
makes the_satisfies's existence proof defeq to reciprocal's.

**ε/δ are now REAL in continuity + derivative** (commit 47bd8ee). ContinuousAt,
ContinuousOn, HasDerivativeAt quantify ε / witness δ over ℝ (textbook form).
Built `Real.minimum` (by `Logic.the`, ℝ has no decidable order — closed form via
`/2` was avoided), Real `/2` facts, `Real.divide_two_less_than_self`,
`Real.nonzero_of_positive`, `Real.eq_of_absolute_value_less_than_all_positive_real`
(real-ε bridge to the rational Cauchy-level lemma). Roofs stay RATIONAL (density
bound on |c|,|L|), cast to ℝ at that one boundary; tolerances use Real division.
Consumers intermediate_value + square_root updated. Foundational Cauchy/convergence
stay rational (ℝ's construction). Gotchas hit: (1) `done by substituting errorZero`
rewrote the wrong `Real.zero` (→ unprovable nested-abs → infinite search/timeout) —
use an explicit calc instead; (2) the `/` side-condition `(2:Real)≠0` discharges by
EXPENSIVE lemma search at every `ε/2` site — add a local `claim (2:Real)≠Real.zero`
so it's a cheap context match; (3) a let-bound roof as a calc `since`-endpoint won't
ζ-unfold for the matcher — spell the endpoint out. HINT POLICY (owner, 2026-06-25):
drop only NOISE hints (re-citing an in-scope hypothesis like `by yClose`); KEEP hints
that aid reading OR that the prover needs for SPEED (`by ring` reorders go from fast
to 100k-step search if dropped). `ε/2+ε/2=ε` genuinely needs `since divide_two_doubled`
— reciprocal-based `/` doesn't compute `2·(1/2)=1` for free, so it's load-bearing, not
noise. The redundant-by checker over-flags (ignores the speed cost of dropping).

continuity.math fully refactored (613→458 lines: lets for roofs/tolerances,
`epsilon/2`, division-based cancellation). derivative.math had only casts
cleaned (def + 7 theorems); its halve→/2 conversion is NOT done — it uses
`halve(halve(epsilon))` (ε/4, 46×), `halve(min(...))`, and
`halve_less_than_self` (no `/` analogue), so it needs more division lemmas +
a multiply/scale rewrite. Deliberately-left residuals: `castSum` symmetric
bridge and the pervasive `(d : Real)` probe-point cluster in `unique`. See
[[coercion_join_project]].

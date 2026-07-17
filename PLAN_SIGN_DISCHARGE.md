# PLAN_SIGN_DISCHARGE — sign side conditions checked at the point of use

## Goal

A proof should never have to *state* that something is nonnegative,
positive, or nonzero unless the fact is a mathematical waypoint the
reader wants. Routine sign facts — "a product of nonnegatives is
nonnegative", "a cast natural is nonnegative", "a square is
nonnegative" — should be discharged silently where a lemma's side
condition needs them, the way `/`'s denominator condition already is
(the structural `tryProveNonzero` walker).

## Case study and what it taught us (2026-07-17)

`Real/arithmetic_geometric_mean.math` carried ~50 lines of sign
bookkeeping: a 20-line "nonnegativity inventory" (pairwise `IsNonneg`
product pyramid feeding `multiply_by_nonneg_right` side conditions),
three 4-line cast ladders (`Rational.IsNonneg((m : ℚ))` →
`Rational.zero ≤ (m : ℚ)` → `(Rational.zero : ℝ) ≤ (m : ℝ)` →
`0 ≤ (m : ℝ)`), duplicate `0 ≤ X` / `Real.IsNonneg(X)` pairs, and
hand-rolled `-(square) = 0 - square ≤ square - square = 0` chains.

**Finding 1 — the existing machinery is stronger than the proofs
assume.** After adding THREE one-hop `automatic` lemmas
(`Real.from_natural_LessOrEqual_zero`, `Real.from_natural_IsNonneg`,
`Real.negate_nonneg_le_zero`), *every* line of that bookkeeping became
deletable: `tryResolvePremiseSlot`'s backward chaining recurses through
`IsNonneg.multiply` / `power_nonneg` / the `IsNonneg` ↔ `0 ≤` bridge
lemmas to considerable depth, both for calc-step side conditions and
for bare claims. Verification wall-clock was unchanged (~15 s). The
inventory existed because the proofs predate parts of the discharge
machinery, and because a few LEAF lemmas were missing their one-hop
`automatic` forms.

**Finding 2 — the genuine mechanism gap is ∀-instantiation.** A
universally-quantified context fact (`termsNonneg : ∀ j. 0 ≤ s(j)`)
does NOT discharge a premise `0 ≤ s(k ∸ 1)`; the instantiation had to
stay written out. This is the one place the case study could not be
cleaned.

**Finding 3 — beware stale sealed caches while iterating.** One-off
`kernel verify` runs against a stale `Real.interface` cache produced
misleading "search failed"/"unknown lemma" results and nearly caused
wrong depth conclusions; conclusions about prover reach must be drawn
after `make -j 16 library`.

**Finding 4 — error quality.** A failed bare sign claim inside a
`∀ … by { take …; if … }` block surfaced as "decide P { … } needs an
expected type from context" — the underlying claim failure was
invisible (filed in the inbox).

## Remaining scope, by stage

### S1 — complete the one-hop `automatic` sign battery (library only)

Audit and fill the table: for each judgment {`IsNonneg`, `0 ≤`, `0 <`,
`≠ 0`} × operation {cast-of-ℕ, `+`, `*`, `^`, square, `negate`,
`partialSum`, `partialProduct`, `absolute_value`, `reciprocal`} × carrier
{ℝ, ℚ}, there should be a directly-citable (and, where safe,
`automatic`) lemma in BOTH spellings the discharge sites want. Most
exist; the AM-GM session showed which kinds were missing (cast-nonneg
at ℝ, negate-of-nonneg-below-zero). Each fill is a 5-line lemma next
to its family. Acceptance: grep-driven checklist, no elaborator change.

### S2 — ∀-fact instantiation in premise discharge (elaborator)

In context-discharge (and `tryResolvePremiseSlot` leaves), when a
premise `P(t)` fails direct type-match, try context facts of the form
`∀ (x : T). P(x)` whose body matches the premise with `x := t`
(matchAgainstPattern with one metavariable — the same machinery, no
new search). Gate: only for Proposition-typed premises; the
instantiation is pinned by the match, so no search widening. This
closes the one residual line in AM-GM (`0 ≤ s(k ∸ 1)`) and the same
pattern everywhere sequences/families appear (`termsNonneg`-style
hypotheses are ubiquitous in the analysis corpus).

### S3 — decide: is a dedicated structural sign tier still warranted?

The original idea (mirror `tryProveNonzero` as a recursive
`tryProveSign` walker: multiply/add/power/negate/cast/literal/square
rules, context + ground leaves, hooked into `autoProveClaim` and
premise discharge). After Finding 1 this is NOT clearly needed for
*capability* — backward chaining already reaches these proofs. Its
remaining value would be:
  - **predictability/perf**: search-free, so sign goals stop depending
    on the `automatic` pool, import scope, and chain-depth budgets
    (the ε-δ files' prover cost is context-scan-bound; a syntactic
    walker adds nothing there);
  - **uniformity**: one place that knows the `IsNonneg` / `0 ≤` / `≥`
    spelling triangle and the cast tower, instead of a lemma battery
    per carrier.
Decision gate: run the B5 hint classifier (`MATH_CLASSIFY_HINTS`,
tier-4 sign counts) after S1+S2 and the S4 sweep; build the tier only
if a meaningful residue of sign hints/claims survives, or if the sweep
shows search-time regressions. Owner sign-off before starting.

### S4 — sweep the corpus (library only, after S1/S2)

Delete now-redundant sign inventories file by file, keeping the
mathematical waypoints (a `0 < partialSum` case pivot, a `mean ≥ 0`
the argument turns on). Candidates by density (sign-statement lines):
`Real/exponential.math` (37), `Real/derivative.math` (36),
`Real/continuity.math` (19), `Real/division.math` (18), plus spot
passes over `cauchy_schwarz`, `harmonic_series`, `square_root`,
`binomial_theorem`, and the ℂ modulus files. Method: the AM-GM recipe —
delete a cluster, verify, restore only what breaks, and record every
restored line as either a missing S1 lemma or an S2/S3 gap. Each file
is its own commit; re-verify wall-clock per file (no silent perf
regressions).

## Non-goals

- No new surface syntax: the win is *deleting* lines, not adding a
  `positivity`-style tactic keyword. (If S3 lands, it is invisible.)
- No change to the `automatic`-pool discipline: S1 lemmas are one-hop
  facts of the kind already marked `automatic` throughout the order
  files.
- ℕ needs nothing (0 ≤ n is definitional); ℤ only via the ground tier,
  which already decides its sign goals.

## Status

- 2026-07-17: case study + quick wins LANDED (3 lemmas, AM-GM swept
  ~50 → 4 waypoint lines, tests green). Inbox
  entries filed: misleading decide-shaped error for failed take/if
  claims; ∀-instantiation gap.
- 2026-07-17 (second pass): **S1, S2, S4 ALL DONE.** S3 remains
  decision-gated (see evidence below).
  - **S1 (a4bc868d + follow-ups):** probe-driven audit — every
    judgment × operation cell as a bare claim in a scratch module —
    then 20 one-hop fills: ℝ add-positivity trio,
    negate_nonpositive_ge_zero, positive_of_nonneg_nonzero,
    nonneg_of_positive (the 0-anchored weaken BRIDGE the sign index
    needs — LessThan.weaken itself is not 0-anchored so never
    registers), power_nonzero, negate_nonzero, reciprocal_nonzero,
    divide_nonzero, absolute_value_positive; the
    LessOrEqual_zero_of_IsNonneg bridge flipped automatic (ℚ parity);
    ℚ twins of all of the above plus less_or_equal_add_of_nonneg,
    power_positive, reciprocal_function_nonzero, divide_nonneg. The
    full 46-cell probe discharges silently at both carriers.
  - **S2 (ca15c22f):** ∀-fact instantiation
    (`tryInstantiateUniversalContextFact` + `factIsUniversalOverData`
    gate) wired into the THREE premise passes that only did
    direct/conjunction-leg matching: the sign-judgment recursion, the
    monotonicity recursion, and citation context-discharge Step 5b.
    Match pins every binder — no search. AM-GM's residual line is gone.
  - **S4 (7 commits):** exponential −73, derivative −67, continuity
    −29 (zero restorations), division −9, harmonic_series −5,
    square_root −5, ℂ modulus −17. Restored-on-break residuals, each
    recorded in its commit: (a) no one-hop `k! > 0` at ℕ; (b) the
    REWRITE-INDEX precondition pass (abs(x)=x needs IsNonneg(x)) only
    scans binders — two IsNonneg lines restored; (c) `Real.one +
    Real.one` roofs are outside the numeral battery ((2:ℝ) ≢ 1+1);
    (d) done-goals that flowed through a motive arrive WHNF'd as
    `IsNonneg(x − Real.zero)`, invisible to the sign index (sealed
    negate ⇒ not defeq) — cauchy_schwarz's `done by
    LessOrEqual_zero_of_IsNonneg` closers are load-bearing for exactly
    this reason.

## S3 decision-gate evidence (collected by the sweep)

- **Perf:** derivative.math re-verify 8.1 s → 12.9 s (+59%); the
  auto-prover spends 4.3 s across 404 claims re-deriving sign facts
  per premise slot that one context line used to feed. Other files
  unchanged. A search-free structural tier (or per-context sign-fact
  memoization) would recover this.
- **Reach:** three structural holes a tier could own: the WHNF'd
  `IsNonneg(x − 0)` form (needs transport-carrying −0 absorption);
  δ-unfolding of defined subjects (exponentialTerm, modulus) before
  head dispatch; the rewrite-index precondition pass sharing the sign
  machinery.
- Run `MATH_CLASSIFY_HINTS` (B5, tier-4 counts) before deciding;
  owner sign-off required.

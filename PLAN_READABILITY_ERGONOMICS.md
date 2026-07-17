# PLAN_READABILITY_ERGONOMICS — evaluation-driven ergonomic improvements

Source: clean-manifest quality evaluation (2026-07-16, session
01UFc422S3b5EbN7uLoSQCa7). The manifest's theorem tier reads like
mathematics; the residual friction is concentrated in quotient-descent
ergonomics and a few statement-level noise patterns. Numbers at time of
writing: 276 flagged constructions over 189 files (101 direct calls — 62 of
them ≥3-arg, mostly statements/definitions; 95 unfold — boundary files; 69
`Quotient.` — descent files; 11 misc).

Working style: implement → `make -j 16 tests` → apply to a testbed file →
measure (leak counts + read the proof) → commit or revert. Testbed for
R1/R2: `library/Real/density.math` (6× `Quotient.class_of(...)` respellings,
11-line ∃ restated twice). Testbed for R3: `library/Real/algebra.math`
(`sequenceFunction` walls). Wrong paths are fine; git revert and try again.

## R1 — descent keeps the original name (HIGHEST VALUE)

`by_representatives x as ⟨seq, seqCauchy⟩ => body`: after the descent, the
goal is instantiated at `Quotient.class_of(CauchyRationalSequence.make(seq,
seqCauchy))` and the surface name `x` is GONE — so proofs respell the class
6× per theorem (`Real/density.math`) and every ε–δ statement bloats. Fix:
REBIND `x` inside the body as a let-value binder
(`x := Quotient.class_of(make(seq, seqCauchy))`, non-proof LocalBinder with
value) so the user keeps writing `x`. The elaborator's ζ-unfold pathways
(ring/field/sign batteries, autoFillHintForClaim's fallback, block (c)'s
letValues map) already bridge let-aliases; audit the remaining matchers
(calc steps, claim subsumption, substituting) for ζ-blindness and extend
where they fight. Acceptance: density.math's respellings replaced by `x`,
file verifies, no new hints needed. Sweep candidates afterwards: the 30
`Quotient.`-leak files.

## R2 — choose without restating the existential

Two independent halves:
(a) **Multi-witness choose through ∧**: `choose lb, si such that
    0 < lb ∧ (tail…) from fact` where the source is
    `∃ lb. 0 < lb ∧ ∃ si. tail` — peel ∃-layers THROUGH conjunction legs
    (each non-∃ leg becomes a context fact, each ∃ leg supplies the next
    witness). Kills density.math's second 9-line restatement (it re-claims
    the inner ∃ just to choose from it).
(b) **Typed witness annotation**: `choose x : T such that P from <lemma>`
    — the annotation supplies what the closed-witness-type guard cannot
    read from a parameter-typed lemma existential (the map_member_invert
    shape), so the two-step `∃ … by L as name; choose … from name` collapses
    to one.

## R3 — application convention (CoeFun): `rep(n)` for wrapped functions

`CauchyRationalSequence.sequenceFunction(rep_x, n)` walls (Real/algebra's
distributivity_left, all sequence files). Let a type register an
APPLICATION convention: elaborating `f(a)` where `f`'s type is a non-Pi
constant `T` with a registered unwrapper `T.apply : T → (A → B)` rewrites
to `T.apply(f, a)`. Registration piggybacks on the existing name-bound
`convention` mechanism (structures-and-inference.md). Print-side: consider
the reverse sugar later; elaboration-side alone removes the walls from new
proofs. Candidates: CauchyRationalSequence.sequenceFunction,
Permutation.apply, Matrix entries (`M(i,j)` already exists? check),
List.get?.

## R4 — opaque-forcing in the by-lambda path

`… by unfold Real.IsNonneg in ((ε)(εpos) ↦ …)` — elaborateLambda already
peels opaque expected types (weakHeadNormalFormForcingOpaqueHead), but the
`by <lambda>` proof path apparently reaches the lambda with the goal still
folded (two opacity layers: LessOrEqual → IsNonneg → ∀ε…). Reproduce by
deleting one `unfold … in` in density.math; fix the by-proof path to force
opaque heads the same way; re-verify. Low effort, removes mechanics from
boundary files.

## Deferred (noted, not this pass)

- Record-transport sugar for `make_equal_*` statements (the ≥3-arg
  transport walls in finite_permutation): needs proof-irrelevant field
  update syntax; big design.
- Print-side abbreviation of long qualified names in errors/warnings.
- The endpoint-retry WHNF overshoot (bounded one-step-unfold retry) — filed
  in the inbox 2026-07-16.

## Status ledger

| item | state | notes |
|------|-------|-------|
| R1   | DONE 2026-07-16 | Transparent INLINE alias (not a ζ-opaque let): elaborateIdentifier substitutes the class spelling at every use, so terms are byte-identical to hand-spelled form and no matcher changes were needed. Bare pattern: alias bound in elaborateQuotientCases; destructure: threaded via pendingScrutineeAlias_ into buildCaseLambda (value = class_of(constructor-applied), built after pattern binders exist). Gated on the body mentioning the name. density.math converted (6 respellings → `x`); library+tests green. Learned: quotient-cases auto-reverts scrutinee-dependent hypotheses (the "cases … refining" frame), so x-hypotheses arrive at the arm already respelled — the alias was the only missing piece. |
| R2a  | —     | |
| R2b  | —     | |
| R3   | —     | |
| R4   | —     | |

Frictions found en route (filed in the inbox): statement-level `≠ 0`
numeral cast-tower (nonzero_of_positive invisible to matchers); citation
head report `False`-vs-`Not` asymmetry; `<`-at-Natural resolution message
(fixed: structural line info + successor-desugar explanation + left-numeral
hint).

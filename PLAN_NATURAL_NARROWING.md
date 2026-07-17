# PLAN_NATURAL_NARROWING — `a - b` as a Natural, by proof obligation

Owner design decision (2026-07-17 session, during the notation work):
mathematicians write `a - b` with an ambient guarantee `b ≤ a` when the
result is used as a natural number. The library already has the honest
WIDENING half: `operator (-) on (Natural, Natural) := Natural.subtract`
returns an Integer (`Integer/natural_subtraction.math` — "no truncation
lie, no proof obligation"). This plan adds the NARROWING half: an
Integer-valued expression used where a **Natural** is expected picks up
a proof obligation `Integer.IsNonneg(e)` (equivalently `0 ≤ e`), and
elaborates through a canonical section of the ℕ ↪ ℤ embedding. The
mathematician writes `p[a - b]` under a hypothesis `b ≤ a` and the
system fills the rest.

Explicitly REJECTED alternative: promoting monus to notation (`∸` was
prototyped and backed out same-day). `Natural.monus` remains the
machine-level truncated operation, spelled by name.

## Design

1. **The section.** A canonical
   `Integer.toNatural (e : Integer) (nonneg : Integer.IsNonneg(e)) : Natural`
   with characterising lemmas:
   - `Integer.toNatural_from_natural : Integer.toNatural((n : Integer), _) = n`
   - `Integer.from_toNatural : (Integer.toNatural(e, h) : Integer) = e`
   - transport through `+`/`*` where both obligations hold (as needed by
     testbeds, not speculatively).
   Candidate implementation: via `Integer.absolute_value_natural`
   (equal to it on the nonneg cone, so the value function can BE
   `absolute_value_natural` with the obligation carried separately —
   keeps the data proof-irrelevant and matcher-friendly; decide at
   implementation time whether a separate name earns its keep).
   Proof-irrelevance discipline: the `nonneg` argument must never block
   matching — follow the `Subtype`/`Logic.the` precedent
   ([[value_level_conditional_decide_if]], Real.reciprocal idiom).

2. **The elaborator hook.** Where an Integer-typed term meets a
   Natural expected type (argument positions, `[]` indices, calc
   endpoints), insert `Integer.toNatural(e, ?obligation)` and discharge
   the obligation like `/` discharges nonzero:
   - first the auto-prover against the local context (a hypothesis
     `b ≤ a` should close `IsNonneg(a - b)` through one bridging lemma
     `Integer.IsNonneg_of_le : b ≤ a → Integer.IsNonneg(a - b)`),
   - then a structural `nonneg` battery walking the cast tower
     (mirror `tryProveNonzero` / the `nonzero` fallback in
     desugar_equality.cpp — same shape, different predicate).
   Entry point: alongside `coerceToExpectedTypeViaRegistry` (the
   registry's unconditional coercions run first; the narrowing is the
   conditional fallback — it must NEVER fire when a widening solves the
   mismatch, so it only triggers on the strictly-downward ℤ→ℕ case).

3. **Failure mode.** When the obligation cannot be discharged, the
   error must name the missing fact and the recipe:
   "`a - b` is used as a Natural, which needs `Integer.IsNonneg(a - b)`
   — no in-scope hypothesis gives it (a `b ≤ a` would); state one, or
   use `Natural.monus` if truncation is intended."
   A total-lambda site (see Non-goals) hits exactly this error; the
   message's monus pointer is the escape hatch.

4. **Registration form.** Hard-wire ℤ→ℕ first (the `()`/`[]` playbook:
   prove value, then decide). If a surface form earns its keep, the
   natural spelling is a variant of the coercion statement —
   `narrowing (Integer, Natural) := Integer.toNatural requiring Integer.IsNonneg`
   — but do NOT build the general mechanism speculatively; ℚ→ℤ / ℝ→ℚ
   narrowings have no current demand.

## Non-goals

- **Binder-position / total-lambda sites keep monus.** The convolution
  summand `(i : ℕ) ↦ p[i] * q[k - i]` must be total in `i`; inside the
  lambda no `i ≤ k` exists and the obligation is false for `i > k`.
  `Natural.monus` stays at those sites (Polynomial multiply internals,
  `Ring.Sum.reverse`, degree_product bounds). A future alternative —
  range-restricted aggregation over `NaturalsBelow(k+1)` — is a
  separate, larger design (det-cone sumOver/productOver would want the
  same treatment); out of scope here.
- Print-side folding of `toNatural` applications.
- Touching the sealed Natural/Integer opacity boundaries
  ([[natural_sealing_plan]], [[opaque_integer_boundary]]).

## Testbeds and acceptance

- **Discovery stage first**: sweep the library for (a) contortions that
  exist only to avoid ℤ→ℕ narrowing (index arithmetic staged through
  helper lets/lemmas, monus used where a bound IS in scope), and
  (b) natural statements currently unwritable (`p[degree - 1]` under a
  `1 ≤ degree` hypothesis — Polynomial/division.math's degree descent is
  the likely first customer). The evaluation decides the testbed list;
  do not force sites.
- Acceptance per site: the narrowed spelling verifies with NO new
  hints beyond the mathematically-honest hypothesis, reads like the
  paper form, and the obligation failure message fires usefully when
  the hypothesis is removed.
- Gates: `make -j 16 library` + `tests` + error-tests green; new
  ErrorTest for the undischargeable-obligation message; feature test
  for the section's characterising lemmas and the hook.

## Status ledger

| item | state | notes |
|------|-------|-------|
| N0 discovery sweep | TODO | Inventory ℤ→ℕ-avoidance contortions + candidate sites; pick testbeds. |
| N1 section + lemmas | TODO | `Integer.toNatural` (or absolute_value_natural + obligation), characterising lemmas, `Integer.IsNonneg_of_le` bridge. |
| N2 elaborator hook | TODO | Conditional narrowing at Natural-expected positions + `nonneg` battery (mirror `tryProveNonzero`); loud failure message; ErrorTest. |
| N3 testbed + read | TODO | Apply at N0's sites, read the proofs, measure; friction to inbox. |
| N4 registration/docs | TODO | Decide hard-wired vs surface form; docs (structures-and-inference.md coercions section, reference.md). |

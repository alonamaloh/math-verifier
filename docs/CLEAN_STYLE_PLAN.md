# Clean-style plan: growing the "reads like math" set toward the whole library

The overriding goal of this project is that proofs read like what a
mathematician would write in a textbook, with the kernel doing the
typechecking (see `docs/conventions/proof-style.md`). This document tracks the
plan for extending that *clean* style from a small seed set to the entire
library.

## The clean manifest and its ratchet

`scripts/clean_manifest.txt` lists the files held to clean style. It is a
**growing set**: a file joins it once it reads like math and is
redundancy-clean, with only *intended-boundary* residuals left (opaque
`unfold`, the quotient-construction `Quotient.` lifts, foundational raw-CIC, a
documented elaborator gap). The set was seeded from the original headliner cone
(the former "baby library", 35 files).

- `make clean-status` — milestone dashboard.
- `make clean-check` — verifies every manifest file and asserts their residual
  leak total ≤ `CLEAN_LEAK_BUDGET`. Wired into `make check`, so **a file in the
  manifest cannot regress**, and the budget ratchets *down* as elaborator
  features remove the intended residuals.

Adding a file to the manifest is a one-line edit *after* it is cleaned; bump
`CLEAN_LEAK_BUDGET` only by the file's documented intended residuals.

## The milestone ladder (vertical slices)

Rather than clean horizontally by layer, we chase **headline theorems** whose
entire import cone — every line down to the axioms — reads like math. The cones
nest along the analytic tower, so each is a checkpoint toward the next:

| Milestone | cone | tower |
|---|---:|---|
| **FTA** — unique factorization of naturals | 20 | shared base (`Natural`/`Algebra`) |
| **ℚ is a field** | 78 | + `Integer` (quotient) + `Rational` |
| **ℝ is a field** | 97 | + `Real` (Cauchy construction) |
| **IVT** — intermediate value theorem | 113 | + `Real` analysis |

(A second, non-overlapping marquee is Fermat's two-square theorem,
`GaussianInteger/fermat_two_squares` — Freek #20 — whose 130-file cone runs up
the *algebraic* number-theory tower: ℤ[i] as a Euclidean domain/UFD,
`IntegerMod`, `Polynomial`. Deferred behind the analytic ladder.)

A milestone is **GREEN** once its whole cone is in the clean manifest:
`make clean-status` shows the percentage; the cost is dominated by *constructing
ℝ* — the analysis on top of "ℝ is a field" is cheap (IVT is only ~16 files more).

## The loop (per file / per batch)

1. **Scout** the next layer's leaks/redundancy (`cic_leak_report`, the
   `--check-redundant-by` checks; parallel review agents for breadth).
2. **Clean bottom-up**, applying the conventions; a clean lower layer lets the
   upper proofs reuse already-clean idioms. Commit per file or small batch.
3. **Add cleaned files to the manifest**; re-run `make clean-check`.
4. **When a leak recurs, fix the elaborator, not the proof.** The biggest wins
   so far were exactly this — conjunction-introduction through a definition,
   citation premise-discharge over `choose`-witnesses, the `by unfolding`
   redundancy false-positive. Each fix makes the next files clean themselves
   with less manual work, so treat recurring leaks as first-class feature work.

## Order of attack

Currently in progress: **FTA** (the shared base). Then `ℚ-field` → `ℝ-field` →
`IVT`, greening each milestone in turn. Within `Real`: basics → sequences →
Cauchy/completeness → field → continuity → IVT.

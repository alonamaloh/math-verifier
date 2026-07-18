# Clean-style plan: growing the "reads like math" set toward the whole library

The overriding goal of this project is that proofs read like what a
mathematician would write in a textbook, with the kernel doing the
typechecking (see `docs/style.md`). This document tracks the
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
  leak total ≤ `CLEAN_LEAK_BUDGET` (the `cic_leak_report` axis: positional
  lemma calls, raw `congruenceOf`/`rewrite`, etc.). Wired into `make check`, so
  **a file in the manifest cannot regress**, and the budget ratchets *down* as
  elaborator features remove the intended residuals.
- `make clean-anon-ratchet` — a second, independent axis: the count of
  user-written `⟨…⟩` over a logical connective (`And`/`Exists`) must stay
  ≤ `CLEAN_ANON_BUDGET` (currently 4 — `factorization_list`'s negation-leg
  destructures, awaiting a records refactor). Also wired into `make check`;
  `make anon-tuple-report` is the same audit grouped by file. This axis is
  elaborator-measured (it needs the expected/scrutinee type), so it rebuilds the
  manifest with `MATH_CHECK_ANON_TUPLES=1` rather than reading the leak report.

Adding a file to the manifest is a one-line edit *after* it is cleaned; bump
`CLEAN_LEAK_BUDGET` (and, if it carries intended connective-`⟨…⟩` residuals,
`CLEAN_ANON_BUDGET`) only by the file's documented intended residuals.

**The manifest is the highest-standard set, and it is the *only* such list.**
A file joins it only after someone has **read the proof** and judged it reads
like a textbook — passing the ratchets is the precondition, not the gate.
Adding a line asserts the read happened. We deliberately keep *one* list rather
than a separate "reviewed" file: the ratchets already give the manifest the
automated regression guard a hand-maintained list can't, and a second list
would only create a "scores clean but unread" gray zone (which is how
`arithmetic_geometric_mean` — leak/anon-clean yet carrying an inlined-15× `cases
k` piecewise term — slipped in). The re-read worklist is not a list either: it
is the per-file successor-outside-`Natural/` advisory that `scripts/clean_status.py`
prints (high count first). Some seed/score-only entries still owe their
confirming read; that backlog is worked as part of the cleaning loop.

**The two ratchets are necessary, not sufficient.** A leak count of 0 (plus 0
anonymous tuples) is where the readability read *starts*, not proof a file is
done — "leak-clean" ≠ "clean". Two things neither axis sees: a pattern-match
`cases <value> { | zero => … | successor(k) => … }` in a proof (discouraged in
`docs/style.md` in favour of an equation-shaped split that keeps the scrutinee
abstract, but with no scanner), and `successor` leaking outside `Natural/` (its
own deferred ratchet, kept out of `clean-check` per the
successor-elimination campaign). A file can score 0/0 and still read like
machine output — e.g. `IntegerMod/euler_fermat.math` once did, with a
pattern-match `cases n` and 27 `successor` tokens. So before adding a file,
*read it*; `scripts/clean_status.py` prints an advisory `successor`-outside-
`Natural/` count per manifest file (a high count is a re-read signal), and a
human/LLM pass against the readability bar is the real gate.

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

**FTA** (20/20) and **ℚ is a field** (78/78) are **GREEN** — their cones are
fully in the manifest (`make clean-status`). The live front is **ℝ-field**
(~80%) → then **IVT**, greening each in turn. Within `Real`: basics →
sequences → Cauchy/completeness → field → continuity → IVT.

The fine-grained residual checklist for the green cones (the few intended
`⟨…⟩`/leg-applied residuals, and the elaborator gaps fixed to clear them) is in
the `clean_cone_remaining_work` memory.

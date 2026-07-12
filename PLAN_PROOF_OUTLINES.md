# PLAN_PROOF_OUTLINES.md — skeleton-first elaboration, outline rendering, and (maybe) footnotes

**Status: design note only — nothing here is scheduled.** Recorded 2026-07-12
from a design discussion with the owner, so the sequencing and its reasons
survive across sessions. If work starts, add a Status ledger and treat this
like the other plan files.

## The idea (owner's framing)

Proofs should have a "fractal" structure: a reader sees the overall argument
first and expands the steps that are unclear, recursively. Three renderings of
the same abstract argument exist today or could:

1. **Inline** — `<fact> by { …detail… };` (today's style). Detail interleaved
   with the argument.
2. **Footnote** — `<fact> by footnote (∗);` with the detail in a trailing
   `footnotes { (∗): { … } }` section. C++-forward-declaration flavor.
3. **Lemma extraction** — prove each step as a named lemma, main proof cites
   `by <lemma>` (today's style for reusable steps).

The capture distinction (owner's observation): lemma extraction forces a
careful extraction of the relevant context into a signature; inline and
footnote both capture the local context like a lambda — sloppier to write,
and the dependencies are invisible to the reader. proof-style.md's
"avoid auxiliary `CauchyXxx` definitions for one-off proofs" rule is the
existing acknowledgment that forced extraction of one-off, context-heavy
steps produces junk (throwaway names, re-plumbed parameters); that is
exactly the niche footnotes would serve.

Owner style constraints: the primary criterion is clarity, secondary is
closeness to what a mathematician writes; the owner prefers bottom-up
argument order (facts first, goal last) over `suffices`-style goal
rewriting, so footnotes must not become a backdoor reordering of arguments —
they move *detail*, not *logic*.

## Decision: three steps, in order; syntax last and conditional

### Step 1 — obligation ledger + named holes (highest value, no new syntax)

Skeleton-first authoring: write the argument with named holes in the
`by`-positions, elaborate, and get ONE batch report of all open obligations,
each a self-contained (context, goal) pair:

```
skeleton OK — assembly verified; 3 open obligations:
(zero) at line 6:
  <hypotheses>
  ⊢ VectorSpace.zero(V) ∈ S ∧ VectorSpace.zero(V) ∈ T
…
```

- Checks the argument's ARCHITECTURE (the final `done`/assembly) before any
  detail is written — errors in the plan cost 12 lines of elaboration, not
  300.
- Each obligation is an independent work unit: exactly a prompt for an LLM
  (or a subagent fan-out), and a human-sized chunk too.
- Implementation is mostly a batch loop over what `--goal-at` already
  computes (it already prints context+goal at a `sorry` site and survives
  later elaboration failures). Missing pieces: NAMED holes; all sites in one
  report; per-obligation incremental re-elaboration (an open hole's failure
  should not invalidate sibling obligations).
- Works with today's inline blocks; useful even if steps 2–3 never happen.
- An open obligation is `sorry`-equivalent for soundness: loud warning,
  gates export-check's sorry-freedom the same way.

### Step 2 — outline rendering (reading value over the whole corpus)

The fractal READING experience needs no source change: proofs are already
trees of blocks whose statement lines are the summaries. A renderer that
folds every block body to an expander — a viewer for humans, an `--outline`
mode for LLMs (which read raw bytes and pay real attention cost for
interleaved detail; a contiguous skeleton reads better than the same
skeleton smeared over 60 lines) — delivers collapse/expand against the
existing corpus, including its worst offenders.

### Step 3 — `by footnote (<id>)` + trailing `footnotes { }` (conditional)

Only after living with 1+2, and only if the long proofs still hurt. Sketch:

```math
theorem … := {
  take u : …;
  <fact> as name by footnote (∗);
  …main argument…
  done
} footnotes {
  (∗): { …elaborated in the context AT THE MARKER… }
}
```

- Footnote elaborates against the goal and context captured at its marker;
  proof term is spliced — no kernel/trust change.
- Nesting: a footnote body is an ordinary block and may carry its own
  `footnotes { }`.
- Labels are identifiers (documentation!) with typographic ones (∗ † ‡)
  allowed. `by (∗)` alone is not available — `by (<fact>)` already means
  cite-a-proposition.
- Scope: footnotes attach to one proof body; cross-theorem reuse stays the
  job of named lemmas.
- **Capture-visibility mitigation**: the ledger/outline should print which
  hypotheses each footnote actually consumed (known from the elaborated
  term): `(∗) uses: imagesEqual, trivialKernel`. That recovers the
  dependency documentation a lemma signature gives, without the extraction
  ceremony.
- Sanctioned NICHE, not a general alternative: long proofs with one-off,
  context-heavy steps. The style question "inline or footnote?" must not
  arise for ordinary proofs — see the data below.

## Why the syntax is last

Its two benefits arrive earlier by other means (authoring loop ← step 1,
fractal reading ← step 2), and it is the only piece with a PERMANENT corpus
cost: a second idiom every reader must know, a new style axis for every
review and polish pass. It should be paid for by demonstrated demand from
steps 1–2, not by the design being attractive.

## Baseline data (2026-07-12, 1994 theorems)

Proof length (non-comment lines): median 10, mean 17.7;
>40 lines: 165 · >60: 83 · >100: 32.
Largest: Real.cauchy_product_converges 535,
ComplexNumber.cauchy_product_converges 370,
Real.exponential_series_absolutely_convergent 357,
Real.cosine_two_negative 273, Real.HasDerivativeAt.multiply 196.
So footnotes' customer base is ~2–4% of the corpus — but it is exactly the
expensive-to-maintain analysis tail, unreadable as a linear stream.

## Prior art

Lamport, "How to Write a 21st Century Proof" — hierarchical numbered proofs
with leaf obligations, motivated by mechanical checking; the TLA+ toolbox
renders them with expand/collapse. Isabelle/Isar structured proofs. The
LLM-side observation (skeleton-first = early architecture checking +
independent prompt-sized obligations) is what step 1 operationalizes.

---
name: polish-proofs
description: Polish recently written .math proofs - run the kernel's redundancy checks, clean the proofs up with readability (not hint-count) as the target, settle the unused-name cascade, verify and commit, then file error-message and usability feedback. Use after landing new proofs, or when asked to polish, clean up proofs, or run redundancy checks.
argument-hint: "[files... — defaults to .math files touched by the recent commits / working tree]"
---

# Polish proofs: redundancy checks → readability cleanup → feedback

The goal is **readability, not zero hints**. A finding from the checker
is a prompt to ask "what does the reader need here?", not an order to
delete. The depth behind these rules is in
`docs/style.md` ("Polishing with the redundancy
checks"); this skill is the operational sequence.

## 1. Identify the target files

Use `$ARGUMENTS` if given. Otherwise collect the `.math` files this
session touched: `git diff --name-only HEAD~5 -- 'library/**/*.math'`
plus any uncommitted ones (`git status --short library/`). Only polish
files YOU wrote or extended — for shared files that were appended to,
filter findings to the appended line range and leave pre-existing
findings alone.

## 2. Mark the findings inline

```
python3 .mark_redundant.py <file> [more.math ...]
```

This runs the redundancy checks and appends each warning VERBATIM as a
`-- «…»` marker comment on the flagged source line — so the fix
instruction sits next to the site while you edit, and line numbers
never drift. Edit each marked site per the triage table (removing the
marker as you resolve it), then strip any leftovers with
`python3 .mark_redundant.py --unmark <file>`.

For a quick findings count (or for the checks the marker script does
not cover), run the checks directly:

```
./kernel verify --source <file> --output /tmp/<name>.v --cache-root build \
    --check-redundant-by --check-redundant-by-non-eq --check-redundant-calc-steps
```

(Also heed `expensive by-less proof step` and `unused fact/let`
warnings from the plain build — they count as findings here. Note the
marker pass can surface "arguments inferable — `by <lemma>` alone
suffices" findings: take those — dropping spelled-out lambda arguments
is a large readability win.)

## 3. Triage each finding — by readability, not by chasing zero

(`since` was **removed from the language** (2026-07-02): it no longer
parses — never write it, and there is no exempt-explanation keyword
anymore. A hint you deliberately keep will stay flagged; that standing
warning is the accepted cost. The landed way to surface a fact **for
the reader** without the prover needing it is `note P [by …];` — a
verified comment that is *not* added to the context, so never use it for
a fact a later step must consume by type-match (state that bare instead;
see the `by` vs `note` mnemonic below).)

| Finding | Resolution |
|---|---|
| Redundant `by ring` / `by <plumbing lemma>` on a chain step | **By-less it.** The chain already shows the intermediate forms; mechanism citations are noise. |
| Redundant `by` on a step citing the **induction hypothesis** | **Keep `by IH`** (accept the warning) — the marker for where induction lands. |
| Redundant `by <Lemma>` where the *named result is the insight* (a closed form, `absolute_value_multiplicative`, a `partition` equation, …) | **Keep `by <Lemma>`** (argument-free; accept the warning) — the explanation is reader-load-bearing. |
| Redundant `by` on a stated fact citing a self-evident proposition (`0 < 1`) | **Bare the fact.** The statement is its own explanation. |
| Redundant `by` whose removal makes the prover **search expensively** (watch for the expensive-step warning re-appearing) | **Keep the hint** — performance-load-bearing. |
| `unused name` on an `as`-named fact or chain | **Anonymize** (`T by V;` / drop the `as`) — unless the name is referenced later by name, or appears in a `cases … refining` list (known false positive: refining usage doesn't count — leave the name). |
| Redundant `by <binder>` where the binder is an `obtain`/`suppose`/lambda hypothesis used nowhere else | **Leave it** — by-less'ing just moves the warning to an unused binder. |
| A whole stated fact the prover derives without its stated proof | Try **deleting the scaffolding entirely** (the checker sometimes reveals a 5-line derivation is unnecessary); keep the fact itself only if it documents a milestone. |
| An intermediate fact that is **only there to orient the reader** — the prover doesn't need it and no later step consumes it by type-match | Turn it into `note P [by …];` — a verified comment kept out of the context. (Do NOT use `note` for a fact a later step consumes by type-match: `note` isn't in context, so the match fails — state that one bare.) |
| `redundant by` on the stated fact that is the theorem's **final proof expression** | **Not a hint** — the fact+`by` IS the proof term; a bare Proposition there fails with "proof has type … Proposition". Leave it (or restructure the whole ending, only if that genuinely reads better). |

**Verify every removal.** The checker's speculative re-proof can
disagree with real elaboration (documented false positives in
`docs/error_message_inbox.md`) — a flagged hint whose removal breaks the
build is a **keep**, whatever the warning says. Re-verify the file after
each batch of drops, before moving on.

**Batch re-passes over previously-polished files: triage provenance
first.** Standing warnings on files already brought to the bar are
accepted keeps from an earlier session — do NOT re-litigate them
wholesale. Confirm empirically where cheap: run the checker on the
pre-change version of a representative file (swap the file in place,
verify, swap back — import caches stay valid if the imports' sources are
unchanged) and compare warning counts; identical counts mean the pass
owes nothing there.

**`by` vs `note` — the mnemonic** (full version in `docs/style.md`):
`by` = the prover needs it (or you insist the reader does — a kept,
flagged hint). Bare `T;` / `T by V;` = the fact stays in context
(anonymously) for a later type-match. `note P [by …];` = a verified
comment that is **not** added to the context — reader-only, never for a
consumed fact.

**Comment hygiene — no checker catches this.** Restructuring a proof
strands its comments. Re-read every comment in a site you edited and
confirm it names the lemma/tactic actually used — we have shipped a
`by ring` header on steps that became an explicit chain, and an `inverse_right`
note on an `inverse_left` proof. Fix it to name the real lemma or describe
the step generically ("gather into one factor of `c`"). While there: lead
each comment block with the math and pull kernel/elaborator mechanics
(`WHNF`, `Quotient.lift` reduction, why an `unfold` is needed) into a
marked `-- Implementation note:` aside.

## 4. Settle the cascade and re-verify

Anonymizing names and removing hints makes the prover consume facts by
type-match, which produces NEW findings. Re-run step 2 after editing;
the cascade is finite. Stop when the checks come back clean (or only
the documented false positives remain). Edit each site by hand — do
NOT write an automated rewriter (see the warning-cleanup memory).

Then a full `make -j 16 library` and `make -j 16 tests` must pass.

## 5. Commit

One commit for the polish pass (message: what was cleaned and by what
rule), per the commit-often convention. Never include other sessions'
WIP files.

## 6. File the feedback

- Any **confusing error message** hit during the session goes into
  `docs/error_message_inbox.md` with the verbatim text and a diagnosis
  while context is fresh (workflow: `docs/error_message_corpus.md`).
  Surprisingly *good* messages are worth an entry too.
- Close with a short usability report to the user: what worked, what
  fought back, concrete improvement suggestions ranked by how much time
  each would have saved.

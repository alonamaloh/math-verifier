---
name: polish-proofs
description: Polish recently written .math proofs - run the kernel's redundancy checks, clean the proofs up with readability (not hint-count) as the target, settle the unused-name cascade, verify and commit, then file error-message and usability feedback. Use after landing new proofs, or when asked to polish, clean up proofs, or run redundancy checks.
argument-hint: "[files... — defaults to .math files touched by the recent commits / working tree]"
---

# Polish proofs: redundancy checks → readability cleanup → feedback

The goal is **readability, not zero hints**. A finding from the checker
is a prompt to ask "what does the reader need here?", not an order to
delete. The depth behind these rules is in
`docs/conventions/proof-style.md` ("Polishing with the redundancy
checks"); this skill is the operational sequence.

## 1. Identify the target files

Use `$ARGUMENTS` if given. Otherwise collect the `.math` files this
session touched: `git diff --name-only HEAD~5 -- 'library/**/*.math'`
plus any uncommitted ones (`git status --short library/`). Only polish
files YOU wrote or extended — for shared files that were appended to,
filter findings to the appended line range and leave pre-existing
findings alone.

## 2. Run the three checks per file

```
./kernel verify --source <file> --output /tmp/<name>.v --cache-root build \
    --check-redundant-by --check-redundant-by-non-eq --check-redundant-calc-steps
```

(Also heed `expensive by-less proof step` and `unused claim/let`
warnings from the plain build — they count as findings here.)

## 3. Triage each finding — by readability, not by chasing zero

| Finding | Resolution |
|---|---|
| Redundant `by ring` / `by <plumbing lemma>` on a calc step | **By-less it.** The calc already shows the intermediate forms; mechanism citations are noise. |
| Redundant `by` on a step citing the **induction hypothesis** | **`since IH`** — keep the marker for where induction lands. |
| Redundant `by <Lemma>` where the *named result is the insight* (a closed form, `absolute_value_multiplicative`, a `partition` equation, …) | **`since <Lemma>`** (argument-free) — keep the explanation; `since` is exempt from the check. |
| Redundant `by` on a claim citing a self-evident fact (`0 < 1`) | **Bare claim.** The statement is its own explanation. |
| Redundant `by` whose removal makes the prover **search expensively** (watch for the expensive-step warning re-appearing) | **Keep the hint as `since ring` / `since <reason>`** — performance-load-bearing, and `since` silences the checker. |
| `unused name` on a claim/calc-`as` | **Anonymize** (`claim T by V;` / drop the `as`) — unless the name is referenced later by name, or appears in a `cases … refining` list (known false positive: refining usage doesn't count — leave the name). |
| Redundant `by <binder>` where the binder is an `obtain`/`suppose`/lambda hypothesis used nowhere else | **Leave it** — by-less'ing just moves the warning to an unused binder. |
| A whole claim the prover derives without its stated proof | Try **deleting the scaffolding entirely** (the checker sometimes reveals a 5-line derivation is unnecessary); keep the claim itself only if it documents a milestone. |

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

---
name: update-library-docs
description: Bring the library/**/*.md documentation (area READMEs and focused notes) up to date with recent library changes, then verify freshness with make docs-check. Use right after landing new public definitions/theorems, after renames or removals, or periodically when asked to sync/refresh the library docs.
argument-hint: "[areas or commit range — defaults to areas touched since the docs were last updated]"
---

# Update library docs: diff → edit → verify

The area READMEs are LLM entry points: an agent reads
`library/<Area>/README.md` before working in an area and trusts it over
grepping. A stale README is therefore worse than none. This skill keeps
them truthful.

## 1. Scope: what changed

Use `$ARGUMENTS` if given (area names or a commit range). Otherwise
find the areas whose sources changed since the docs last did:

```sh
git log --oneline -15 -- 'library/**/*.math'
git log -1 --format=%H -- 'library/**/*.md'
git diff --stat <that-commit> -- 'library/**/*.math'
```

For each affected area, list what the changes ADDED, RENAMED, REMOVED,
or RESEMANTICIZED at the public level: `theorem`/`definition`/
`opaque definition`/`construction`/`inductive` declarations, operator
or instance registrations, new modules. Ignore internals (helpers below
the abstraction boundary, `*_at_representatives` adapters, private
riders) — READMEs document the public interface only.

## 2. Edit the area docs

Targets, in order of likelihood:

- `library/<Area>/README.md` — the entry point.
- Focused notes when the area has them (`Natural/core.md`,
  `Natural/number-theory.md`, `Algebra/fifteen-theorem.md`).
- `library/README.md` — only if a whole area appeared or changed scope.

What belongs in a README (keep each ~50–100 lines; look at
`library/Natural/README.md` as the exemplar):

- **Main definitions** — the public types/operations, each with the
  owning module linked.
- **Main theorems** — the trunk names an agent should know before
  grepping; not the long tail.
- **Semantic contracts** that prevent wrong-lemma detours (argument
  order, edge-case values like division by zero, "this operation lives
  in a different area").
- **Abstraction rules** — which names are boundary-only and what to use
  instead.
- **Where to look** — module map for the area.

Rules:

- Every name you write must be copied from a declaration you just
  looked at — never from memory. Distinguish module names from
  definition names (`Rational.field_bundle` is a module; the bundle is
  `Rational.field`).
- Vocabulary: no `claim`/`calc` (retired terms — say "stated fact",
  "relation chain"); `successor` only within `Natural/`'s own docs;
  never show retired or discouraged syntax, even as a negative example.
- Do not narrate history ("X used to be…") — describe the current
  library.
- Removals and renames: fix every mention, do not annotate the old
  name.

## 3. Verify

```sh
make docs-check
```

This resolves every backticked qualified name in `library/**/*.md`
against the actual declarations and enforces the vocabulary rules. Fix
findings by correcting the DOCS (or, for a genuine new naming pattern
the checker mishandles, improve `scripts/check_library_docs.py` — never
by deleting the mention to silence it).

Also spot-read the edited README top to bottom once: the checker
verifies names, not prose truth (it cannot catch a wrong semantic
contract — those must be checked against the source when written).

## 4. Commit

Commit the doc updates (with the triggering library change when run in
the same session, otherwise standalone), message style:
"library docs: sync <areas> (<what changed>)".

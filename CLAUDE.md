# CLAUDE.md — project conventions (index)

This file is auto-loaded into every session, so it is kept **slim**: the
always-apply rules below, plus pointers to the detailed convention files
under `docs/conventions/`. Read only the file(s) relevant to the task at
hand.

The overriding goal is that proofs read like what a mathematician would
write in a textbook, with the kernel doing the typechecking. Optimize for
**readability**, not terseness.

## Always-apply rules

- **Fix bugs; never work around them.** When something misbehaves — a build
  flake, a tactic that "shouldn't" fail, a stale cache, a spurious error —
  diagnose the root cause and fix it at the source (kernel, elaborator,
  Makefile, build logic). Do not paper over it with retries, re-runs, ad-hoc
  reorderings, or proof hacks. A workaround hides the defect and lets it bite
  the next person; a fix removes it for everyone.
- **Flag friction; don't contort the proof.** The goal is an environment where
  a mathematician writes proofs the natural way, with kernel-grade rigor. If the
  system won't accept a mathematically natural phrasing, do NOT bend the argument
  to force it through — stop and flag the friction clearly (what you tried, what
  fought, what the natural form should be). Surfacing these frictions is a primary
  deliverable, not a distraction: each is a chance to fix the language, tactics,
  or library. Distinguish genuine mathematical subtlety from mere tooling friction
  and say which.
- **Build with `make -j 16 library`** from the project root (never bare
  `make`). `make -j 16 tests` also verifies the `Test/` feature files.
  Warm rebuilds are sub-second; a change to `*.cpp`/`*.hpp` (kernel or
  elaborator) re-verifies the whole library (the `.mathv` cache depends
  on the `kernel` binary), so **always validate elaborator changes with a
  clean `make tests`**.
- **No abbreviations in declared identifiers.** `representative`, not
  `rep`; long qualified names are searchable. Local-variable abbreviations
  are fine.
- **A comment is an admission of defeat.** The proof should carry the
  reasoning itself: a comment explaining *what* a step does is a signal the
  step wasn't saying enough — push it into the code (`by <named-lemma>`, a
  named stated proposition, a relation-chain form) and delete the comment.
  A one-line *why* comment (a non-obvious strategy) may still earn its
  place, for now; kernel mechanics stay quarantined as
  `-- Implementation note:` in the foundational files only. Full rule +
  the what/why split: `docs/style.md`.
- **`ring` / `field` first.** For any commutative-ring identity, the
  default is `:= ring` (or `field(h1, ...)` when reciprocals are
  involved). Reach for hand-written `congruenceOf`/associativity only
  after the tactic fails with a real limitation. See
  `docs/conventions/algebra-tactics.md`.
- **Line width: wrap at column 140**, and only when the line genuinely
  needs it — wrapped lines have their own readability cost.
- **Numeric literals.** Prefer `0`/`1`/`2` over
  `zero`/`successor(zero)`/`two`. Bare numerals now coerce in
  argument/operand positions (`Real.power(2, m)`, `x + 2`), so drop the
  ascription there; prefer `(x + y) / 2` over `* (one_half)`. Caveat:
  `(2 : Real)` is *not* defeq to `1 + 1`, and `let`s are still opaque to
  `linear_combination` (`ring`/`field` and the sign battery now ζ-unfold
  them) — see the `2`-vs-`1+1` and `let`-caveat rules. Outside
  `Natural/`, never use `successor`; write `1 + n` or `n + 1`. See
  `docs/conventions/numerals-and-naming.md`.

## Documentation (`docs/`)

- **`library/<Area>/README.md`** — the brief LLM-oriented entry point for a
  library area. Read it before using or extending that area.
- **tutorial.md** — a 10-minute, example-driven introduction to writing
  proofs. Start here.
- **reference.md** — a catalogue of every surface construct.
- **style.md** — how to make a proof read well (and what to avoid); the
  `docs/conventions/` files below are the depth behind it.
- **library.md** — a map of `library/` by mathematical area.

## Convention files (`docs/conventions/`)

- **quotients.md** — `Quotient.mk`/`.sound`/`.lift`/`.induct[_two/_three]`
  short forms, `construction` intro forms, and pattern-binders
  (`by_representatives`, `cases`, `take`, `suppose`) on quotients.
- **relation-chains.md** — the bare relation-chain form with mixed
  `=`/`≤`/`<`/`≥`/`>`, chains over preorders (`∣`/`⊆`), by-less `=` steps
  via the full prover, `let` abbreviations, `<chain> as NAME`,
  `… by substituting`, equation transport (`rewrite(…)` is retired),
  diff-inferred `by`, and rewrite-under-binder.
- **algebra-tactics.md** — `ring`, `field`, `linear_combination`, and the
  foundational-vs-derived ring-lemma split.
- **structures-and-inference.md** — name-bound `convention`s, implicit
  arguments `{x : T}`, canonical `instance` inference, operator
  overloading (including the `·` group operator and postfix `⁻¹`), and
  citing a lemma `by <name>` (goal-driven + context-discharge +
  match-and-unify, `recalling <fact>, …`).
- **numerals-and-naming.md** — naming, line width, `1 + n` vs
  `successor`, and binding a repeated cast with `let`.
- **opaque.md** — `opaque definition` discipline: when to use it, the
  characterising-lemma boundary, and the cost/benefit lesson.
- **build-and-layout.md** — the build system and the `library/` module
  layout (imports flow up the dependency layers).

## Kernel quirks

CIC restrictions and recurring gotchas (no large elimination from Prop,
function-wrapping for `cases`-on-expression, universe-inference notes,
the auto-prover closedness invariant, ...) live in memory:
`~/.claude/projects/-Users-alvaro-claude-math/memory/kernel_quirks.md`.

## Memory

Persistent notes index: `MEMORY.md` in the memory directory above.
Notable: `padic_construction_status`, `finite_fields_status`,
`complex_numbers_status`, `group_theory_status`,
`software_engineering_for_math`, `keep_git_current`.

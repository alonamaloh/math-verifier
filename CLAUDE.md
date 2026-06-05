# CLAUDE.md — project conventions (index)

This file is auto-loaded into every session, so it is kept **slim**: the
always-apply rules below, plus pointers to the detailed convention files
under `docs/conventions/`. Read only the file(s) relevant to the task at
hand.

The overriding goal is that proofs read like what a mathematician would
write in a textbook, with the kernel doing the typechecking. Optimize for
**readability**, not terseness.

## Always-apply rules

- **Build with `make -j 16 library`** from the project root (never bare
  `make`). `make -j 16 tests` also verifies the `Test/` feature files.
  Warm rebuilds are sub-second; a change to `*.cpp`/`*.hpp` (kernel or
  elaborator) re-verifies the whole library (the `.mathv` cache depends
  on the `kernel` binary), so **always validate elaborator changes with a
  clean `make tests`**.
- **No abbreviations in declared identifiers.** `representative`, not
  `rep`; long qualified names are searchable. Local-variable abbreviations
  are fine.
- **`ring` / `field` first.** For any commutative-ring identity, the
  default is `:= ring` (or `field(h1, ...)` when reciprocals are
  involved). Reach for hand-written `congruenceOf`/associativity only
  after the tactic fails with a real limitation. See
  `docs/conventions/algebra-tactics.md`.
- **Line width: wrap at column 140**, and only when the line genuinely
  needs it — wrapped lines have their own readability cost.
- **Numeric literals & `1 + n`.** Prefer `0`/`1`/`2` over
  `zero`/`successor(zero)`/`two`, and `1 + n` over `successor(n)` in
  expressions (both kernel-defeq). Exceptions and the pattern-position
  caveat: `docs/conventions/numerals-and-naming.md`.

## Convention files (`docs/conventions/`)

- **quotients.md** — `Quotient.mk`/`.sound`/`.lift`/`.induct[_two/_three]`
  short forms, `construction` intro forms, and pattern-binders
  (`by_representatives`, `cases`, `take`, `suppose`) on quotients.
- **calc-and-rewrite.md** — `calc` with mixed `=`/`≤`/`<`/`≥`/`>`, `calc`
  over preorders (`∣`/`⊆`), by-less `=` steps via the full prover, `let`
  abbreviations, `calc ... as NAME`, `claim … by substituting` /
  `rewrite(eq, term)`, diff-inferred `by`, and rewrite-under-binder.
- **algebra-tactics.md** — `ring`, `field`, `linear_combination`, and the
  foundational-vs-derived ring-lemma split.
- **proof-style.md** — math-like phrasing; **what an ideal proof looks
  like and the raw-CIC tells to avoid** (no `congruenceOf`/
  `transport_proposition`/raw `Subtype.make`/positional lemma calls —
  read this BEFORE writing proofs); `cases`/`by_induction` over
  pattern-match; `cases ... with`; `decide`; statement-level sugar
  (`claim`/`goal`/`obtain`/`choose`/`take`/`suppose`/`let`/`note`/
  `change`/`unfold`); `since` (kept hint) and `note … by` (verified
  comment); CIC-noise-reduction idioms; and the **redundancy-check
  polishing workflow** (`--check-redundant-by`… + the unused-name cascade
  and how to settle it).
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

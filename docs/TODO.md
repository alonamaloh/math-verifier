# Project TODO / ideas

Durable backlog of ideas worth trying. Promote to a real task when picked up.

## Build / lint

- **[DONE]** The unused-name check is now **default-ON** (`src/main.cpp`
  `reportUnusedNames = true`; opt out with `--no-check-unused-names`). The
  whole library was cleaned by hand (anonymize named claims, drop dead
  `… as X` names, or `note`/delete truly-dead bindings; spellings predate
  the A1 keyword retirement). `Test/` opts out via a target-specific Makefile flag because
  its fixtures deliberately exercise named/unused claims. Also fixed a
  real check bug along the way: `surfaceMentionsName` didn't descend into
  `linear_combination(...)` arguments, so names used only there were
  false-positives (mirrors the pre-existing `SurfaceField` case).

- **[FIXED]** `since` was not exempt from the redundant-`by` check inside
  `by induction`/`cases` bodies: the `byIsExplanation` flag was dropped by
  the two claim-rebuild sites (parser `substituteSurfaceName` and
  elaborator `rewriteRecursiveCalls`), both of which omitted it from
  `makeSurfaceStructuredClaim`. Now plumbed through.

## Prover / citations

- **`by Lemma unfolding <opaque>` — cross an opaque while solving a
  citation's hidden arguments.** Goal-driven `by Lemma` / `done by Lemma`
  fails when the lemma's arguments live *under an opaque definition* in its
  conclusion. The matcher can't see them, so it reports "the hint's
  arguments could not be inferred … or its conclusion does not unify".

  Canonical example (`library/Real/supremum.math`): `Real.IsNonneg` is
  `opaque` and `≤` on `Real` unfolds to it. After a `cases B refining`, the
  goal β-reduces (through the quotient) to
  `IsEventuallyNonneg(seqFun(make(b) + -make(s)))`, while
  `LessOrEqual_of_pointwise_at_make`'s conclusion is the folded
  `from_cauchy(s) ≤ from_cauchy(b)`. The args `b, s` only appear *under*
  `Real.IsNonneg`, so matching can't recover them.

  Root cause — two different operations, only one respects opacity:
    1. *Check a concrete term against a type* (`change`, a bare hypothesis,
       `done` closing from an in-context fact). Runs the kernel's full
       conversion → crosses the opaque. All of these work.
    2. *Solve metavariables by matching a lemma's conclusion-with-holes
       against the goal* (goal-driven `by Lemma`). Respects opacity → can't
       unfold to expose the holes → fails.

  Verified asymmetry on the example: `change X; done by L`,
  `claim h : X by L; h`, and `claim X by L; done` ALL verify (each routes
  the opaque crossing through a term-vs-type conversion); only the direct
  `by L` against the reduced goal fails. So the inconsistency is purely
  phrasing-dependent metavar-inference under an opaque.

  Proposal: an opt-in hint `done by Lemma unfolding Real.IsNonneg` (mirrors
  `recalling`) that marks the named opaque(s) transparent *while solving
  metavariables for that one citation*. Sound — the kernel re-checks the
  resulting term anyway. Keep it (a) opt-in via keyword, (b) for **explicit
  citations only** — never blind auto-prover search, so opacity keeps its
  performance guard, and (c) naming the opaque, so the encoding leak is
  visible at the call site. Lands in the citation/by-matching path
  (`inference.cpp` / `prover.cpp`): add a transparency override for the
  listed constants in the conclusion-vs-goal unify (and premise discharge).

  Scope / don't oversell: this fixes the **opacity** bridge only. Other
  matcher-depth gaps are separate and won't be solved by it —
  `let`-unfolding (`supValue := bisectionLimit(…)`), ι on projections
  (`right(make(a0,b0)) ≡ b0` during premise discharge), and the
  `_step`-lemma case (an explicit `decision : Decidable(…)` argument that
  the goal doesn't determine at all). Those stay explicit regardless.

  Priority: modest. The plain idiom `claim <folded form> by Lemma; done`
  already handles the opacity case (it routes through conversion), so this
  is ergonomic sugar for when stating the folded intermediate is painful —
  not a capability we lack. Already used it to clean the two `_at_make`
  lifts in `supremum.math`.

## Error messages (see docs/error_message_corpus.md for the full catalogue)

- Approach B — provenance quoting: carry the exact surface type string /
  source span and quote it in errors (needs surface end-positions).
- Global elaboration fuel/recursion cap so a runaway becomes an error,
  never an OOM (corpus entry 6).
- `?` in And/Exists tuple proof slots: either auto-prove or emit a clear
  message suggesting `claim <component> by …` (corpus entry 7).
- `obtain` pattern arity mismatch surfaces an internal "index 0 … must be
  a local variable" (inbox); give a "pattern has N components but … has M".

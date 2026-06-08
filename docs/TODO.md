# Project TODO / ideas

Durable backlog of ideas worth trying. Promote to a real task when picked up.

## Build / lint

- **[DONE]** The unused-name check is now **default-ON** (`src/main.cpp`
  `reportUnusedNames = true`; opt out with `--no-check-unused-names`). The
  whole library was cleaned by hand (anonymize `claim X : T by V` →
  `claim T by V`, drop `calc … as X`, or `note`/delete truly-dead
  bindings). `Test/` opts out via a target-specific Makefile flag because
  its fixtures deliberately exercise named/unused claims. Also fixed a
  real check bug along the way: `surfaceMentionsName` didn't descend into
  `linear_combination(...)` arguments, so names used only there were
  false-positives (mirrors the pre-existing `SurfaceField` case).

- **[FIXED]** `since` was not exempt from the redundant-`by` check inside
  `by_induction`/`cases` bodies: the `byIsExplanation` flag was dropped by
  the two claim-rebuild sites (parser `substituteSurfaceName` and
  elaborator `rewriteRecursiveCalls`), both of which omitted it from
  `makeSurfaceStructuredClaim`. Now plumbed through.

## Error messages (see docs/error_message_corpus.md for the full catalogue)

- Approach B — provenance quoting: carry the exact surface type string /
  source span and quote it in errors (needs surface end-positions).
- Global elaboration fuel/recursion cap so a runaway becomes an error,
  never an OOM (corpus entry 6).
- `?` in And/Exists tuple proof slots: either auto-prove or emit a clear
  message suggesting `claim <component> by …` (corpus entry 7).
- `obtain` pattern arity mismatch surfaces an internal "index 0 … must be
  a local variable" (inbox); give a "pattern has N components but … has M".

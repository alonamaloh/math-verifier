# Project TODO / ideas

Durable backlog of ideas worth trying. Promote to a real task when picked up.

## Build / lint

- **Turn the unused-name check on by default.** The unused-name warning
  (`--check-redundant-by` surfaces it; it flags `claim NAME : T …` where
  `NAME` is never referenced — dead-weight names and truly-dead bindings)
  is *cheap*: it's a simple scope/use query, not a speculative re-run of
  the auto-prover (that's the redundant-`by` check, which IS expensive and
  should stay opt-in). So the unused-name part could be on for every
  `make library` / `make tests` without a perf cost. Try splitting the
  flag so unused-name is always-on while redundant-`by` stays behind the
  opt-in flag, and confirm the build stays fast and noise-free.
  (Raised 2026-06-07 during the proof-readability sweep.)

- **`since` is not exempt from the redundant-`by` check.** Design intent
  (and the proof-style docs) say `since <proof>` is "like `by` but exempt
  from the redundant-`by` check — an explanation kept for the reader."
  Empirically (2026-06-07), `claim P since L` / `done since L` STILL emit
  "redundant `by` on `claim`" under `--check-redundant-by`. So converting
  `by`→`since` does not silence the lint; only dropping the hint does.
  Fix the checker to actually exempt `since` so kept-for-readability cites
  don't show as redundant — otherwise the opt-in check is noisy on exactly
  the cites we deliberately keep.

## Error messages (see docs/error_message_corpus.md for the full catalogue)

- Approach B — provenance quoting: carry the exact surface type string /
  source span and quote it in errors (needs surface end-positions).
- Global elaboration fuel/recursion cap so a runaway becomes an error,
  never an OOM (corpus entry 6).
- `?` in And/Exists tuple proof slots: either auto-prove or emit a clear
  message suggesting `claim <component> by …` (corpus entry 7).
- `obtain` pattern arity mismatch surfaces an internal "index 0 … must be
  a local variable" (inbox); give a "pattern has N components but … has M".

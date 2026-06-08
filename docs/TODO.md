# Project TODO / ideas

Durable backlog of ideas worth trying. Promote to a real task when picked up.

## Build / lint

- **Finish making the unused-name check always-on.** The flag is now
  split out (`--check-unused-names`, separate from the expensive
  redundant-`by` check) and 124 dead names were cleaned. It is still
  default-OFF; flip it to default-ON once the library is fully clean. The
  check itself is CORRECT (an earlier "false positive" scare was a script
  bug — a `count=1` regex hit the first same-named `claim`, not the flagged
  line). Remaining flagged names: `ComplexNumber/irreducible` (~12),
  `Natural/padic_valuation` (~17), `IntegerMod/field` (~3), and 9
  truly-dead bindings (`Polynomial/additive_group` foldedTail,
  `Natural/add_order` cIsZero, `Algebra/second_isomorphism`/`third_isomorphism`,
  `Algebra/euclidean_domain` d, `ComplexNumber/embedding_injective`
  differenceZero, `Real/supremum` negZeroEqZero) — delete or `note` those.
  Do a LINE-AWARE cleanup (target the flagged line, not the first
  same-named claim), `make library` to verify, then default the flag on.

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

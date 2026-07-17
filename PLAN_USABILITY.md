# PLAN_USABILITY — peripheral friction, from the 2026-07-17 overnight report

Source: a full working session (notation round 2, the order-chain closer,
LA wave 3 polish — commits c1de8bd8..9aa37672) used as a usability probe.
Verdict recorded there: the residual friction is almost entirely
PERIPHERAL (imports, error leaf detail, checker precision), not central
(the proof language). These items close the periphery. Distinct in scope
from PLAN_ERGONOMICS.md (F1–F9, "equal spellings treated differently")
and PLAN_NATURAL_NARROWING.md (the `a - b` design).

Ranked by measured time-cost during the probe session.

## U1 — always print the innermost goal on elaborate errors

Failures inside nested cases print the frame chain ("claim at line 119 /
case for 'Exists.introduce' / choose δ at line 88 …") but not always the
failing GOAL TERM — one file-open round trip per failure to learn what
the claim was. The strategy-enumeration tail ("no in-scope hypothesis
matches structurally, … no transitivity chain reaches the goal") is the
gold standard — it reads as a to-do list; every elaborate error should
carry (a) the innermost goal, pretty-printed, and (b) where applicable,
that enumeration. Entry point: `formatErrorWithContext` /
`innermostFramePosition` (internal.hpp ~600-670) — the frames know their
goals; they just don't all print them.

## U2 — "registered but not imported" hints

`import Natural.power` missing gave: "operator '^' is not supported for
operand type 'Natural'" — false as stated (it is registered, in a module
not in scope). The biggest newcomer trap. The environment can distinguish
three cases: never registered anywhere / registered in module M not
imported / registered and in scope but mismatched types. Same treatment
for `by <lemma>` citations of not-imported names ("unknown lemma" should
say which module exports it when the global registry knows). Entry
points: the `targetFunction.empty()` error in desugarArithmeticOperator
(desugar_equality.cpp ~495) and the unknown-citation error path. Needs a
name→module index at verify time — the deps machinery already computes
module contents; thread a lookup through.

## U3 — the redundancy checker verifies its own suggestions

Six false positives in one session (Real/apartness:216, Real/order:528,
four in basis_pruning), each costing an edit-verify-revert cycle, and —
worse — training distrust of the tool. Two sub-items:
  (a) before emitting "redundant `by`", re-run the ACTUAL elaboration
      path with the hint removed (not the speculative approximation);
      suppress the warning if it fails. The inbox entries (2026-07-17)
      have the reproduction cases.
  (b) a claim that is a theorem/block's FINAL proof expression has no
      droppable hint — suppress or reword (inbox, Real/order:528).
Acceptance: re-run the wave-3 polish inputs; zero warnings whose
suggested edit breaks the build.

## U4 — mixed same-precedence additive operators require parens

`a ∸ b + b ∸ a` silently left-associated to `((a ∸ b) + b) ∸ a` — a
SEMANTIC change that verified the definition and one downstream theorem
before failing the second (Natural/distance.math during the ∸ sweep; the
one silent-wrong-meaning hazard of the whole session). Proposal: when a
chain at the additive level mixes DISTINCT operators (∸ with +/-, ∖ with
-), require explicit parentheses (parse error with a "did you mean"
showing both groupings). Homogeneous chains (`a + b + c`) unaffected.
Same guard at the multiplicative level (∘ with */·) for safety.
Entry point: parseAdditive/parseMultiplicative — track the first
operator of the chain, error on a different one.

## U5 — single-file verify auto-refreshes stale import ifaces

"stale cache … run `make -j 16 library` and retry" appeared ~a dozen
times during multi-file work. The verify already knows exactly which
iface is stale; stage-1 iface builds are cheap (~4% of work) — rebuild
the stale import's iface in-process (respecting the srchash) and
continue, instead of refusing. Full `make` stays the tool for proof-cache
rebuilds; this only covers the iface staleness case.

## U6 — auto-settle the mechanical redundancy categories

~40% of polish volume needs no judgment: (a) `unused name` where the
name has zero textual references in the file, (b) `redundant by
Logic.excluded_middle`. Teach `.mark_redundant.py` (or a `--settle-safe`
kernel mode) to apply those two edits itself — with U3(a) so its edits
are pre-verified — leaving only judgment cases marked. The wave-3 flow
(judge ~40 sites to derive a table, delegate the rest) then starts from
a much smaller marked set.

## U7 — `kernel suggest-imports`

Import bookkeeping is the last real chore: long manual lists, and a
missing one surfaces as U2's confusing errors. A subcommand that parses
a file, resolves unknown names/operators against the global registry,
and prints the missing `import` lines. Depends on U2's name→module
index. Stretch: `--fix` appends them (sorted into the existing block).

## Cross-references (open items living elsewhere)

- Checker/message inbox entries backing U1/U3: docs/error_message_inbox.md
  (2026-07-17 entries).
- Order-chain closer v2 (mid-proof hint absorption question, proven-
  equality edges, lazy ground endpoint edges): readability memory,
  "Order-chain closer" + close-out sections.
- Ellipsis simplified-prefix inference (defeq-tolerant anti-unification /
  two-prefix probe): inbox 2026-07-17 + proof-style.md caveat.
- `a - b` obligation-narrowing: PLAN_NATURAL_NARROWING.md N0–N4.

## Status ledger

| item | state | effort | notes |
|------|-------|--------|-------|
| U1 goal-at-leaf errors | TODO | S–M | frames already carry goals; print + enumerate |
| U2 not-imported hints | TODO | M | needs name→module index; two error sites |
| U3 checker self-verify | DONE 2026-07-17 | M | (a) probe now runs the real path's final defeq gate (calc.cpp + induction.cpp); (b) parser marks unnamed `P by H` proof-tails `isTerminalProofTail`, checker skips them (Test/redundant_by_terminal_claim_test.math + probe-script assertions). order.math:528 FP gone; 4 sampled basis_pruning edits verified |
| U4 mixed-operator parens | TODO | S | parseAdditive/Multiplicative chain guard + ErrorTest |
| U5 stale-iface auto-refresh | TODO | S–M | in-process stage-1 rebuild of the one stale import |
| U6 auto-settle safe categories | DONE 2026-07-17 | S (after U3a) | .mark_redundant.py settles by default (`--no-settle` opts out): drops ` as X` on `unused name`/`calc … as` warnings and `by Logic.excluded_middle` on redundant-`by` sites; batch re-verified, full revert + mark-all fallback on failure |
| U7 suggest-imports | TODO | M (after U2) | new subcommand; --fix stretch |

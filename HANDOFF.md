# HANDOFF — session pause 2026-08-08

Read this on the next machine, act on it, then fold anything durable into
`PLAN_SCHOENFLIES_TRANSLATION.md` and delete this file. Session memory does
not travel between machines; this file is the bridge.

## Where things stand

**H6 (polygonal redrawing): B1–B7 built, merged, gated, pushed.** One brick
remains — **B8, the assembly** (`Plane.Graph.polygonal_redrawing`). Its
wrap-up state is **on `main`, fully gated**: all its green supporting
material landed (`Plane/arcchain.math` — every polygonal walk contains a
SIMPLE one; `Plane/radial.math` — the sup-metric frame geometry;
`Lists/choice.math` — finite choice by list induction, no axiom;
`Plane/Graph/redrawing.math` — the `IsCore`/`coreChannel`/`redrawnRegion`
vocabulary), and the drafted-but-unverified assembly is
**`B8_ASSEMBLY_WIP.math` at the repo root** (not compiled by the build).
The headline theorem is NOT yet proved.

**What blocked it: friction L17** (see `FRICTION_PLANE_LAYER6.md`) — the
elaborator refuses `coreOf(edge) ⊆ X` when `coreOf` is a `choose`-bound
function ("operand type `<unknown>`"), though the same spelling works for a
theorem parameter. **Resume options: fix L17 in the elaborator first
(Fable-tier; operand-type resolution over applications of choose-bound
functions), or rewrite the draft's `⊆` claims in `take z; suppose z ∈ …`
form.** Then the B8 continuation, verbatim from the wrap-up report: (1)
re-verify the draft prefix (green up to `everyChannelJoinsItsContacts`);
(2) write the per-edge chain — `exists_arcChain`, `IsArcChain.extend` at
the far contact, `List.prepend` at the near one, `IsArcChain.IsArcBetween`,
`IsPolygonal` by witness, and one final `List.exists_choice_function` at
`B := ℝ → Plane.Point`; (3) `noVertexInRegion` + `regionsMeetAtVertices`
via `Plane.radial_meet` + channel disjointness, then the four `IsDrawing`
clauses. The Lean guide is `Schoenflies/Graph/Redrawing.lean:544–659`.

Everything B8 consumes is on `main` (B1 `Real/positive_bound.math`, B2+B4
`Plane/Graph/{vertexsquares,cores}.math`, B3 `Metric/entry_exit.math`, B5
`Plane/locally_polygonal.math`, B6 `Plane/polygonal_carrier.math`, B7
`Plane/Graph/tubes.math` + `Plane/separation.math` nearSet).

**Merge protocol used all session** (keep it): agent worktree branch →
review the proof by reading it → `git cherry-pick` onto main →
`ulimit -v 16000000 && make -j 16 library && make -j 16 tests` both green →
push → remove worktree + branch.

## The two ledgers (the Part I / Part II roadmaps)

- `T1_LEDGER.md` — Part I. Order: T1.0a shared stubs → T1.0b simple-arc
  extraction → **T1.3 region API first** → remaining waves.
- `T2_LEDGER.md` — Part II. Read "Wave order and parallelism" first; four
  scheduling corrections live there. A third of Part II is plane-free and
  parallel-safe with Part I. Two design decisions need the owner:
  named-inverse homeomorphism (before ~33 sites), diameter pointwise-vs-sup
  (before T2.2).

## Friction queue (elaborator/tooling, all logged in FRICTION_PLANE_LAYER6.md)

Fixed this session: untyped `let` in block bodies; auto-prover ζ-retry
(goal + hypothesis frames, outermost-only). Open: L10 (`suppose` should
ζ/WHNF the goal), L11 (`ordered_field` ground reciprocals under `let`),
L12 (printer folds goals into set-shaped definitions — worst offender for
error readability), L13 (`suppose ¬P` toward positive goal: diagnostic),
L14 (overload dispatch before numeral coercion), L15 (applying through a
let-bound predicate head), L16 (vacuous `x ≠ x` reductio cost), plus:
`choose … from { braced ∀-fact }` does not instantiate, and a named-argument
citation being weaker than the bare one (B7 report).

## Warnings

- **Two STALE worktrees from 2026-07-04 were rescue-committed and pushed**
  at pause time, so nothing is machine-local any more: branches
  `stale-2026-07-04-complexnumber-cone` (~139 lines, ComplexNumber cone) and
  `stale-2026-07-04-suffices-by-definition` (~192 lines incl. 129 in
  `src/syntax/parser.cpp` — looks like an abandoned `suffices … by
  definition` feature). Neither is reviewed or merged; ask the owner whether
  to salvage or delete.
- Process rules that earned their place today: agents read `docs/style.md`
  before writing; no scripted edits of `.math` ever; brief carries the
  friction list; Opus 5 is the worker tier, Fable for elaborator/design.

## Suggested next moves (in order)

1. Fetch + finish B8 from its WIP branch (or re-launch with the WIP as
   context), merge, full gate, push. H6 closes.
2. `/polish-proofs` pass over the seven H6 files, then update library docs
   (`update-library-docs`) and the tex's H6-adjacent sections.
3. Start T1.0a (shared stubs) per `T1_LEDGER.md`; the plane-free Part II
   track (T2.1a graph relabelling) can run in parallel.

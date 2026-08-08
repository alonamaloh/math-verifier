# PLAN — translating the Lean Jordan–Schönflies proof into this system

Companion to `PLAN_JORDAN_SCHOENFLIES.md`, which planned (and delivered) the
foundation Layers 0–6. This file plans the *content*: Part I (the Jordan curve
theorem and the general crosscut theorem) and Part II (the Schönflies
extension), translated from the Lean 4 / Mathlib development at
`~/claude/schoenflies-lean`.

## The one framing decision

**The Lean development, not `jordan_schoenflies.tex`, is now the proof
source.** The blueprint remains the prose narrative, but the Lean repo is the
debugged version of it: formalization found 21 places where the blueprint or
the companion design was over-assuming, under-assuming, or false-as-stated,
and every repair is machine-checked there. (The findings list was trimmed
from the README when the theorem was finished; the full record survives in
the Lean repo on branch `local-route-2026-08-02`, `README.md`, "Findings".)
Translating from the tex and rediscovering those 21 defects would be paying
for them twice.
Concretely: before starting any statement, read its module in
`~/claude/schoenflies-lean/Schoenflies/` and its row in
`schoenflies-lean/docs/ROADMAP.md`; the tex supplies the prose argument, the
Lean file supplies the corrected statement, the hypothesis list, and the
decomposition into lemmas.

What is *not* being translated is Lean text. The two foundations differ by
design (see "Representation deltas" below), our proofs must read like
`docs/style.md` proofs, and a Lean tactic script is only a witness that the
argument works. The unit of translation is the **statement and the proof
strategy** — the lemma decomposition, the invariants, the case structure.

## Honest status of both sides (measured 2026-08-08)

**This side.** Layers 0–6 built except H6 (polygonal redrawing), which is
designed brick-by-brick (B1–B8 in `PLAN_JORDAN_SCHOENFLIES.md`, with the three
design corrections found by building it in Lean already folded in, commit
`afc8f5cb`). Zero lines of Part I or Part II content.

**The Lean side is FINISHED** (pulled 2026-08-08; last commit 2026-08-06).
`Schoenflies.jordan_schoenflies_of_homeomorph` is unconditional — no `sorry`,
no named hypotheses, `propext` / `Classical.choice` / `Quot.sound` alone —
and its ROADMAP records zero live obligations in both parts. The whole
translation therefore has a finished original end to end.

**Fork note, for anyone reading old records.** The checkout at
`~/claude/schoenflies-lean` held a divergent Part II route (the
`EarStep`/`MeshSteps`/`GridSteps`/`StageRecursion` chain, 505 commits) that
was superseded: the theorem was finished elsewhere along a different route
(the `Quantitative*` recursion, `FiniteTransferTarget*`, `BoundaryAnchors`
chain) and `main` now tracks that finished version (111 modules, ~77k
lines). The superseded route is preserved on branch
`local-route-2026-08-02` in that repo — its README's "Findings" section and
its much longer ROADMAP narrative remain valuable reading, but **module
names from that narrative do not match `main`**; when a findings entry names
a Part II module, locate the corresponding statement on `main` (via
`docs/INVENTORY.md`) rather than trusting the old file name.

## Representation deltas — the standing translation table

The Lean development deliberately diverged from this foundation in a few
places. Each is a known, bounded re-typing, and each has a trap recorded with
it. Check this table before starting any module.

| There | Here | What to watch |
|---|---|---|
| one normed space `Plane`; `p + q` writable | sealed `Plane.Point` / `Plane.Vector`, affine over linear | every statement re-types; the blueprint's affine idiom is already our native one, so this is usually a *simplification* on our side |
| Mathlib compactness (open cover) and connectedness (separation) | sequential compactness; clopen criterion as the definition | proofs that reach for open covers or `IsPreconnected` re-route through the sequential/clopen forms; Layers 2–3 were built for exactly this, so the re-route is local |
| Mathlib `openSegment a a = {a}` | our `openSegment(a, a) = ∅` | the `subdivide`/`splitAt_avoids` nondegeneracy hypothesis appears on their side and not ours (Lean finding 2); do not import their hypothesis, and do not drop ours where theirs is stated without it |
| Mathlib multigraph; loops allowed, handshake with loops, looplessness derived per-theorem | `Graph.IsWellFormed` excludes loops globally | Lean findings 3–9 list statements that are cleaner loop-free-per-theorem; where a Lean statement carries no looplessness and ours would, prefer restating ours only if a consumer pays — do not sweep Layer 5 preemptively |
| edge relabelling: the finished route built `Graph/Relabel.lean` (fresh edge names along an injective-on-edges map; walks/paths/path graphs push forward) | no edge relabelling here | the ear construction needs it; plan on porting the relabelling module rather than the superseded route's `adj_congr` workaround |
| model curve = square boundary, `IsSeparating` predicate | same square model; no separation predicate yet | **adopt** Lean's design: state `thm:jordan` through the *same* `IsSeparating` predicate as the polygonal case, so `inside`/`outside` and the region API transfer with nothing to transport |

Two Lean design lessons to adopt wholesale, both from its README:

1. **Export the construction, not a bundle** (finding 17, four instances).
   When a theorem is the interface to a construction, return the structure
   (`StripData`-style) and let consumers project; a tuple of imagined-useful
   properties keeps coming up one clause short.
2. **A named hypothesis must be one a later module can discharge** — and
   writing down what the discharger will pass, *before* writing the
   discharger, is the cheap defence that caught five defects there.

## The findings ledger — carry, don't rediscover

The corrected statements to use, by area. (Numbers = findings in the
preserved branch's README.) The cell-structure and transfer items below were
recorded on the superseded route, but the structures they name
(`boundaryStart`, `paths_meet`, `anchor_uniqueFaceAt`, `IsFaceJordan`,
`MeetsFinitely`, `FreshDense`, …) carried over into the finished route —
verify each against its module on `main` when translating.

- **Overlay/subdivision**: nondegeneracy in `splitAt_avoids` (2) — ours is
  immune by convention, see table above.
- **Strip/polygon**: the set-level polygonal Jordan curve needs a
  **realization theorem** — every simple closed polygonal curve admits a
  corner-free vertex-list presentation, via deleting collinear vertices (18).
  Lean's `Realization.lean` (1.6k lines) is the bridge the blueprint takes
  for granted; budget it as a full wave, and its arc twin `PolyArcRealize`.
- **Outer chain**: `CrosscutEncloses` as first stated is **false** (19); the
  repair is the clause `x ∈ exterior`. Take the repaired statement.
- **Grid attachment**: the blueprint's "finitely many components of
  `|L| ∖ C`" is **false** as a plane fact; the honest invariant is
  `MeetsFinitely` (every fed segment meets `C` finitely), under which
  coverage is a theorem via midpoints between crossing parameters — no
  component ever named.
- **Square mesh**: clause 5 (2-connectivity) is false for ≤ 1 fresh point;
  the repair is `FreshDense` **plus `δ < 4`** (20), both free at the call
  site (`δ = 2⁻ⁿ`).
- **Cell structures**: the boundary walk of a 2-cell is **data, carried by
  the structure** with a `boundaryStart` field (orientation cannot be a
  closed form); `paths_meet` not `paths_disjoint`; `IsFaceJordan` and
  `tgt_isPolygonal` are *fields of the stage bundle* discharged at stage 0 —
  each of these was a consumer-found shortfall there, and the bundle should
  be born complete here.
- **Finite transfer**: `EarStep` needs `[Infinite γ]` (fresh names); the ear
  step is one split with **no subdivision** (both ends are already 0-cells);
  `edge_subset` triggers only at meeting points that are not vertices (the
  repaired overlay convention); `anchor_uniqueFaceAt` and `homeo_eqOn` are
  invariants of the partial-transfer bundles, both sides.
- **Source vs target are not mirror images**: outer edges of a source stage
  are subarcs of the wild curve, so polygonality is always restricted to
  nonboundary edges; the reflex to mirror the two sides is the recorded
  recurring cost.

## Phases

Waves are sized from the Lean module line counts; the working assumption from
`PLAN_JORDAN_SCHOENFLIES.md` stands — ~1k foundational lines/day, and the
hard constructions do not bulk-generate. Keep `make -j 16 plane` /
`make -j 16 graph` as the inner loop, full `library` + `tests` at commits.

### Phase T0 — H6, polygonal redrawing (~2.5–5k lines)

Already designed and corrected (B1–B8). Build it first: it closes Layer 6, it
is the first result needing Layers 0–6 at once, and Part I's parity/overlay
waves sit directly on the same machinery. Nothing in it waits on the Lean
side.

### Phase T1 — Part I (~20k lines here; ~15k lines of Lean original)

In Lean dependency order, one wave per row. Each wave starts by listing the
Layer 0–4 stubs it consumes that our side deferred ("not built,
deliberately" items — e.g. diameter of a set, the nested-compact
intersection, `distanceToSet`) and builds only those it actually needs.

| Wave | Content | Lean modules (lines) |
|---|---|---|
| T1.1 | parity of crossings, polygon parity | `Parity` (1038) |
| T1.2 | the two-sided strip and its constants | `Strip` (1013), `StripConnected` (523), `StripConstants`, `StripLocal` (448) |
| T1.3 | the separation predicate and region API: `IsSeparating`, `inside`/`outside`, absorption, crosscut cells | `CrosscutCells` (461) |
| T1.4 | **H7 — the polygonal Jordan curve theorem** | `PolygonBridge`, `Bounded`, `PolygonalJordan` (626) |
| T1.5 | parity splitting, the polygonal crosscut theorem, alternating crosscuts | `ParitySplitting` (576), `PolygonalCrosscut` (645), `AlternatingCrosscuts` (260) |
| T1.6 | the realization theorems (set-level polygonal curve → vertex-list presentation; arc case) | `Realization` (1600), `PrePolygonSep` (519), later `PolyArcRealize` (739) |
| T1.7 | **H8 — `K₃,₃` has no plane drawing**; face cycles | `Graph/K33Land`, `FaceCyclesProof`, `FaceCyclesLand` (457) |
| T1.8 | **H9 — the outer-chain lemma** (with the repaired `CrosscutEncloses`) | `OuterChain` (791), `CrosscutExists` (491), `CrosscutEncloses` (552), `OuterChainClosed` |
| T1.9 | strong accessibility; accessible endpoints | `Accessible`, `AccessibleJoin` |
| T1.10 | the arc-complement theorem | `ArcComplementPrep`, `ArcComplement` (779) |
| T1.11 | **the Jordan curve theorem** | `JordanSeparates` (659), `Jordan` (902), `JordanClosed` |
| T1.12 | **H10 — the general crosscut theorem** | `CrosscutAtMostTwo` (630), `ArcCollars` (1966), `GeneralCrosscut` (542) |

T1.2 is the blueprint's own predicted stress point (the strip lemma) — but it
now has a finished original, so the risk left is *language* risk: whether our
tactics carry the choice-of-constants arithmetic readably. Treat frictions
found there as first-class deliverables, per the always-apply rule.

The Jordan curve theorem (end of T1.11) is the natural publish-and-reassess
point, exactly as the original plan said.

### Phase T2 — Part II scaffolding, parallel-safe (~8k lines)

The abstract cell-structure layer has **no geometric prerequisites** — the
Lean side proved `lem:combinatorial-invariance` before its Jordan curve
theorem existed. Any session blocked on a T1 wave can advance here.

- T2.1 `CellStructure`, `Realization`, `SkeletonHomeo`,
  `lem:combinatorial-invariance` (`CombinatorialInvariance.lean`).
- T2.2 the generated structure, both elementary operations, boundary walks
  **as data** with `boundaryStart`, the cellulation invariants
  (`GeneratedStructure`, `BoundaryCycles`, `BoundaryCyclesGenerated`,
  `CellulationInvariants`).
- T2.3 realization constructors and skeleton-map transport for both
  operations (`RealizeSubdiv`, `RealizeSplit`, `RealizeSubdivHomeo`,
  `MatchedSplit`, `ArcMonotone`).
- T2.4 the limit tower and limit map against the abstract interface
  (`RefinementStars`, `StageTower`, `LimitMap`) — on the Lean side this
  whole block has *no free hypotheses*: every obligation is a field.

Build the bundles **born complete**: `GeneratedPair` there grew `walks`,
`src/tgt_isFaceJordan`, `tgt_isPolygonal`, `homeo_eqOn`, `anchor_uniqueFaceAt`
one consumer-discovered shortfall at a time; here they go in on day one, and
the "write down what the discharger passes first" rule is the check.

### Phase T3 — Part II geometry and the endgame (~20k lines)

In the finished route's order: the initial pair (`InitialPair*`,
`InitialGenerated`, `InitialOuterCycle`, `InitialReverseTransfer`), finite
transfer both directions (`FiniteTransfer`, `CommonSubdivision`,
`FiniteTransferTarget`, `FiniteTransferTargetMesh`), the overlay and mesh
machinery (`SquareMesh*`, `SourceOverlay`, `TargetOverlay`,
`OverlayExtension`, `FreshDenseSelection`), the source attachment and the
quantitative recursion (`Windows`, `LocalGrid`, `GridAttach`,
`SourceAttachment`, `SourceJoining`, `QuantitativeStages`,
`QuantitativeForwardStages`, `QuantitativeRecursion`, `StageTransition`),
the limit map and boundary continuity (`LimitMap`,
`InteriorHomeomorphism`, `BoundaryAnchors`, `MatchedArc`,
`BoundaryContinuity2`), and the endgame (`Inversion`, `SquareMover`,
`Endgame`, `JordanSchoenflies`). Derive the exact wave order from the
import graph when T3 starts, the way T1's table was derived.

## The ledger

Maintain the statement-level map as translation proceeds, one row per
blueprint label: label → Lean module → math file → status
(open / conditional-on-what / done). Seed it from the two tables at the end
of `schoenflies-lean/docs/ROADMAP.md` ("Part I" and "Part II"), which are
exactly that map for the Lean side. The ROADMAP's own status discipline
transfers verbatim and is worth keeping: *a "done" that is really a
"conditional" costs the next agent a day — and so does the reverse.*

## Size and rate, honestly

Lean total is ~77k lines including its own foundation re-build; the content
above its foundation is roughly 40–45k. Our side historically runs wordier
per statement but starts from a finished foundation and a debugged original.
Working estimate: **~45–55k lines, multi-month at the ~1k/day foundational
rate** — consistent with the original plan's Part I ~20k + Part II ~28k.
First real calibration: T0 + T1.1, both bounded and fully specified.

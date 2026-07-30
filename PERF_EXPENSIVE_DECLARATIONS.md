# Surprisingly expensive declarations

A ledger of single declarations whose verification cost is out of all
proportion to what they say, with the measurement that found them and what the
cost turned out to be. Kept because each is a candidate for a *different
proof*, not for a bigger budget — and because the first three all turned out to
be the same shape.

Measure with:

```sh
MATH_TIME_DECLARATIONS=1 make -j 1 <area>      # per-declaration wall clock
MATH_PROFILE_AUTOPROVER=1 ./kernel verify --source <file> --cache-root build
                                               # per-claim, per-tactic breakdown
```

## The ledger

| declaration | file | wall clock |
| --- | --- | --- |
| `Plane.IsEndOf.orientSegment` | `Plane/Graph/orient.math` | **191 s** |
| `Plane.subdivide_common_segment` | `Plane/Graph/overlay.math` | **94 s** |
| `Plane.subdivide_separated` | `Plane/Graph/overlay.math` | **40 s** |
| `Graph.basics:287` (`Graph.Joins.ends_agree` region) | `Graph/basics.math` | 3.8 s |

Everything else in `Plane/Graph/` is under 1.5 s, so these four are ~5.5 of the
~6 minutes the area costs. Found 2026-07-30 while asking why `overlay.math`
was slow; the answer was that `overlay.math` is not slow, three declarations
are.

## What the cost is

Isolate the cheapest one (`Plane.subdivide_separated`, 40 s) into a scratch
module that imports `Plane.Graph.overlay` and restates it — that gives a 40 s
iteration loop instead of a 135 s one. Then:

```
[autoprove-summary] claims=11 (closed=7, unresolved=4)
                    losing=25100ms winning=32ms losing_share=99%
  contextEqualityBridge: inv=11 ok=3 avg=1924928 us total=21174 ms wins=0
  contextFactMatch:      inv=11 ok=7 avg=267919 us  total=2947 ms  wins=7
```

**99% of the prover time loses.** `contextEqualityBridge` alone is 21.2 s of
the 25.1 s and wins nothing: these proofs carry ~30 stated facts, almost all
`Product.first/second` projections of `Plane.Segment := Pair(Point, Point)`,
and the bridge tries to rewrite the goal along every one of them.

## Three hypotheses, all measured, two wrong

Worth recording because each looked obviously right.

1. **`by substituting (<bare equation>)` re-proves the equation.** It does —
   the parenthesised form is auto-proved rather than cited — and
   `orientSegment` hides a classical `if`, so the re-proof is not cheap.
   Naming the equation moved `Plane.IsEndOf.orientSegment` from 191 s to
   188 s. **Not the cause.**
2. **Turn `contextEqualityBridge` off.** Its own comment said it was
   "disabled by default to measure the saving" while the predicate enabled it
   unless an opt-out was set — code and comment disagreed. Defaulting it off
   **fails 11+ library files** (`Lists`, `Natural`, `Logic`, `Polynomial`) on
   "no in-scope hypothesis matches structurally". The code was right and the
   comment was wrong; the comment now records the measurement instead.
3. **Add explicit `by` hints to the expensive claims.** There are none to
   add. Only ~0.7 s of the 40 s sits in by-less claims — the rest is premise
   discharge for citations the author has *already* written
   (`… by Plane.subdivide_avoids`, `… by Plane.subdivide_ends_are_cuts`),
   each searching a 30-fact context for its premises. **"Add a `by`" is not
   the fix for these.**

## Where the time actually is — one claim each

`MATH_TIME_CLAIMS=1` answers this directly. Every one of these declarations is
**one or two claims**, not a diffuse cost:

| declaration | line | self | hint as written | what closed it |
| --- | --- | --- | --- | --- |
| `Plane.IsEndOf.orientSegment` | orient:202 | **188 s** | `by substituting <eq>` | `localFactExactMatch` |
| `Plane.subdivide_common_segment` | overlay:251 | 46 s | `by <proof>` | *nothing — the claim failed* |
| `Plane.subdivide_common_segment` | overlay:248 | 46 s | `by <proof>` | `localFactExactMatch` |
| `Plane.subdivide_separated` | overlay:323 | 39 s | `by <proof>` | `contextEqualityBridge`, via `Plane.segmentDrawing_arcFinish` |

Three separate things to notice, none of which the old instrumentation could
have told us:

- **orient:202 is `by substituting isReversed` closed by `localFactExactMatch`.**
  The rewritten goal is proved by a fact stated on the line above — the
  cheapest rung there is. So the 188 s is spent inside the SUBSTITUTION, not
  in proving anything. Naming the equation (already done) does not help,
  because the equation was never the search; the rewrite is.
- **overlay:323 is closed by `Plane.segmentDrawing_arcFinish`** — a lemma about
  DRAWINGS, in a claim about segment endpoints. The author's cited lemma
  (`Plane.same_ends_of_meeting_interiors`) is not what proves the step. This
  is friction L4's site: the goal is `(A ∧ B) ∨ (C ∧ D)` and the prover works
  through the false side first.
- **overlay:251 cost 46 s and closed nothing** — a speculative path that
  failed after 3.0M kernel steps and fell back. Any instrumentation keyed on
  success is blind to it by construction.

## What the instrumentation does and does not see

The expensive-step warning gained two things (2026-07-30):

- it names the **winning fact's proposition** when the winner has no citable
  name (an anonymous claim, or a conjunction leg — which is what wins most
  such steps; `citableNameFromFactSource` returns empty for those and the
  message used to name only the strategy);
- it names the **dominant losing tactic** and what it cost, and fires on
  **wall clock** as well as kernel steps (`MATH_AUTOPROVE_WARN_MS`, default
  1500). The two triggers catch different things: kernel steps catch a hidden
  *computation*, wall clock catches a hidden *search*, whose cost is defeq
  probes in the elaborator and barely moves the step counter.

That took the library from ~35 to 47 expensive-step warnings, all now
carrying a millisecond figure — and it still does not surface the four
declarations above, because it fires only on a by-less claim that SUCCEEDS
(`if (proof)`), and their cost is neither.

**`MATH_TIME_CLAIMS=1` closes that gap** and is the tool to reach for first.
It times EVERY structured claim — hinted, by-less, failed, speculative — and
reports per declaration, sorted by SELF time (inclusive minus nested claims,
so the line that pays is named rather than the block containing it):

```
[claim-cost] Plane.Graph.overlay Plane.subdivide_separated: 40130 ms over 31 claim(s)
[claim-cost]   self_ms  incl_ms   steps  line  hint / closed by / wasted by
[claim-cost]     39199    39199 3376345   323  by <proof> | closed: contextEqualityBridge
                                                (library lemma Plane.segmentDrawing_arcFinish)
                                                | wasted: contextEqualityBridge 5287 ms
```

Rows are recorded from the scope's DESTRUCTOR, so a claim that throws is
reported too. Declarations under 200 ms print nothing. Off by default and
costing one branch per claim when off.

Known imprecision: `closed by` is the last prover win anywhere in the claim's
subtree, so for a hinted claim it may name a premise's winner rather than the
claim's own. The self-time column is the reliable number.

## Library-wide ranking (2026-07-30, `MATH_TIME_CLAIMS=1`, cold)

**Nothing below is fixed yet.** This is the baseline the fixes get measured
against.

Over a cold `make library`: 2537 claims reported (only from declarations above
the 200 ms floor), **1087 s of claim self-time in total**. The distribution is
extremely concentrated:

- **top 10 claims = 499 s = 46%** of all reported claim time
- top 20 claims = 617 s = 57%

By area: `Plane` 448 s, `Algebra` 424 s, `Real` 60 s, `Natural` 40 s,
`Metric` 25 s, `Graph` 24 s, `Polynomial` 21 s.

| ms | declaration | line | hint as written | closed by |
| --- | --- | --- | --- | --- |
| **193758** | `Plane.Graph.orient Plane.IsEndOf.orientSegment` | 202 | `by substituting <eq>` | `localFactExactMatch` |
| **48010** | `Algebra.basis_pruning VectorSpace.size_one_finite_dimensional` | 808 | `by pointNonzero` | `contextFactDiffBridge` |
| **47162** | `Plane.Graph.overlay Plane.subdivide_common_segment` | 248 | `by <proof>` | `localFactExactMatch` |
| **46566** | `Plane.Graph.overlay Plane.subdivide_common_segment` | 251 | `by <proof>` | *nothing — hint checked directly, or it failed* |
| **40108** | `Plane.Graph.overlay Plane.subdivide_separated` | 323 | `by <proof>` | `contextEqualityBridge (library lemma Plane.segmentDrawing_arcFinish)` |
| **37154** | `Algebra.schur_complement Matrix.quadraticForm_schurComplement` | 575 | `by Matrix.quadraticForm_bordered` | *nothing — hint checked directly, or it failed* |
| **24980** | `Algebra.rank_nullity LinearMap.appended_images_independent` | 1836 | `by <proof>` | *nothing — hint checked directly, or it failed* |
| **23080** | `Plane.concatenate Plane.IsLoop.concatenate` | 798 | `by Plane.concatenate_across_seam_of_loop` | *nothing — hint checked directly, or it failed* |
| **20061** | `Algebra.characteristic_polynomial Matrix.characteristic_entry_leading` | 388 | `by substituting <eq>` | `equalityBattery` |
| **18195** | `Algebra.characteristic_polynomial Matrix.characteristic_entry_constant` | 415 | `by substituting <eq>` | `equalityBattery` |
| **17619** | `Real.arithmetic_geometric_mean Real.means_inequality_doubling` | 269 | `by substituting <eq>` | `contextFactMatch (local binder _claim_anon_268_9)` |
| **16152** | `Natural.floor_divide Natural.monus_succ_implies_gt` | 370 | `by cases` | `monotonicityRecursion` |
| **13532** | `Algebra.rank_four_diagonal_branch Matrix.diagonalExtension_apply_appendCoordinate_general` | 178 | `by cases` | `contextFactDiffBridge` |
| **11322** | `Real.arithmetic_geometric_mean Real.means_inequality_downward` | 296 | `by substituting <eq>` | `contextFactMatch (local binder atIndex)` |
| **11247** | `Algebra.rank_nullity VectorSpace.independent_append_outside_span` | 724 | `by <proof>` | `localFactExactMatch` |

Patterns worth naming, since they recur down the list:

- **`by substituting <eq>` is the single worst hint form.** It takes four of
  the top eleven, including the 194 s outlier. In each case the rewritten goal
  is then closed by a cheap rung (`localFactExactMatch`, `equalityBattery`,
  an exact context fact) — so the cost is the REWRITE SEARCH, not the proof.
- **"closed by nothing" appears four times in the top ten.** Those are claims
  whose hint was checked directly (so the prover's verdict is empty) or which
  failed and fell back. Either way, seconds spent with no prover win to show
  for it.
- **`Plane.IsLoop.concatenate:798` (23 s) is mine**, added in this session's
  cycle→Jordan-curve work. `by Plane.concatenate_across_seam_of_loop` is the
  right lemma mathematically and it is the 8th most expensive claim in the
  library; worth revisiting when the `by`-citation discharge path is
  understood.

## FIXED 2026-07-30: the cheap-prover pass in `by substituting`

**The `by substituting` family is solved.** Measured with `MATH_TIME_SUBST=1`,
which times the phases of `elaborateClaimBySubstitution` using LOCAL
accumulators (the function reaches itself through `autoProveClaim`, so member
accumulators had an inner call wipe the outer one's tally):

```
BEFORE  [subst] Plane.Graph.orient:202 total 189461 | prepare 0 | occurrence 0
                | typecheck 2 | defeq 0 | prove 188981 (FAILED 188980, calls 5)
AFTER   [subst] Plane.Graph.orient:202 total   1407 | prepare 0 | occurrence 0
                | typecheck 52 | defeq 0 | prove 855 (FAILED 855, calls 5)
```

The substitution machinery is **entirely innocent** — occurrence search,
type-checks, defeq probes and candidate preparation are all ~0 ms. Essentially
100% of the cost was the auto-prover FAILING on rewrite candidates that do not
work, while the candidate that succeeds costs about a millisecond.

The fix is one new pass. The loop was `pass 0` = fast path only (no prover),
`pass 1` = prover at full budget. It is now:

- **pass 0** — fast path only (reflexivity/defeq), unchanged;
- **pass 1** — every candidate under a LOW effort cap (`RedundancyBudgetGuard`);
- **pass 2** — the old pass 1, at full budget, unchanged.

Completeness is unaffected: anything that needed the full search still reaches
pass 2. What changes is that a cheap winner is found before an expensive loser
can burn the whole budget. An `AutoProverBudgetError` in the cheap pass is
caught and treated as a miss (it is rethrown in the full pass, where it still
means what it always did).

Measured results:

| site | before | after | factor |
| --- | --- | --- | --- |
| `Plane.IsEndOf.orientSegment:202` | 189 461 ms | 1 407 ms | **135×** |
| `Matrix.characteristic_entry_leading:388` | 9 532 ms | 411 ms | 23× |
| `Matrix.characteristic_entry_constant:415` | 7 704 ms | 441 ms | 17× |
| `Plane/Graph/orient.math` (whole file) | ~191 s | 3.1 s | 62× |

Library-wide, both runs under `make -j 16` so they are comparable to each
other: **total claim self-time 1087 s → 910 s (−16%)**, and the **top 10
claims 499 s → 297 s (−40%)**. Zero errors, `tests` and `docs-check` green.

`by substituting` no longer appears anywhere in the top 10.

## What `contextEqualityBridge` actually does — and why it is not linear

Worth writing down, because the natural mental model is wrong and the wrong
model suggests the wrong fixes.

It is **not** congruence closure. It does not build a graph of known-equal
terms and search for a path from the goal's LHS to its RHS. For each equality
`a = b` in context, and each of the two directions, it:

1. searches the GOAL structurally for occurrences of one endpoint;
2. rewrites them — building a motive plus `Equality.transport_proposition`;
3. **calls the full auto-prover recursively on the rewritten goal.**

So it is depth-1 rewriting followed by a complete proof search, per equation,
per direction. The transitive "path" a reader imagines is not enumerated by
the bridge; it emerges only because the recursive prove can re-enter the
bridge (bounded by `budget - 1`). That is where the cost lives: one candidate
rewrite spawns a whole search, and the search may spawn more.

A real congruence-closure / union-find pass over the context equalities WOULD
be near-linear, and would make this rung cheap. It is also a genuinely
different algorithm, not a tuning change.

## Attempt: capping the bridge's recursive prove — FAILED

Measured on `Metric/connected.math`, where the bridge is 74 invocations,
**ONE win**, and 10.4 s of the file's 24 s.

- **Cheap-pass-first** (the shape that fixed `by substituting`): **worse**,
  14.7 s → 15.6 s. That fix works by finding a cheap winner before an
  expensive loser spends the budget. Here there is a winner in 1 case out of
  74, so there is almost never a cheap winner to find and the extra pass is
  pure overhead. *The same shape does not transfer to a rung with a low win
  rate.*
- **Capping the recursive prove outright** at the redundancy budget: 14.7 s →
  **4.9 s**, but **breaks 4 library files** (`Algebra/integral_domain`,
  `Natural/cancellation`, `Natural/arithmetic`, `Natural/binomial`). Some of
  the rare wins genuinely need the room.
- **Capping at 200k / 400k kernel steps**: library green, but **no speedup at
  all** (15.0 s / 15.0 s) — the losing searches each stay under the cap, so
  nothing is cut.

There is no single step-count cap that both keeps the library green and cuts
the cost: the searches that must be allowed and the searches that waste time
are not separated by total step count. A different discriminator is needed —
or the congruence-closure rewrite above.

**Kept from the attempt:** `CheapProveWindow` (`internal.hpp`), a correct
self-contained low-effort window. `RedundancyBudgetGuard` only lowers the
ceiling, and since the budget is cumulative from the armed frame's snapshot,
lowering it mid-search trips instantly AND leaves `autoProveBudgetTripped_`
set, poisoning the rest of the claim — which is exactly how the first version
of this attempt broke `Metric/connected.math`. `CheapProveWindow` saves and
restores the snapshot, ceiling, trip flag and active flag. The
`by substituting` fix now uses it.

## Optimisation attempts so far — both failed, measured

Recorded so the next attempt does not repeat them.

1. **Lazy goal forms in `elaborateClaimBySubstitution`.** The function builds
   up to five normalisations of the goal — deep WHNF through application
   spines, a force-unfold of opaque heads, head WHNF, a ζ-expansion and its
   deep WHNF — **eagerly, before trying the surface form that usually
   works**. On a goal mentioning `Plane.orientSegment`, whose body is a
   classical `if`, deep-WHNF grinds through the choice operator. Making the
   forms materialise on demand (same forms, same order, same dedup) is
   obviously right in principle and, measured serially on
   `Algebra.characteristic_polynomial`, worth **20.9 s → 20.5 s: 2%, i.e.
   noise**. Reverted. Do not re-attempt without first showing the deep forms
   are actually being built.
2. **Reading a 2× win off a parallel build.** `-j 16` wall-clock per claim is
   heavily contended: the same declaration measures 13–16 s under `-j 16` and
   9.7 s serially. An "improvement" measured across the two is meaningless.
   **Measure serially, one file, or not at all.**

## Where the substitution cost is — routing confirmed

`by substituting <eq>` takes four of the top eleven and looks like one shared
root cause. The routing is confirmed:

```
dispatch.cpp  SurfaceStructuredClaim
  → induction.cpp:1677  Elaborator::elaborateStructuredClaim
      → induction.cpp:1753  if (claim.bySubstitution)
          → claim.cpp:9     elaborateClaimBySubstitution
```

**Correction to an earlier note here.** I recorded that the expensive claims
"never execute `elaborateClaimBySubstitution`", on the strength of sub-phase
counters that reported zero attempts. That conclusion was wrong: the counters
were being reset by NESTED `ClaimCostScope`s (an enclosing claim's tally wiped
by the claims inside it). The reset bug was fixed but never re-validated on
the right row before the whole batch was reverted, so the "zero attempts"
reading should be treated as unmeasured, not as a fact about the code.

`reportClaimHintDiagnostics`, which runs right after the substitution returns,
is gated behind `classifyHintsEnabled()` / the redundancy flags, so it is NOT
a suspect in an ordinary build.

**Next step: re-instrument with the nested-reset fix in place, and confirm
which phase of `elaborateClaimBySubstitution` holds the 9.8 s** before
optimising anything. Both failed attempts below came from acting ahead of
that measurement.

## Directions worth trying

- **Shrink the context.** These proofs state ~30 facts before using any of
  them. Splitting each into a lemma that takes only what it needs would cut
  the scan quadratically. This is the most promising and needs no engine work.
- **Give `Plane.Segment` an element interface.** Every fact is about
  `Product.first(part)` / `Product.second(part)`; naming the two ends once per
  piece (`let nearEnd := …`) or carving the type out with accessors would stop
  the matcher from re-deriving projections at every candidate.
- **Bound `contextEqualityBridge` per claim.** It cannot be removed, but a
  per-claim time or candidate cap would turn a 2 s loss into a 50 ms one.
  Needs care: it wins 16 of 217 outermost claim sites library-wide.
- **`Plane.IsEndOf.orientSegment` specifically** — 191 s for a statement that
  says "orienting a segment keeps its ends" deserves a different proof, not a
  faster prover. Now localised to one `by substituting` whose rewrite, not
  whose proof, is the cost: worth trying a boundary lemma that states the
  transported form directly, so no rewrite is searched for at all.
- **Profile `elaborateClaimBySubstitution`.** orient:202 shows a *narrowed*
  `by substituting <eq>` costing 188 s and 610k kernel steps to move one
  equation through one predicate. That is disproportionate on its face and is
  the single biggest number in the ledger.

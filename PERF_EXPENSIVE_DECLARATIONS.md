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
carrying a millisecond figure — and it still **does not surface any of the
four declarations above**, because the warning fires only on a by-less claim
that SUCCEEDS (`if (proof)`), and their cost is neither. Closing that gap is
the next instrumentation step: time premise discharge for an explicit
citation, and report a claim whose `by` was cheap to state but expensive to
check.

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
  faster prover.

# Metric spaces, and topology developed once

**Status: proposed 2026-07-27. Not started.**

## The problem

`Plane/` defines the topology only for `Set(Plane.Point)`, so a curve had
to be parametrised by a *plane set* (`Plane.unitSegment`) and a
parametrisation is a `Plane.Point → Plane.Point` map. A mathematician
writes `γ : [0,1] → ℝ²`. We wrote what we did because the topology we had
was the only topology there was.

The cost is not abstract. `Plane/twoarcs.math` is 838 lines, and most of
them are the encoding: `Plane.Point.first(x)` unpacking (477 sites
area-wide), `Plane.Point.make(1, 0)` for "the parameter 1" (109 sites), an
entire parameter-order characterisation of a subsegment
(`member_segment_of_first_coordinate` and friends) whose content over ℝ is
`0 ≤ t ≤ 1`, and `Plane.walk` / `first_of_walk` /
`unitSegment_at_first_coordinate` / `unitSegment_equal_of_first_coordinate`
which exist only to move between a parameter and the plane point encoding
it. Over a real interval, parameter equality is equality and
`Plane.retime` is `t ↦ 2t - 1`.

It also multiplies. There are already two continuity families
(`ContinuousOn` for `Plane → Plane`, `RealContinuousOn` for `Plane → ℝ`);
doing intervals by hand adds `ℝ → ℝ` and `ℝ → Plane`, and the Schoenflies
work ahead wants carriers that are subsets of arcs. That is the number to
worry about, not the 477 unpackings.

## What is NOT wrong

The **carrier-set style is right and should be kept**: `ContinuousOn(f, S)`
with points living in the ambient type, rather than subspaces as
`Subtype`s. Subtype subspaces would put a proof beside every point and
leak the CIC encoding into every statement — exactly what `docs/style.md`
fights. Mathlib carries both `Continuous f` and `ContinuousOn f s` for the
same reason. The defect is the *domain type*, not the carrier.

## Recommendation: generic over a bundled METRIC space

Not general topological spaces. Reasons:

- Every proof in the development is metric: ε-δ continuity, sequential
  compactness, Bolzano–Weierstrass. With open-cover compactness we would
  owe a bridge to the sequential form before any existing proof compiles.
- Nothing in Jordan–Schoenflies needs a non-metrisable space.
- Separation axioms (T0/T1/T2) are *theorems* in a metric space, not
  hypotheses to carry.

The structural test — "could the foundation be replaced without touching
consumers?" — is still met: consumers speak `ContinuousOn` / `IsCompact` /
`IsConnected` / `OpenIn` over an abstract space, so a topological-space
layer could later be slid underneath and the metric development re-derived,
with `Plane/`, `Curve/` and the blueprint untouched. That is the property
that makes this "the right structure" rather than "the cheapest thing that
works".

## The design, in the library's own idiom

`Algebra/ring_bundle.math` already shows the pattern, and it is the one to
copy: a bundle in `Type(1)` carrying its `Type(0)` carrier, projections
taking the bundle implicitly, and `instance` registering the canonical
bundle per carrier.

```math
inductive MetricSpace : Type(1) where
  | MetricSpace.make
      : (carrier : Type(0)) → (distance : carrier → carrier → ℝ)
        → IsMetric(carrier, distance) → MetricSpace

definition MetricSpace.distance {m : MetricSpace}
        : MetricSpace.carrier(m) → MetricSpace.carrier(m) → ℝ := …

definition MetricSpace.OpenIn {m : MetricSpace}
        (subset region : Set(MetricSpace.carrier(m))) : Proposition := …
```

Then `Real.metricSpace` and `Plane.metricSpace` as instances, and ONE
development of `OpenIn` / `ClosedIn` / `IsCompact` / `IsConnected` /
`ContinuousOn` / `UniformlyContinuousOn` / `IsHomeomorphismOn`. The four
continuity families collapse to one: `ContinuousOn(γ, Real.unitInterval)`
for `γ : ℝ → Plane.Point` is the same definition as the `Plane → Plane`
case, with two instances instead of one.

## Prototype findings (2026-07-27)

Verified against the real kernel, not assumed:

- **The generic definitions elaborate.** `MetricSpace`, the carrier and
  distance projections, and `MetricSpace.OpenIn` over
  `Set(MetricSpace.carrier(m))` all typecheck, using the `Ring` projection
  idiom (`let ⟨…⟩ := m in …`).
- **`instance` registration does not yet accept the bundle.** Both
  `instance Real.metricSpace` and `instance Plane.metricSpace` fail with
  *"could not determine the carrier of its bundle type 'MetricSpace'"* —
  so it is not carrier-specific. Registration reads the carrier via
  `carrierProjectionField` in `src/elaborator/statements.cpp` (~line 205);
  that helper returns nothing for this bundle although the shape matches
  `Ring`'s. **This is the one blocking unknown, and it is narrow.** Settle
  it before committing to the plan.
- **No competing metric.** `Plane.supBall` is defined and never used, and
  no topology is built on `supDistance` — it appears only as a
  real-valued function (the square-boundary level set, some estimates). So
  one canonical instance per carrier is enough, and canonical inference is
  not at risk.

## Staged migration (keeps the tree green throughout)

1. `Metric/` : the bundle, `IsMetric`, instances for ℝ and `Plane.Point`.
   Resolve the registration issue first.
2. Port the topology definitions and their theorems generically. Most
   proof text carries over with `Plane.distance` → `MetricSpace.distance`.
3. Make the existing `Plane.*` names thin aliases of the generic ones, so
   every downstream file keeps building unchanged. Retire the aliases file
   by file afterwards.
4. Switch parametrisation domains to ℝ with carrier `Real.unitInterval`.
   Delete `walk`, `first_of_walk`, `unitSegment_at_first_coordinate`,
   `unitSegment_equal_of_first_coordinate`, the `first_coordinate_*`
   family, and the parameter-order characterisation in `twoarcs.math`;
   `retime` becomes arithmetic.

Step 3 is the de-risking move — without it this is a big-bang rewrite of
9,300 lines.

## Honest cost

400–700 lines of new generic material, against deleting substantially more
than that from `Plane/` and not writing the two families the interval
would otherwise need. The new material is permanent library value:
`Real/intermediate_value.math` and `Real/derivative.math` already exist
with no topology underneath them.

# Metric spaces and their topology

A metric space is **bundled**: one value `m : MetricSpace` carries its carrier
type, its distance, and the four axioms together. The whole relative topology
is developed once over an abstract `m` and read at ℝ, at the plane, and at
anything else that supplies a metric.

Two conventions make that readable. A bundle value used where a **type** is
expected means its carrier, so a signature names the space:

```math
theorem MetricSpace.IsCompact.image (source target : MetricSpace)
        (f : source → target)
        (region : Set(source))
        (compact : MetricSpace.IsCompact(region))
        (continuous : MetricSpace.ContinuousOn(f, region))
        : MetricSpace.IsCompact(Set.image(f, region))
```

And an `instance` per carrier lets an implicit `{m : MetricSpace}` resolve from
a bare `Set(ℝ)` or `Set(Plane.Point)`, so consumers never pass the space.

Everything is stated **relative to a region** from the start; the absolute
notions are the `region = Set.universe` case. Connectedness and compactness get
applied to arcs and curves as subspaces, so relativising later would cost more
than paying for it once.

The relative notions describe the **trace** `subset ∩ region` and nothing else:
a point outside the region is never tested for relative openness, never in a
relative interior, and never a witness for a relative closure. (`subset ⊆ region`
is *not* required — consumers that need the inclusion carry it separately — but
where it holds, the relative notions say exactly what the absolute ones say
about the subspace.)

## Main definitions

- The bundle `MetricSpace`, `IsMetric`, `MetricSpace.carrier`,
  `MetricSpace.distance` — [space.math](space.math)
- `MetricSpace.OpenIn`, `IsOpen`, `Ball`, `Closure` — [topology.math](topology.math).
  `MetricSpace.IsOpen.ball_inside` and `MetricSpace.Closure.meets_every_ball`
  (with their `of_…` converses) are the absolute readings, free of the
  `Set.universe` membership the relative definitions carry
- `MetricSpace.ContinuousWithinAt`, `ContinuousAt`, `ContinuousOn` —
  [continuity.math](continuity.math). Continuity **within a region** at a point
  is the primitive; `ContinuousAt(f, x)` is the whole-space case.
  `MetricSpace.ContinuousAt.near` / `.of_near` cross to `Near`, and
  `MetricSpace.ContinuousWithinAt.near` / `.of_near` to `NearWithin`
- `MetricSpace.Near` — [near.math](near.math), the spatial twin of
  `Natural.Eventually`: "P holds throughout some ball around x". Same four
  moves, with the **minimum** of two radii where sequences take the maximum
  of two thresholds. **Unpunctured**, so it is proper with no
  non-isolated-point side condition (`MetricSpace.Near.at_center`)
- `MetricSpace.NearWithin` — the relative twin, "P holds at every point of the
  region on some ball around x". A filter in its own right, so
  `for y sufficiently near x within region: { … }` proves one, folding every
  in-scope `NearWithin` fact **at the same region**. Its body is not handed the
  region membership; state `MetricSpace.NearWithin.in_region` when the argument
  splits on where in the region the point lies
- `MetricSpace.SequenceConverges`, `IsBounded`, `SubsequenceConverges` —
  [sequence.math](sequence.math)
- `MetricSpace.IsCompact` — [compactness.math](compactness.math). Its image
  theorem is stated over the ordinary `Set.image`, which involves no metric
- `MetricSpace.IsConnected`, `preimageIn` — [connected.math](connected.math)
- `MetricSpace.UniformlyContinuousOn` — [uniform.math](uniform.math)
- `MetricSpace.InjectiveOn`, `HasContinuousInverseOn`, `IsHomeomorphismOn` —
  [homeomorphism.math](homeomorphism.math)
- ℝ as a metric space (`Real.distance`, `Real.metricSpace`) —
  [real.math](real.math); the unit interval and its compactness —
  [interval.math](interval.math)

## Main theorems

- `MetricSpace.IsCompact.image` — the continuous image of a compactum is
  compact, and `MetricSpace.IsConnected.image` for connectedness
- `MetricSpace.uniformly_continuous_on_compact` — Heine–Cantor
- `MetricSpace.compact_separation` — disjoint compacta are a positive
  distance apart
- `MetricSpace.IsCompact.bounded` and `.Closure_subset` — the two halves of
  Heine–Borel that hold in any metric space
- `MetricSpace.ContinuousOn.compose`, `.restrict`, `.paste`, `.of_agreeing`
- `Real.unitInterval_IsCompact`

## Reading it at ℝ

`Real.distance(x, y)` is `abs(y - x)` — oriented that way on purpose, so a real
ε–δ statement and its metric reading are the **same term** and need no
translation between them. `Real.ContinuousAt` is then not a second notion; it
is `MetricSpace.ContinuousAt(f, x)` by definition, and the
analysis layer reaches the generic theorems directly (see `Real/uniform.math`,
which proves Heine–Cantor on `[0, 1]` by citing the generic one and nothing
else).

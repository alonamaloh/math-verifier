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
        : MetricSpace.IsCompact(MetricSpace.imageSet(f, region))
```

And an `instance` per carrier lets an implicit `{m : MetricSpace}` resolve from
a bare `Set(ℝ)` or `Set(Plane.Point)`, so consumers never pass the space.

Everything is stated **relative to a carrier set** from the start; the absolute
notions are the `carrier = Set.universe` case. Connectedness and compactness get
applied to arcs and curves as subspaces, so relativising later would cost more
than paying for it once.

## Main definitions

- The bundle `MetricSpace`, `IsMetric`, `MetricSpace.carrier`,
  `MetricSpace.distance` — [space.math](space.math)
- `MetricSpace.OpenIn`, `IsOpen`, `Ball`, `Closure` — [topology.math](topology.math)
- `MetricSpace.ContinuousAt`, `ContinuousOn` — [continuity.math](continuity.math)
- `MetricSpace.Near` — [near.math](near.math), the spatial twin of
  `Natural.Eventually`: "P holds throughout some ball around x". Same four
  moves, with the **minimum** of two radii where sequences take the maximum
  of two thresholds. **Unpunctured**, so it is proper with no
  non-isolated-point side condition (`Near.at_centre`)
- `MetricSpace.SequenceConverges`, `IsBounded`, `SubsequenceConverges` —
  [sequence.math](sequence.math)
- `MetricSpace.IsCompact`, `imageSet` — [compactness.math](compactness.math)
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
is `MetricSpace.ContinuousAt(f, Set.universe(ℝ), x)` by definition, and the
analysis layer reaches the generic theorems directly (see `Real/uniform.math`,
which proves Heine–Cantor on `[0, 1]` by citing the generic one and nothing
else).

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
  `MetricSpace.distance`, and `MetricSpace.Ball` —
  [space.math](space.math)
- `MetricSpace.OpenIn`, `IsOpen`, `ClosedIn`, and the relative
  `InteriorIn` / `ClosureIn` / `BoundaryIn` —
  [topology.math](topology.math). `MetricSpace.IsOpen.ball_inside` (with its
  `of_…` converse) is the absolute reading, free of the `Set.universe`
  membership the relative definitions carry. `MetricSpace.OpenIn.cut_by_open`
  is the textbook characterisation — some open set cuts the region along the
  trace — with `MetricSpace.OpenIn.cut_out_of_region` as its
  `subset ⊆ region` reading, and `MetricSpace.OpenIn_of_cut` /
  `MetricSpace.OpenIn.of_cut_by_open` the direction that *builds* a
  relatively open set
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
- `MetricSpace.SequenceConverges`, `IsBounded` (of a set),
  `SequenceIsBounded`, `SubsequenceConverges` —
  [sequence.math](sequence.math)
- `MetricSpace.IsCompact` and `MetricSpace.Closure` —
  [compactness.math](compactness.math). `MetricSpace.Closure.meets_every_ball`
  and its converse are the absolute reading; the image theorem is stated over
  the ordinary `Set.image`, which involves no metric
- `MetricSpace.IsConnected`, `preimageIn` — [connected.math](connected.math)
- `MetricSpace.UniformlyContinuousOn` — [uniform.math](uniform.math)
- `MetricSpace.InjectiveOn`, `HasContinuousInverseOn`, `IsHomeomorphismOn` —
  [homeomorphism.math](homeomorphism.math)
- ℝ as a metric space (`Real.distance`, `Real.metricSpace`) —
  [real.math](real.math)
- The real unit interval — [interval.math](interval.math): `Real.unitInterval`
  and `Real.segment`, the affine parametrisation `Real.between(a, b, t)`, and
  `Real.IsConvex`. This is the parameter domain every arc and curve of
  `Plane/` runs on, so it is also where the interval's compactness,
  convexity and connectedness are proved
- `Real.reflect(a, b, t)` — the interval reflected in its midpoint,
  `t ↦ a + b - t`, and `MetricSpace.landingParameters` — the parameters at
  which a curve has landed in a set — [entry_exit.math](entry_exit.math)

## Main theorems

- `MetricSpace.IsCompact.image` — the continuous image of a compactum is
  compact, and `MetricSpace.IsConnected.image` for connectedness
- `MetricSpace.uniformly_continuous_on_compact` — Heine–Cantor
- `MetricSpace.compact_separation` — disjoint compacta are a positive
  distance apart ([separation.math](separation.math)). The argument is the
  closing-pairs one: `MetricSpace.close_pair_at_every_scale` denies the gap,
  `MetricSpace.closing_pairs_share_a_limit` and
  `MetricSpace.equal_limits_of_closing` put the two sequences at one point.
  `MetricSpace.distance_shift_bound` is the estimate they run on
- `MetricSpace.IsCompact.bounded` and `.Closure_subset` — the two halves of
  Heine–Borel that hold in any metric space — and
  `MetricSpace.IsCompact.intersection`, where the subsequence comes from one
  set and its limit lands in the other because a compactum is closed
- **`MetricSpace.complement_IsOpen`** — the complement of a closed set
  (`Closure(region) ⊆ region`) is open. The one place the negation of "every
  ball meets the set" is taken classically, and it is taken here once
- **`MetricSpace.complement_unionOver_IsOpen`** — a finite union of closed
  sets has an open complement ([finite_union.math](finite_union.math)). The
  induction over the list names no radius: De Morgan turns each step into
  `MetricSpace.OpenIn.intersection`. With `MetricSpace.Closure.empty_subset` and
  `.singleton_subset` as the two base cases a union is built from
- `MetricSpace.ContinuousOn.compose`, `.restrict`, `.paste`, `.of_agreeing`
- `MetricSpace.IsHomeomorphismOn.of_continuous_injective_on_compact` — a
  continuous injection on a compactum is a homeomorphism onto its image,
  out of `MetricSpace.inverse_continuous_on_compact`
- `Real.unitInterval_IsCompact` and `Real.unitInterval_IsConnected`, the
  second out of `Real.IsConvex.connected`; `Real.between_injective` and
  `Real.between_distance` are what make a nondegenerate `Real.segment` usable
  as the domain of an arc, and `Real.member_segment_of_bounds` is its ordered
  reading
- **`MetricSpace.exists_last_inside`** and **`.exists_first_inside`** — a curve
  continuous on `Real.segment(a, b)` that lands in a closed set at some
  parameter has a **last** such parameter and a **first** one; past the last,
  and before the first, it is outside for good
  ([entry_exit.math](entry_exit.math)). The set of landing parameters is
  bounded and nonempty, so it has a supremum, and continuity plus closedness
  put the curve there back in the set. Stated over an arbitrary interval
  because the question that wants both is "the first entry into one set *after*
  the last exit from another"; `.exists_last_inside_unitInterval` and
  `.exists_first_inside_unitInterval` are the `[0, 1]` wrappers. The first
  entry is the last exit of the curve run backwards, along `Real.reflect(a, b)`

## Reading it at ℝ

`Real.distance(x, y)` is `abs(y - x)` — oriented that way on purpose, so a real
ε–δ statement and its metric reading are the **same term** and need no
translation between them. `Real.ContinuousAt` is then not a second notion; it
is `MetricSpace.ContinuousAt(f, x)` by definition, and the
analysis layer reaches the generic theorems directly (see `Real/uniform.math`,
which proves Heine–Cantor on `[0, 1]` by citing the generic one and nothing
else).

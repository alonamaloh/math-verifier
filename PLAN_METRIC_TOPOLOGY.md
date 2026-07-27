# Metric spaces, and topology developed once

**Status: steps 1–3 DONE 2026-07-27; step 4 IN PROGRESS on the branch
`metric-interval-parametrisation`. `main` is green.**

| Step | State |
| --- | --- |
| 0. `instance` accepts the bundle | **done** — `carrierProjectionField` reads the carrier off the constructor's telescope instead of a four-name table (8a898f6a). Regression test: `library/Test/bundle_carrier_registration_test.math`. |
| 1. `Metric/` : bundle, `IsMetric`, instances | **done** — `Metric/space.math`; instances `Real.metricSpace` (`Metric/real.math`) and `Plane.metricSpace` (`Plane/metric.math`). |
| 2. Topology ported generically | **done** — `Metric/{topology,continuity,sequence,compactness,homeomorphism,connected,separation,uniform}.math`. |
| 3. `Plane.*` as thin aliases | **done** — `Plane/{topology,sequence,compact,compactness,homeomorphism,connected,separation,extremum}.math` keep every name; the tree is green throughout. |
| 4. Parametrisation domains → ℝ | **prerequisites done on `main`; three files left, on a branch** — see "Where step 4 stands" below. |

What the port actually removed: `Plane/topology.math` 830 → 260 lines,
`Plane/connected.math` 853 → 486, `Plane/compactness.math` 425 → 130,
`Plane/homeomorphism.math` 239 → 84, and the second continuity family
(`Plane.RealContinuousAt`/`RealContinuousOn`) collapsed onto the generic
one with ℝ as the target space.

Two statements changed shape on the way, both for the better:

- Uniqueness of limits was proved coordinatewise in the plane; over a
  metric space it is the triangle inequality plus separation.
- `IsCompact.bounded` now takes the centre it measures from as an
  argument. A metric space has no distinguished point (and the empty
  space has none at all), so this is not a generic theorem without one;
  the plane supplies the origin at the call site.

## Where step 4 stands

The prerequisites are all **done and on `main`** (`Metric/interval.math`,
537 lines):

- `Real.unitInterval`, compact (Bolzano–Weierstrass plus the limit staying
  between the same two bounds) and connected.
- Connectedness comes from `Real.IsConvex.connected`, the supremum
  argument written directly on ℝ — the honest route, not the three-line
  push-forward along `Plane.Point.first`, which would have made the
  interval's connectedness depend on the plane.
- `Real.between`, `Real.segment`, and the ordered characterisation
  `x ∈ Real.segment(a, b) ↔ a ≤ x ≤ b`. That last one is the whole
  content of what `Plane/model.math` needed 130 lines of coordinate
  detour for; over ℝ it is three short proofs.
- `MetricSpace.UniformlyContinuousOn` and compact separation, ported
  generically — the last of the step-2 gap.

**The migration proper is in progress on the branch
`metric-interval-parametrisation`, which does NOT build.** Converted
there: `Plane/model.math` (the whole `unitSegment` / `walk` /
`first_coordinate_*` section deleted, 612 → 354), `Plane/curve.math`
(`Plane.IsArc`, `arc`, `arcStart`/`arcFinish`, `IsLoop`,
`IsJordanCurve` all on `γ : ℝ → Plane.Point` over `Real.unitInterval`),
and `Plane/subarc.math` (the reparametrisation is `Real.between(a, b)`,
plain arithmetic; `Plane.walkOnto` is gone, and a plane segment is an arc
directly via `Plane.between(a, b)`). Each of the three verifies on its
own.

Still on plane parameters, and what makes the branch red:

| file | lines | what it needs |
| --- | --- | --- |
| `Plane/concatenate.math` | 954 | `retime` becomes `t ↦ scale·t + shift`; the halves become `Set(ℝ)`; every "a coordinate gap never exceeds the distance" step **disappears** — over ℝ the gap IS the distance |
| `Plane/twoarcs.math` | 838 | 149 `Point.make(1, 0)` sites become `1`; the parameter-order characterisation becomes `Real.segment_atLeast`/`_atMost`/`member_segment_of_bounds` |
| `Plane/polyline.math` | 213 | `Plane.walkOnto(a, b)` becomes `Plane.between(a, b)`; the lemmas it needs (`Plane.IsArc.between`, `Plane.arc_between`, `Plane.between_arcStart`/`_arcFinish`) are already on the branch |

The transformation is uniform and mechanical: `Plane.unitSegment` →
`Real.unitInterval`, `Plane.walk(t)` → `t`, `Plane.Point.first(x)` → `x`,
`Plane.Point.make(1, 0)` → `1`, `Plane.origin` (as a parameter) → `0`,
`Plane.distance` (between parameters) → `MetricSpace.distance`. Nothing
found so far needs a new idea.

Afterwards: retire the `Plane.*` aliases file by file, and add the
`Plane/` files that now qualify to `scripts/clean_manifest.txt` — it
still holds zero of them.

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

## Prototype findings (2026-07-27), and how they resolved

Verified against the real kernel, not assumed:

- **The generic definitions elaborate.** `MetricSpace`, the carrier and
  distance projections, and `MetricSpace.OpenIn` over
  `Set(MetricSpace.carrier(m))` all typecheck, using the `Ring` projection
  idiom (`let ⟨…⟩ := m in …`).
- **`instance` registration did not accept the bundle.** Both
  `instance Real.metricSpace` and `instance Plane.metricSpace` failed with
  *"could not determine the carrier of its bundle type 'MetricSpace'"* —
  the blocking unknown, and it was narrow. `carrierProjectionField`
  matched a hard-coded list of four projector names
  (`Ring`/`CommutativeRing`/`Field`/`VectorSpace`) and four constructor
  names, so no fifth bundle could ever register. **Fixed** by reading the
  rule off the constructor's own telescope: the carrier is the first
  argument whose declared type is a sort (which is what lets
  `VectorSpace(f)`'s leading field parameter be skipped without
  special-casing it), and failing that the first argument that is itself a
  bundle with a carrier projection (how `CommutativeRing` and `Field`
  reach the `Ring` one layer down).
- **No competing metric.** `Plane.supBall` is defined and never used, and
  no topology is built on `supDistance` — it appears only as a
  real-valued function (the square-boundary level set, some estimates). So
  one canonical instance per carrier is enough, and canonical inference is
  not at risk.

## Friction met during the port

- **A `choose` reports the generic spelling, not the stated one.** With
  `Plane.IsCompact` an alias, `choose index, limit such that limit ∈ region
  ∧ Plane.SubsequenceConverges(s, index, limit) from compact;` introduces
  the hypothesis with `MetricSpace.SubsequenceConverges` in it, so a later
  argument-free `by Plane.SubsequenceConverges.increasing` no longer
  matches — the two are definitionally equal but citation matching is
  syntactic. The fix at each site is one bare restatement in the alias's
  spelling, which the prover closes by defeq. Three sites needed it. The
  natural behaviour would be for `choose … such that <prop>` to introduce
  **the proposition the author wrote** (the kernel checks it either way),
  which is what `docs/style.md` says the form is for.
- **`choose x such that … from <lemma>` cannot always read the witness
  type** when the carrier is `MetricSpace.carrier(m)`; it asks for the
  annotation `choose x : MetricSpace.carrier(m) such that …`. Two sites.
- **`let` in a proof block requires its type**: `let far := Natural.maximum(a, b);`
  is a parse error, `let far : ℕ := …` is fine. Inferring it from the
  right-hand side would remove a piece of pure bureaucracy.

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

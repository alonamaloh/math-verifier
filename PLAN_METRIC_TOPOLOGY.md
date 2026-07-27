# Metric spaces, and topology developed once

**Status: steps 1–4 DONE 2026-07-27. `main` is green.**

| Step | State |
| --- | --- |
| 0. `instance` accepts the bundle | **done** — `carrierProjectionField` reads the carrier off the constructor's telescope instead of a four-name table (8a898f6a). Regression test: `library/Test/bundle_carrier_registration_test.math`. |
| 1. `Metric/` : bundle, `IsMetric`, instances | **done** — `Metric/space.math`; instances `Real.metricSpace` (`Metric/real.math`) and `Plane.metricSpace` (`Plane/metric.math`). |
| 2. Topology ported generically | **done** — `Metric/{topology,continuity,sequence,compactness,homeomorphism,connected,separation,uniform}.math`. |
| 3. `Plane.*` as thin aliases | **done** — `Plane/{topology,sequence,compact,compactness,homeomorphism,connected,separation,extremum}.math` keep every name; the tree is green throughout. |
| 4. Parametrisation domains → ℝ | **done** — every parametrisation is `γ : ℝ → Plane.Point` on `Real.unitInterval`; see "What step 4 removed" below. |

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

## What step 4 removed

The prerequisites went in first (`Metric/interval.math`, 537 lines):

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

Then the six parametrisation files, in dependency order:

| file | lines | what happened |
| --- | --- | --- |
| `Plane/model.math` | 612 → 354 | the whole `unitSegment` / `walk` / `first_coordinate_*` / `unitSegment_at_first_coordinate` / `unitSegment_equal_of_first_coordinate` section deleted — all of it existed to move between a parameter and the plane point encoding it. What remains is the circle side. |
| `Plane/curve.math` | 252 → 267 | `IsArc`, `arc`, `arcStart`/`arcFinish`, `IsLoop`, `IsJordanCurve` on `γ : ℝ → Plane.Point`. `arcStart` is `γ(0)`, not `γ(Point.make(0, 0))`. |
| `Plane/subarc.math` | 612 → 646 | the reparametrisation is `Real.between(a, b)`, plain arithmetic; `Plane.walkOnto` is gone, and a plane segment is an arc directly via `Plane.between(a, b)`. |
| `Plane/concatenate.math` | 954 → 735 | the glued map is literally `t ↦ γ₁(2t)` / `t ↦ γ₂(2t - 1)`; `Plane.retime` is gone, and the two doublings are walks (`Real.between(0, 2)`, `Real.between(-1, 1)`), so their continuity is the walk's. Every "a coordinate gap never exceeds the distance" step disappeared — over ℝ the gap IS the distance. |
| `Plane/twoarcs.math` | 838 → 790 | the parameter-order characterisation is `Real.segment_atLeast`/`_atMost`/`member_segment_of_bounds`; the whole "where a parameter sits, in coordinates" section is gone, and so is `distinct_of_first_coordinate` (`a < b → a ≠ b` needs no plane). The line count barely moves because the old file ran well past column 140 and the new one does not. |
| `Plane/polyline.math` | 213 → 176 | a leg is `Plane.between(a, b)` directly, so the four `walkOnto` adapters are gone. |

Net: 3,481 → 2,968 lines across the six, and the encoding — 477
`Point.first` unpackings, 109 `Point.make(1, 0)`s — is gone entirely.

Remaining: retire the `Plane.*` aliases file by file, and add the
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

### From the last leg (concatenate / twoarcs / polyline)

- **`1 / 2` and `(1 : ℝ) / 2` are different terms.** The first elaborates
  to a *rational* literal cast into ℝ, the second to `Real.divide`. A fact
  stated with one spelling does not discharge a goal stated with the
  other, and `ordered_field` reports them as unrelated atoms. Every `1/2`
  in `concatenate.math` is therefore the bare spelling, with the ambient
  type pinned on the *other* operand (`1 / 2 > (0 : ℝ)`). Two spellings of
  the same number is the F-queue's "equal spellings treated differently"
  exactly.
- **`-(1 : ℝ)` and `(-1 : ℝ)` are also different terms**, and only the
  first is one `ring` can read: `(-1 : ℝ)` is a negative *integer* literal
  cast into ℝ, which ring treats as an opaque atom, so
  `2·t - 1 = (-1 : ℝ) + t·(1 - (-1 : ℝ))` fails while the same identity
  spelled `-(1 : ℝ)` closes. The negation-of-a-cast spelling is the one to
  write, which is a shame — `(-1 : ℝ)` is what a reader would.
- **A `witness` at a compound arithmetic parameter is expensive.**
  `value ∈ Plane.arc(γ) by { witness 2·source }` costs nothing;
  `witness 2·source - 1`, with both halves of the membership already
  stated in context, costs ~300k kernel-steps through the
  `conjunctionIntro` search — the subtraction alone is the difference.
  Naming the step (`Plane.member_arc`, added to `Plane/curve.math`) fixes
  it and reads better besides, but the underlying cost is worth a look:
  nothing about `2·s - 1` should make an already-stated conjunction hard.
- **`Real.segment_atLeast`/`_atMost` need their far endpoint named.** The
  goal `a ≤ x` does not mention `b`, and having `x ∈ Real.segment(a, b)`
  in context is not enough for the citation to pin it — the premise is
  only matched once the arguments are known, not the other way round. So
  every site reads `by Real.segment_atMost(a := 0)`. This is the deferred-
  premise-argument friction (QUIRK Q13) at a new lemma family; it is also
  arguably the right thing to write, since the conclusion genuinely does
  not mention which segment.

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

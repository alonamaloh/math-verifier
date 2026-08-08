# The plane

The Euclidean plane, built for the Jordan–Schönflies development
(`PLAN_JORDAN_SCHOENFLIES.md`). Two types, deliberately kept apart:

- **`Plane.Vector`** — a displacement. Carries the linear structure.
- **`Plane.Point`** — a location. Acted on by vectors, so `p + v` is a
  point and `q - p` is a vector.

Keeping them distinct is what makes `p + q` unwritable. The blueprint
already speaks this way — inversion is `a + (x - a)/‖x - a‖²` — and the
types should agree with it.

## Building

```sh
make -j 16 plane      # this area and exactly its transitive imports
```

The target covers this area's 206-module import cone — including 19 of the
106 Algebra files, the bundled-structure basics that `Real`'s field and ring
instances need — and nothing else, so it stays a narrow inner loop while
`make -j 16 library` is what you run before committing.

Seconds warm; a re-verification of the whole cone after a kernel or
elaborator change, which invalidates every module's proofs. The target asks
for the cone's proofs, not just its interfaces, so that second case really is
re-verified rather than silently skipped (`scripts/module_cone.py`).

`Plane/Graph/` is part of this cone; `library/Graph/`, which has no geometry
in it, has its own narrower `make -j 16 graph`.

## The plane is a metric space, and its topology is the generic one

`Plane.metricSpace` ([metric.math](metric.math)) registers `Plane.Point` with
its Euclidean distance as the canonical `MetricSpace`. Everything topological
here is then a **name** for the generic notion of
[`Metric/`](../Metric/README.md), not a second copy of it:
`Plane.OpenIn`, `Plane.IsCompact`, `Plane.Closure`, `Plane.IsConnected`,
`Plane.ContinuousOn`, `Plane.compact_separation` and their relatives all
unfold to the `MetricSpace.…` definition and are proved `done by` the generic
theorem. The names are kept because the Jordan–Schönflies development speaks
them; the mathematics lives in `Metric/`, where it is written once and also
serves the real line.

So: a general topological fact belongs in `Metric/`, and only the plane's own
geometry — coordinates, the norm, convexity, orientation — belongs here. What
this area adds on top of the generic topology is Bolzano–Weierstrass in two
coordinates, convexity, and the curve theory.

That inherited topology is **relative to a region** throughout — `OpenIn`
speaks about the trace `subset ∩ region` and does not require
`subset ⊆ region`; see `Metric/README.md` for the contract and the cut
characterisation `Plane.OpenIn.cut_by_open`. The reason it had to be relative
from the start is the plane's, though: an open subarc of a Jordan curve has
empty interior in the plane — the only plane-open subset of a curve is empty —
so "the relatively open subarcs form a basis" cannot even be *stated*
absolutely. Connectedness gets applied to arcs and curves as subspaces for the
same reason, and retrofitting relativisation after Layers 1–3 were built would
have cost more than paying for it once.

## Main definitions

- `Plane.Vector`, its coordinates `first` / `second`, `make`, `zero`, and
  the operators `+`, `-` (binary and unary), `*` for scaling by a real —
  [vector.math](vector.math)
- `Plane.Point`, `Plane.Point.position`, and the operators `+`
  (`Point + Vector → Point`) and `-` (`Point - Point → Vector`) —
  [point.math](point.math)
- `Plane.Vector.innerProduct`, `Plane.Vector.determinant`, and
  `Plane.Vector.perpendicular` — [bilinear.math](bilinear.math)
- `Plane.Vector.IsNonzero`, `Parallel`, `SameRay`, `OppositeRay`, and
  `Plane.Vector.Counterclockwise` — [direction.math](direction.math)
- `Plane.Vector.norm`, `Plane.Vector.supNorm`, `Plane.distance`, and
  `Plane.supDistance` — [norm.math](norm.math)
- `Plane.between`, `Plane.segment`, `Plane.openSegment`, `Plane.IsConvex`,
  `Plane.Ball`, and `Plane.supBall` — [segment.math](segment.math)
- `Plane.Point.Precedes` — the points ordered lexicographically, used only to
  pick one of two canonically — [point_order.math](point_order.math)
- `Plane.is_metric`, `Plane.metricSpace` — [metric.math](metric.math)
- `Plane.OpenIn`, `Plane.IsOpen`, `Plane.ClosedIn`, `Plane.InteriorIn`,
  `Plane.ClosureIn`, `Plane.BoundaryIn`, `Plane.ContinuousAt`,
  `Plane.ContinuousOn` — [topology.math](topology.math). **Relative to a
  region from the start**; the absolute notions are the
  `region = universe` case.
- `Plane.SequenceConverges`, `Plane.IsBounded` —
  [sequence.math](sequence.math); `Plane.SubsequenceConverges` —
  [compact.math](compact.math)
- `Plane.IsCompact` (**sequential**), `Plane.Closure` —
  [compactness.math](compactness.math)
- `Plane.RealContinuousAt`, `Plane.RealContinuousOn`, `Plane.image`,
  `Plane.UniformlyContinuousOn` — [extremum.math](extremum.math), the
  real-valued functions an extremum argument runs on
- `Plane.IsConnected` (**the clopen criterion, as the definition**),
  `Plane.preimageIn`, `Plane.reachedParameters`, `Plane.parameterGap` —
  [connected.math](connected.math)
- `Plane.Component`, `Plane.IsRegion` — [component.math](component.math)
- `Plane.PolygonalReach`, `Plane.reachableFrom` —
  [polygonal.math](polygonal.math)
- `Plane.origin`, `Plane.squareBoundary`, `Plane.circle` —
  [model.math](model.math)
- `Plane.InjectiveOn`, `Plane.HasContinuousInverseOn`,
  `Plane.IsHomeomorphismOn` — [homeomorphism.math](homeomorphism.math)
- `Plane.IsArc`, `Plane.arc`, `Plane.arcStart`, `Plane.arcFinish`,
  `Plane.IsLoop`, `Plane.IsJordanCurve`, `Plane.IsJordanParametrisation` —
  [curve.math](curve.math)
- `Plane.subarc`, `Real.openUnitInterval`, `Plane.openArc` —
  [subarc.math](subarc.math)
- `Plane.IsArcBetween` — an arc *between two named points*, the set-level
  reading of an arc and the form most of the development speaks —
  [curve.math](curve.math)
- `Plane.lowerHalf`, `Plane.upperHalf`, `Plane.concatenate` —
  [concatenate.math](concatenate.math)
- `Plane.IsAffineCoordinate`, `Plane.HalfPlane`, `Plane.square`,
  `Plane.farRight` / `.farAbove` / `.farLeft` / `.farBelow`,
  `Plane.beyondSquare` — [exterior.math](exterior.math)
- `Plane.polyline`, `Plane.chainFrom`, and `Plane.IsPolygonal` —
  [polyline.math](polyline.math). A polygonal arc is built **from its vertex
  list** rather than existentially recovered from a union of segments:
  `Plane.polyline(start, vertices)` is the parametrisation,
  `Plane.chainFrom(start, vertices)` the set of points it covers, and
  `Plane.IsPolygonal` the blueprint's set-level predicate. The
  parametrisation is deliberately not constant speed — each remaining tail
  gets half of what is left of the interval — because only the image and the
  order along it are ever used

## Main theorems

- `Plane.Vector.equal_of_coordinates` and `Plane.Point.equal_of_position`
  — the bridges from coordinates to equations. **Every law goes through
  one of them**; reach for these rather than unfolding the construction.
- The coordinate-reduction lemmas `first_add`, `first_negate`,
  `first_scale`, `first_subtract`, `first_zero`, `first_perpendicular`
  and their `second_` counterparts
- Vector-space laws: `add_commutative`, `add_associative`, `add_zero`,
  `add_negate`, `subtract_add`, `subtract_self`, `add_subtract_left`,
  `add_subtract_cancel`, `scale_add`, `scale_scale`, `scale_one`
- Affine laws: `translate_zero`, `translate_translate`,
  `translate_difference` (the action is transitive),
  `difference_translate` and `translate_injective` (it is free),
  `difference_self`
- Bilinear forms: `innerProduct_symmetric`, `innerProduct_add_left`,
  `innerProduct_scale_left`, `innerProduct_self_nonneg`,
  `innerProduct_add_self`; `determinant_antisymmetric`, `determinant_self`,
  `determinant_add_left`, `determinant_scale_left`
- **`lagrange_identity`** — `⟨u,v⟩² + det(u,v)² = ⟨u,u⟩⟨v,v⟩`, a ring
  identity in coordinates — and `cauchy_schwarz` as its corollary
- **`Plane.distance_make`** — the distance between two points named by
  coordinates. A square root is not a computation, so the caller names the
  value and the lemma checks its square; cite it argument-free and the
  goal supplies the coordinates (`Plane.pole_in_circle` is two lines this
  way). Its sup-metric siblings are `supNorm_triangle`, `supNorm_negate`,
  `supDistance_symmetric`, `supDistance_triangle` and
  `supDistance_shift_bound`
- Metric: `norm_nonneg`, `norm_squared`, `supNorm_LessOrEqual_norm`,
  `norm_LessOrEqual_rootTwo_supNorm` (together, `‖v‖∞ ≤ ‖v‖ ≤ √2·‖v‖∞`),
  `norm_triangle`, `distance_triangle`
- The right-angle turn: `innerProduct_perpendicular` (it is a right
  angle), `perpendicular_perpendicular` (twice reverses), and
  **`determinant_perpendicular`** — `det(v, v⊥) = ⟨v, v⟩`, the identity
  the strip lemma runs on
- Convexity: `between_zero`, `between_one`, `between_difference`,
  `left_in_segment`, `right_in_segment`, `Plane.IsConvex.intersection`,
  `Plane.between_degenerate` / `Plane.segment_degenerate` (a segment with
  equal endpoints is the one point),
  **`Plane.Vector.norm_affine_combination`** (a weighted average is no
  longer than the longer summand — the estimate every convexity argument
  runs on), and **`Plane.Ball_IsConvex`**

### Compactness, connectedness, curves

- **`Plane.bolzano_weierstrass`** in the plane (the line's theorem twice),
  **`Plane.compact_of_closed_bounded`** and `Plane.IsCompact.bounded`
  (Heine–Borel as an equivalence), `Plane.IsCompact.image`,
  `Plane.attains_maximum` / `attains_minimum`,
  `Plane.uniformly_continuous_on_compact`, and `Plane.compact_separation`
  ([separation.math](separation.math)) — disjoint compacta are a positive
  distance apart, with `Plane.compact_separation_from_point` for the case
  where one side is a single point (a compact set is closed, so its
  complement is open). `Plane.segment_IsCompact`, and `Plane.circle_IsCompact` /
  `Plane.squareBoundary_IsCompact` for the model curves, which are compact
  because they are bounded level sets
- `Plane.IsConnected.image`, `.union` (through a common point), `.swallows`,
  `.lands_in_side`, `.adjoin_limits`; **`Plane.IsConvex.connected`** (the
  layer's one analytic proof — a walk with a supremum), hence
  `Plane.Ball_IsConnected` and `Plane.segment_IsConnected`
- `Plane.Component_IsConnected`, `Plane.Component_IsOpen`,
  `Plane.Component.equal_of_meeting` (components partition),
  **`Plane.Component.recognize`**, `Plane.Component_boundary_in_closed`
- `Plane.Component_IsRegion` and `Plane.Ball_IsRegion` — the two sources of a
  `Plane.IsRegion`, which is what a consumer of connectedness holds
- **`Plane.polygonal_connected`** — any two points of an open connected set
  are joined by a chain of segments inside it (`Plane.IsRegion.polygonal_connected`
  is the same statement for a region) — and
  `Plane.Component_is_reachable_set`, which identifies the components of an
  open set with the walk classes
- **`Plane.IsHomeomorphismOn.of_continuous_injective_on_compact`** (H4's
  engine) and `Plane.IsJordanParametrisation.IsHomeomorphismOn` — a
  continuous injection on the circle is a homeomorphism onto its image
- `Plane.ContinuousOn.compose`, `Plane.between_injective`, and
  **`Plane.IsArc.subarc`** — a subarc between distinct parameters is an arc,
  with `Plane.subarc_image` identifying its image as the arc restricted to
  the subsegment, and
  `Plane.IsArc.openArc_is_arc_without_endpoints` for `P°`
- **`Plane.IsArc.concatenate`** — two arcs meeting only at the endpoint they
  share glue to an arc. Continuity is `Plane.ContinuousOn.paste` over the two
  closed halves (with `Plane.ContinuousOn.of_agreeing`, since the glued map only
  *agrees* with a composition on each); injectivity splits four ways, and
  the seam case is where the meet-only-there hypothesis is used
- **`Plane.segment_meet`** — two segments meet in nothing, or in a segment
  ([segment_meet.math](segment_meet.math)). The blueprint's "empty set, one
  point, or one closed interval", folded to a dichotomy because a point *is*
  a degenerate segment. No parallel/non-parallel split and no determinant:
  the meet is compact (`MetricSpace.IsCompact.intersection`) and convex, so
  the distance from the left endpoint attains a minimum and a maximum there,
  and `Plane.parameter_LessOrEqual_of_distance` — along a nondegenerate
  segment that distance **orders the parameters** — makes those two extreme
  points the endpoints. Supporting:
  `Plane.RealContinuousOn.distance_from` (the distance from a fixed point is
  continuous, every tolerance its own nearness — `Plane.attains_maximum`'s
  first customer) and `Plane.distance_from_left`
- **`Plane.IsArc.image_OpenIn`** — a parametrisation is an open map onto its
  arc (this is what the inverse's continuity is *for*), and
  `Plane.IsArc.basic_piece_inside_ball` puts one such image inside every
  neighbourhood: together, the images of relatively open subsegments are a
  basis of the arc's topology

### Cutting a segment, and cutting a curve

- The open segment is the vocabulary a plane graph's edges are stated in:
  `Plane.openSegment_symmetric`, `Plane.openSegment_nearer` (a point strictly
  inside is strictly nearer the left end), and hence
  **`Plane.openSegment_left_inside`** / **`Plane.openSegment_right_inside`** —
  cutting at an interior point leaves both halves' interiors inside the
  original, so a cut is permanent
- **`Plane.segment_split`** — the converse half: the two pieces cover the
  whole segment, so cutting loses nothing. With `Plane.between_nested`,
  `Plane.between_nested_from_start` and `Plane.between_nested_to_finish` as
  the parameter arithmetic underneath
- **`Plane.IsJordanCurve.two_arcs`** — two distinct points of a Jordan curve
  cut it into two arcs between them, which cover the curve and meet in
  exactly those two points ([twoarcs.math](twoarcs.math)). Carried entirely by
  the loop's parameters: `Plane.IsLoop.parameter_before_finish` pulls the two
  points back to parameters short of the finish,
  `Plane.IsLoop.two_arcs_at_parameters` is the statement there, and the pieces
  are the middle interval and the two end pieces glued where the loop closes
  up (`Plane.IsLoop.middle_IsArcBetween`, `.outside_IsArcBetween`). The
  meeting is `Plane.IsLoop.pieces_meet_at_ends`, and the injectivity it needs
  splits into `Plane.IsLoop.injective_on_front` / `_middle` / `_back`
- **`Plane.arc_polyline`** — what a polyline covers is the chain of its
  vertices, hence `Plane.IsPolygonal.of_polyline`; `Plane.polyline_arcStart`
  names where it begins. Both are proved with the start **generalised**, since
  the recursion moves it
- **`Plane.IsArcBetween.concatenate`** and **`Plane.IsJordanCurve.of_two_arcs`**
  — the set-level gluing theorems, and the form every construction of a curve
  uses: two pieces meeting only where they are joined make one piece, and two
  meeting at both of their ends make a Jordan curve (the converse of
  `Plane.IsJordanCurve.two_arcs`). Their engine is `Plane.IsLoop.concatenate`,
  whose seam analysis has two legitimate meeting points instead of one — the
  middle, and the parameter where the loop is allowed to repeat itself.
  `Plane.IsArcBetween.reverse` runs a piece the other way round, as
  `Plane.subarc(_, 1, 0)`
- **`Plane.beyondSquare_IsConnected`** — the plane outside a square is all one
  piece ([exterior.math](exterior.math)). A SQUARE, not a disk: its outside is
  exactly a union of four half-planes, each convex and hence connected, with
  consecutive ones sharing a corner. The exterior of a *disk* is not a union
  of half-planes, and cutting it into pieces that are would need the polar
  decomposition this development withholds. `Plane.HalfPlane` is stated for an
  arbitrary affine coordinate, so one convexity proof serves all four sides.
  Alongside it, `Plane.square` as the shape a bounded set is caught inside
  (`Plane.IsBounded.inside_square`, `Plane.unionOver_inside_square`), with
  radii kept nonnegative so two squares merge by **adding** them — no maximum,
  and no case split on which is larger. `Plane.squareAbout(center, radius)` is
  the same shape about an arbitrary centre, monotone in the radius
  (`Plane.squareAbout_monotone`), reaching no further than `2 * radius`
  (`Plane.squareAbout_distance_bound`, which is why every radius chosen against
  a gap is a quarter of it), and read in both directions as the closed ball of
  the sup metric (`Plane.supDistance_of_squareAbout`,
  `Plane.squareAbout_of_supDistance`) — the bridge every comparison of two
  squares crosses to reach `Plane.supDistance_triangle`

### Along one segment: the distance from an end as a coordinate

[segment_order.math](segment_order.math) makes collinear arguments
one-dimensional. Along a nondegenerate `Plane.segment(a, b)`, the distance
from `a` **determines** the point (`Plane.equal_of_distance_from_left`) and
reads betweenness off as a pair of inequalities
(`Plane.distance_between_of_member_segment` and its converse
`Plane.member_segment_of_distance_between`, plus the strict pair for
interiors), so a claim about four collinear points becomes a claim about four
reals. No new geometry: this is `Plane.distance_from_left` and
`Plane.between_nested` turned into a translation.

The two results it exists for, both stated inside one ambient segment —
collinearity is not optional, since a piece crossing an overlap transversally
would satisfy the hypotheses without the conclusion:

- **`Plane.segment_inside_of_ends_outside`** — a piece that meets an overlap
  and keeps the overlap's ends out of its interior lies inside the overlap;
- **`Plane.same_ends_of_meeting_interiors`** — two pieces whose interiors meet,
  each keeping the other's ends out of its interior, are the same pair of
  points (in one order or the other).

Both are stated with no orientation asked of the caller; the `_oriented` forms
they wrap are near-end-first, which is what the arithmetic wants. The whole
one-dimensional argument is carried by
`Plane.distance_LessOrEqual_left_of_not_interior` and its mirror: a point of
the ambient segment kept out of `[s, t]` and lying before `t` lies at or
before `s`.

## Connectedness is the clopen criterion

`Plane.IsConnected(region)` — the generic `MetricSpace.IsConnected` — says: a
subset of the region that is relatively open, whose complement in the region
is relatively open, and which is nonempty, **is the region**. Not the absence
of a separation.

Every consumer of connectedness in the blueprint is discharging exactly
those three obligations and concluding the fourth, so taking the criterion
as the definition spares each of them a reductio — and the blueprint's own
"Recognizing a component" is then `Plane.Component.recognize`, two lines.

## Arcs and curves are parametrised by the real unit interval

An arc is a continuous injective map on `Real.unitInterval`; a Jordan curve
is a **set** carried onto by a **loop** on the same interval — continuous,
returning to its start, injective until it does — which is the blueprint's
definition. The parameter domain is a subset of **ℝ**, and the topology it
carries is the generic one of `Metric/`, so everything above applies unchanged:
a parametrisation is an ordinary `ℝ → Plane.Point` map, its continuity is
`ContinuousOn`, its image is `Set.image`, its compactness is `IsCompact`.
Making the interval a type of its own would need a second relative topology for
maps out of it, and taking the circle as the domain would need a quotient.

Two consequences worth knowing before extending this area:

- **A Jordan curve is defined by a loop, not by the circle**, because the
  parameters are what its theorems use: two points of the curve pull back
  to two parameters, and the two arcs they determine are a subarc and a
  concatenation. Against the circle those same arcs need a *traversal* of
  the circle by an interval, which is the one thing the
  trigonometry-free setting does not hand over.
- `Plane.circle` (`‖x‖ = 1`) and `Plane.squareBoundary` (`‖x‖∞ = 1`) both
  remain as model curves — level sets, so compact in three lines — and the
  circle-side theorem (a continuous injection on it is a homeomorphism onto
  its image) is proved. **Not built**: the bridge from a loop to such a
  parametrisation, which needs `∂Q`'s decomposition into four sides plus
  the radial projection (`x ↦ x/‖x‖`, `x ↦ x/‖x‖∞`).
- A curve's parameter **is** a real number: the domain is
  `Real.unitInterval`, so a reparametrisation composes on ℝ with nothing to
  extract and no inverse to construct.

The inverse of a homeomorphism is never named:
`Plane.HasContinuousInverseOn(f, region)` says points whose images are
close are themselves close. That is the form consumers use, and it avoids
choosing a preimage for every point of the image.

## The Euclidean norm is primary

`Real.square_root` takes the nonnegativity of its argument as an
argument. That obligation is discharged **once**, in the definition of
`Plane.Vector.norm`, out of `innerProduct_self_nonneg`. Downstream
`norm(v)` takes only `v` and no proof term ever appears at a call site —
a mathematician does not think twice before writing ‖v‖, and neither
should a proof here.

Estimates go through `norm_squared` (`‖v‖·‖v‖ = ⟨v,v⟩`) rather than
through the root itself, and `Real.LessOrEqual_of_square_LessOrEqual`
turns a comparison of squares back into a comparison of values. The sup
norm sits alongside for the axis-parallel squares the polygonal work is
built on.

## Orientation instead of angles

`Plane.Vector.determinant(u, v) = u₁v₂ - u₂v₁`, and its **sign** is the
orientation of the pair — Sedgewick's `ccw`. The Jordan–Schönflies
development uses it wherever a textbook would use an angle, which is why
nothing here needs trigonometry: the library has sine and cosine only as
power series, with no π and no periodicity. `innerProduct(v, v)` serves
as the squared length; no square root is taken.

## How proofs here go

Every law is proved the same way, and new ones should follow it:

```math
Plane.Vector.first(u + v)
    = Plane.Vector.first(u) + Plane.Vector.first(v)
    = Plane.Vector.first(v) + Plane.Vector.first(u)
    = Plane.Vector.first(v + u);
-- the same chain for `second`;
done by Plane.Vector.equal_of_coordinates
```

Expand into coordinates, do the real arithmetic, reassemble. The
expansion and reassembly steps are definitional, so they need no `by`;
the auto-prover also closes the real-arithmetic steps at this size, so
`by ring` is not written either. Only the closing
`equal_of_coordinates` is spelled out, because how the two coordinate
equations yield the vector equation is the one step a reader should not
have to guess.

**Do not** state a coordinate goal in unreduced form and hope `ring`
will close it: `ring` treats `Plane.Vector.first(u + v)` as an opaque
atom. Expand first — that is what the chain above is for.

## Which `by` to keep

The redundancy checker flags every citation the auto-prover could have
found itself. The line taken here: **keep the citation when it names a
theorem, drop it when it names a computation.**

So the coordinate expansions and the real arithmetic in `vector.math` are
bare — a mathematician writing "the first coordinate of `u + v` is
`u₁ + v₁`" cites nothing. But `point.math` keeps nearly all of its
citations, because each one names the vector law being transported to
points: translations compose *because* vector addition is associative,
and saying so is the content of the lemma. Every `done by
equal_of_coordinates` / `equal_of_position` stays too — how two
coordinate equations become one vector equation is the step a reader
should not have to reconstruct.

## Friction worth removing

The two coordinate chains in every law are identical up to
`first`/`second`. A `componentwise` tactic — prove the goal for both
coordinates and close by `equal_of_coordinates` — would collapse each
proof to its one interesting line. Roughly two thirds of `vector.math` is
that duplication, and the norm and determinant laws are no better.

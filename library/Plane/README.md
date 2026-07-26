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

Not `make library`: that verifies the Algebra/ fifteen-theorem material,
which dominates the wall clock. The `plane` target covers the 156-module
import cone — including 19 of the 546 Algebra files, the bundled-structure
basics that `Real`'s field and ring instances need — and nothing else.

About two seconds warm; about eighteen after a kernel or elaborator
change, which invalidates every module's proofs. The target asks for the
cone's proofs, not just its interfaces, so that second case is actually
re-verified rather than silently skipped (`scripts/module_cone.py`).

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
- `Plane.between`, `Plane.segment`, `Plane.IsConvex`, `Plane.Ball`, and
  `Plane.supBall` — [segment.math](segment.math)
- `Plane.OpenIn`, `Plane.IsOpen`, `Plane.ClosedIn`, `Plane.InteriorIn`,
  `Plane.ClosureIn`, `Plane.BoundaryIn`, `Plane.ContinuousAt`,
  `Plane.ContinuousOn` — [topology.math](topology.math). **Relative to a
  carrier from the start**; the absolute notions are the
  `carrier = universe` case.
- `Plane.SequenceConverges`, `Plane.IsBounded` —
  [sequence.math](sequence.math); `Plane.SubsequenceConverges` —
  [compact.math](compact.math)
- `Plane.IsCompact` (**sequential**), `Plane.Closure`, `Plane.imageSet` —
  [compactness.math](compactness.math)
- `Plane.RealContinuousOn`, `Plane.image`, `Plane.UniformlyContinuousOn` —
  [extremum.math](extremum.math)
- `Plane.IsConnected` (**the clopen criterion, as the definition**),
  `Plane.preimageIn`, `Plane.reachedParameters`, `Plane.parameterGap` —
  [connected.math](connected.math)
- `Plane.Component`, `Plane.IsRegion` — [component.math](component.math)
- `Plane.PolygonalReach`, `Plane.reachableFrom` —
  [polygonal.math](polygonal.math)
- `Plane.origin`, `Plane.unitSegment`, `Plane.squareBoundary`,
  `Plane.circle` — [model.math](model.math)
- `Plane.InjectiveOn`, `Plane.HasContinuousInverseOn`,
  `Plane.IsHomeomorphismOn` — [homeomorphism.math](homeomorphism.math)
- `Plane.IsArc`, `Plane.arc`, `Plane.arcStart`, `Plane.arcFinish`,
  `Plane.IsJordanParametrisation`, `Plane.IsJordanCurve` —
  [curve.math](curve.math)
- `Plane.walkOnto`, `Plane.subarc`, `Plane.openUnitSegment`,
  `Plane.openArc` — [subarc.math](subarc.math)

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
  `left_in_segment`, `right_in_segment`,
  **`Plane.Vector.norm_affine_combination`** (a weighted average is no
  longer than the longer summand — the estimate every convexity argument
  runs on), and **`Plane.Ball_IsConvex`**

### Compactness, connectedness, curves

- **`Plane.bolzano_weierstrass`** in the plane (the line's theorem twice),
  **`Plane.compact_of_closed_bounded`** and `Plane.IsCompact.bounded`
  (Heine–Borel as an equivalence), `Plane.IsCompact.image`,
  `Plane.attains_maximum` / `attains_minimum`,
  `Plane.uniformly_continuous_on_compact`, `Plane.compact_separation`
- `Plane.IsConnected.image`, `.union` (through a common point), `.swallows`,
  `.lands_in_side`, `.adjoin_limits`; **`Plane.IsConvex.connected`** (the
  layer's one analytic proof — a walk with a supremum), hence
  `Plane.Ball_IsConnected` and `Plane.segment_IsConnected`
- `Plane.Component_IsConnected`, `Plane.Component_IsOpen`,
  `Plane.Component.equal_of_meeting` (components partition),
  **`Plane.Component.recognize`**, `Plane.Component_boundary_in_closed`
- **`Plane.polygonal_connected`** — any two points of an open connected set
  are joined by a chain of segments inside it — and
  `Plane.Component_is_reachable_set`, which identifies the components of an
  open set with the walk classes
- `Plane.segment_IsCompact`, `Plane.squareBoundary_IsCompact`
- **`Plane.IsHomeomorphismOn.of_continuous_injective_on_compact`** and
  **`Plane.IsJordanCurve.homeomorphic_to_circle`** (H4)
- `Plane.ContinuousOn.compose`, `Plane.between_injective`, and
  **`Plane.IsArc.subarc`** — a subarc between distinct parameters is an arc,
  with `Plane.subarc_image` identifying its image as the arc restricted to
  the subsegment, and
  `Plane.IsArc.openArc_is_arc_without_endpoints` for `P°`

## Connectedness is the clopen criterion

`Plane.IsConnected(region)` says: a subset of the region that is relatively
open, whose complement in the region is relatively open, and which is
nonempty, **is the region**. Not the absence of a separation.

Every consumer of connectedness in the blueprint is discharging exactly
those three obligations and concluding the fourth, so taking the criterion
as the definition spares each of them a reductio — and the blueprint's own
"Recognizing a component" is then `Plane.Component.recognize`, two lines.

## Arcs and curves are parametrised by plane sets

An arc is a continuous injective map on `Plane.unitSegment`; a Jordan curve
is a **set** carried onto by a continuous injection from `Plane.circle`.
**Both model domains are subsets of the plane, not of ℝ.** That is what
lets everything above apply unchanged: a
parametrisation is an ordinary `Plane.Point → Plane.Point` map, its
continuity is `ContinuousOn`, its image is `imageSet`, its compactness is
`IsCompact`. Parametrising by `[0,1] ⊆ ℝ` would need a second relative
topology for real-domain maps, and a circle would need a quotient.

Two consequences worth knowing before extending this area:

- There are **two model curves, on purpose**. `Plane.circle` (`‖x‖ = 1`) is
  what a Jordan curve is defined against, because that is the textbook
  definition and a circle needs no trigonometry to *define* — only to
  traverse. `Plane.squareBoundary` (`‖x‖∞ = 1`) is the working model
  wherever a traversal is wanted, because its traversal is piecewise
  affine. Both are level sets, so both are compact in three lines. The
  radial-projection bridge between them (`x ↦ x/‖x‖`, `x ↦ x/‖x‖∞`) and
  `∂Q`'s decomposition into four sides are **not** built yet; everything
  needing the arc structure of a model curve waits on them.
- The parameter of a point of the unit segment is its **first coordinate**
  (`Plane.unitSegment_at_first_coordinate`). The model interval runs along
  the axis for exactly this reason: a reparametrisation reads its parameter
  off the point, with no inverse to construct.

The inverse of a homeomorphism is never named:
`Plane.HasContinuousInverseOn(f, carrier)` says points whose images are
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

## Relative topology

`Plane.OpenIn(subset, carrier)` is the ε-ball condition with the ball cut
down to the carrier: only `y ∈ carrier` within the radius is constrained.
Drop that clause and you have ordinary openness, which is why
`Plane.IsOpen(U)` is literally `OpenIn(U, Set.universe)` rather than a
second definition.

This is not decoration. An open subarc of a Jordan curve has empty
interior in the plane — the only plane-open subset of a curve is empty —
so "the relatively open subarcs form a basis" cannot even be *stated*
absolutely. Connectedness will be applied to arcs as subspaces for the
same reason.

`OpenIn` deliberately does **not** require `subset ⊆ carrier`: the ε-ball
condition is meaningful without it and demanding it would put a proof
obligation at every use. `Plane.OpenIn_cut_by_open` supplies the textbook
characterization (`subset = openHull ∩ carrier`) where the inclusion is
genuinely needed, and `Plane.OpenIn_of_cut` is the converse — the
direction consumers use to *build* relatively open sets.

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
proof to its one interesting line. Roughly two thirds of this file is
that duplication, and the ratio will be worse in the norm and
determinant laws to come.

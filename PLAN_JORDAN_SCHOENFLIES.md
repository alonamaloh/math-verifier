# PLAN — Jordan–Schönflies

Target: **every homeomorphism between two Jordan curves extends to a
homeomorphism of the plane.** The blueprint is
`~/claude/schoenflies/jordan_schoenflies.tex` (51 pp, 84 labelled
statements, Appendix A is a statement-level dependency index, Appendix D
maps it to the compact companion).

This file is the layer plan for the *foundation the library does not yet
have*, plus the milestones to steer by. It is not a proof outline — the
blueprint is that.

## Why this target

Two reasons beyond the theorem itself.

1. **It is the furthest thing from what the library does.** 433k lines of
   algebra and number theory; zero geometry, zero topology, zero graphs.
   The auto-prover, lemma search and calc machinery have never been
   pointed at ε-δ plane geometry with configuration case analysis. That
   is the real test.
2. **The foundation is reusable.** Layers 0–3 are the point-set topology
   of the plane. They unlock a large amount of further analysis and
   several more Freek entries. Nothing here is sunk into one theorem.

## What is missing (measured, 2026-07-25)

| Needed by the blueprint | In library |
|---|---|
| ℝ², Euclidean + sup metric, segments, convexity, affine maps | — |
| open / closed / interior / closure / boundary | — (0 files mention `Open`, `Interior`, `Neighborhood`) |
| compactness, Bolzano–Weierstrass, min attainment, uniform continuity | — (0 files mention `Compact`) |
| connectedness, components, local connectedness | — (0 files mention `Connected`) |
| compact→Hausdorff homeomorphism, pasting lemma | — |
| finite graphs: walks, paths, cycles, 2-connectivity, trees | — |
| ℝ, supremum, sequences, `ContinuousAt`, IVT, `square_root` | ✅ `Real/` |
| `Set(T) = T → Proposition`, `Subtype`, `HasSize`, `NaturalsBelow` | ✅ `Set/`, `Logic/` |
| `Product(A, B)`, `Quotient`, lists with permutations/ranges/filter | ✅ `Logic/`, `Lists/` |

Estimated foundation: **~40k lines**. Blueprint content on top: **~48k**.
Both figures are soft; see *Unknowns*.

---

## Layer 0 — `Plane/` : points, metrics, segments

Everything geometric rests here, so the representation choices below are
the ones worth arguing about before any of it is written.

**Two types, affine over linear.** `Plane.Vector` carries the linear
structure; `Plane.Point` is an affine space over it. The blueprint
already writes this way — the inversion is `a + (x − a)/‖x − a‖²` and
the strong-accessibility estimate is `‖p + t·w − q‖²`, both
point-plus-vector. Adding two points is meaningless and the types should
say so.

Build both **concretely** over `Product(ℝ, ℝ)` and **seal** them
(`interface module Plane.interface implemented by Plane.coordinates`, as
`Real/interface.math` does). Sealing is what makes the discipline real:
defined transparently, `Point` and `Vector` would be defeq and the
type system would happily accept `p + q`. The sealed interface exposes
the coordinate accessors, so the coordinate-heavy parts of Part I —
parity counting, axis-parallel grids, "rotate so no edge is horizontal" —
still compute. Do **not** build an abstract torsor over a bundled vector
space: the abstraction is taxed at every call site and buys nothing the
sealed concrete version doesn't give.

**Definitions.** *Vector:* `+`, `−`, scalar `·`, `Plane.innerProduct`,
`Plane.determinant` (`u₁v₂ − u₂v₁`), `Plane.norm`, `Plane.supNorm`.
*Point:* `Point + Vector → Point`, `Point − Point → Vector`,
`Plane.distance`, `Plane.supDistance`, `Plane.segment(a, b)`,
`Plane.openSegment`, `Plane.IsConvex`, `Plane.Ball`, `Plane.supBall`
(the axis-parallel open square), `Plane.AffineMap`, `Plane.Direction`
(unit vectors).

**Main results.** Torsor laws (`p + 0 = p`, `(p + v) + w = p + (v + w)`,
`p + (q − p) = q`, and uniqueness of the difference); triangle inequality
in both metrics; the comparison `‖x‖_∞ ≤ ‖x‖ ≤ √2·‖x‖_∞`; Cauchy–Schwarz
for `innerProduct`; convexity of balls, squares, triangles; a segment is
the convex hull of its endpoints; an affine map is determined by its
values at three affinely independent points; an affine map fixing two
points of a line fixes the line pointwise.

### No trigonometry — two substitutions

`ComplexNumber/` has sine and cosine as power series, with the
Pythagorean identity, addition formulas and bounds. It has **no π, no
periodicity, and no surjectivity onto the unit circle.** So
`t ↦ (cos 2πt, sin 2πt)` is unavailable, and building it is a project in
its own right. Two substitutions avoid needing it at all, and **both
require editing the blueprint**, whose Appendix C imports "polar
coordinates about a point, and the decomposition of a circle by finitely
many directions into arcs".

1. **Working model curve = the boundary of the unit square. The
   *definition* keeps the circle.** *(Revised 2026-07-26, on building
   Layer 4.)* The original form of this substitution — restate
   `lem:jordan-circle` against `∂Q` — went further than the missing
   trigonometry forces. The unit circle is `{x : ‖x‖ = 1}`, a level set of
   the Euclidean norm, and needs no trigonometry to **define**: it is
   `Plane.circle`, and its compactness is the same three lines as `∂Q`'s.
   Trigonometry is only wanted to **traverse** a circle at constant speed.

   So: `Plane.IsJordanCurve(C)` is the textbook statement — `C` is carried
   onto by a continuous injection from the circle — and H4 is *a Jordan
   curve is homeomorphic to the circle*, with no substitution at all. `∂Q`
   stays as the working model wherever a traversal is wanted, because its
   traversal is piecewise affine, and Part II targets the square anyway.
   The two models are bridged by radial projection (`x ↦ x/‖x‖` one way,
   `x ↦ x/‖x‖∞` the other) — **not yet built**, and the one place the
   trigonometry-free choice still costs something.

2. **Circular order on directions via the determinant, not via angles.**
   The strip lemma's argument — that the left germs at polar angles
   `π − δ` and `θ + δ` lie in the same component of the circle minus
   `{θ, π}` — is really a statement about the cyclic order of four
   directions. Define `Plane.Between(u, v, w)` on unit vectors by the
   signs of `determinant(u, v)` and `determinant(v, w)`, prove it is a
   cyclic order, and rephrase the vertex bookkeeping with it. Rotation by
   `π/2` becomes `(x, y) ↦ (−y, x)`, and "rotate so no edge is
   horizontal" becomes multiplication by a unit vector `(c, s)` with
   `c² + s² = 1`, chosen to avoid finitely many bad directions — no angle
   ever named.

This is the single largest deviation from the blueprint that the target
system forces, and it should be settled before Layer 0 is written.

> **Headliner H0 — `Plane.supNorm_le_norm_le_sqrt_two_supNorm`.**
> Trivial mathematics, deliberately chosen: it is the first thing the
> blueprint uses without comment, and getting it to read well tells you
> whether the metric layer's shape is right before 40k lines are built on it.
> Second target in the same layer, and the real test of the affine
> discipline: `Plane.affine_map_determined_by_three_points`.

**Size:** 5–8k lines (raised from 4–6k: two sealed types, the torsor
laws, and the direction/orientation apparatus that replaces angles).

## Layer 1 — `Plane/Topology/` : relative topology

**Definitions.** `Plane.OpenIn(U, A)`, `ClosedIn`, `InteriorIn`,
`ClosureIn`, `BoundaryIn`, `NeighborhoodIn`; absolute versions as the
`A = universe` case; `Plane.ContinuousOn(f, A)`;
`Plane.IsHomeomorphism`.

**Main results.** The usual closure/interior/boundary algebra;
`∂U = closure(U) \ U` for open `U`; continuity is preserved by
composition and restriction; the **pasting lemma** (finitely many closed
pieces with agreeing maps); a homeomorphism between open subsets carries
relative boundaries to relative boundaries.

> **Headliner H1 — the pasting lemma.**
> It is used at the very end of the main proof to glue the interior and
> exterior extensions, and it is the first result that forces the relative
> machinery to be usable rather than merely defined.

**Size:** 5–8k lines.

## Layer 2 — `Plane/Compactness/` — **DONE 2026-07-26**

Delivered in `Natural/{frequently,subsequence}.math`,
`Real/{archimedean,cluster}.math`, and
`Plane/{sequence,compact,compactness,extremum,separation}.math`:
sequences and the coordinatewise bridge; Bolzano–Weierstrass on the line
(limsup + canonical extraction, no choice) and in the plane (the line's
theorem twice); `IsCompact` sequential, with **Heine–Borel** as an
equivalence; the extremum theorem for real-valued continuous functions;
uniform continuity; the continuous image of a compactum; and the
blueprint's `lem:compact-separation` for two disjoint compacta.

`Logic.countable_choice` was added to `axioms.math` for this layer and is
used at exactly the points where a witness must be produced per tolerance
with nothing to distinguish the options.

**Not built, deliberately.** `Plane.distanceToSet` and its 1-Lipschitz
property — `lem:compact-separation` turned out not to need it, and a
total `distanceToSet` wants infimum machinery the library does not yet
have. Finite products of compacta — no consumer yet. The
compact→Hausdorff homeomorphism is deferred to Layer 4, where H4 is its
only customer.

**Definitions.** `Plane.IsBounded`, `Plane.IsCompact` (recommend:
*sequential*, then prove equivalence with closed-and-bounded);
`Plane.distanceToSet`.

**Main results.** Bolzano–Weierstrass in ℝ²; **Heine–Borel**; continuous
images of compacta are compact; a continuous real function on a nonempty
compactum attains its minimum; finite products of compacta are compact;
uniform continuity on a compactum; `distanceToSet(·, S)` is 1-Lipschitz
in both metrics; **a continuous bijection from a compactum onto a
Hausdorff space is a homeomorphism**.

Then the blueprint's own `lem:compact-separation`, which is the single
most-cited lemma in the document: a compactum inside an open set has a
positive-radius neighbourhood inside it; two disjoint nonempty compacta
are at positive distance; and the punctured version.

> **Headliner H2 — Heine–Borel for the plane.**
> The layer's load-bearing theorem, and the first one whose proof is long
> enough to tell you what ε-δ reasoning costs in this language.

**Size:** 6–9k lines.

## Layer 3 — `Plane/Connectedness/` — **set-level content DONE 2026-07-26**

Delivered in `Plane/{connected,component,polygonal}.math`, with
`Plane/segment.math` picking up the Layer 0 facts they needed
(`between_reverse`, `segment_symmetric`, `between_nested`,
`segment_IsConvex`, `IsConvex.segment_inside`, the coordinates of a
walk):

- **Connectedness** is the clopen criterion taken as the definition — a
  nonempty relatively-clopen piece is everything — so every consumer
  discharges three positive obligations instead of refuting a separation.
- Continuous images; unions through a common point; **convex sets are
  connected** (the walk with a supremum, the layer's one analytic proof),
  hence disks and segments; a connected set caught between two disjoint
  open sets lies in the one it meets; adjoining limit points.
- **Components** as the union of the connected parts through a point —
  a comprehension, so no indexed unions. Connected, maximal, partitioning
  (`Component.equal_of_member`, `equal_of_meeting`), open when the set is,
  and `Component.recognize` for the blueprint's *Recognizing a component*.
  The boundary of a component of an open set misses the set, so the
  boundary of a component of a closed set's complement lies in the closed
  set.
- **`Plane.PolygonalReach`** — a walk is a finite chain of segments inside
  the region, taken as an inductive relation — and
  **`Plane.polygonal_connected`**: in an open connected set every point
  is reachable from every other. `Plane.Component_is_reachable_set`
  identifies the components of an open set with the walk classes, which
  is the local-connectedness item in the form the blueprint uses it.

**Not built, deliberately.** The **simplicity** clause of H3 (any two
points of a region are joined by a *simple* polygonal arc). A walk is
currently a derivation, not an object, so "simple" has nothing to be
predicated of; stating it wants Layer 4's arc type and proving it wants
the subdivide-at-intersections step of Layer 6. The walk relation is what
Part I's clopen arguments actually consume, so this is a deferral of the
statement, not of the workhorse. The general "locally path-connected
carrier" formulation was also skipped in favour of the plane fact above —
no consumer wants the abstract version.

**Definitions.** `Plane.IsConnected` (relative), `Plane.Component`,
`Plane.IsRegion` (nonempty open connected).

**Main results.** Continuous images of connected sets are connected;
unions with a common point; a connected set inside a disjoint union of
opens lies in one of them; a nonempty clopen subset of a connected set is
everything; adjoining limit points preserves connectedness; components
partition; components of open plane sets are open; in a locally
path-connected set, components of relatively open subsets are relatively
open; the boundary of a component of the complement of a closed set lies
in that closed set.

Then `lem:clopen-component` (blueprint *Recognizing a component*) and
`lem:polygonal-connected` (any two points of a region are joined by a
simple polygonal arc — the workhorse of Part I).

> **Headliner H3 — `Plane.polygonal_connected`:** any two points of a
> region are joined in it by a **simple** polygonal arc.
> Chosen because the simplicity clause is where it stops being a routine
> clopen argument: it needs the subdivide-at-intersections step, which is
> a first taste of Layer 6.

**Size:** 5–8k lines.

## Layer 4 — `Plane/Curve/` : arcs and Jordan curves — **H4 DONE 2026-07-26**

Delivered in `Plane/{model,homeomorphism,curve}.math`, with `Plane/norm.math`
picking up the sup metric's missing facts (triangle inequality, sign
blindness, symmetry, and the shift bound that makes `supDistance(origin, ·)`
continuous):

- **Settled: parametrisation domains are PLANE sets**, not `[0,1] ⊆ ℝ`.
  `Plane.unitSegment` is the model interval and `Plane.squareBoundary` the
  model curve, so a parametrisation is a `Plane.Point → Plane.Point` map,
  its continuity is Layer 1's `ContinuousOn`, its image is `imageSet`, and
  its compactness is Layer 2's `IsCompact` — Layers 1–3 apply to arcs and
  curves with nothing added. Parametrising by a real interval would need a
  second copy of the relative topology for real-domain maps, and the circle
  would need a quotient.
- `Plane.squareBoundary` is the **sup-metric level set** `‖x‖∞ = 1`, so
  compactness is closed-and-bounded with no four-way case analysis.
  `Plane.segment_IsCompact` is Bolzano–Weierstrass on the parameters,
  carried back by the walk's Lipschitz estimate.
- **`Plane.IsHomeomorphismOn`**, with the inverse's continuity stated
  *without naming the inverse* (`HasContinuousInverseOn`: points with close
  images are close) — the form every consumer uses, and no choice needed.
  Then the engine Layer 2 deferred: **a continuous injection on a compactum
  is a homeomorphism onto its image**.
- **`Plane.circle`** as `{x : ‖x‖ = 1}` — no trigonometry needed to define
  a circle, only to traverse one. `Plane.IsJordanParametrisation` names a
  continuous injection on it, and that it is a homeomorphism onto its image
  is proved (H4's engine applied to the model curve).
- **`Plane.IsJordanCurve` is the blueprint's LOOP definition** (revised
  2026-07-26): `C` is the image of a continuous map on the model interval
  that returns to its start and is injective until it does. A **set**, with
  the loop recovered by `choose`. The reason is the parameters: two points
  of the curve pull back to two parameters, and the two arcs they determine
  are a subarc and a concatenation — both built. Against the circle those
  same arcs need a *traversal* of the circle by an interval, which is
  exactly what the trigonometry-free setting withholds.
- Arcs are compact, connected, and homeomorphic copies of the unit segment;
  Jordan curves are compact, connected and nonempty.
- The parameter of a point of the unit segment is **its first coordinate**
  (`Plane.unitSegment_at_first_coordinate` and the two range lemmas) — the
  reason the model interval runs along the axis, and what makes a subarc's
  reparametrisation need no inverse.

**Subarcs and `P°` are built** (`Plane/subarc.math`). A subarc is the arc
composed with `Plane.walkOnto(a, b)`, the reparametrisation that reads a
point's parameter off its **first coordinate** and walks that fraction from
`a` to `b` — the payoff of laying the model interval along the axis, since
it needs no inverse and no choice. Continuity and injectivity are then
inherited from the composition (Layer 1 gained `ContinuousOn.compose`), and
`Plane.between_injective` — the walk is injective in its parameter unless
it never moves — is what makes a subarc between *distinct* parameters an
arc. `Plane.openArc` is the image of the model interval minus its ends, and
on an arc that is exactly the arc minus its two endpoint values.

**Concatenation is built** (`Plane/concatenate.math`, 830 lines).
`Plane.retime(scale, shift)` is the affine reparametrisation of the model
interval; the halves are named by their parameter, not as segments, because
every obligation is about that parameter. Continuity is the pasting lemma
(plus `ContinuousOn.of_agreeing`, which Layer 1 also lacked): on each half
the glued map *agrees* with a composition. **The midpoint is where the
hypotheses earn their place** — the `if` still takes the first branch
there, and the two branches agree only because the arcs share that
endpoint, so the assumption is what makes the map well defined rather than
merely continuous. Injectivity splits four ways: inside a half it is that
arc's injectivity through the retiming, and across the halves the common
value must be the shared endpoint, which pins both parameters to the
midpoint (`lowerHalf_at_finish_is_midpoint`, `upperHalf_at_start_is_midpoint`).

**The subarc basis is built.** `Plane.IsArc.image_OpenIn` — a
parametrisation is an **open map onto its arc**, which is where the
inverse's continuity finally earns its keep: it is exactly what turns a
parameter-radius into a value-radius. With
`Plane.IsArc.basic_piece_inside_ball` putting the image of a relatively
open subsegment inside every neighbourhood, the two together say the images
of relatively open subsegments are a basis of the arc's subspace topology.
Stated for subsegments rather than subarcs because at an ENDPOINT the basic
neighbourhood is half-open; `Plane.openArc` of a subarc is the interior
case.

**Not built.** In dependency order:

1. **`Plane.IsPolygonal`.** Blocked on a design decision, not on
   mathematics: it wants a **vertex list**, and `Plane.PolygonalReach` is a
   derivation rather than an object. Either give the walk a list of
   vertices (see `fold_refactor_plan`) or define `IsPolygonal(f)` as "the
   arc is a finite union of segments" over `Lists`. Settle this before
   Layer 6, which needs polygonal edges as data.
2. **The loop-to-circle bridge** — that a loop induces a continuous
   injection on the circle, which is what would restore
   "every Jordan curve is homeomorphic to the circle" as a theorem about
   `IsJordanCurve`. Blocked on the **traversal of a model curve by an
   interval**: `∂Q`'s decomposition into four sides (a
   coordinate case analysis on `max(|x₁|, |x₂|) = 1`) plus the
   **radial-projection bridge** `∂Q ≅ circle` (`x ↦ x/‖x‖` one way,
   `x ↦ x/‖x‖∞` the other, both continuous on the level sets, a
   homeomorphism by Layer 4's own theorem). Neither level-set definition
   supplies that structure; both defer it.
The loop presentation is now the DEFINITION, so what was "also not built"
above is exactly the bridge in item 2 — and constructions no longer wait on
it, since a polygonal closed curve arrives as a loop already.

**Definitions.** `Plane.Arc` (recommend bundling the parametrisation:
a continuous injective map from `[0,1]`, with the image derived, not
primitive); `Plane.JordanCurve`; `Plane.IsPolygonal`;
`Plane.Arc.subarc`; the two arcs of a Jordan curve between two of its
points; `P°` for an arc minus its endpoints; `Plane.squareBoundary` as
the model curve.

**Main results.** An arc is compact; subarcs are arcs; concatenation of
arcs meeting only at an endpoint is an arc; the two arcs determined by
two points meet exactly in those points; open subarcs form a basis.

> **Headliner H4 — `Plane.JordanCurve.homeomorphic_to_square_boundary`
> (blueprint `lem:jordan-circle`, restated per Layer 0's substitution 1).**
> The first genuine theorem of the development: it consumes Layer 2's
> compact→Hausdorff result and Layer 4's parametrisation API at once, and
> everything about arcs downstream is transported through it. Stated
> against `∂Q` rather than the circle, it needs no analysis at all beyond
> what Layers 0–3 supply.

**Size:** 4–7k lines.

### Two arcs between two points — **DONE 2026-07-27**

`Plane.IsJordanCurve.two_arcs` (`Plane/twoarcs.math`, 838 lines): two
distinct points of a Jordan curve cut it into two arcs between them, which
cover the curve and meet in exactly those two points. Layer 4 is closed
apart from the loop→circle bridge, which needs a traversal of the circle by
an interval and waits on the trigonometry-free construction.

Landed on the way: `Plane.imageSet_union`, `Set.union_commutative`,
`Set.intersection_commutative`, and `Plane.IsArcBetween` (a piece with two
named endpoints), stated RIGHT-NESTED so `IsArc` is a direct leg — see the
measurement note at the definition.

The whole argument runs on the loop's PARAMETERS: pull the two points back
to parameters `s` and `t` short of the finish, with `s` first; the two arcs
are then the loop's image of the parameters between them, and of the
parameters outside them.

Done and in the kernel:

- `Plane.first_coordinate_atLeast_on_segment` / `…_atMost_on_segment` and
  `Plane.member_segment_of_first_coordinate` (`model.math`) — a point of
  the interval lies between two others exactly when its coordinate does.
  The converse is the substantive one; its parameter is the fraction of the
  span the point has covered, which is what needs
  `Real.LessOrEqual.divide_by_positive`.
- `Plane.IsLoop.parameter_before_finish`, `…injective_before_finish`,
  `Plane.start_not_finish` (`curve.math`) — every point of the curve has a
  parameter short of the finish, by replacing a parameter AT the finish
  with the start. This is the only use the closing condition gets.
- `Plane.unitSegment_split` — the interval splits three ways around any two
  parameters (linearity of the order, nothing more).
- `Plane.IsLoop.pieces_meet_at_ends` — the loop's images of the middle and
  of the outside meet EXACTLY at the two chosen points. Three cases; the
  one that matters is the outside parameter being the finish, which carries
  the same point as the start and so lands back on `s`. That case is why
  the argument needs a loop rather than an arc.

What remains — the assembly:

1. Pull `p`, `q` back to parameters and order them. The ordering wants a
   symmetric conclusion so the second case is the first applied to `(q, p)`
   rather than a second copy of the proof.
2. The middle piece is an arc by `IsArc.subarc_on_subsegment` (which is why
   that lemma was relaxed to need injectivity only on the subsegment).
3. The outside piece is `IsArc.concatenate` of `subarc(γ, t, finish)` and
   `subarc(γ, origin, s)`, sharing the endpoint where the loop closes.
   **Case split when `s = origin`**: the second piece degenerates to a
   constant, and the arc is just `subarc(γ, t, finish)` — the missing point
   is already on it, since `γ(origin) = γ(finish)`. Keep this split inside
   the "exhibit a parametrisation" step only; the set-level covering and
   meeting facts above hold uniformly and must not be duplicated.

## Layer 5 — `Graph/` : finite graphs — **STARTED 2026-07-29**

Abstract, no geometry. Keep it that way — Layer 6 maps into it.

Built so far: `Graph/{basics,walk,path,connected,deletion,cycle}.math`,
with `library/Graph/README.md` as the entry point.

- **Settled: an edge is a NAME.** A graph lives over an ambient
  `(V, E, ends)` — vertex type, edge type, and `ends : E → Pair(V, V)` —
  and is itself two finite lists. Two names with the same ends are two
  parallel edges, which is what a two-vertex cycle needs and what a list
  of vertex pairs cannot express: a walk along one of two parallel edges
  could not say which. The ambient is a parameter of the *type*, so a
  subgraph, a deletion and a union all have the same type and their edges
  are comparable; it is carried by file-level `convention`s, so no
  statement spells it.
- **Loops are excluded by `Graph.IsWellFormed`**, together with
  repetition-freeness of the two lists and the requirement that an edge's
  ends be vertices of the graph — a predicate, not a constructor
  obligation, so deletions and unions stay easy to build.
- **A walk is a list of edges** (`Graph.IsWalk`), taken from where the
  last one arrived. Naming edges rather than vertices is forced by
  parallel edges, and costs nothing: an edge with two distinct ends
  determines where taking it arrives (`Graph.Joins.unique`).
  Concatenation and reversal are proved once, so no later argument cares
  which end a walk was built at.
- **A path carries its own freshness** — the vertex a step departs from is
  not among those the rest of the path visits — rather than a
  distinctness condition on a separately computed vertex list. The
  visited vertices are a `Set(V)`, since nothing counts them.
- **`Graph.IsWalk.contains_path`**: every walk contains a path between the
  same two vertices, using only the walk's own edges. Its engine is
  `Graph.IsPath.from_visited` (cut a path at a vertex it passes through),
  so the construction never lengthens anything.
- `Graph.Reaches` is stated with walks, not paths — walks concatenate and
  reverse without a side condition — and a path is recovered on demand.
- **A cycle is presented through one of its edges**: the edge plus a path
  between its two ends that avoids it. Every question the blueprint asks
  is of that shape, so the closed walk is never assembled and the path
  relation already forbids the repetitions a closed walk would have to
  rule out by hand. Length two is included, and is the reason edges are
  names. `Graph.LiesOnCycle.deletion_reaches` and its converse are the
  plan's "an edge lies on a cycle iff deleting it does not disconnect its
  endpoints"; `Graph.IsBridge` is read off them.

**Frictions.** `FRICTION_GRAPH_LAYER5.md`. **G1 and G5 are FIXED** (a
`choose … such that` clause is now checked in every form, and with `from`
omitted the condition is the search key). G2/G3 stand, and are the reason
each inductive here has a transparent reader and one wrapper per
constructor.

**Still to build.** Vertex deletion; degree counting and trees;
2-connectivity and cut vertices; subdivisions and ears; then H5.

**Definitions.** `Graph` on a finite vertex type with an edge multiset
(parallel edges **allowed**, loops forbidden — the blueprint needs
two-vertex cycles); `Graph.Walk`, `Path`, `Cycle`; `Graph.IsConnected`,
`Graph.IsTwoConnected`, `Graph.cutVertex`, `Graph.bridge`;
`Graph.IsTree`, `Graph.leaf`, `Graph.degree`; `Graph.Subdivision`,
`Graph.Ear`.

**Main results.** Every walk contains a simple path; an edge lies on a
cycle iff deleting it does not disconnect its endpoints; a tree on `n`
vertices has `n-1` edges and `Σ(deg v − 2) = −2`; a tree with exactly
three leaves has one degree-3 vertex; two 2-connected graphs sharing two
vertices have 2-connected union; subdivisions and ears preserve
2-connectivity (**including ears with no internal vertices**).

> **Headliner H5 — `Graph.relative_ear_decomposition`:** a 2-connected
> subgraph of a finite 2-connected graph grows to it by adding ears.
> This is the engine of `lem:face-cycles` and of the entire finite-transfer
> theorem in Part II. If it is comfortable to state and use, Part II will go
> well.

**Size:** 8–12k lines. The largest foundation layer, and the least risky —
it is pure finite combinatorics over `Lists`/`HasSize`.

## Layer 6 — `Plane/Graph/` : plane graphs and arrangements

Where the two halves meet, and the layer I would expect to hurt.

**Definitions.** `Plane.Graph`: distinct vertex points, edges as simple
arcs with pairwise disjoint interiors avoiding all vertices;
`Plane.Graph.face` as a component of the complement;
`Plane.Graph.outerFace`; `Plane.Graph.overlay` — the subdivision of a
finite union of polygonal graphs at all intersections.

**Main results.** The overlay of finitely many finite polygonal plane
graphs is a plane graph after subdividing at all crossings and identifying
duplicated subsegments (`lem:polygonal-overlay`); segments meet in nothing,
a point, or an interval; a plane graph realises an abstract finite graph.

> **Headliner H6 — `Plane.Graph.polygonal_redrawing`
> (blueprint `lem:polygonal-redrawing`):** every finite plane graph is
> isomorphic to one with polygonal edges.
> Chosen as the headliner because it is the first result that needs Layers
> 0–6 simultaneously, and because it is the point where "subdivide at all
> intersections" stops being a phrase.

**Size:** 5–9k lines.

---

## After the foundation: the blueprint itself

Follow Appendix A of `jordan_schoenflies.tex` — it is a machine-generated
dependency index and it is what makes this shardable. Regenerate it with
`python3 regen_appendix.py` in the schoenflies repo after any edit.

Milestones, in order:

> **H7 — the polygonal Jordan curve theorem** (`thm:polygonal-jordan`).
> Requires the two-sided strip lemma, which is *the* stress test of the
> blueprint: one informal paragraph hides a large choice-of-constants
> argument over vertex disks and edge blocks. If the blueprint is going to
> be found insufficient anywhere, it is here. Do not skip ahead of it.

> **H8 — `K₃,₃` has no plane drawing** (`lem:k33`).
> Small, and it certifies that Layer 6 plus the polygonal crosscut theorem
> actually compose.

> **H9 — the Jordan curve theorem** (`thm:jordan`).
> On Freek's 100 list. A natural place to stop, publish, and reassess.

> **H10 — the crosscut theorem** (`thm:general-crosscut`).
> The instrument all of Part II uses.

> **H11 — Jordan–Schönflies** (`thm:main`).

Part I after the foundation: ~20k lines. Part II (cellulations, finite
transfer, shrinking stars, the limit map, inversion): ~28k lines. Part II
is the largest single block but is the most carefully written part of the
blueprint — invariants stated explicitly, parent maps defined,
combinatorial invariance isolated from geometry. I expect it to survive
contact better than Part I's geometry.

---

## Design questions to settle before writing

Flagging these rather than deciding them, per the always-apply rule.

1. ~~**`Plane.Point` representation.**~~ **Settled.** Two sealed types,
   `Plane.Vector` (linear) and `Plane.Point` (affine over it), both
   concrete over `Product(ℝ, ℝ)`. Not `Algebra/`'s vector spaces, and not
   an abstract torsor. See Layer 0.

   Still open within that: whether the seal should also hide the
   coordinate accessors behind a `Plane.coordinates` view, or expose them
   directly. Part I's parity counting is coordinate-heavy enough that I
   would expose them and revisit only if the seal proves leaky.

2. **Relative from the start, or absolute then relativised?**
   Recommendation: **relative from the start.** Connectedness is applied
   to arcs and curves as subspaces, and `lem:jordan-circle` needs
   compact→Hausdorff on a subspace. Retrofitting relativisation across
   Layers 1–3 would be worse than paying for it up front.

3. **Compactness: sequential or open-cover?** Recommendation:
   **sequential as the definition**, open-cover as a proved equivalence
   if anything needs it. Every use in the blueprint is sequential or
   min-attainment, and the library's `Real/` convergence machinery feeds
   it directly.

4. **Arcs: parametrised or set-level?** Recommendation: **carry the
   parametrisation.** The blueprint slides between "the arc" and "the
   map" constantly, and subarcs/concatenation are painful set-first.

5. **Plane graph edges: arcs or polygonal-only?** The blueprint needs
   general arcs for `lem:polygonal-redrawing` and polygonal thereafter.
   Recommendation: general arcs in the definition; a `IsPolygonal`
   predicate; every later result assumes it.

## Frictions found so far

`FRICTION_PLANE_LAYER0.md` — the running log from Layer 0, in
`QUIRK.md`'s format. Section I is inequalities and is the priority: every
entry there is a step a mathematician writes without pausing, and a
`linarith` over ordered fields would absorb most of them.

## Unknowns, honestly

- **Geometry is a new domain for this system.** Every line-count estimate
  here is extrapolated from algebraic material. `Real/intermediate_value.math`
  is 226 lines for one theorem and is the closest existing precedent — a
  thin base. Layer 2 is the first honest measurement.
- **The recent 35k lines/day is not the rate to plan with.** That was bulk
  algebra. The steady rate on foundational material (May 18 → Jul 15) is
  ~1k lines/day; that is the figure these estimates assume.
- **The hard constructions do not bulk-generate.** The strip lemma, the
  chain lemma and the finite transfer need design, not pattern-following.
- **Build time.** The library is already 433k lines and `.mathv` caching
  keys on the kernel binary. Adding ~88k lines of real-arithmetic-heavy
  material may change the clean-build economics; worth watching from
  Layer 2 on.

## Building while working here

`make -j 16 plane` — the narrow target added for this development. It
names only `library/Plane/*.math`; the generated dependency file supplies
the transitive closure, which reaches 19 of the 546 `Algebra/` files and
none of the fifteen-theorem material. Warm runs are seconds. Reserve
`make -j 16 library` for pre-commit checks.

## Suggested first move

Layer 0 through **H2 (Heine–Borel)**. It is self-contained, the design
questions blocking it are settled, and it is the measurement that turns
every other number in this file from a guess into an estimate.

Before writing: decide the two trigonometry substitutions in Layer 0.
They change the blueprint, not just this plan — Appendix C's polar-
coordinate item and `lem:jordan-circle`'s statement both need editing in
`~/claude/schoenflies/jordan_schoenflies.tex`, and Appendix A regenerates
with `python3 regen_appendix.py`.

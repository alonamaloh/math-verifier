# Plane graphs

Layer 6 of `PLAN_JORDAN_SCHOENFLIES.md` — where the abstract combinatorics
of [`library/Graph/`](../../Graph/README.md) meets the geometry of
[`library/Plane/`](../README.md).

## Building

```sh
make -j 16 plane      # this area and exactly its transitive imports
```

## A plane graph is a graph plus a drawing

There is no `Plane.Graph` type. A plane graph is a pair — an abstract
`Graph(Plane.Point, E, ends)` and a `drawing : E → (ℝ → Plane.Point)`
assigning an arc to each edge name — related by the predicate

```math
Plane.Graph.IsDrawing(graph, drawing)
```

**Why unbundled.** Every theorem of `Graph/` — connectedness, cycles,
2-connectivity, ears, trees, the handshake lemma — is about a
`Graph(V, E, ends)`. Keeping the abstract graph as itself means all of it
applies with nothing to project through; a bundled record would put a
projection inside every combinatorial citation. It also makes "a plane graph
realises an abstract finite graph" true by construction rather than a
theorem.

`Plane.Graph.IsDrawing` says four things, each with a reader theorem (the arc
clause is read back in two):

| clause | reader |
| --- | --- |
| the abstract graph is well formed | `.IsWellFormed` |
| each edge is drawn by a simple arc… | `.IsArc` |
| …running between the two points its name says | `.joins_ends` |
| no vertex lies in an edge's interior | `.vertex_off_interior` |
| distinct edges have disjoint interiors | `.interiors_disjoint` |

The vertices are plane **points**, so "the vertices are distinct" is already
`Graph.IsWellFormed`'s distinctness of the vertex list, and loops are
already excluded there. Nothing about the plane repeats it.

## What consumers actually use

Not the condition — its consequence. The blueprint's phrase "distinct edges
of a plane graph meet only at shared vertices" is

- **`Plane.Graph.IsDrawing.arcs_meet_at_vertex`** — a common point of two
  distinct edge arcs is a vertex incident with both,

proved through `Plane.Graph.IsDrawing.endpoint_or_interior`: a point of an
edge arc is read off its parameter, and the two ends of the unit interval
are the two vertices. Its corollary is the form the overlay wants:

- **`Plane.Graph.IsDrawing.unique_edge_at`** — away from the vertices, a
  point of the drawing lies on exactly one edge.

`Plane.Graph.IsDrawing.subgraph` passes a drawing to any well-formed
subgraph, with the same family of arcs: `Graph.Joins` reads only the ambient
`ends`, so an edge joins the same two points in the part as in the whole.

## The point set and the faces

- `Plane.Graph.pointSet` — what the drawing occupies: the union of
  `Plane.Graph.vertexSet` and `Plane.Graph.edgeSet`. Both halves are
  `List.unionOver` over the graph's **own** vertex and edge lists, which is
  how finiteness is carried (`Lists/set_union.math`).
  `Plane.Graph.pointSet_subset` carries it down a subgraph.
- `Plane.Graph.exterior` — the complement, open by
  `Plane.Graph.complement_pointSet_IsOpen`. That reduces, through
  `MetricSpace.complement_unionOver_IsOpen`, to a point being closed and an
  arc being compact.
- **`Plane.Graph.face(graph, drawing, base)`** — the face through a point
  off the drawing: the component of the exterior containing it. Named by a
  point rather than indexed, exactly as `Plane.Component` is, so no face has
  to be produced before it can be spoken about. It is a region
  (`Plane.Graph.face_IsRegion`), and the faces partition the exterior
  (`Plane.Graph.face.equal_of_meeting`,
  `Plane.Graph.face.equal_of_member`).

## Polygonal plane graphs, and the overlay

**The edge name is the pair of endpoints** (`Plane.Segment`), and `ends` is
the identity (`Plane.segmentEnds`), so a polygonal plane graph is a
`Plane.PolygonalGraph` — [segments.math](segments.math). A straight segment is
determined by its endpoints, so naming one by anything else would name a
distinction that does not exist; the general representation allows parallel
edges only because a Jordan curve cut at two points is a two-vertex cycle,
which segments cannot be. The payoff is that "represent every duplicate
geometric subsegment only once" becomes deduplication of a list of **names**.
The wrinkle: `(a, b)` and `(b, a)` name one segment, and a graph holding both
is refused, so a construction owes an edge list that picks one orientation.

`Plane.segmentDrawing(piece)` is the drawing every such graph carries: the
walk between the name's own two components. `Plane.segmentEdge_joins` is why
the incidence half of the drawing condition is free — with `ends` the
identity, an edge joins its own components — and
`Plane.segmentEdge_ends_distinct` reads the endpoints' distinctness off
well-formedness.

**`Plane.Graph.polygonal_IsDrawing`** is what a construction discharges. For
segments the two arc obligations are free — `Plane.between` is a simple arc
between any two distinct points, and well-formedness supplies the
distinctness — so being a polygonal plane graph is well-formedness plus the
two disjointness conditions, stated about `Plane.openSegment`, which is the
form `Plane.segment_meet` can check.

**`Plane.subdivide(pieces, points)`** cuts a list of segments at a list of
points — [subdivide.math](subdivide.math). Structural in the **point** list:
cut every current piece at one point (`Plane.splitAllAt`), recurse with the
rest. One piece and one point is `Plane.splitSegmentAt`, which splits in two
at an interior point and is the identity anywhere else. This is what avoids
both a choice operator (the meets are existential, so naming them as data
would need one) and a sort (no ordering of the cut points along a segment is
ever required, because cutting at a point that has already become an endpoint
is a no-op).

`Plane.piecesCover` is the set a list of pieces occupies, and the two
recursion equations `Plane.subdivide_empty` / `Plane.subdivide_prepend` are
how a proof steps through a cut list.

Five properties of a subdivision, each proved of one cut and then lifted
across the piece list and the point list:

| property | what it says |
| --- | --- |
| `Plane.subdivide_ends_distinct` | no piece degenerates |
| `Plane.subdivide_inside` | a piece lies inside a source piece — segment in segment AND interior in interior, at the **same** source, which is what the separation argument needs |
| `Plane.subdivide_avoids` | no cut point stays interior to any piece |
| `Plane.subdivide_covers` | the pieces occupy exactly what they came from |
| `Plane.subdivide_ends` | an end of a piece that is not a cut point was an end all along; so `Plane.subdivide_ends_are_cuts`, once the source ends are cut too |

## Separation, and the overlay itself

`Plane.polygonal_overlay` ([overlay.math](overlay.math)) is
`lem:polygonal-overlay`: finitely many nondegenerate segments become a
polygonal plane graph occupying exactly the points they cover. The graph is
`Plane.overlayGraph` — the subdivision, oriented and deduplicated, with the
ends of those edges as vertices — and the cut points are never computed:
`Plane.exists_cut_points` produces them existentially, by the same induction
that proves they exist.

The theorem it turns on is **separation**:

- **`Plane.subdivide_separated`** — cut at every end of every source piece
  (`Plane.EndsAreCut`) and at both ends of every meet (`Plane.MeetsAreCut`),
  and two pieces of the subdivision that share an interior point are the
  **same** segment. Equal, not disjoint: overlapping collinear pieces cannot
  be pulled apart by cutting, and that is exactly what the deduplication
  clause is for.

Its first step, `Plane.subdivide_common_segment`, is collinearity — two such
pieces lie in one segment (their common source, or the sources' overlap, which
is nondegenerate because the shared point is interior to it). The rest is
one-dimensional and lives in
[`Plane/segment_order.math`](../segment_order.math).

`Plane.MeetsAreCut` asks for **some** pair of ends of each meet to be cut,
not every pair: a meet is `segment(u, v)` and `segment(v, u)` alike, and that
a nondegenerate segment's ends are determined by its point set is a theorem
this development neither has nor needs.

**Deduplication is up to equality, not up to reversal**, because of
`Plane.orientSegment` ([orient.math](orient.math)): it puts the
lexicographically smaller end first (`Plane.Point.Precedes`, in
[`Plane/point_order.math`](../point_order.math)), and
`Plane.orientSegment_of_SameSegment` says two names for one segment orient to
the same name. So `List.deduplicate` — plain list deduplication, carrying no
geometry — is all the "represent each duplicated subsegment once" clause
needs. `Plane.SameSegment` (in [segments.math](segments.math)) is the relation
being quotiented, and `Plane.SameSegment.segment` / `.openSegment` say both
names draw the same points.

## Where to look

| module | what is in it |
| --- | --- |
| [basics.math](basics.math) | `Plane.Graph.IsDrawing`, its five readers, and the meet-at-a-vertex theorems |
| [pointset.math](pointset.math) | `vertexSet` / `edgeSet` / `pointSet`, the open exterior, and the faces |
| [segments.math](segments.math) | `Plane.Segment`, `Plane.PolygonalGraph`, `Plane.segmentDrawing`, `Plane.SameSegment`, and the polygonal criterion |
| [subdivide.math](subdivide.math) | `Plane.subdivide`, `Plane.IsEndOf`, and the five properties |
| [orient.math](orient.math) | `Plane.orientSegment` — one canonical name per segment |
| [overlay.math](overlay.math) | separation, the cut points, `Plane.overlayGraph`, and `Plane.polygonal_overlay` |

Each module opens with `convention E` and `convention ends`, as
[`library/Graph/`](../../Graph/README.md) does, so a statement names the graph
and the drawing and nothing else.

## Not built yet

- **The outer face.** That exactly one face is unbounded needs the exterior
  of a large disk to be connected — a genuine plane fact that nothing here
  supplies.
- **H6, polygonal redrawing** — every finite plane graph is isomorphic to
  one with polygonal edges.
- **The realisation of a cycle is a Jordan curve.** Needs the edge arcs of a
  cycle concatenated in order.

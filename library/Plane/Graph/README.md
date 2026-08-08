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
  `Plane.Graph.edgesCover(drawing, edgeList)` is the same union over an
  arbitrary edge list — a walk, a path and a cycle each arrive as one — and
  `edgeSet` is that at the graph's own list.
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

`Plane.polygonal_overlay_of_graphs` is the same result for finitely many
polygonal **graphs**, which is how the blueprint states it: concatenate the
edge lists (`Plane.graphEdges`), take nondegeneracy from well-formedness, and
cite the segment form. It covers the graphs' **edge** sets —
`Plane.edgeSet_is_piecesCover` says a graph covers what its edges cover — and
not their isolated vertices, which the overlay cannot keep, since its vertices
are the ends of its edges.

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
| [cycle.math](cycle.math) | the realisation of a cycle is a Jordan curve |
| [outerface.math](outerface.math) | the drawing fits in a square, and exactly one face is unbounded |
| [vertexsquares.math](vertexsquares.math) | `Plane.Graph.ClearSquare`, `Plane.Graph.DisjointSquares`, and one radius that clears every vertex at once |
| [cores.math](cores.math) | the core of an edge — the subarc between the two vertex squares |
| [tubes.math](tubes.math) | distinct cores are disjoint, and one ε makes the tubes about them disjoint |

Each module opens with `convention E` and `convention ends`, as
[`library/Graph/`](../../Graph/README.md) does, so a statement names the graph
and the drawing and nothing else.

## The realisation of a cycle

**`Plane.Graph.cycle_IsJordanCurve`** ([cycle.math](cycle.math)) — the arcs of
a cycle's edges cover a Jordan curve. A cycle arrives as Layer 5 presents it:
an edge, and a path between that edge's two ends which does not use it.

The argument is **set-level throughout**; no parametrisation of a walk is ever
constructed. `Plane.IsArcBetween` is what a path is drawn by, and the two
gluing theorems of [`Plane/concatenate.math`](../concatenate.math) do the
work — `Plane.IsArcBetween.concatenate` and `Plane.IsJordanCurve.of_two_arcs`.
The arcs are chosen inside the induction and their concatenation is chosen by
the gluing theorem, exactly as `Plane.exists_cut_points` produces the
overlay's cut points without naming them.

- `Plane.Graph.IsDrawing.edge_IsArcBetween` — an edge is drawn by an arc
  between its two ends, whichever way round the caller names them
  (`Plane.IsArcBetween.reverse` supplies the other orientation).
- `Plane.Graph.IsDrawing.path_IsArcBetween` — a path that goes anywhere at
  all is drawn by an arc between its ends, covering exactly
  `Plane.Graph.edgesCover` of its edges. The induction is on the path
  derivation, with the singleton case split off inside the step.
- `Plane.Graph.IsDrawing.first_edge_meets_rest` is where the geometry enters,
  and it enters once: the first edge's arc meets the rest of the path only at
  the waypoint, because a common point is a vertex incident with both edges
  (`arcs_meet_at_vertex`) and the path's freshness clause forbids it being the
  source. Taking the same edge again is refused by the same clause.

## The outer face

**Exactly one face is unbounded** ([outerface.math](outerface.math)), which
Layer 6 had deferred. The plane fact it waits on is in
[`Plane/exterior.math`](../exterior.math): the plane outside a **square** is
connected, because that outside is exactly a union of four half-planes, each
convex and hence connected, with consecutive ones sharing a corner. A disk
would need the polar decomposition this development withholds.

- `Plane.Graph.pointSet_inside_square` — the drawing is caught inside some
  square: finitely many points and finitely many compact arcs, merged by
  **adding** radii (`Plane.unionOver_inside_square`).
- `Plane.Graph.beyondSquare_inside_face` — everything beyond that square lies
  in one face, since it is a connected part of the exterior.
- `Plane.Graph.exists_outer_face` and `Plane.Graph.outer_face_unique`. No face
  is ever produced as data: a face is named by a point of it, as
  `Plane.Graph.face` has always been. Uniqueness is
  `Plane.unbounded_escapes_square` — an unbounded face reaches past the
  square, so it is named by a point of the outside and swallows all of it.

## The vertex squares

**`Plane.Graph.ClearSquare(graph, drawing, vertex, radius)`**
([vertexsquares.math](vertexsquares.math)) — the closed axis-parallel square
of that radius about that vertex holds no other vertex and meets no arc of an
edge the vertex is not on. Squares rather than disks, because the redrawing
needs a boundary made of segments; convexity, which its radial segments want,
both shapes have. `Plane.squareAbout` and its sup-metric readers are in
[`Plane/exterior.math`](../exterior.math).

- `Plane.Graph.IsDrawing.vertex_off_arc` — a vertex lies on no arc but those
  of its own edges, which is what the separation is run against.
- `Plane.Graph.IsDrawing.exists_square_off_vertices` and
  `.exists_square_off_edges` — one radius clearing each family, by
  `Real.exists_common_positive_bound` over the graph's own vertex and edge
  lists; `.exists_clear_square` keeps the smaller of the two.
- **`Plane.Graph.IsDrawing.exists_vertex_squares`** is the form to consume:
  ONE radius serving every vertex, and squares about distinct vertices
  **disjoint** (`Plane.Graph.DisjointSquares`). Disjointness does not follow
  from the per-vertex statement — that the square about `v` misses `w` says
  nothing about the square about `w`
  reaching back — so the common radius is halved. Two halved squares that met
  would put their centres within the common radius in the sup metric, that is
  each centre inside the other's unhalved square, which the common choice
  already forbids. This is the one place the sup-metric triangle inequality is
  used.
- `Plane.Graph.ClearSquare.misses_arc_of_not_end` — a clear square about a
  vertex that is neither end of an edge misses that edge's **whole arc**. It is
  a statement about the arc, not about any piece of it, so the cores inherit
  "meets no other vertex square" without saying anything themselves.

## The cores

**`Plane.Graph.IsDrawing.exists_core`** ([cores.math](cores.math)) — the
redrawing keeps the middle of each edge and replaces only its two ends, and the
middle is the **core**: the subarc between the LAST parameter at which the arc
is inside the square about the vertex it starts at, and the FIRST parameter
**after that** at which it is inside the square about the vertex it finishes
at.

"After that" is not a decoration. Nothing forbids an arc from dipping into the
far square early, returning to the near one, and only then running to its far
end; taken globally the first entry can precede the last exit and the "core"
would be empty or reversed. That is why `MetricSpace.exists_last_inside` /
`.exists_first_inside` are stated over an arbitrary `Real.segment(a, b)` — the
second half of the choice lives on the subinterval the first half produced.

The core is compact, it is an arc between its two endpoints, it lies in the
edge's arc, it meets each of the two endpoint squares in exactly its own
endpoint there, and — the clause the assembly runs on — it **contains no
vertex** (`Set.Disjoint(core, Plane.Graph.vertexSet(graph))`). That last is
stronger than "distinct cores are disjoint": two cores of distinct edges meet
only at a vertex (`arcs_meet_at_vertex`), so a core holding none meets no
other, and nothing ever quantifies over pairs of cores.

That the core reaches neither vertex is the one place the **positivity** of the
radius is spent: the arc starts at the centre of the near square, so it is
still inside just after starting, and the last exit therefore happens at a
positive parameter.

## The tubes

**`Plane.Graph.IsDrawing.exists_core_separation`** ([tubes.math](tubes.math))
— one ε for the whole redrawing: the tubes about the cores, where the tube is
`Plane.nearSet(core(edge), epsilon)`, are pairwise disjoint. The cores of
distinct edges are disjoint compacta, so `Plane.compact_separation` gives each
pair a positive gap, `Real.exists_common_positive_bound` folds the finitely
many gaps into one, and half of that is the ε — two points ε-near cores a
full `2 * epsilon` apart cannot coincide.

The family of cores arrives as a **function** of the edge carrying B4's
clauses, since a single ε has to speak about all of them at once and no
per-edge existential can.

- **`Plane.Graph.IsDrawing.cores_disjoint`** — this is where B4's clause is
  spent. Two arcs of distinct edges cross only at a vertex incident with
  both, so a piece of one arc holding no vertex misses every other arc; it is
  stated for arbitrary pieces, because that is all the argument uses.

Nothing here says the tube of an edge avoids the squares about the other
vertices, nor confines its contact with a square's boundary. Neither is
needed: the assembly works inside the plane minus the **open** squares, which
holds no vertex at all, and the contact points are pinned by the sup distance
along a radial segment rather than by ε.

## Not built yet

- **H6, polygonal redrawing** — every finite plane graph is isomorphic to
  one with polygonal edges. Bricks B2 (the vertex squares), B4 (the cores),
  B5 (the plane minus the open vertex squares is locally polygonally
  connected, a plane fact stated over a list of centres in
  [`Plane/locally_polygonal.math`](../locally_polygonal.math)) and B7 (the
  ε) have landed; the clopen argument over such a carrier (B6) and the
  assembly (B8) have not.

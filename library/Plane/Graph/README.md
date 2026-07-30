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

`Plane.Graph.IsDrawing` says four things, and each has a reader theorem:

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

- `Plane.Graph.vertexSet`, `Plane.Graph.edgeSet`, `Plane.Graph.pointSet` —
  what the drawing occupies. Both halves are `List.unionOver` over the
  graph's **own** vertex and edge lists, which is how finiteness is carried
  (`Lists/set_union.math`).
- `Plane.Graph.exterior` — the complement, open by
  `Plane.Graph.complement_pointSet_IsOpen`. That reduces, through
  `MetricSpace.complement_unionOver_IsOpen`, to a point being closed and an
  arc being compact.
- **`Plane.Graph.face(graph, drawing, base)`** — the face through a point
  off the drawing: the component of the exterior containing it. Named by a
  point rather than indexed, exactly as `Plane.Component` is, so no face has
  to be produced before it can be spoken about. It is a region
  (`face_IsRegion`), and the faces partition the exterior
  (`face.equal_of_meeting`, `face.equal_of_member`).

## Not built yet

- **The outer face.** That exactly one face is unbounded needs the exterior
  of a large disk to be connected — a genuine plane fact that nothing here
  supplies.
- **The overlay** (`lem:polygonal-overlay`). Its foundation is
  the segment trichotomy (two segments meet in nothing, a point, or a
  segment), which is Layer 0 geometry and independent of everything above.
- **H6, polygonal redrawing** — every finite plane graph is isomorphic to
  one with polygonal edges.
- **The realisation of a cycle is a Jordan curve.** Needs the edge arcs of a
  cycle concatenated in order.

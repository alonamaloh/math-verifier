# Finite graphs

Abstract finite multigraphs — no geometry. Layer 5 of
`PLAN_JORDAN_SCHOENFLIES.md`; Layer 6 (`Plane/Graph/`) maps into this one,
so nothing here may mention the plane.

## The shape of a graph

A graph lives over an **ambient** `(V, E, ends)`: a vertex type, an edge
type, and `ends : E → Pair(V, V)` assigning each edge name its two
endpoints. The graph itself is two finite lists,
`Graph.vertices` and `Graph.edges`.

Edges are **names**, not pairs of vertices. Two names with the same ends
are two parallel edges, which is what a cycle on two vertices needs, and
what a walk needs in order to say which of the two it took. Loops are
excluded by `Graph.IsWellFormed`, not by the ambient.

The ambient is a parameter of the *type*, so every graph over it — a
subgraph, a deletion, a union — has the same type and the edges of one are
comparable with the edges of another. `V`, `E` and `ends` are file-level
`convention`s, so they are never written in a statement; they are read off
the graph argument. That is also why the incidence predicates take the
graph although they only read `ends`.

## Main definitions

- `Graph(V, E, ends)`, `Graph.vertices`, `Graph.edges`, `Graph.order`,
  `Graph.size` in [basics.math](basics.math)
- Incidence: `Graph.Joins(graph, edge, u, v)`, `Graph.Incident`,
  `Graph.Adjacent`, `Graph.degree`, `Graph.incidentEdges`
- `Graph.IsWellFormed` — both lists repetition-free, every edge between
  two distinct vertices of the graph — and `Graph.IsSubgraph`
- `Graph.IsWalk(graph, source, edgeList, target)` in [walk.math](walk.math),
  with `Graph.walkVertices` / `Graph.coveredVertices` as the `Set(V)` of
  vertices a walk visits
- `Graph.IsPath` in [path.math](path.math) — a walk that never departs from
  a vertex the rest of it visits
- `Graph.Reaches` and `Graph.IsConnected` in
  [connected.math](connected.math)
- `Graph.deleteEdge` in [deletion.math](deletion.math)
- `Graph.IsCycleThrough`, `Graph.LiesOnCycle` and `Graph.IsBridge` in
  [cycle.math](cycle.math)
- `Graph.deleteVertex` and `Graph.IsCutVertex` in
  [vertex_deletion.math](vertex_deletion.math)
- `Graph.IsTwoConnected` in [twoconnected.math](twoconnected.math) — the
  blueprint's convention: at least three vertices, connected, and still
  connected after any one vertex goes
- `Graph.union` in [union.math](union.math)

## Main theorems

- `Graph.Joins.unique` — an edge with two distinct ends has no third, so a
  walk that names its edges determines its vertices
- `Graph.Incident.is_end` — a vertex incident to an edge is one of its ends
- `Graph.IsWalk.append`, `Graph.IsWalk.reverse`, `Graph.IsWalk.single`
- `Graph.IsWalk.visits_vertices` — a walk out of a vertex stays in the graph
- `Graph.IsPath.from_visited` — a path passing through a vertex has a piece
  of itself running from there to its target
- **`Graph.IsWalk.contains_path`** — every walk contains a path between the
  same two vertices, using only the walk's own edges
- `Graph.Reaches.{reflexive,symmetric,transitive,path}` and
  `Graph.IsConnected.from_hub`
- `Graph.IsWalk.in_supergraph`, and for a deletion its two directions:
  `Graph.IsWalk.after_deletion` and `Graph.IsWalk.avoiding_edge`
- `Graph.deleteEdge.{IsSubgraph,IsWellFormed,size}`
- **`Graph.IsTwoConnected.no_bridge`** — a 2-connected graph has no bridge,
  so every edge of one lies on a cycle
  (`Graph.IsTwoConnected.edge_on_cycle`)
- **`Graph.IsTwoConnected.union`** — two 2-connected graphs sharing two
  vertices have a 2-connected union
- `Graph.IsWalk.avoiding_vertex` / `.after_vertex_deletion`,
  `Graph.deleteVertex.{IsSubgraph,IsWellFormed,monotone}`, and
  `Graph.IsConnected.after_outside_deletion`
- `Graph.third_vertex` — two named vertices of a graph on three or more
  leave one over
- **`Graph.LiesOnCycle.deletion_reaches`** and
  **`Graph.LiesOnCycle.of_deletion_reaches`** — an edge lies on a cycle
  exactly when the graph without it still joins its two ends; hence
  `Graph.IsBridge.separates_ends` and `Graph.IsBridge.of_separated_ends`

## Working here

Each indexed inductive is declared with the ambient spelled out
(`Graph.IsWalkOver`, `Graph.IsPathOver`) and immediately re-exposed as a
transparent reader (`Graph.IsWalk`, `Graph.IsPath`) that recovers the
ambient from the graph — an inductive takes neither `convention` nor
implicit binders, and no leading-argument inference. Write statements with
the reader; the raw name appears only as the case labels of
`by induction`, and its constructors only inside `Graph.IsWalk.empty` /
`.extend` and their path counterparts.

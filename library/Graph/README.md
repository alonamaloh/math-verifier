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
- `Graph.otherEnd(graph, edge, vertex)` — the end of an edge away from one
  of its ends — and `Graph.walkVertexList(graph, source, edgeList)`, the
  vertices a walk visits AS A LIST, in order. The `Set(V)` above is what
  every argument reads; the list is what BUILDING a graph out of a walk
  needs
- `Graph.IsPath` in [path.math](path.math) — a walk that never departs from
  a vertex the rest of it visits
- `Graph.Reaches` and `Graph.IsConnected` in
  [connected.math](connected.math)
- `Graph.deleteEdge` in [deletion.math](deletion.math)
- `Graph.IsCycleThrough`, `Graph.LiesOnCycle` and `Graph.IsBridge` in
  [cycle.math](cycle.math)
- `Graph.IsAcyclic`, `Graph.IsTree` and `Graph.IsLeaf` in
  [tree.math](tree.math) — a tree is connected with no edge on a cycle,
  and a leaf is a vertex of degree one
- `Graph.incidenceCount` in [degree.math](degree.math) — how many of an
  edge list's edges meet a vertex; at the graph's own edges, the degree
- `Graph.deleteVertex` and `Graph.IsCutVertex` in
  [vertex_deletion.math](vertex_deletion.math)
- `Graph.IsTwoConnected` in [twoconnected.math](twoconnected.math) — the
  blueprint's convention: at least three vertices, connected, and still
  connected after any one vertex goes
- `Graph.union` in [union.math](union.math)
- `Graph.pathGraphOf(graph, source, edgeList)` — a path of `graph`
  presented as a graph of its own, which is how an ear is built
- `Graph.IsPathGraph` in [pathgraph.math](pathgraph.math) — a graph whose
  own edge list walks from one end to the other, and whose vertices are
  exactly what that walk visits

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
- **`Graph.IsTwoConnected.ear`** — attaching a path whose two distinct ends
  lie in a 2-connected graph keeps it 2-connected
- **`Graph.IsTwoConnected.replace_edge_by_path`** — and replacing one of its
  edges by a path does too, which is subdivision
- `Graph.Reaches.reroute` and `.across_edge_replacement` — one edge swapped
  for any route between its ends; `Graph.IsConnected.after_edge_deletion`
  reads off the first
- `Graph.IsWalk.transfer` — a walk moves to any graph holding its edges
- `Graph.IsPath.split` — a path splits at any vertex it visits, and the
  far half never returns to the source
- `Graph.pathGraphOf.IsPathGraph` and `.IsWellFormed` — and so a path of a
  well-formed graph really is a path graph, ready to hand to
  `Graph.IsTwoConnected.ear`; `Graph.IsPath.vertexList_distinct` is what
  makes it well-formed, and `Graph.IsPath.transfer` moves the path down
- `Graph.IsWalk.crossing` — a walk from inside a set of vertices to
  outside it crosses the boundary along one of its edges
- **`Graph.IsTwoConnected.grows_by_ear`** (H5, in
  [relative_ear.math](relative_ear.math)) — a 2-connected subgraph that is
  not all of a 2-connected graph grows to a bigger one by adding an ear;
  `Graph.IsTwoConnected.ear_exists` finds the ear as a path
- `Graph.IsPath.distinct_edges` and `Graph.IsPath.length_le_size` — a path
  takes no edge twice, so it is no longer than the graph it runs in
- `Graph.longest_path` — and so a graph over an inhabited vertex type runs
  a path no shorter than any other (`Graph.HasPathOfLength` names the
  lengths that occur)
- `Graph.IsPath.chord_on_cycle` — an edge from a path's source to a vertex
  the path visits closes the piece between them into a cycle
- `Graph.IsAcyclic.longest_path_source_edge` — hence in an acyclic graph
  every edge at the end of a longest path is one of the path's own
- `Graph.IsPath.one_edge_at_source` — a path leaves its source once and
  for all, so two of its edges there are the same edge
- **`Graph.IsAcyclic.longest_path_source_is_leaf`** — and so a non-isolated
  end of a longest path in an acyclic graph has degree one
- **`Graph.degree_sum`** — the handshake lemma: the degrees of a
  well-formed graph's vertices add up to twice its number of edges, by
  the double count `Graph.incidence_sum` over the edge list
- `Graph.IsTree.has_leaf` — a tree on two or more vertices has one
- `Graph.IsLeaf.path_avoids` — a path whose ends are elsewhere never
  visits a vertex of degree one, so `Graph.IsTree.delete_leaf`: a tree
  minus a leaf is a tree
- **`Graph.IsTree.edge_count`** — and hence a tree has one edge fewer
  than it has vertices
- **`Graph.IsTree.three_leaves`** — a tree with exactly three leaves has a
  vertex of degree three; `Graph.leaves` / `Graph.innerVertices` name the
  two classes, and `Graph.IsConnected.degree_positive` says nothing in a
  connected graph on two or more vertices is isolated
- `Graph.IsPath.reverse` — a path runs backwards over the same vertices;
  `Graph.IsPath.extend_at_target` is what grows one at the far end
- `Graph.IsPathGraph.reaches_an_end` — whatever vertex is deleted, every
  remaining vertex of a path still reaches one of its two ends
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

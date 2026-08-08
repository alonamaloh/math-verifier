<!-- Generated 2026-08-08 by the part-one-wave-survey workflow (13 agents over
     ~/claude/schoenflies-lean + library/). Statuses are point-in-time: the survey ran
     while H6 bricks were still landing, so re-grep any single "missing" before building
     it (e.g. Set.Disjoint landed the same day and is PRESENT despite the T1.3 row).
     Standing consequences, folded into the plan:
     - T1.3 (region API / IsSeparating) runs FIRST: nine waves consume it, it consumes
       no other wave.
     - Two unscheduled chunks are now scheduled: lem:finite-polygonal-union (simple
       polygonal arc from a connected finite union; new wave T1.0b after the shared
       stubs) and SquareCycle/SquaresTwoConnected (attaches to T1.10).
     - The shared stubs above the per-wave lists are a build wave of their own (T1.0a),
       before any numbered wave. -->

# T1 ledger — Part I statement map

## T1.1 — parity of crossings, polygon parity (`Schoenflies/Parity.lean`, 1038 lines)

| Proposed math name | Blueprint label | Summary |
|---|---|---|
| `Plane.Vector.IsDirection` | setup of "The polygonal Jordan and crosscut theorems" | DEF: a direction is a unit vector; the ray direction is a parameter, so nothing is rotated back |
| `Plane.height` | — | DEF: how far ACROSS the direction a point lies (determinant of direction against `point − origin`) |
| `Plane.reach` | — | DEF: how far ALONG the direction a point lies (inner product of `point − origin` with direction) |
| `Plane.height_IsAffineCoordinate` / `Plane.reach_IsAffineCoordinate` | — | both frame coordinates are `IsAffineCoordinate`s, replacing Lean's `hgt_lin`/`fwd_lin` rewriting |
| `Plane.height_difference` / `Plane.reach_difference` | — | change between two points is det/inner against their difference vector; keeps `Plane.origin` out of proofs |
| `Plane.height_translate` / `Plane.reach_translate` | — | height and reach of `point + t * v` in terms of those of `point` |
| `Plane.height_along` / `reach_along` / `height_across` / `reach_across` | — | the four sweep equations for moving the base point along and across the direction |
| `Plane.equal_of_frame_coordinates` | — | equal height and equal reach against a direction ⇒ equal points |
| `Plane.frame_decomposition` | — | every vector is `reach * direction + height * perpendicular(direction)` |
| `Plane.absolute_reach_LessOrEqual_norm` / `absolute_height_LessOrEqual_norm` | — | each frame coordinate of a displacement is bounded by its norm |
| `Plane.levelMeet` | — | DEF: the point of the LINE through `a`, `b` at a given height, well defined when the ends differ in height |
| `Plane.height_levelMeet` | — | the level meet really sits at the requested height |
| `Plane.levelMeet_in_segment` | — | requested height between the two ends' heights ⇒ level meet lies on the closed segment |
| `Plane.levelMeet_unique` | — | a point of a non-level segment is the level meet at its own height |
| `Plane.levelMeet_reverse` | — | naming the segment's ends the other way round does not move the level meet |
| `Plane.levelMeet_of_subsegment` | — | cutting a non-level segment at an interior point moves neither half's level meet |
| `Plane.IsLevelFree` | — | DEF: no piece of the list has its two ends at the same height — the standing hypothesis, named |
| `Plane.IsLevelFree.ends_distinct` | — | a level-free piece is nondegenerate, as `Plane/Graph/subdivide.math` asks |
| `Plane.height_strictly_between_of_openSegment` | — | an interior point of a non-level segment is strictly between its ends in height |
| `Plane.Crosses` | — | DEF: the level line through `base` meets the piece strictly beyond `base` in reach, height test half-open below |
| `Plane.Crosses_reverse` | — | crossing is blind to the orientation of the piece; halves every min/max case split |
| `Plane.crossingCount` | π_C, "The polygonal Jordan and crosscut theorems" | DEF: the number of pieces of the list whose ray from the base point is crossed |
| `Plane.crossingCount_empty` / `_prepend` / `_append` | — | the three recursion equations of the count over the piece list |
| `Plane.SameCrossingParity` | — | DEF: the crossing parity read as a relation between two base points |
| `Plane.splitSegmentAt_IsLevelFree` / `splitAllAt_IsLevelFree` / `subdivide_IsLevelFree` | — | level-freeness survives one cut, one point across the list, and the whole `subdivide` |
| `Plane.crossingCount_splitSegmentAt` / `_splitAllAt` | — | cutting one piece, and cutting every piece at one point, changes no crossing count |
| `Plane.crossingCount_subdivide` | Lemma 2.1 (subdivision invariance) | subdividing a level-free list changes no crossing COUNT, for the whole `subdivide` operation |
| `Plane.IsClosedChain` | — | DEF: the boundary vanishes mod 2, stated by duality over ℕ-valued functions of the two ends |
| `Plane.IsClosedChain.empty` | — | the empty list is a closed chain |
| `Plane.edgeCycle` | — | DEF: the closed edge list of a cyclic vertex list, as an accumulator recursion beside `chainFrom` |
| `Plane.edgeCycle_IsClosedChain` | — | the edge list of a cyclic vertex list is a closed chain: each vertex counted twice |
| `Plane.IsClosedChain.splitAllAt` / `.subdivide` | — | closedness survives cutting: a cut point enters the boundary twice and cancels mod 2 |
| `Plane.piecesCover_complement_IsOpen` | — | the complement of what a finite list of segments occupies is open |
| `Plane.exists_ball_off_pieces` | — | a point off the pieces has a whole ball off them |
| `Plane.segment_along_direction` / `segment_across_direction` | — | membership characterisations of the two elementary moves |
| `Plane.reach_side_constant` | — | a segment inside a height band never meeting the level line stays on one side of it |
| `Plane.crossingCount_move_along` | — | moving the base point along the ray without meeting the polygon changes no crossing at all |
| `Plane.sweepMark` | — | DEF: the marker attached to a vertex when the base point is swept across by `s` |
| `Plane.sweep_mark_step` | — | one edge swept across: gained/lost crossings are the ends whose heights the sweep passes |
| `Plane.crossingParity_move_across` | — | sweeping across without meeting the polygon preserves the parity; the one use of closedness |
| `Plane.crossingParity_constant_on_ball` | — | the parity is constant on a ball that misses the polygon |
| `Plane.crossingParity_constant_on_connected` | Lemma 2.2, first half | π_C is constant on every connected subset of the complement of the polygon |
| `Plane.crossingParity_constant_on_component` | — | π_C is constant on the component of the complement containing a point |
| `Plane.crossingCount_zero_beyond` | — | beyond the polygon in the ray direction the count is ZERO |
| `Plane.crossingParity_flip` | Lemma 4.4, second half (also Lemma 2.2, second half) | across an interior point of an edge that no other edge meets, the parity changes by one |
| `Plane.exists_level_free_direction` | — | for any list of nondegenerate segments there is a direction level for none of them |

## T1.2 — two-sided polygonal strip (collar) and its constants (`Strip`/`StripConnected`/`StripConstants`/`StripLocal`, ~2.3k lines)

| Proposed math name | Blueprint label | Summary |
|---|---|---|
| `Plane.Vector.arc` | app:background, used throughout lem:polygonal-collar | DEF: the open arc of directions from `u` to `w`, as the SET form of `Counterclockwise` |
| `Plane.Vector.arc_of_signs` / `arc_reverse_of_sign` | — | under `det(u,w) > 0` the short arc is a conjunction of sign conditions and the long arc a disjunction |
| `Plane.Vector.arc_disjoint` | — | sign-free: `arc(r₁,r₂)` and `arc(r₂,r₁)` are disjoint when `det(r₁,r₂) ≠ 0` |
| `Plane.Vector.ray_or_arc` | — | sign-free exhaustion: a nonzero direction is a positive multiple of a bounding ray or lies on one arc |
| `Plane.Vector.arc_IsOpen` / `arc_scale` | — | an arc is open and invariant under positive rescaling, so arcs are sets of rays |
| `Plane.Vector.germs_split` | lem:polygonal-collar (the vertex matching) | THE VERTEX MATCHING, sign-free: both left germs lie on one arc and both right germs on the other |
| `Plane.Vector.arc_Ball_IsConnected` | — | an arc met with a ball about the origin is connected (short arc convex, long arc two half-planes) |
| `Plane.coordinateAlong` / `Plane.coordinateAcross` | — | DEF: progress along and signed distance across a directed edge; each affine and 1-Lipschitz |
| `Plane.frame_decomposition` / `Plane.distance_to_foot` | — | `x − a` split in the edge frame, and the distance to the perpendicular foot is `|coordinateAcross|` |
| `Plane.block` | lem:polygonal-collar ("a thin rectangular block around the straight core") | DEF: the open rectangle around a directed edge in the edge's own frame, with its topology |
| `Plane.sector` | lem:polygonal-collar ("a small closed disk about every vertex") | DEF: the open sector of radius `R` about a vertex spanned by a set of directions |
| `Plane.ClosedPolygon` | lem:polygonal-collar (the hypothesis) | DEF: a simple closed polygonal curve by cyclic vertex list — distinct vertices, simplicity, no redundant vertex |
| `Plane.ClosedPolygon.edge` / `carrier` / `length` / `tangent` / `incomingRay` / `offset` / `pointAt` | — | the edge-frame vocabulary of a closed polygon and its basic facts |
| `Plane.ClosedPolygon.carrier_IsCompact` / `.vertex_not_on_far_edge` | — | the carrier is compact; a vertex lies on no edge but the two incident to it (first use of simplicity) |
| `Plane.ClosedPolygon.trimmedEdge` / `.trimmed_disjoint_edge` | — | the trimmed core of an edge, compact and disjoint from every other edge (second use of simplicity) |
| `Plane.StripData` | lem:polygonal-collar ("the blocks may be chosen so that…") | THE CHOICE OF CONSTANTS as a structure: cone radius, trim, half-width, separations, germ threshold |
| `Plane.StripData.leftBlock` / `rightBlock` / `leftSector` / `rightSector` / `leftSide` / `rightSide` / `collar` | lem:polygonal-collar (N_L, N_R, N) | the four families of pieces and the three labelled sets |
| `Plane.StripData.leftSide_disjoint_carrier` / `rightSide_disjoint_carrier` | — | neither labelled side meets the curve |
| `Plane.StripData.sides_disjoint` | lem:polygonal-collar ("every point of N∖P receives exactly one label") | THE HARD HALF: the two sides are disjoint, in four sub-lemmas fed by `germs_split` at each corner |
| `Plane.IsConnected.cyclic_union` | — | a cyclically indexed family of connected sets with consecutive meets has connected union |
| `Plane.StripData.leftSide_IsConnected` / `rightSide_IsConnected` / `leftSide_IsOpen` / `rightSide_IsOpen` | lem:polygonal-collar ("the union of all left pieces is connected") | each side is open and connected, via explicit overlap points |
| `Plane.StripData.collar_difference_carrier` | lem:polygonal-collar (a) — N∖P = N_L ⊔ N_R | removing the curve from the collar leaves exactly the two labelled sides |
| `Plane.StripData.tube` / `collar_IsOpen` | — | the collar re-exhibited as vertex balls plus full edge tubes, hence open |
| `Plane.StripData.collar_within_thickening` | — | the collar lies inside the R-neighbourhood of the curve |
| `Plane.ClosedPolygon.exists_coneRadius` | lem:compact-separation, as consumed by lem:polygonal-collar (step 1) | step 1: one positive R below every edge length and separating all the compacta |
| `Plane.ClosedPolygon.exists_halfWidth` | lem:compact-separation, as consumed by lem:polygonal-collar (step 3) | step 3: one positive half-width separating trimmed edges and meeting the germ threshold |
| `Plane.ClosedPolygon.exists_stripData_inside` / `exists_stripData` | lem:polygonal-collar (the constants) | every simple closed polygon carries a `StripData`, with the collar inside any prescribed open set |
| `Plane.StripData.core_ball_trichotomy` | — | a small ball about a middle-stretch point splits by the SIGN of the transverse coordinate |
| `Plane.StripData.local_two_sided` | lem:polygonal-collar (the local-sides sentence) | LOCAL TWO-SIDEDNESS at an interior point of an edge |
| `Plane.StripData.exists_reference_points` | lem:polygonal-collar, consumed by lem:polygon-parity | THE TWO REFERENCE POINTS: a disk meeting the polygon only in one edge with a point of each side |
| `Plane.StripData.exists_near_sides` | — | every point of the polygon is approached from both sides (block away from a vertex, sector near one) |
| `Plane.StripData.carrier_subset_leftSide_Closure` / `_rightSide_Closure` | lem:polygonal-collar, consumed by thm:polygonal-jordan | every point of the polygon is in the closure of BOTH sides |
| `Plane.ClosedPolygon.exists_two_sided_collar` | lem:polygonal-collar (a) | THE HEADLINE: a simple closed polygon has a collar whose complement in it is two connected open sets |

## T1.3 — the separation predicate and the region API (`Schoenflies/CrosscutCells.lean`, 461 lines)

| Proposed math name | Blueprint label | Summary |
|---|---|---|
| `Plane.inside` | Definition 2.4 (Int(C)) | DEF: the union of the bounded components of the complement, for an ARBITRARY set |
| `Plane.outside` | Definition 2.4 (Ext(C)) | DEF: the union of the unbounded components of the complement |
| `Plane.IsSeparating` | Definition 2.4 | DEF: Jordan curve, both halves nonempty and connected, each with the curve as boundary — right-nested |
| `Plane.IsRegionOf` | — | DEF: "this is one of the two regions", so each region lemma is stated once |
| `Plane.IsRegionPair` | — | DEF: the inside and the outside in one order or the other |
| `Plane.inside_subset_complement` / `outside_subset_complement` | — | each half of the complement lies in the complement |
| `Plane.inside_union_outside` | — | the two halves partition the complement; the only classical step in the file |
| `Plane.inside_outside_Disjoint` | — | the inside and the outside are disjoint |
| `Plane.Component_subset_inside` | — | the inside is a union of WHOLE components (boundedness is constant along a component) |
| `Plane.inside_IsOpen` | — | for closed `curve` the inside is open; twin for the outside |
| `Plane.IsSeparating.IsClosed` | — | a separating curve is closed; the most-cited accessor downstream (85 Lean sites) |
| `Plane.IsSeparating.inside_IsBounded` | — | the inside of a separating curve is bounded — a consequence, not a hypothesis |
| `Plane.IsSeparating.outside_IsUnbounded` | — | the outside of a separating curve is unbounded |
| `Plane.IsSeparating.Component_equals_inside` | — | the inside really is ONE component, not merely a union of them; twin for the outside |
| `Plane.IsSeparating.Component_IsRegionOf` | — | every component of the complement is one of the two regions |
| `Plane.IsRegionOf.inside` / `.outside` | — | the two constructors |
| `Plane.IsRegionOf.subset_complement` | — | a region misses the curve |
| `Plane.IsRegionOf.IsOpen` | — | a region of a separating curve is open |
| `Plane.IsRegionOf.IsConnected` | — | a region of a separating curve is connected and nonempty |
| `Plane.IsRegionOf.Component_equals` | — | a region is the component of each of its points |
| `Plane.IsRegionOf.Boundary_equals` | — | a region has the curve as its boundary (29 downstream citation sites) |
| `Plane.IsRegionOf.curve_subset_Closure` | — | every point of the curve is a limit of points of the region (33 downstream sites) |
| `Plane.IsRegionOf.Closure_equals` | — | `Closure(region) = region ∪ curve` |
| `Plane.IsRegionPair.left` / `.right` / `.symmetric` | — | each member of a pair is a region, and the pair reverses |
| `Plane.IsRegionPair.union_equals` | — | the two regions cover the complement |
| `Plane.IsRegionPair.Disjoint` | — | the two regions are disjoint |
| `Plane.IsRegionPair.swallows_connected` | — | a nonempty connected set off the curve and off one region lies in the other |
| `Plane.IsSeparating.exists_IsRegionPair_containing` | — | a nonempty connected set off the curve lies in one of the two regions; returns the PAIR |
| `Plane.absorption_of_curve_in_Closure` | Lemma 2.5, set-theoretic core | pure point-set core of absorption, with no separation hypothesis |
| `Plane.IsSeparating.absorption` | Lemma 2.5 (absorption) | a region of `C` inside a region of `J` swallows all of `C` off `J` |
| `Plane.crosscut_cell_Disjoint_curve` | — | the near cell misses `C` entirely |
| `Plane.crosscut_cell_subset_region` | Lemma 2.6 (a), first half | the cell `V` is contained in `Ω ∖ P` |
| `Plane.crosscut_cell_IsComponent` | Lemma 2.6 (a) | the cell `V` is a connected component of `Ω ∖ P` |
| `Plane.crosscut_cell_Closure_meets_curve` | Lemma 2.6 (c) | `Closure(V) ∩ C = J ∩ C` |
| `Plane.IsJordanCurve.of_arc_and_crosscut` | — | two arcs meeting only at their shared endpoints glue to a Jordan curve |
| `Plane.two_arcs_distinct` | Lemma 2.6 (b), arc side | the two arcs of `C` from `p` to `q` are distinct |
| `Plane.crosscut_cells` | Lemma 2.6 (crosscut cells), bundled | the full statement, stated WITHOUT the arc hypotheses that the proof never uses |

## T1.4 — polygonal-jordan, H7 (`PolygonBridge` 618, `Bounded` 76, `PolygonalJordan` 626)

| Proposed math name | Blueprint label | Summary |
|---|---|---|
| `Plane.segments_meet_only_at_shared_end` | (unlabelled; PolygonBridge) | two segments sharing an endpoint, with far ends off the other's line, meet nowhere but there |
| `Plane.Polygon.triangle` | §1 non-vacuity of "simple closed polygonal curve" | DEF: three points with nonzero orientation determinant form a `Plane.Polygon` |
| `Plane.Polygon.unitTriangle` | §1 non-vacuity | DEF: the concrete triangle (0,0), (1,0), (0,1) |
| `Plane.Polygon.vertex_distinct_below_modulus` | — | distinct cyclic indices below the modulus name distinct vertices |
| `Plane.Polygon.edge_meets_earlier_at_own_initial_vertex` | — | an edge meets any strictly earlier edge only at its own initial vertex |
| `Plane.Polygon.last_edge_meets_earlier_at_ends` | — | the last edge meets earlier edges at vertex 0 or at its own initial vertex — this closes the curve |
| `Plane.Polygon.edgeList` | — | DEF: the m+3 edges as a list of endpoint pairs in cyclic order |
| `Plane.Polygon.edgeList_basics` | — | member/invert/nondegenerate/distinct: the four reader lemmas the parity layer asks for |
| `Plane.telescoping_boundary_sum` | — | the mod-2 boundary of the chain 0→1→…→n is the sum of its two ends |
| `Plane.Polygon.edgeList_IsClosedChain` | lem:polygon-parity prerequisite | the edge list is a closed chain; the cycle closes because the modulus is zero in the index ring |
| `Plane.Polygon.cover_edgeList_eq_carrier` | — | the edge list occupies exactly the polygon's carrier |
| `Plane.Polygon.carrier_IsJordanCurve` | §1, "a simple closed polygonal curve" | the carrier of a simple closed polygon is a Jordan curve, by growing partial chains |
| `Plane.Polygon.carrier_IsPolygonal` | §1, "a finite union of line segments" | the carrier is polygonal: the chain of the vertex list once round the cycle |
| `Plane.Polygon.exists_admissible_direction` | "rotate so that no edge is horizontal" | there is a unit ray direction level for no edge |
| `Plane.Polygon.crossingParity_constant_on_Component` | lem:polygon-parity, first half | π_C is constant on the component of the complement of the CARRIER |
| `Plane.Polygon.point_off_other_edges_of_member_openSegment` | — | an interior point of one edge lies on no other edge |
| `Plane.Polygon.crossingParity_flips_across_edge` | lem:polygon-parity, second half | just before and just after an interior point of an edge the parity differs by one |
| `Plane.beyondSquare_complement_square` | — | the outside of a square IS the complement of the closed square, as a SET equation |
| `Plane.IsCompact.inside_square` | — | a compact set sits inside a square about the origin, with the nonempty hypothesis discharged |
| `Plane.Polygon.carrier_topology_basics` | — | the carrier is closed, its complement open, and it is nonempty |
| `Plane.Polygon.determinant_tangent_direction_nonzero` | — | no edge is parallel to an admissible ray direction |
| `Plane.Polygon.exists_opposite_parity_across_edge` | thm:polygonal-jordan, "the two reference points have opposite parity" | the two tracks of the collar carry different parities, witnessed at an edge midpoint |
| `Plane.Polygon.crossingParity_constant_on_leftSide` | — | the crossing parity is constant on each track of the collar |
| `Plane.Polygon.crossingParity_differs_on_sides` | — | the two tracks have opposite parity whichever points are chosen |
| `Plane.Polygon.Component_differs_on_sides` | thm:polygonal-jordan, "at least two regions" | a point of each track lies in a different component of the complement |
| `Plane.Polygon.exists_side_point_in_same_Component` | thm:polygonal-jordan, "at most two regions" | every point of the complement is in the component of a point of one of the two tracks |
| `Plane.Polygon.Component_is_left_or_right` | — | every complement point lies in the component of one of two FIXED reference points |
| `Plane.inside_outside_of_two_components` | — | PACKAGING: with two components, the one swallowing the outside of a square is `Plane.outside` |
| `Plane.Component_BoundaryIn_eq_of_subset_Closure` | Appendix C item 5 (one inclusion) | a component of the complement of a closed set has that set as its boundary |
| `Plane.IsSeparating.of_two_components` | — | PACKAGING: two distinct exhausting components with the curve in their closures make it separating |
| `Plane.Polygon.carrier_IsSeparating` | thm:polygonal-jordan (H7), in the def:separating form | THE WAVE'S THEOREM: the carrier of a simple closed polygon is a separating Jordan curve |
| `Plane.Polygon.Component_is_inside_or_outside` | — | "exactly two regions", explicitly |
| `Plane.Polygon.crossingParity_zero_on_outside` | thm:polygonal-jordan, last sentence | π_C = 0 on the unbounded region, for every admissible ray direction |
| `Plane.Polygon.crossingParity_one_on_inside` | thm:polygonal-jordan, last sentence | π_C = 1 on the bounded region |
| `Plane.Polygon.polygonal_jordan` | thm:polygonal-jordan, unfolded | the same theorem with `IsSeparating` unfolded, for a reader who wants it without the definition |
| `Plane.Polygon.unitTriangle_IsSeparating` | — | NON-VACUITY: the whole chain applies to the one polygon the development constructs |
| `Plane.exists_far_along_direction_beyond_square` | — | HELPER: a point far along the ray direction and outside a prescribed square |

## T1.5 — parity splitting, polygonal crosscut, alternating crosscuts (`ParitySplitting` 576, `PolygonalCrosscut` 645, `AlternatingCrosscuts` 260)

| Proposed math name | Blueprint label | Summary |
|---|---|---|
| `Plane.SameSegments` | (definition inside lem:parity-splitting) | DEF: two segment lists carry the same edges — permutation after `orientSegment`, with its algebra |
| `Plane.SameSegments.of_permutation_reversed` | — | the single-step absorber for a curve traversing the crosscut backwards |
| `Plane.SameSegments.crossingParity_equal` / `.piecesCover_equal` / `.exists_member` / `.transverse_transfer` | — | count, occupied set, membership and non-levelness are all invariants of `SameSegments` |
| `Plane.crossingMark_reverse` | — | a segment's contribution is orientation-blind, with NO non-levelness hypothesis |
| `Plane.crossingParity_permutation` / `piecesCover_permutation` / `crossingMark_orientSegment` / `crossingParity_orientSegments` | — | reordering and canonically orienting the edges change neither count nor covered set |
| `Plane.IsChainBetween` | — | DEF: the open-path companion of `IsClosedChain` — the mod-2 boundary is exactly the two named ends |
| `Plane.IsChainBetween.IsClosedChain_append` | — | two chains with the same two ends close up |
| `Plane.pathSegments` | — | DEF: the edge list of a polyline, with its boundary and cover lemmas |
| `Plane.ClosedPolygon.arcSegments` | (the arcs A₁, A₂ of lem:parity-splitting) | DEF: the edge list of the arc leaving vertex `a` running `k` edges, exported as an object |
| `Plane.ClosedPolygon.IsChainBetween_arcSegments` | — | an arc is a chain from its first vertex to its last |
| `Plane.ClosedPolygon.arcSegments_split_permutation` | — | the two arcs at `a` and `a+k` use every edge of `C` exactly once |
| `Plane.ClosedPolygon.carrier_equal_of_SameSegments` / `.not_member_carrier_of_SameSegments` | — | the bridge back to sets: "off C and off P" is "off Jᵢ", from the edge lists alone |
| `Plane.crossing_parity_split` | lem:parity-splitting / eq:parity-splitting | parity splitting in pure edge-list form, with no geometry: the crosscut is counted twice and cancels |
| `Plane.ClosedPolygon.parity_splitting` | lem:parity-splitting | the same identity for a simple closed polygon cut at two vertices, with no hypothesis on the crosscut |
| `Plane.ClosedPolygon.parity_odd_iff_inside` | thm:polygonal-jordan (last sentence, as a criterion) | off the polygon, the crossing count is odd exactly on the bounded region |
| `Plane.ClosedPolygon.crosscut_inside_exactly_one` / `.crosscut_outside_agree` | lem:parity-splitting (the "Consequently") | a point of Int(C) is inside exactly one of J₁, J₂; a point of Ext(C) inside both or neither |
| `Plane.farRegion` | thm:polygonal-crosscut (Ω†, Vᵢ, Wᵢ) | DEF: the region of ℝ²∖C not containing a reference point, so Theorem 2.8 is proved once |
| `Plane.IsSeparating.IsRegionPair_farRegion` / `.farRegion_equal_inside` / `.farRegion_equal_outside` | — | the two rewrites that read the blueprint's cases (a) and (b) off the uniform theorem |
| `Plane.ClosedPolygon.arc` | thm:polygonal-crosscut (A₁, A₂) | DEF: the arc as a SET, with arc union and carrier equations |
| `Plane.ClosedPolygon.parity_distinct_iff_member_farRegion` | thm:polygonal-jordan (as a separation criterion) | two complement points lie in different regions precisely when their counts differ |
| `Plane.ClosedPolygon.vertex_member_arc` / `.vertex_shifted_member_arc` / `.endpoints_subset_arc` / `.endpoints_subset_other_arc` | — | the two cut vertices lie on BOTH arcs |
| `Plane.IsPolygonalCrosscut` | thm:polygonal-crosscut (hypotheses) | DEF: the bundled setting — seven fields — with `.of_endpoints` as the front door and `.symmetric` |
| `Plane.IsPolygonalCrosscut` elementary readers | — | not-member, carrier, subset and nondegeneracy readers, plus a direction transverse to everything |
| `Plane.IsPolygonalCrosscut` cell facts | lem:crosscut-cells | region pairs, near-region inclusion, cell inclusion, cells as components, frontiers, closures |
| `Plane.IsPolygonalCrosscut.separates_exactly_one` | thm:polygonal-crosscut (exhaustion) | a point is separated from `y` by `C` exactly when separated by exactly one of J₁, J₂ |
| `Plane.IsPolygonalCrosscut.region_split` / `.cells_disjoint` / `.cells_distinct` / `.cell_distinct_from_near_first` | thm:polygonal-crosscut | the entered region minus the crosscut is the disjoint union of the two cells |
| `Plane.IsPolygonalCrosscut.complement_split` / `.near_IsComponent` / `.frontier_near` / `.cell_IsComponent_complement_first` / `.three_regions` | thm:polygonal-crosscut | ℝ²∖(C∪P) has exactly three regions, each a component, with frontiers J₁, J₂, C |
| `Plane.IsPolygonalCrosscut.inside_difference` | thm:polygonal-crosscut (a) | case (a): a crosscut inside C splits Int(C)∖P into Int(J₁) ∪ Int(J₂), disjointly |
| `Plane.IsPolygonalCrosscut.outside_difference` / `.inside_exactly_one` | thm:polygonal-crosscut (b) | case (b): Ext(C)∖P is the two far regions, and Int(C) lies inside exactly one of J₁, J₂ |
| `Plane.polygonal_crosscut` | thm:polygonal-crosscut | Theorem 2.8, bundled |
| `Plane.IsArcBetween.IsConnected_without_endpoints` / `.start_in_Closure_without_endpoints` / `.finish_in_Closure_without_endpoints` / `.nonempty_without_endpoints` | — | the interior of an arc is connected, nonempty, and has both endpoints in its closure |
| `Plane.IsPolygonalCrosscut.Component_piecesCover_equal` | — | the entered region is the component of ℝ²∖C containing any crosscut point off C |
| `Plane.IsPolygonalCrosscut.meets_crosscut` | cor:alternating-crosscuts (core form) | a connected set on the same side with alternating closure points must meet the crosscut |
| `Plane.IsPolygonalCrosscut.arc_meets_crosscut` | cor:alternating-crosscuts | the same with the second crosscut presented as a simple arc; the meeting is in its INTERIOR |
| `Plane.IsPolygonalCrosscut.alternating_meets_crosscut` (+ `_of_same_component`, `_inside`, `_outside`) | cor:alternating-crosscuts | the packaged forms, verbatim the data a K₃,₃ configuration returns |
| `Plane.alternating_crosscuts` | cor:alternating-crosscuts | the corollary bundled, with the two hypotheses the Lean proof shows are never used dropped |

## T1.6 — realization theorems (`Realization` 1600, `PrePolygonSep` 519, `PolyArcRealize` 740)

| Proposed math name | Blueprint label | Summary |
|---|---|---|
| `Plane.PrePolygon` | §1 ("simple closed polygonal curve presented by a vertex list") | DEF: `ClosedPolygon` minus the `corner` field — redundant (collinear) vertices allowed |
| `Plane.PrePolygon.edge` / `.carrier` | — | the edge leaving vertex `i`, the carrier, and their basic membership lemmas |
| `Plane.ClosedPolygon.forgetCorner` | — | a `ClosedPolygon` read as a `PrePolygon` (the forgetful map) |
| `Plane.PrePolygon.rotate` / `.carrier_rotate` | — | the same polygon read from vertex `a` onwards; rotating does not move the carrier |
| `Plane.PrePolygon.deleteLastVertex` / `.carrier_deleteLastVertex` | Lemma 1.8, opening move | deleting a redundant vertex: simplicity survives and the carrier is unchanged |
| `Plane.PrePolygon.redundant_vertex_inside_neighbour_segment` | — | a vertex with zero determinant lies in the OPEN segment joining its two neighbours |
| `Plane.PrePolygon.triangle_has_no_redundant_vertex` | — | a three-vertex `PrePolygon` has no redundant vertex — the base case of normalization |
| `Plane.PrePolygon.exists_closedPolygon` | Lemma 1.8 (normalization) | every `PrePolygon` normalizes to a `ClosedPolygon` with the same carrier |
| `Plane.exists_prePolygon_of_vertex_family` | — | assembling a cyclic family of ≥3 points into a `PrePolygon` — the index-arithmetic adaptor |
| `Plane.IsCleanPresentation` | lem:polygonal-overlay (Lemma 3.7), combinatorics dropped | DEF: pieces cover the set, none degenerate, no end interior to a piece, disjoint interiors |
| `Plane.exists_clean_presentation` | lem:polygonal-overlay | every polygonal set holding two distinct points has a clean presentation with prescribed cut points |
| `Plane.nearPiece` / `.nearPiece_IsOpen` | — | the plane-open set isolating one piece from the others |
| `Plane.IsCleanPresentation.pieces_meet_at_ends` | — | two distinct clean pieces meet only at ends of the first |
| `Plane.IsCleanPresentation.without_ends_is_union_of_interiors` | — | the curve minus the piece ends is the union of the piece interiors |
| `Plane.IsCleanPresentation.exists_ball_inside_piece` | — | near an interior point of a piece the curve IS that piece |
| `Plane.IsCleanPresentation.connected_subset_inside_one_piece` | — | a connected subset of the curve away from the ends lies inside a single piece interior |
| `Plane.increasingParameters` (`parameterAt` / `nextParameter`) | — | DEF: a finite list of reals in strictly increasing order, with its full order API |
| `Plane.exists_containing_gap` | — | the gaps tile `[0,1)` minus the parameters: every parameter-free point lies in exactly one |
| `Plane.exists_prePolygon_of_IsJordanCurve` | §1 | a polygonal Jordan curve is the carrier of a cyclic vertex list — the 270-line core |
| `Plane.exists_closedPolygon` | §1 — the realization theorem | every set-level simple closed polygonal curve is the carrier of a `ClosedPolygon` |
| `Plane.IsStraightAt` / `Plane.IsCornerAt` | — | DEF: the curve runs straight through a point; a corner is where it does not |
| `Plane.ClosedPolygon.exists_vertex_at_corner` | — | every corner is a vertex |
| `Plane.ClosedPolygon.vertex_IsCornerAt` | — | every vertex is a corner — so the vertex set of a realization is exactly the corner set |
| `Plane.exists_closedPolygon_with_corners` | — | the realization theorem with any finite list of corners required among the vertices |
| `Plane.exists_closedPolygon_split` | — | the realization theorem tracking a splitting at two corners |
| `Plane.ClosedPolygon.rotate` / `.arc_is_chain` / `.arc_IsArcBetween` / `.arc_intersection` | — | the two arcs of a splitting, as arcs of the polygon |
| `Plane.IsArcBetween.interior_IsConnected` | — | the interior of an arc is connected and nonempty |
| `Plane.two_arcs_unique` | — | two points cut a Jordan curve into two arcs in only one way |
| `Plane.exists_closedPolygon_arcs` | — | the realization theorem tracking a splitting, with the two arcs identified |
| `Plane.exists_closedPolygon_arcs_ordered` | — | the same with the disjunction moved onto the two cut vertices — the shape `IsHexRealization` asks for |
| `Plane.PrePolygon.pieces` | — | the m+3 edges of an unnormalized polygon as a list, with its six reader lemmas |
| `Plane.PrePolygon.carrier_IsCompact` / `_IsClosed` / `_IsJordanCurve` / `_IsPolygonal` | — | carrier properties, each three lines: normalize and quote the `ClosedPolygon` version |
| `Plane.PrePolygon.carrier_IsSeparating` | thm:polygonal-jordan, in the Definition 2.4 form | the polygonal Jordan curve theorem for a presentation with redundant vertices |
| `Plane.PrePolygon.component_is_inside_or_outside` | — | exactly two regions |
| `Plane.parity_zero_of_outside_cover` | Theorem 2.3, last sentence | for ANY separating closed chain, the crossing parity is 0 on the unbounded region |
| `Plane.parity_one_of_inside_cover` | Theorem 2.3, last sentence | for any separating closed chain with two differing complement points, the parity is 1 inside |
| `Plane.PrePolygon.vertex_off_other_edges` | — | an interior point of one edge lies on no other edge |
| `Plane.PrePolygon.exists_direction_off_pieces` / `parity_constant_on_component` / `parity_flip_carrier` / `exists_parity_ne` | Lemma 2.2 | a level-free direction, parity constancy, the flip across an edge, and two differing points |
| `Plane.PrePolygon.parity_zero_of_outside` / `parity_one_of_inside` / `parity_one_iff_inside` / `parity_zero_iff_outside` | Theorem 2.3 | the two parity values and the two criteria, re-derived from separation, NOT transported |
| `Plane.exists_injective_extension` | — | a vertex family injective on an initial segment extends to a globally injective sequence |
| `Plane.skipIndex` | — | the index map skipping one vertex, with injectivity, successor and avoidance lemmas |
| `Plane.PreArc` | — | DEF: a simple polygonal arc by vertex list with redundant vertices allowed |
| `Plane.PreArc.deleteVertex` / `.carrier_deleteVertex` | Lemma 1.8, opening move (arc case) | delete a collinear vertex; carrier and both extreme vertices unchanged |
| `Plane.PreArc.exists_polyArc` | — | every `PreArc` normalizes to a `PolyArc` with the same carrier and same extreme vertices |
| `Plane.exists_preArc_of_IsArcBetween` | — | a simple polygonal arc is the carrier of a vertex list, on a linear index |
| `Plane.IsPolyArcCarrier_of_IsPolygonal` | — | THE REALIZATION THEOREM FOR ARCS, discharging `ArcCollars`' presentation hypothesis |
| `Plane.hasArcCollars_of_IsPolygonal` | lem:polygonal-collar (Lemma 1.8 (b)) | Lemma 1.8 (b) for a set-level simple polygonal arc; lands with T1.12 |
| `Plane.crosscut_at_most_two_of_IsPolygonal` / `crosscut_components_exhaust_of_IsPolygonal` / `IsCrosscut.hasArcCollars` | lem:crosscut-at-most-two, thm:general-crosscut | the collar hypothesis discharged at the call sites; T1.12-side |

## T1.7 — k33-face-cycles, H8 (`K33Land` 893, `FaceCyclesProof` 970, `FaceCyclesLand` 457, plus unassigned modules)

| Proposed math name | Blueprint label | Summary |
|---|---|---|
| `Plane.PrePolygon` | (supports thm:polygonal-crosscut) | DEF: a closed polygonal presentation WITHOUT the corner condition — the structure this wave runs on |
| `Plane.PrePolygon.arcPieces` / `.arc` | §1 realization | the edge list of a forward stretch and the point set it covers |
| `Plane.PrePolygon.arc_IsArcBetween` | — | a stretch of at least one and at most all-but-one edge is an arc between its end vertices |
| `Plane.PrePolygon.arc_union` / `.arc_intersection` / `.arc_not_inside_endpoints` | — | the two stretches cover the carrier, meet exactly in the cut vertices, neither is just two points |
| `Plane.PrePolygon.isPolygonal_arc` | — | every stretch of a `PrePolygon` is a polygonal set |
| `Plane.PrePolygon.insertLast` | — | a point interior to an edge can be made a vertex — the crux the wave turns on |
| `Plane.exists_prePolygon_vertices` | §1 realization | a polygonal Jordan curve has a `PrePolygon` presentation with prescribed points among the vertices |
| `Plane.exists_prePolygon_split` | §1 realization | the same cut at two prescribed points, with NO corner condition on them |
| `Plane.PrePolygon.reverse` (+ `.reverse_arc`, `.sameEdges_reverse_arcPieces`) | — | the presentation traversed the other way — pins the direction of a prescribed arc |
| `Plane.PrePolygon.exists_splice` | — | two chains with the same ends lay end to end into a `PrePolygon` whose edge list is the concatenation |
| `Plane.exists_prePolygon_arcs` / `_oriented` | §1 realization, splitting-tracking | realization tracking a prescribed splitting, first unordered then with order and direction pinned |
| `Plane.two_arcs_unique_of_closed` | — | the two-arc decomposition is determined, the competitor known only to be closed and nondegenerate |
| `Plane.IsArcBetween.endpoints_distinct` | — | an arc between two named points has distinct endpoints |
| `Plane.IsArcBetween.eq_of_subset` | — | an arc inside an arc with the same ends is the whole of it |
| `Plane.IsArcBetween.exists_polyline_presentation` | — | a polygonal arc is the chain of a vertex list running end to end |
| `Plane.IsPrePolygonalCrosscut` | thm:polygonal-crosscut | DEF: the crosscut setting with the cut points unrestricted |
| `Plane.IsPrePolygonalCrosscut.of_endpoints` | — | the front door: the crosscut meets C exactly in its two endpoints, which are the cut vertices |
| `Plane.IsPrePolygonalCrosscut.region_eq` (+ `.cell_subset`, `.cell_IsComponent`, `.closure_cell_intersection`, `.separates_xor`) | thm:polygonal-crosscut | the crosscut replaces the reference region by exactly two cells with the expected closures |
| `Plane.IsPrePolygonalCrosscut.alternating_intersection_nonempty_of_same_side` | cor:alternating-crosscuts | two crosscuts with alternating ends must meet, with split points anywhere on the curve |
| `Plane.crosscut_splits_region` | thm:polygonal-crosscut (exhaustion clause) | THE KEYSTONE: every component of the region minus P is a region of A₁∪P or of A₂∪P |
| `Plane.Component.after_removal` | — | cutting inside one component sees only that component |
| `Plane.chainFrom_append` / `Plane.chainFrom_append_joined` | — | appending two vertex lists joins their chains by one segment, which collapses at a shared seam |
| `Graph.IsPath.append` | — | two paths meeting only at the junction concatenate into a path |
| `Graph.IsPath.split_at_visited` | — | a path splits at a visited vertex into two paths sharing only it |
| `Graph.IsCycleThrough.split_at` | combinatorial half of "the ear is a crosscut" | a cycle cut at two vertices is two paths using every edge once and meeting only there |
| `Graph.exists_spliced_cycle` | — | the cycle an ear splices onto an arc of the old cycle, with its edge list named |
| `Plane.Graph.IsDrawing.pointSet_pathGraphOf` / `.pointSet_cycleGraph` | — | the subgraph spanned by a nonempty walk occupies exactly what its edges draw |
| `Plane.Graph.IsDrawing.exists_polyline_edgesCover` | — | a walk with polygonal edges draws the chain of a single vertex list |
| `Plane.Graph.IsDrawing.cycle_IsSeparating` | thm:polygonal-jordan applied | the realisation of a cycle of a polygonal plane graph is a SEPARATING Jordan curve |
| `Plane.Graph.IsDrawing.arcs_of_split` | — | a cycle cut at two vertices realises as two arcs meeting exactly in those two points |
| `Plane.Graph.IsFaceCycle` (+ `.frontier_eq`, `.eq_inside_or_outside`, `.eq_inside_of_IsBounded`, `.in_supergraph`) | lem:face-cycles, at one face | DEF: a face with a named separating cycle of which it is one of the two regions |
| `Plane.Graph.HasFaceCycles` | — | every face of the plane graph has such a cycle |
| `Plane.Graph.IsDrawing.hasFaceCycles_cycleGraph` | — | the base case: both faces of a single cycle are its two regions |
| `Plane.Graph.IsDrawing.hasFaceCycles_after_ear` | — | one ear: face cycles survive enlarging a 2-connected subgraph by an ear |
| `Plane.Graph.face_cycles` | lem:face-cycles | HEADLINE 1: every face of a finite 2-connected polygonal plane graph is a region of a boundary cycle |
| `Plane.Graph.IsPreHexagonCrosscut` / `IsK33Configuration.isPreHexagonCrosscut` | lem:k33, the crosscut step | the hexagon cut at the ends of a remaining edge, realized as a `IsPrePolygonalCrosscut` |
| `Plane.Graph.IsK33Configuration.absurd_of_isPreHexagonCrosscut` | — | two consecutive remaining edges cannot lie in one region: alternating crosscuts forces them to meet |
| `Plane.Graph.IsK33Configuration.absurd_of_polygonal` | — | lem:k33 for a drawing that is already polygonal |
| `Plane.Graph.IsK33Configuration.no_drawing` | lem:k33 | HEADLINE 2 (H8): a finite graph carrying a copy of K(3,3) has no plane drawing |
| `Plane.IsArcK33.absurd` | lem:k33 for nine arcs | no nine arcs in the plane meet only where K(3,3) forces them to |
| `Plane.Graph.IsK33Subdivision.absurd` | cor:k33-subdivision | no subdivision of K(3,3) has a plane drawing |
| `Plane.Graph.k33Graph_no_drawing` | lem:k33 for the concrete graph | the concrete K(3,3) on six distinct plane points has no plane drawing |

## T1.8 — H9, the outer-chain lemma (`OuterChain` 791, `CrosscutExists` 491, `CrosscutEncloses` 552, `OuterChainClosed` 56)

| Proposed math name | Blueprint label | Summary |
|---|---|---|
| `Graph.IsPath.split_at_edge` | — | a path cut at one of its edges, with the two freshness clauses |
| `Graph.IsCycleThrough.rotate` | — | a cycle re-presented through any one of its edges |
| `Graph.IsCycleThrough.edge_is_edge` | — | every edge on a cycle is an edge of the graph |
| `Graph.IsCycleThrough.ends_are_visited` | — | both ends of any cycle edge are visited by the detour walk |
| `Graph.IsCycleThrough.transfer` / `.in_supergraph` | — | a cycle moves down into a subgraph holding its edges and up into a supergraph |
| `Graph.IsCycleThrough.split_at_two_edges` | lem:outer-chain ("the two arcs of C from a to b are internally disjoint") | two distinct cycle edges cut it into two arcs with disjoint vertex sets covering the cycle |
| `Graph.IsCycleCrosscut` | — | DEF: the bundled crosscut of a cycle — twelve clauses in Lean |
| `Graph.exists_spliced_cycles` | — | the two cycles a crosscut splices, with edge lists named as permutations |
| `Graph.foreignEdges` / `Graph.foreignEdgeCount` | — | DEF: the edges of a list a graph does not have, and the count the descent decreases |
| `Graph.foreignEdgeCount_splice_shrinks` | lem:outer-chain ("fewer edges outside Γ(j−1) than C") | replacing an arc that carried a foreign edge strictly lowers the count |
| `Graph.exists_cycle_crosscut` | lem:outer-chain (the minimality paragraph) | a minimum-length path of F from one side to the other is a crosscut; all four clauses from one minimisation |
| `Plane.two_arcs_meet_at_ends` | — | two arcs with the same ends whose union is a Jordan curve meet exactly at those ends |
| `Plane.crosscut_inside_one_side` | thm:polygonal-crosscut (at the level of sets) | a point inside J and off P is inside A₁∪P or A₂∪P, uniformly, with NO case split |
| `Plane.Graph.Encloses` | lem:outer-chain ("that face is the interior of its boundary cycle") | DEF: some cycle of the graph has the point inside its realisation; monotone in the graph |
| `Plane.Graph.face_IsBounded_of_Encloses` | — | an enclosed point off the drawing has a bounded face |
| `Plane.Graph.Encloses_of_face_IsBounded` | lem:face-cycles (consumed) | the converse for a finite 2-connected polygonal plane graph |
| `Plane.Graph.exists_cycle_with_fewer_foreign_edges` | — | the last mile of the descent step, once one spliced cycle is known to enclose |
| `Plane.Graph.IsDrawing.walkVertices_in_edgesCover` | — | every vertex a nonempty walk visits lies on what the walk draws |
| `Plane.Graph.crosscut_encloses_one_side` | lem:outer-chain ("one of R∪C₁, R∪C₂ encloses x") | THE REPAIRED GEOMETRIC HALF: the `x ∈ exterior` clause is load-bearing (Lean finding 19) |
| `Plane.Graph.chainBlock` | — | DEF: `Γ i ∪ ⋯ ∪ Γ (i+m)`, indexed by LENGTH so the minimality is a plain strong induction |
| `Plane.Graph.chainBlock_IsTwoConnected` | lem:union-two-connected (iterated) | a block of 2-connected graphs with consecutive shared vertex pairs is 2-connected |
| `Plane.Graph.IsPlaneChain` | — | DEF: the hypotheses of lem:outer-chain as a structure over one ambient plane graph |
| `Plane.Graph.IsPlaneChain.blocks_meet_only_through_neighbour` | — | "Γ j meets the earlier chain only through Γ (j−1)" — the only geometry the combinatorial half uses |
| `Plane.Graph.InOuterFaceOnPairs` | — | DEF: x is in the outer face of every consecutive pair |
| `Plane.Graph.IsPlaneChain.exists_descent_crosscut` | lem:outer-chain (combinatorial half of the crosscut paragraph) | build a crosscut of the block's cycle inside Γ (i+m+1) |
| `Plane.Graph.IsPlaneChain.descent_step` | lem:outer-chain (the middle paragraph) | one descent step: strictly fewer edges outside Γ (i+m+1), with the exterior clause supplied locally |
| `Plane.Graph.IsPlaneChain.no_block_encloses` | — | the double minimal-counterexample argument: no block of the chain encloses x |
| `Plane.Graph.IsPlaneChain.point_off_chain` | — | x is off the whole chain's drawing |
| `Plane.Graph.outer_chain` | lem:outer-chain | H9, WITH NOTHING ASSUMED — the wave's single public interface |

## T1.9 — strong accessibility; accessible endpoints (`Accessible` 267, `AccessibleJoin` 429)

| Proposed math name | Blueprint label | Summary |
|---|---|---|
| `Plane.StronglyAccessible` | Definition 8.1 (strong accessibility) | DEF: an open disk inside D with p on its boundary circle |
| `Plane.StronglyAccessible.mono` | — | strong accessibility passes to a larger set |
| `Plane.StronglyAccessible.center_in_region` | — | the centre of the tangent disk is a point of D distinct from p |
| `Plane.stronglyAccessible_of_nearest` | Lemma 8.2 (nearest points are strongly accessible) | a nearest point of C is strongly accessible, with the component hypothesis phrased as an inclusion |
| `Plane.accessCone` | — | DEF: the open truncated cone of straight access directions, written without normalising `x − p` |
| `Plane.accessCone_subset_Ball_self` | — | the cone of reach s sits inside `Ball(p, s)` |
| `Plane.apex_not_in_accessCone` | — | the apex is not in its own cone |
| `Plane.accessCone_monotone` | — | shrinking the reach shrinks the cone |
| `Plane.accessCone_IsOpen` | — | the cone is open |
| `Plane.member_accessCone` | — | membership in the blueprint's own words, for a unit direction within 60° |
| `Plane.accessCone_IsNonempty` | — | for a unit direction and positive reach the cone is nonempty |
| `Plane.openSegment_subset_accessCone` | — | the open segment along an admissible unit direction lies in the cone |
| `Plane.accessCone_subset_Ball` | Lemma 8.4 (tangent-disk cone), packaged | the whole truncated cone about the centre direction lies inside a tangent disk |
| `Plane.tangent_cone` | Lemma 8.4, literal form | a straight ray within 60° of the centre stays inside the disk up to distance radius |
| `Plane.StronglyAccessible.exists_cone` | — | a strongly accessible point carries a direction and radius with every truncation inside D |
| `Plane.StronglyAccessible.openSegment_inside` | — | the open segment from p to the disk centre lies in D |
| `Plane.exists_dense_strongly_accessible_sequence` | Proposition 8.5 (countable dense strong-access set) | a SEQUENCE of strongly accessible points of C dense in C |
| `Plane.PolyAccessible` | the hypothesis of lem:accessible-endpoints | DEF: a polygonal access chain from Ω, deliberately not required to be simple |
| `Plane.polyAccessible_of_member` | — | a point of Ω is polygonally accessible from it |
| `Plane.PolyAccessible.mono` | — | polygonal accessibility passes to a larger set |
| `Plane.PolyAccessible.of_openSegment` | — | a straight access segment gives polygonal accessibility |
| `Plane.StronglyAccessible.polyAccessible` | — | a strongly accessible point is polygonally accessible — the bridge between the two halves |
| `Plane.polyAccessible_of_chain` | — | the constructor a consumer holding an arc should use |
| `Plane.polyAccessible_of_chain_at_finish` | — | the same read from the far end; needs chain reversal |
| `Plane.PolyAccessible.exists_simple` | — | the access chain can be taken to be a simple polygonal arc, with the far endpoint returned |
| `Plane.exists_simple_polygonal_arc_of_unionOver` | lem:finite-polygonal-union, finite-family form | a connected finite union of polygonal sets joins any two of its points by a simple polygonal arc |
| `Plane.exists_simple_polygonal_arc_pinned` | — | the endpoint-pinned extraction — the most general form the development needs |
| `Plane.exists_simple_polygonal_arc_of_IsPolygonal_pinned` | — | the same for a union presented as one polygonal set |
| `Plane.exists_crosscut_of_unionOver` | lem:skeleton-crosscuts, extraction step | a simple polygonal arc meeting C only at its endpoints — a polygonal crosscut |
| `Plane.exists_crosscut_arc_of_unionOver` | — | the same at the level of sets |
| `Plane.exists_polygonal_arc_of_polyAccessible` | lem:accessible-endpoints | two accessible points are joined by a simple polygonal arc whose remaining points lie in Ω |
| `Plane.exists_arc_of_polyAccessible` | lem:accessible-endpoints, set level | the same as a polygonal set P with `IsArcBetween(P, a, b)` |
| `Plane.exists_crosscut_of_polyAccessible` | lem:accessible-endpoints in crosscut form | with Ω disjoint from C, the joining arc meets C exactly at its endpoints |
| `Plane.Graph.exists_simple_polygonal_arc_of_pointSet` | — | the pinned extraction on a finite plane graph with connected point set; no drawing condition |

## T1.10 — the arc-complement theorem (`ArcComplementPrep` 1121, `ArcComplement` 779)

| Proposed math name | Blueprint label | Summary |
|---|---|---|
| `Plane.squareBoundaryAbout` | (Lean `frontier_closedSquare`) | DEF: the sup-sphere of radius `radius` about `center`, equal to the union of the four sides |
| `Plane.squareCornerNorthEast` … `SouthEast`, `Plane.squareSides` | (Lean `sqNE`…`sqSE`, `squarePieces`) | DEF: the four corners and the four sides in counterclockwise order |
| `Plane.squareSides_cover` | (Lean `cover_squarePieces`) | the four sides occupy exactly the boundary |
| `Plane.squareSides_ends_distinct` | (Lean `squarePieces_nondeg`) | for a positive radius every side is nondegenerate |
| `Plane.squareBoundaryAbout_IsJordanCurve` | thm:polygonal-jordan (specialised) | the boundary of a square is a Jordan curve |
| `Plane.squareBoundaryAbout_IsPolygonal` | thm:polygonal-jordan (specialised) | the boundary of a square is a polygonal set |
| `Plane.squareBoundaryAbout_IsSeparating` | thm:polygonal-jordan (specialised) | the boundary of a square separates the plane |
| `Plane.inside_squareBoundaryAbout` | (Lean `inside_frontier_closedSquare`) | the inside of a square boundary is the open square |
| `Plane.outside_squareBoundaryAbout` | (Lean `outside_frontier_closedSquare`) | the outside is the complement of the closed square |
| `Plane.beyondSquareAbout` (+ `_IsConnected`, `_IsUnbounded`) | (Lean `isConnected_compl_closedSquare`) | the complement of a closed square about an arbitrary centre is connected and unbounded |
| `Plane.supBall_IsOpen` / `supBall_IsConvex` / `squareAbout_IsClosed` / `squareAbout_IsBounded` / `complement_squareBoundaryAbout` | (Lean elementary square API) | the square API the two component-recognition arguments consume |
| `Plane.squares_meet_transversally_twice` | thm:arc-complement ("their boundary cycles meet in at least two points") | two nearby congruent squares have two DISTINCT singleton crossing points |
| `Plane.squareBoundaries_meet_twice` | thm:arc-complement | the blueprint's weaker reading: the two boundaries share at least two points |
| `Plane.overlayGraph_vertex_of_singleton_meet` | — | a transversal crossing of two source segments is a cut point, hence an overlay vertex |
| `Plane.squares_two_common_vertices` | lem:union-two-connected (its input) | two nearby squares contribute two distinct common VERTICES to the overlay |
| `Plane.squares_two_common_cut_points` | (Lean `exists_two_cut_points`) | the localizable form: two distinct cut points on both boundaries |
| `Plane.overlayPiece_at_cut_point_inside_source` | — | a cut point on a source segment is an END of an overlay edge inside it |
| `Plane.overlayPiece_covering_inside_source` | — | every point of a source segment lies on an overlay edge staying inside it |
| `Plane.subdivide_monotone` | (Lean `subdivide_mono`) | subdividing a sublist at the same cut points gives a sublist of the full subdivision |
| `Real.samplePoint` | thm:arc-complement ("By uniform continuity, choose a partition …") | DEF: the even partition `index / count`, with order lemmas and the refinement identity |
| `Plane.exists_mesh_partition` | thm:arc-complement / prop:anchored-square-mesh | a multiple of a prescribed count on whose cells the parametrisation moves by less than a tolerance |
| `Plane.subarcCell` (+ `_IsCompact`, `_disjoint_nonadjacent`) | — | the index-th subarc, its compactness, and disjointness of nonadjacent cells |
| `Plane.exists_separation_of_nonadjacent_subarcs` | lem:compact-separation(b) | one positive separation serving every pair of nonadjacent subarcs |
| `Plane.arc_covered_by_sample_squares` | thm:arc-complement ("every point of A lies in or on one of the small squares") | under a mesh bound the arc is inside the union of the closed sample squares |
| `Plane.spannedGraph` | (Lean `segGraph`) | DEF: the polygonal plane graph spanned by a LIST of segments, with the overlay bridge |
| `Plane.squareGraph` (+ `_pointSet`, `_vertex_of_cut_point`, `_two_common_vertices`) | thm:arc-complement (single-ambient-graph obligation) | DEF: the part of ONE overlay lying on one square's boundary, a subgraph by construction |
| `Plane.familySides` / `familyCutPoints` / `familyOverlay` / `familySquare` / `familyChain` | thm:arc-complement (the construction) | ONE side list, ONE cut-point choice, ONE overlay, the j-th square graph, the i-th chain link |
| `Plane.SquareGraphIsTwoConnected` | (Lean `SquaresTwoConnected` — a NAMED HYPOTHESIS) | the hypothesis that a square's part of a polygonal overlay is 2-connected |
| `Plane.familySquare_IsTwoConnected` / `familyChain_IsTwoConnected` | lem:union-two-connected | each square graph and each chain link is 2-connected |
| `Plane.familyChain_IsPlaneChain` | thm:arc-complement (consecutive/nonconsecutive clauses) | the chain of square boundaries is a plane chain, on two geometric hypotheses only |
| `Plane.Graph.outer_face_of_off_squareAbout` | (Lean `outer_of_notMem_closedSquare`) | a drawing inside a closed square puts every point outside it in an unbounded face |
| `Plane.Graph.face_misses_supBall` | thm:arc-complement ("the boundary cycle separates it from the outer face") | a point strictly inside a carried square boundary lies in no unbounded face |
| `Plane.familyChain_OuterOnPairs` | lem:outer-chain (its hypothesis) | every consecutive pair sits inside one square with the given point outside it |
| `Plane.familyChain_outer_face` | lem:outer-chain (applied) | the point is in the exterior of the whole chain union with an unbounded face there |
| `Plane.supDistance_greater_of_distance` | (Lean `lt_supDist_of_le_dist`) | a Euclidean lower bound gives a STRICT sup-metric lower bound at half the size |
| `Plane.exists_face_off_arc` | thm:arc-complement (the whole proof but the last sentence) | two points off a simple arc lie in a common open connected set missing the arc |
| `Plane.exists_polygonal_arc_off_arc` | thm:arc-complement, polygonal half | two points off a simple arc are joined off it by a simple POLYGONAL arc |
| `Plane.arc_complement_IsConnected` | thm:arc-complement | THE THEOREM: the complement of a simple arc in the plane is connected |

## T1.11 — the Jordan curve theorem (`JordanSeparates` 659, `Jordan` 902, `JordanClosed` 86)

| Proposed math name | Blueprint label | Summary |
|---|---|---|
| `Plane.IsArcBetween.split_at_interior_point` | arc twin of lem:jordan-circle, second clause | an arc splits at any interior point into two arcs covering it and meeting exactly there |
| `Plane.coordinate_constant_on_segment` / `coordinate_bounded_on_segment` | — | an affine coordinate on a segment is squeezed by its values at the two ends |
| `Plane.Point.moveCoordinate` | — | DEF: move one coordinate of a point to a named value, leaving the other |
| `Plane.exists_unique_unbounded_component_of_compact_complement` | opening sentence of the blueprint's Jordan section | the complement of a compact set has exactly one unbounded component, swallowing any square's outside |
| `Plane.arcK33_of_pieces` | cor:k33-subdivision (packaging) | nine arcs on six named points form a plane K(3,3) arc configuration |
| `Plane.IsJordanCurve.complement_not_connected_in_coordinate` | prop:jordan-disconnected | two curve points differing in one coordinate ⇒ the complement is not connected |
| `Plane.IsJordanCurve.exists_distinct_points` | — | a Jordan curve carries two distinct points |
| `Plane.IsJordanCurve.complement_not_connected` | prop:jordan-disconnected | the complement of a Jordan curve is not connected |
| `Plane.IsJordanCurve.exists_distinct_components` | prop:jordan-disconnected, consumed form | two points of the complement lie in different components |
| `Plane.exists_first_meeting_on_segment` | — | a segment reaching a closed obstacle has a first meeting point, with the part before it in one component |
| `Plane.exists_first_meeting_on_chain` | — | the same for a polygonal chain, by recursion on the vertex list |
| `Plane.exists_arc_to_first_meeting` | — | the initial chain re-extracted as a simple polygonal arc meeting S only at that point |
| `Plane.polygonally_accessible_at_first_meeting` | — | the first meeting point is polygonally accessible from the component the chain started in |
| `Plane.PolygonallyAccessible.in_closure` | — | a point accessible from a region but not in it lies in the region's closure |
| `Plane.IsLoop.curve_without_open_subarc` | lem:jordan-circle, the form used here | a Jordan curve minus a relatively open subarc is the complementary closed arc |
| `Plane.exists_accessible_point_on_open_subarc` | lem:accessible-dense, parameter form | every open parameter subinterval carries a curve point accessible from the component of x |
| `Plane.accessible_points_dense` | lem:accessible-dense | the points reachable from x by a polygonal arc meeting the curve only at its endpoint are dense |
| `Plane.exists_tripod` | the blueprint's T_i, at the H5 step of thm:jordan | three internally disjoint arcs from one point to three distinct accessible points |
| `Plane.exists_separated_parameter_windows` | — | nine pairwise separated parameter windows in three blocks of three |
| `Plane.subarcs_meet_at_middle` | — | two closed parameter intervals sharing an endpoint meet only there |
| `Plane.IsJordanCurve.not_three_components` | thm:jordan, the K(3,3) half | three complement points cannot lie in three distinct components |
| `Plane.IsJordanCurve.curve_in_closure_of_component` | — | the whole curve lies in the closure of any component of its complement |
| `Plane.IsJordanCurve.IsSeparating` | thm:jordan | a Jordan curve is separating, in the SAME predicate as the polygonal case; carries the arc-complement hypothesis |
| `Plane.jordan_curve_theorem` | thm:jordan, headline and unconditional | exactly two regions, one bounded one unbounded, both with the curve as boundary |
| `Plane.IsArc.complement_IsConnected` | thm:arc-complement, unconditional restatement | the complement of a simple arc is connected, with the carried hypothesis discharged |
| `Plane.IsArc.complement_polygonally_connected` | thm:arc-complement, polygonal form | two points off a simple arc are joined off it by a simple polygonal arc |

## T1.12 — H10, the general crosscut theorem (`CrosscutAtMostTwo` 630, `ArcCollars` 1966, `GeneralCrosscut` 542)

| Proposed math name | Blueprint label | Summary |
|---|---|---|
| `Plane.IsArcCollar` | Lemma 1.8 (b) — two-sided polygonal strips, arc case, as an interface | DEF: an open neighbourhood of a compact piece split by the arc into two connected tracks |
| `Plane.HasArcCollars` | Lemma 1.8 (b) as a hypothesis | DEF: every nondegenerate compact connected piece of the arc in the region carries a collar |
| `Plane.IsArcCollar.connected_piece_inside_two_Components` | — | a connected subset meeting the collar lies in the component of one of the two reference points |
| `Plane.outside_two_Components_IsOpen` | — | the points of an open set lying in neither of two components form an open set |
| `Plane.covered_by_two_Components_of_local` | the clopen step — the whole of lem:crosscut-at-most-two once a collar exists | local two-sidedness at every arc point covers all of `region ∖ arc` by two components |
| `Plane.crosscut_at_most_two` | lem:crosscut-at-most-two ("At most two sides") | two points of `region ∖ arc` whose components cover it, given `HasArcCollars` |
| `Plane.covered_by_two_Components_of_distinct` | — | pure bookkeeping: two covering components with distinct named points ARE the two |
| `Plane.crosscut_components_exhaust` | lem:crosscut-at-most-two, the form thm:general-crosscut cites | two distinct components of `region ∖ arc` exhaust it |
| `Plane.member_segment_of_frame_coordinates` | — | a nondegenerate segment read in its own frame, with direction/length existentials |
| `Plane.hasArcCollars_segment` | Lemma 1.8 (b) for a straight crosscut | a segment crosscut has two-sided collars: an open rectangle split into two convex halves |
| `Plane.segment_crosscut_at_most_two` | — | "At most two sides" for a straight crosscut, with no hypothesis standing |
| `Plane.IsPolyArc` | the arc analogue of `ClosedPolygon` | DEF: a simple polygonal arc by globally injective vertex list with a corner at every interior vertex |
| `Plane.PolyArc.edge` / `.carrier` / `.edgeLength` / `.tangent` / `.backTangent` / `.offset` / `.pointAlong` / `.trimmed` | — | the edge-frame vocabulary and its ~25 computational lemmas |
| `Plane.PolyArc.vertex_not_in_far_edge` | — | simplicity, first form: a vertex lies on no edge but the incident ones |
| `Plane.PolyArc.trimmed_disjoint_edge` | — | simplicity, second form: a trimmed core misses every other edge |
| `Plane.PolyArc.germ_in_left_arc_at_start` / `_at_finish` (+ right forms) | — | the four germs at an interior vertex: small offsets land in the left/right direction arcs |
| `Plane.IsArcStrip` | Lemma 1.8 (b), the constants | DEF: cone radius, trim, half-width with separations, germ threshold, and three arc-only clauses |
| `Plane.ArcStrip.leftBlock` / `rightBlock` / `tube` / `leftSector` / `rightSector` / `leftChain` / `rightChain` / `leftTrack` / `rightTrack` / `neighbourhood` | — | the four block families, the two chains, and a manifestly open neighbourhood |
| `Plane.ArcStrip.blocks_avoid_carrier` / `.sectors_avoid_carrier` | — | nonadjacent disjointness: a block or sector point lies on no edge of the arc |
| `Plane.ArcStrip.neighbourhood_difference_carrier` | — | `neighbourhood ∖ carrier = leftTrack ∪ rightTrack` |
| `Plane.ArcStrip.leftTrack_IsConnected` / `.rightTrack_IsConnected` | — | each track is connected, via explicitly exhibited consecutive overlaps |
| `Plane.ArcStrip.tracks_disjoint` | — | the two tracks are disjoint, by four cases |
| `Plane.ArcStrip.compact_piece_inside_neighbourhood` | — | the compact piece lies inside the neighbourhood |
| `Plane.ArcStrip.compact_piece_inside_Closure_leftTrack` / `_rightTrack` | — | both tracks approach every point of the piece |
| `Plane.ArcStrip.IsArcCollar` | Lemma 1.8 (b) itself | the collar, assembled |
| `Plane.PolyArc.exists_cone_radius` | — | step 1 of the constants: one radius below five families of positive quantities |
| `Plane.PolyArc.exists_half_width` | — | step 3: one half-width below the trimmed separations, meeting the germ threshold, inside the region |
| `Plane.exists_arcStrip` | — | the constants exist for every compact piece — steps 1–3 composed |
| `Plane.PolyArc.exists_arcCollar` / `Plane.PolyArc.hasArcCollars` | Lemma 1.8 (b), discharged for a vertex-list arc | every compact piece has a collar; hence `HasArcCollars` |
| `Plane.IsPolyArcCarrier` | — | DEF: P is the carrier of some `PolyArc` with named extreme vertices; carried as a HYPOTHESIS |
| `Plane.hasArcCollars_of_polyArcCarrier` / `crosscut_at_most_two_of_polyArcCarrier` / `crosscut_components_exhaust_of_polyArcCarrier` | — | the set-level forms of "At most two sides" |
| `Plane.PolyArc.carrier_IsArcBetween` / `.carrier_IsPolygonal` | — | the presentation is faithful: the carrier IS a simple polygonal arc between its extreme vertices |
| `Plane.polyArc_crosscut_at_most_two` / `polyArc_crosscut_components_exhaust` | — | "At most two sides" for a `PolyArc`, with NO hypothesis standing |
| `Plane.segmentPolyArc` / `Plane.isPolyArcCarrier_segment` | — | a nondegenerate segment is a one-edge `PolyArc`, so the apparatus is not vacuous |
| `Plane.IsArcBetween.not_inside_endpoint_pair` | — | an arc is more than its two endpoints |
| `Plane.IsCrosscut` | the hypotheses of thm:general-crosscut | DEF: a Jordan curve, a simple polygonal arc between two of its points, interior inside |
| `Plane.IsCutPair` | lem:jordan-circle — the two arcs of C from p to q | DEF: two arcs covering C meeting exactly in {p,q}, with `.symmetric` and `Plane.exists_isCutPair` |
| `Plane.IsCrosscut.endpoints_not_inside` / `.meet_curve_eq_pair` / `.disjoint_outside` / `.arc_union_meet` / `.union_IsJordanCurve` / `.union_IsSeparating` / `.outside_inside_outside_union` | — | the elementary consequences feeding `crosscut_cells` |
| `Plane.crosscutSide` | lem:crosscut-side-correspondence | DEF: the side belonging to an arc, `inside(arc ∪ P)` — a function of the arc, not an existential |
| `Plane.IsCrosscut.side_inside_region_difference` / `.side_is_Component` / `.side_nonempty` / `.side_IsOpen` / `.side_IsConnected` / `.side_IsBounded` / `.side_Boundary` / `.side_Closure` | thm:general-crosscut, clause (a) of lem:crosscut-cells | the side is a component of `inside(C) ∖ P`, with its full topology |
| `Plane.IsCrosscut.Closure_side_meets_curve` | lem:crosscut-cells clause (c) — the labelling lemma | `Closure(inside(A₁ ∪ P)) ∩ C = A₁`; `.sides_distinct` and `.sides_disjoint` follow |
| `Plane.IsCrosscut.components_are_sides` / `.inside_difference_eq` | — | every component of `inside(C) ∖ P` is one of the two sides, and they exhaust it |
| `Plane.general_crosscut` | thm:general-crosscut, first sentence | bundled: `inside(C) ∖ P` has exactly two components, with both labelling equations |
| `Plane.IsCrosscut.complement_eq` / `.complement_eq_three` / `.outside_is_Component` / `.side_is_Component_of_complement` / `.three_regions` / `.outside_side_disjoint` / `.outside_ne_side` | thm:general-crosscut, the "consequently" sentence | the three-way split of `(C ∪ P)ᶜ`, each piece a component |
| `Plane.general_crosscut_three_regions` | thm:general-crosscut, second sentence | bundled: precisely three regions, pairwise disjoint, pairwise DISTINCT, with their boundaries |

---

# Shared stubs

Dependencies reported `missing` or `partial` that two or more waves consume. Build these before any wave starts.

| Shared stub | Waves | Suggested home | Note |
|---|---|---|---|
| `Plane.IsSeparating` / `Plane.inside` / `Plane.outside` / `IsRegionOf` / `IsRegionPair` + region API | T1.3 (owner), T1.4, T1.5, T1.6, T1.7, T1.8, T1.10, T1.11, T1.12 | `library/Plane/region.math` | Zero occurrences in `library/` today; 101 of 111 Lean modules mention `inside`; T1.3 has no dependency on T1.1/T1.2 and should be built first |
| Crossing-count apparatus (`Crosses`, `crossingCount`, `IsClosedChain`, `height`/`reach`, parity constancy, `parity_split`) | T1.1 (owner), T1.4, T1.5, T1.6, T1.7, T1.8 | `library/Plane/Graph/parity.math` + `library/Plane/frame.math` | Nothing of it exists; T1.5/T1.7/T1.8 cannot be stated without it |
| `crosscut_cells` (Lemma 2.6) + `cell_subset_region_diff` / `cell_isComponent` / `closure_cell_inter_curve` | T1.3 (owner), T1.5, T1.7, T1.12 | `library/Plane/crosscut.math` | T1.12's `GeneralCrosscut` is three applications plus assembly |
| Cyclic vertex-index representation (`ZMod`-style `val`, `val_lt`, `natCast_rightInverse`, all-residues enumeration, or a vertex-LIST representation) | T1.2 (decides), T1.4, T1.5, T1.6, T1.7 | `library/IntegerMod/representative.math` or the T1.2 polygon file | `IntegerMod(n)` is an opaque quotient with only an EXISTENTIAL representative and no `decide`; the decision must be made once, in T1.2 |
| Parity value type / `Natural.SameParity`, `Natural.IsEven`/`IsOdd` and their algebra | T1.1, T1.5 | new `library/Natural/parity.math` | `IntegerMod(2)` has no `decide`; both waves recommend ℕ + `2 ∣ (m+n)` |
| `Plane.Vector.IsDirection` (unit vector) + `Plane.Vector.direction` (normalisation) + `norm_positive` | T1.1, T1.2, T1.4, T1.12 (via T1.2) | `library/Plane/direction.math` | `Plane/direction.math` has `IsNonzero`/`Parallel`/`SameRay`/`Counterclockwise` but no unit-vector predicate |
| Right-slot bilinearity `determinant_add_right` / `determinant_scale_right` / `innerProduct_add_right`, and `det`-vs-`perpendicular` identities | T1.1, T1.2 | `library/Plane/bilinear.math` | Only the LEFT forms exist; ~3 lines each via `determinant_antisymmetric` |
| Absolute-valued bilinear bounds: `|⟪u,v⟫| ≤ ‖u‖‖v‖` and `|det(u,v)| ≤ ‖u‖‖v‖` | T1.1, T1.2 | `library/Plane/norm.math` | The existing `cauchy_schwarz` is one-sided |
| Frame coordinates on a directed line (`height`/`reach` = `coordinateAlong`/`coordinateAcross`), `frame_decomposition`, `distance_to_foot`, 1-Lipschitz | T1.1, T1.2, T1.12 (via T1.2) | new `library/Plane/frame.math` | The two waves name the same abstraction differently — unify before either starts |
| `MetricSpace.IsCompact.union` / `.unionOver` (a finite union of compacta is compact) | T1.2, T1.4, T1.6, T1.7, T1.9, T1.11 | `library/Metric/compactness.math` | Only `.intersection` exists; also blocks `chainFrom_IsCompact` and the overlay-connectedness clopen argument |
| `MetricSpace.IsClosed` / `Plane.IsClosed` + the compact ⇒ closed (complement-open) bridge | T1.3, T1.4, T1.7, T1.11 | `library/Metric/topology.math`, `library/Plane/topology.math` | `Plane.IsCompact.Closure_subset` exists but there is no `Plane.IsClosed`; `IsJordanCurve.isClosed` is the most-cited Lean fact (85 sites) |
| `Plane.Boundary` — the absolute frontier, shadowing `Plane.BoundaryIn` | T1.3, T1.5, T1.7, T1.12 | `library/Plane/topology.math` | Only the RELATIVE boundary exists; `IsRegionOf.Boundary_equals` alone is cited 29 times |
| `Plane.Closure.monotone` / `MetricSpace.ClosureIn.monotone` | T1.3, T1.5 | `library/Plane/compactness.math` | Grep for closure monotonicity returns zero |
| `Plane.Component.recognize` in FRONTIER/BOUNDARY form (`recognize_by_frontier`) | T1.3, T1.4, T1.5, T1.7, T1.12 | `library/Plane/component.math` | Ours takes `ClosedIn`; every consumer holds "the boundary misses the ambient set" |
| `Set.complement` vs `Set.universe ∖ S` reconciliation, and `Plane.Component_boundary_in_closed` restated in complement form | T1.3, T1.4 | `library/Set/algebra.math`, `library/Plane/component.math` | Only 4 sites use the `∖ universe` spelling; restating is the cheap fix |
| `Set.Disjoint` and its algebra (symmetric, shrink-right, intersection-empty) | T1.3, T1.5 | `library/Set/algebra.math` | T1.3 reports it MISSING; T1.5 reports it present at `Set/algebra.math` — resolve before either wave |
| Set-algebra gaps: distributivity, `∪`-monotonicity, `(T ∖ S) ∪ S = T`, `empty_of_no_members`, `empty_union` | T1.3, T1.5 | `library/Set/algebra.math` | Individually trivial, collectively a half-day invisible to any Lean line count |
| `Set.pair(X, p, q)` with `{p, q}` notation | T1.5, T1.7 | `library/Set/basics.math` | `A ∩ B = {p,q}` is the entire T1.5↔T1.7 interface |
| `List.Permutation` congruences: `.map`, `.append`, `.append_commutative`, `.reverse`, filter-length invariance | T1.5, T1.7, T1.8 | `library/Lists/permutation.math` | The relation and membership transport exist; the congruences do not |
| `Plane.piecesCover` readers (`_append`, `_prepend`, `exists_member_of_`, `_map_orientSegment`) | T1.1, T1.5, T1.6 | `library/Plane/Graph/subdivide.math` | The definition exists; the readers exist only where `subdivide.math` happened to need them |
| `Plane.IsArcBetween.openArc_IsConnected` + both endpoints in the closure of the open arc + nonemptiness | T1.5, T1.6, T1.7, T1.8 | `library/Plane/subarc.math` | The set identity `openArc = arc ∖ endpoints` exists; connectedness and the closure facts do not |
| `Plane.two_arcs_unique` (the two-arc decomposition is determined), including the weaker closed-competitor form | T1.5, T1.6, T1.7, T1.8 | `library/Plane/twoarcs.math` | Existence exists (`IsJordanCurve.two_arcs`); uniqueness is genuinely new |
| `Plane.chainFrom_append` / `chainFinish` / start-and-finish membership / `chainFrom_reverse` | T1.4, T1.7, T1.9, T1.11 | `library/Plane/polyline.math` | No append law, no `List.last`, and chain reversal is not `List.reverse` here |
| `Plane.chainFrom_IsConnected` / `Plane.chainFrom_IsCompact` (`IsPolygonal.IsCompact`) | T1.4, T1.9, T1.11 | `library/Plane/polyline.math` | `isConnected_poly` alone is used ~6 times in `Jordan.lean`; needs `IsCompact.union` first |
| `Plane.PolygonalReach.exists_chain` — bridge from the inductive reach predicate to a vertex LIST | T1.9, T1.11 | `library/Plane/polygonal.math` | `Plane.polygonal_connected` yields a derivation, not a list; every consumer wants the list |
| lem:finite-polygonal-union — extract a SIMPLE polygonal arc from a connected finite union of polygonal sets (with the pinned/endpoint variants) and `overlayGraph_Reaches` | T1.6, T1.9, T1.11 | new `library/Plane/Graph/simple_arc.math` | **Unassigned to any wave**; explicitly deferred at `PLAN_JORDAN_SCHOENFLIES.md:232`; 1.5–2.5k lines |
| `Real.exists_above_list` / upper-bound-over-a-list (mirror of `Real.exists_positive_lower_bound`) | T1.1, T1.6 | `library/Real/positive_bound.math` | The Mathlib cofiniteness route does not transfer |
| `Real.openInterval` / `Real.closedInterval` with convexity, connectedness and COMPACTNESS (incl. `Real.segment_IsCompact`) | T1.5, T1.6, T1.11, T1.12 | `library/Metric/interval.math` | Only `Real.unitInterval` is proved compact/convex |
| `Plane.IsConnected.unionOver_chain` (a list-indexed chain of connected sets with consecutive meets) and its cyclic corollary | T1.2, T1.12 | `library/Plane/connected.math` | Only the BINARY `IsConnected.union` exists; both waves chain it by hand today |
| `Plane.IsOpen.unionOver` (list union of opens is open) and half-plane openness / continuity of a linear functional | T1.2, T1.11 | `library/Plane/topology.math`, `library/Plane/exterior.math` | `HalfPlane_IsConvex`/`_IsConnected` exist but never `_IsOpen`; no coordinate continuity anywhere |
| `Plane.distanceToSet` (attained, 1-Lipschitz) and `Plane.exists_closest_pair` | T1.2 (for `thickening`), T1.11 | `library/Plane/extremum.math` or `separation.math` | Explicitly deferred in the plan; removes T1.11's need for product compactness |
| `Graph.IsCycleThrough` family: `.rotate`, `.transfer`, `.in_supergraph`, `.split_at`, `Graph.cycleGraph`, `Graph.exists_spliced_cycle` | T1.7, T1.8 | `library/Graph/cycle.math`, new `library/Graph/cycle_split.math` | Grep of `library/Graph/` returns zero for `cycleGraph`, `splice`, `rotate`; ownership between T1.7/T1.8 must be settled |
| `Graph.IsPath.append` and `Graph.IsPath.split_at_visited` (split with the meeting clause) | T1.7, T1.8 | `library/Graph/path.math` | Ours `Graph.IsPath.split` lacks the "the two halves meet only at the cut vertex" clause |
| `Plane.Graph.edgesCover_append` / `_permutation` / `_monotone` and `IsDrawing.walkVertices_in_edgesCover` | T1.7, T1.8 | `library/Plane/Graph/pointset.math`, `cycle.math` | Available as `List.unionOver` facts but not stated at the `edgesCover` name |
| `Graph.chainUnion` / `Graph.IsPlaneChain` / `OuterOnPairs` / `outer_chain` | T1.8 (owner), T1.10 | `library/Plane/Graph/chain.math` | T1.10 uses ~a dozen `chainUnion` readers; hard blocker for T1.10's assembly |
| `Plane.PrePolygon` (the corner-free presentation) and its arc apparatus (`arcPieces`, `insertLast`, `exists_prePolygon_split`, `parity_eq_one_iff`) | T1.6 (owner), T1.7 | T1.2's polygon file, per the Lean integrator's own note | `PrePolygonArc.lean` (943 lines) belongs to NO wave; both K33Land and FaceCyclesLand import it |
| `Plane.PolyAccessible` and `exists_crosscut_of_polyAccessible` | T1.9 (owner), T1.11 | `library/Plane/Jordan/accessible_join.math` | `exists_tripod` is built on it; T1.11 cannot start before T1.9 |
| `Plane.IsPolyArcCarrier` discharged (arc realization) | T1.6 (owner), T1.12 | `library/Plane/Jordan/arc_realization.math` | Carried as a HYPOTHESIS in both the Lean original and T1.12; discharged only at `JordanClosed` |
| `Plane.Vector.arc` theory (`arc_IsOpen`, `arc_disjoint`, `ray_or_arc`, `arc_scale`, `arc_Ball_IsConnected`) + SIGN-FREE `germs_split'` + `exists_germ_bound` | T1.2 (owner), T1.12 | `library/Plane/arc.math` | T1.12 uses ONLY the sign-free form; if T1.2 lands only the signed form, `ArcCollars` stalls |
| `Plane.strip` / `block` / `sector` / `cone` primitives with `coordAlong`/`coordAcross` and `mem_strip_param` | T1.2 (owner), T1.12 | `library/Plane/frame.math` | Every block family of the arc collar is one of these — T1.12's single largest external dependency |
| `Graph.IsIncWalk`, `Graph.IsLongCycle`, and `SquaresTwoConnected` discharged (`SquareCycle.lean`, 1052 lines) | T1.10, T1.11 | `library/Graph/`, `library/Plane/Graph/` | **In no wave row**; until it is scheduled, thm:arc-complement and therefore thm:jordan are conditional |
| `Real.exists_common_positive_bound` applied over PRODUCT index families (`List.cartesianProduct` of `List.range_up`) | T1.2, T1.10, T1.12 | `library/Lists/cartesian.math` usage pattern | The pieces exist; the shape differs from Lean's `Set`-finite indexing at ~8 call sites |

---

# Per-wave stubs

Remaining missing items, per wave, in dependency order.

### T1.1
1. `Plane.Vector.norm_perpendicular` — the right-angle turn preserves length (`Plane/norm.math`).
2. `Plane.openSegment_parameter` — a point strictly inside a nondegenerate segment is `between(a,b,t)` for `0 < t < 1`, and conversely (`Plane/segment.math`).
3. `List.sumOver_even` — if two divides every term, it divides the total (`Lists/sum.math`).
4. `Plane.edgeCycle` as an accumulator recursion beside `Plane.chainFrom` (no `zip`, `rotate` or `Perm.sum_eq`).
5. `Plane.segment_Closure_subset` → `Plane.piecesCover_complement_IsOpen`.
6. `Plane.exists_transverse_direction` / `Plane.exists_level_free_direction` — a direction whose determinant against each of a list of nonzero vectors is nonzero (`Plane/direction.math`).

### T1.2
1. `Plane.thickening(region, radius)` + `thickening_monotone`.
2. `Plane.compact_neighbourhood_inside_open` — **Lemma 1.4 (a)**; the one stub with real proof content (~100 lines, sequential re-proof).
3. `IntegerMod.allResidues(n)` with completeness and distinctness, plus `one_not_zero` / `successor_not_self` at modulus ≥ 2.
4. `Plane.block` with openness/convexity/connectedness and the parametric membership criterion.
5. `Plane.sector` with `sector_IsOpen`, `sector_subset_Ball`, `sector_IsConnected` for an arc of directions.

### T1.3
1. `Plane.OpenIn.of_IsOpen` — a convenience wrapper used at every `Component.recognize` call.
2. `Plane.ClosedIn.of_Boundary_off_region` — the bridge from a frontier-disjoint hypothesis to `ClosedIn`.
3. `Plane.Component.recognize_of_Boundary_off_region` — Lemma 1.7 in the form this wave's consumers hold.
4. `Plane.IsJordanCurve.IsClosed`.
5. `Plane.IsCompact.IsClosed`.

### T1.4
1. `Plane.IsArcBetween(Plane.segment(a,b), a, b)` for `a ≠ b`.
2. `Plane.left_not_in_openSegment` / `Plane.right_not_in_openSegment`.
3. `List.append_of_mem` — a member splits a list as `before ++ (x :: after)`.
4. `IntegerMod.representative_below_modulus` (+ `make_representative`, `representative_lt_modulus`) — the `ZMod.val` analogue, or the alternative index representation.
5. `IntegerMod.successor_not_self` and `eq_one_of_nonzero` at modulus 2.
6. `Plane.beyondSquare_complement_square` — the two existing pointwise directions as one SET equation.
7. `Plane.IsCompact.inside_square` — wraps `IsBounded.inside_square` + `IsCompact.bounded`.
8. `Plane.Component.disjoint_of_distinct`.
9. `Plane.Component_BoundaryIn_eq_of_subset_Closure`.
10. `Plane.nearest_point_segment_avoids` — **Lemma 1.3 / lem:nearest-segment**; a genuine Layer-1 hole.
11. `Plane.exists_far_along_direction_beyond_square` — rests on the one genuinely nonlinear inequality of the wave.
12. `Plane.telescoping_boundary_sum`.

### T1.5
1. `List.reverse` on polymorphic lists, with `reverse_append`, `reverse_reverse`, `member_reverse` (new `library/Lists/reverse.math`).
2. `List.range_up_split(k, l)` — the workhorse behind `arcSegments_add`.
3. `Plane.orientSegment_identity_or_reversed`.
4. `Plane.crossingMark_reverse` stated in T1.1 **without** the non-levelness hypothesis, not restated here.

### T1.6
1. `Plane.overlayPieces_covers` — extract the chain currently inline in `Plane.overlayGraph_pointSet`.
2. `Plane.exists_nondegenerate_pieces_of_IsPolygonal` — bridge `chainFrom` to a nondegenerate segment LIST (Lean's `segsOf` + `cover_segsOf_eq`).
3. `List.increasingListing` with permutation, membership and strict-order lemmas (new `library/Lists/increasing.math`).
4. `Plane.parameterAt` / `Plane.nextParameter` and their order lemmas.
5. `Plane.gap` / `gapClosure` / `no_parameter_inside_gap` / `gaps_disjoint` / `gap_inside_unitInterval` / `exists_containing_gap`.
6. `Plane.IsConnected.lands_in_one_of_two_opens` and `Plane.IsConnected.lands_in_one_closed_piece` (list form).
7. `Plane.nearPiece` + `Plane.nearPiece_IsOpen`.
8. `Plane.IsCleanPresentation` and its four consequence readers.
9. `Plane.collinear_middle_of_meeting_at_shared_end` and `Plane.collinear_of_three_in_one_segment`.
10. `Plane.Segment.points` / `Plane.Segment.interior` accessors (prerequisite for readability of every clean-piece statement).

### T1.7
1. `Graph.IsPath.empty_of_closed`.
2. `Graph.IsWalk.walkVertices_eq_coveredVertices` (nonempty walk), `.walkVertices_reverse`, `walkVertices.in_subgraph`, `coveredVertices.in_subgraph`.
3. `Graph.IsTwoConnected.exists_adjacent_other_than`.
4. `Graph.IsLongCycle`, `Graph.IsTwoConnected.exists_long_cycle`, `Graph.IsLongCycle.IsTwoConnected`, `Graph.banana_not_IsTwoConnected`.
5. `Graph.IsTwoConnected.ear_decomposition` — the ear decomposition as a motive-parametric induction principle.
6. `Graph.ear_edges_new_or_union_unchanged`.
7. `Plane.Graph.pointSet_union` / `.exterior_union` / `.face_union_subset` / `.face_unchanged_if_disjoint` / `.exists_face_containing_connected`.
8. `Plane.Graph.IsDrawing.edgesCover_meets_pointSet` / `.exists_face_of_ear` / `.ends_in_face_boundary`.
9. `Plane.Graph.IsDrawing.isPolygonal_edgesCover`.
10. `Plane.Component.after_removal`.
11. `Plane.IsArcBetween.eq_of_subset` (arc uniqueness).
12. `Plane.Graph.IsK33Configuration` and the hexagon apparatus (`hexList`, `hexSet`, `arcA`/`arcB`, `chords_alternate`, `exists_two_chords_same_region`, `exists_reference_point`).
13. `Plane.IsArcK33`, `Plane.Graph.IsK33Subdivision`, `Plane.Graph.k33Graph`.

### T1.8
1. `Graph.HasWalkOfLength` / `Graph.shortest_walk_between` (template: `Graph.longest_path`).
2. `Graph.IsPath.split_at_edge`.
3. `Graph.IsCycleThrough.edge_is_edge` / `.ends_are_visited` / `.split_at_two_edges`.
4. `Graph.IsCycleCrosscut` and `Graph.exists_cycle_crosscut`.
5. `Graph.foreignEdges` / `foreignEdgeCount` / `foreignEdgeCount_splice_shrinks` (as `List.filter` length, NOT `Set.ncard`).
6. `Plane.two_arcs_meet_at_ends`.
7. `Plane.crosscut_inside_one_side` (gated on T1.1 parity, T1.3 inside/outside, T1.6 `PrePolygon`).
8. `Plane.Graph.Encloses` / `.monotone` / `face_IsBounded_of_Encloses` / `Encloses_of_face_IsBounded`.
9. `Plane.Graph.crosscut_encloses_one_side` — **keep the `x ∈ exterior` clause** (Lean finding 19).
10. `Plane.Graph.chainBlock` + readers; `Plane.Graph.IsPlaneChain` + `blocks_meet_only_through_neighbour`; `InOuterFaceOnPairs`; `exists_descent_crosscut`; `descent_step`; `no_block_encloses`; `outer_chain`.

### T1.9
1. `Real.exists_rational_near` — a rational within any tolerance of a real (`Real/density.math`).
2. `Plane.rationalPoint` — the ℕ-indexed enumeration of rational-coordinate points; `Plane.rationalPoint_dense` (separability as a sequence).
3. `Plane.nearest_point_on_compact` — name the assembly currently inline at `Plane/segment_meet.math:107`.
4. `Plane.Vector.norm_subtract_squared`.
5. `Plane.accessCone` and its eight lemmas; `Plane.accessCone_subset_Ball` / `Plane.tangent_cone`.
6. `Plane.StronglyAccessible` + `.mono` / `.center_in_region` / `.exists_cone` / `.openSegment_inside`.
7. `Plane.exists_dense_strongly_accessible_sequence` (restated over a sequence, not a countable set).
8. `Plane.PolyAccessible` and its five producers; the three forms of lem:accessible-endpoints; the skeleton-crosscut extraction.

### T1.10
1. `List.flatten` / `List.flatMap` with membership inversion (`Plane.graphEdges` becomes an instance).
2. `Plane.supBall_IsOpen`; `Plane.Vector.supNorm_affine_combination` → `supBall_IsConvex`/`_IsConnected`.
3. `Plane.squareAbout_IsClosed` / `_IsBounded`; `Plane.beyondSquareAbout` + `_IsConnected` / `_IsUnbounded`.
4. `Plane.squareBoundaryAbout` (as the sup-sphere) + `Plane.complement_squareBoundaryAbout`.
5. `Plane.squareSides` / `squareCorner*` + `squareSides_cover` + `squareSides_ends_distinct`.
6. `Plane.segments_meet_at_one_point` (both orientations).
7. `Plane.overlayGraph_vertex_of_cover_cut_point`; `Plane.subdivide_monotone`.
8. `Plane.spannedGraph` + `_IsSubgraph_of_includes` + `_pointSet` + `overlayGraph_is_spannedGraph`.
9. `Real.samplePoint` + its order/refinement lemmas + `Real.exists_sample_cell_containing`.
10. `MetricSpace.exists_mesh_partition` (generic, with the prescribed-multiple clause).
11. `Plane.subarcCell` + `_IsCompact` + `_disjoint_nonadjacent`; `Plane.exists_separation_of_nonadjacent_subarcs`.
12. `Plane.squareGraph` + its three readers; `Plane.familySides`/`familyCutPoints`/`familyOverlay`/`familySquare`/`familyChain`.
13. `Plane.Graph.outer_face_of_off_squareAbout`; `Plane.Graph.face_misses_supBall`; `Plane.supDistance_greater_of_distance`.

### T1.11
1. `Plane.RealContinuousOn.coordinate` — coordinate continuity (used at four sites).
2. `Real.closed_bounded_above_attains_supremum` / `_below_attains_infimum` (used at three sites).
3. `MetricSpace.IsCompact.intersection_closed`.
4. `Plane.IsArc.ClosedIn`.
5. `Plane.intermediate_value_along_arc`.
6. `Plane.IsArc.subarc_IsArcBetween`; `Plane.IsArc.basic_interval_inside_ball` (open INTERVAL, strictly inside (0,1)).
7. `Plane.IsLoop.injective_on_half_open`.
8. `Plane.Point.moveCoordinate` + its two readers; the segment-coordinate squeeze lemmas; `Plane.Point.equal_of_coordinate_pair`.
9. The four first-meeting statements + `Plane.PolygonallyAccessible.in_closure`.
10. `Plane.exists_tripod`; `Plane.exists_separated_parameter_windows`; `Plane.subarcs_meet_at_middle`.
11. `Plane.arcK33_of_pieces` (file it beside `IsArcK33` in T1.7's module).

### T1.12
1. `Plane.Vector.perpendicular_negate`.
2. `Real.exists_offset_bound` — the numeric ε-shrinking used by `exists_near_sides`.
3. `Plane.exists_direction_and_length` (kept OPAQUE) and `Plane.member_segment_of_frame_coordinates`, `Plane.point_of_zero_across_coordinate`.
4. `Plane.IsArcCollar` / `HasArcCollars` + projections; `outside_two_Components_IsOpen`; `covered_by_two_Components_of_local`; `crosscut_at_most_two`; `covered_by_two_Components_of_distinct`; `crosscut_components_exhaust`.
5. `Plane.hasArcCollars_segment` and `segment_crosscut_at_most_two`.
6. `Plane.IsPolyArc` + edge-frame vocabulary + the two simplicity forms + the four germs.
7. `Plane.IsArcStrip` + the block families + tracks + neighbourhood + all disjointness/connectedness/closure clauses + `ArcStrip.IsArcCollar`.
8. `Plane.PolyArc.exists_cone_radius` / `exists_half_width` / `exists_arcStrip` / `exists_arcCollar` / `hasArcCollars`.
9. `Plane.PolyArc.carrier_IsArcBetween` / `carrier_IsPolygonal`; `Plane.segmentPolyArc`.
10. `Plane.IsArcBetween.not_inside_endpoint_pair`; `Plane.IsCutPair` (+ `.symmetric`) and the reversal repackaging of `two_arcs`.
11. `Plane.IsCrosscut`, `Plane.crosscutSide`, the labelled-side family, `general_crosscut`, the three-regions paragraph, `general_crosscut_three_regions`.

---

# Notation candidates

| Candidate | Waves proposing |
|---|---|
| File-level `convention` blocks binding the ambient data (direction/pieces; polygon + `StripData`; curve/region/points; graph + drawing; chain + block; polygon + collar; `n` + `vertex` + the three constants) | T1.1, T1.2, T1.3, T1.4, T1.5, T1.6, T1.7, T1.8, T1.9, T1.10, T1.12 |
| `Plane.inside(curve)` / `Plane.outside(curve)` as total functions (Int(C)/Ext(C)), NOT existentially bound | T1.3, T1.4, T1.5, T1.7 |
| `Plane.IsClosed` — the missing sibling of the existing `Plane.IsOpen` | T1.3 |
| `Plane.Boundary(subset)` — the absolute shadow of `Plane.BoundaryIn`, matching `Closure`/`ClosureIn` | T1.3, T1.5, T1.7 |
| `Set.Disjoint(left, right)` as a named predicate, replacing the bare ∀-form | T1.3 |
| `Set.pair(X, p, q)` with `{p, q}` brace notation | T1.5, T1.7 |
| A `∁` prefix operator for `Set.complement` | T1.3 |
| `Plane.IsLevelFree(direction, pieces)` — one name for ~20 Lean statement signatures | T1.1 |
| `Plane.height` / `Plane.reach` (or `coordinateAlong` / `coordinateAcross`) as named frame coordinates | T1.1, T1.2 |
| `Plane.levelMeet(direction, a, b, level)` — one name for the crossing point of a non-level segment | T1.1 |
| `Plane.IsClosedChain(pieces)` stated by duality (no boundary operator) | T1.1 |
| `Plane.edgeCycle(start, vertices)` beside `Plane.chainFrom` / `Plane.polyline` | T1.1 |
| `Plane.crossingCount` reserved for the COUNT, with `crossingParity` separate (three theorems are true of the count) | T1.1, T1.4 |
| `Natural.SameParity(m, n)` / `Natural.IsOdd` / `IsEven` as named notions | T1.1, T1.5 |
| Postfix `⊥` for `Plane.Vector.perpendicular` | T1.2 |
| Operators for `Plane.Vector.innerProduct` and `determinant` (e.g. `u · v`, `u × v`) | T1.2 |
| `Plane.ClosedPolygon.offset(i, t, s)` / `.pointAt(i, c)` / `.tangent(i)` / `.length(i)` / `.nextVertex(i)` — the edge-frame working vocabulary | T1.2, T1.4, T1.12 |
| `Plane.thickening(region, radius)` for the blueprint's `N_ρ(K)` | T1.2 |
| `Plane.Vector.arc(u, w)` with an arrow-ish spelling for the direction of travel | T1.2 |
| Constants named `coneRadius` / `trim` / `halfWidth` rather than `R`/`lam`/`rho`; `leftSide` / `rightSide` / `collar` for N_L/N_R/N | T1.2, T1.12 |
| `Plane.IsRegionPair(curve, first, second)` — "the two regions, in either order" | T1.3 |
| `Plane.Polygon.IsAdmissibleDirection(polygon, direction)` — a name for the two-hypothesis pair | T1.4 |
| `Plane.Polygon.edgeList` rather than `pieces` | T1.4 |
| A `Plane.Polygon.carrier` coercion so a polygon can be written where a set is expected | T1.4 |
| A `componentwise` tactic for repeated coordinate chains (already a standing `Plane/README.md` friction) | T1.4 |
| `Plane.SameSegments` as an infix relation with `.reflexive`/`.symmetric`/`.transitive` registered | T1.5 |
| `Plane.IsChainBetween(pieces, p, q)` — NOT `chainFrom`, which already means the point set of a polyline | T1.5 |
| A name for the interior of an arc (`Plane.openArcBetween` or a `.interior` reader; blueprint writes `P°`) | T1.5, T1.6 |
| `Plane.farRegion(C, y)` — one function replacing the blueprint's four named regions | T1.5 |
| `.symmetric` as the index-swapping idiom, so every "second" theorem is its "first" twin | T1.5, T1.12 |
| `Plane.ClosedPolygon.otherArc(a, k)` — or parameterise by `k + l = m + 3` — so `m + 3 − k` never appears | T1.5, T1.7 |
| `∈` overloaded on `PrePolygon`/`ClosedPolygon`/`PreArc`/`PolyArc` carriers | T1.6 |
| `Plane.IsRedundantVertex(P, i)` — the deletion hypothesis and the negation of `corner` | T1.6 |
| `Plane.RunsStraightAt` / `Plane.IsCornerOf` | T1.6 |
| `Plane.gap(parameters, i)` / `Plane.gapClosure(parameters, i)` as named definitions | T1.6 |
| `Plane.Segment.points(piece)` / `Plane.Segment.interior(piece)` — replacing `segment(Product.first(p), Product.second(p))` | T1.6 |
| `Plane.Graph.HasFaceCycles` as a NAMED definition (it is the ear induction's motive) | T1.7 |
| `Plane.Graph.InOuterFace(graph, drawing, base)` — the two-clause conjunction, named | T1.8 |
| `Graph.foreignEdges` ("foreign", not "outside", which collides with `Plane.Graph.exterior`) | T1.8 |
| `Graph.IsCycleCrosscut` / `IsPlaneChain` as structures with named clause readers, not n-fold conjunctions | T1.8, T1.12 |
| Drop `Descent` / `CrosscutExists` / `CrosscutEnclosesOff` as Prop-valued abbreviations (owner decision) | T1.8 |
| `Plane.IsCrosscut(arc, curve, region, a, b)` — the three-clause crosscut conclusion, named once | T1.9, T1.12 |
| `Plane.IsTangentDisk(center, radius, p, region)` | T1.9 |
| `Plane.IsDenseIn(subset, target)` | T1.9 |
| `Plane.IsNearestOn(a, curve, q)` | T1.9 |
| `Plane.Vector.IsUnit(v)` / `Plane.WithinCone(v, w)` (the 60° condition) | T1.9 |
| `Plane.chainFinish(start, vertices)` | T1.9, T1.11 |
| A `Plane.Square` bundle (`center`, `radius`) with `.closed` / `.open` / `.boundary` / `.sides` / `.corners` | T1.10 |
| `⊆` on lists in place of `∀ P ∈ squareSides …, P ∈ pieces` | T1.10 |
| An infix or `‖p − q‖∞` spelling for `Plane.supDistance` | T1.10 |
| A named scope for "the even partition into `count` cells", so `samplePoint(count, i)` reads as `t(i)` | T1.10 |
| `Plane.CoordinateFrame` — a pair of affine coordinates that jointly separate points (replacing `i j : Fin 2`) | T1.11 |
| `Plane.Point.moveCoordinate(point, coordinate, value)` | T1.11 |
| `Plane.PolygonallyAccessible(region, point)` | T1.11 |
| `Plane.distanceToSet(point, set)`, with `distance(point, set)` overloaded | T1.11 |
| State the K(3,3) configuration through `Plane.Graph.IsDrawing` on an explicit six-vertex graph rather than a Fin-indexed `IsArcK33` | T1.11 |
| The nine terminals as an explicit ordered LIST with one strictly-increasing relation chain | T1.11 |
| `Plane.crosscutSide(arc, crosscut) := Plane.inside(arc ∪ crosscut)` | T1.12 |
| `Plane.PolyArc.carrier` / `.trimmed(i, trim)` / `.offset(i, t, s)` as the high-traffic names | T1.12 |
| `let`-bound frames and graphs inside proofs (`let base := vertex(i)`, `let subdivided := …`) | T1.2, T1.7 |

---

# Risk register

Deduplicated, ordered by severity. **L** = language/elaborator/tactic risk; **M** = mathematical content; **S** = scheduling/interface.

| # | Risk | Kind | Waves |
|---|---|---|---|
| 1 | **Cyclic vertex indexing is undecided and determines the cost of five waves.** Lean uses `ZMod (m+3)` with `val`, `val_lt`, `natCast_rightInverse` and `decide`; our `IntegerMod(n)` is an opaque quotient with only an existential representative and no decision procedure. Options: add a canonical `val`, or represent polygons by a cyclic vertex LIST (arcs become take/drop, the split permutation becomes `append_commutative`). Decide once, in T1.2, before any line is written; getting it wrong is a full-wave rewrite, not a refactor. | L / M | T1.2, T1.4, T1.5, T1.6, T1.7 |
| 2 | **Prerequisites owned by no wave.** `SimpleArc.lean` (lem:finite-polygonal-union, ~528 lines, consumed by T1.6/T1.9/T1.11), `SquareCycle.lean` (1052 lines, makes thm:arc-complement and thus thm:jordan unconditional), `PrePolygonArc.lean` (943), `FaceCycles.lean` (644), `Graph/K33.lean` (565). T1.7's real scope is ~4.8k Lean lines against a 2.3k row. Until these are scheduled the publish milestone cannot close. | S | T1.6, T1.7, T1.9, T1.10, T1.11 |
| 3 | **The ℤ/2 representation decision.** Lean leans on `ZMod 2` + `decide` in ~8 places (including a sixteen-case tautology and the closers inside `mark_step`). `IntegerMod(2)` is a quotient with no `decide` and no `by cases`. Recommended: stay in ℕ and spell parity as `2 ∣ (m+n)` / `Natural.IsOdd`; the identity is genuinely FALSE in ℕ without the mod-2 structure, so it can only be re-spelled, not dropped. A fresh two-constructor `Parity` type is the fallback if `2 ∣` starts fighting. | L | T1.1, T1.5, T1.4 |
| 4 | **No `omega`.** Natural-number index and block arithmetic that Lean discharges in one word becomes hand-written order reasoning: `PolygonBridge` (25–40% of its content on our side vs ~10% on Lean's), the `i*m … i*m+m` block bookkeeping in `outerOnPairs_familyChain`/`isPlaneChain_familyChain`, and the `i ≤ n` / `i ≠ j ± 1` side conditions on nearly every line of `ArcCollars`' disjointness section. | L | T1.4, T1.6, T1.10, T1.12 |
| 5 | **No `nlinarith`; `ordered_field` is linear over ring monomials.** Real instances: `‖x−q‖² < r²` with three coupled unknowns in Lemma 8.4; the germ product inequality `ρ(1+|⟪r₁,r₂⟫|) ≤ λ|det|` in `exists_half_width` (Lean uses `nlinarith` twice); `u₀² + u₁² = 1 ∧ |u₀| ≤ ½ ∧ |u₁| ≤ ½ → False`. Each needs an explicit squaring/monotonicity chain. Treat any friction as a deliverable, not a proof to bend. | L | T1.2, T1.4, T1.9 |
| 6 | **No `structure` keyword.** `IsSeparating` (5 fields), `IsPlaneChain` (9), `IsPolygonalCrosscut` (7), `IsArcCollar` (8), `IsArcStrip` (14), `StripData`, `IsFaceCycle`, `IsCycleCrosscut` (12) all become conjunctions. Follow the `Plane.IsArcBetween` precedent: right-nest so the most-cited leg is a direct projection (~90k kernel steps a site for getting it wrong), and supply a named accessor for every leg so no consumer destructures. The "export the construction, not a bundle" lesson is kept only by making the derived sets DEFINITIONS of the parameters, not fields. | L | T1.3, T1.5, T1.8, T1.10, T1.12 |
| 7 | **Case explosion, four named sites.** `sweep_mark_step` (Lean ~70 lines with `decide`; budget 250–350 here); `sides_disjoint` (4 sub-lemmas × index cases × a 3-way `Counterclockwise` disjunction); the K(3,3) `Fin 3 × Fin 3` bookkeeping (81 index pairs closed by `decide` in Lean, with no `Fin` and no enumeration tactic here); `tracks_disjoint` + `exists_near_sides` (~170 Lean lines) in T1.12. Mitigations that already work on the Lean side: prove the oriented form and get the other from `Crosses_reverse`; prove sign-free arc lemmas ONCE at the vector level so the collar file never unfolds `Counterclockwise`. | L / M | T1.1, T1.2, T1.7, T1.11, T1.12 |
| 8 | **Choice-of-constants threading.** `exists_cone_radius` combines four (T1.2) or five (T1.12) bounds through nested `min` towers; `exists_half_width` combines three including a product inequality; `exists_face_of_notMem_arc` threads seven named constants plus the √2/2 metric bridge. Our `Real.exists_common_positive_bound` folds a whole family at once and is better than a `min` fold — but only if each clause is phrased as `HoldsAtSmallerBounds`, and product index families need `List.cartesianProduct` of `List.range_up` at ~8 sites. | L | T1.2, T1.10, T1.12 |
| 9 | **The ordered-enumeration substrate does not exist.** `Finset.orderEmbOfFin` + `omega` gives Lean `par`/`parNext`/`exists_mem_gap` (~15 order lemmas over a finite set of reals); we have no sorting, no `Finset`, and `Set.IsFinite` is a predicate on TYPES. Carry the parameters as a LIST pulled back through the loop (finiteness becomes a length), but `List.increasingListing` with its permutation and strict-order lemmas is a day of work before any geometry. | M / L | T1.6 |
| 10 | **Natural subtraction `m + 3 − k`.** It appears ~30 times in `PolygonalCrosscut` and every proof of it goes through `omega`; the honest-subtraction convention widens `−` on ℕ to ℤ. Fix at the STATEMENT level: parameterise by two naturals with `k + l = m + 3`, and the subtraction never exists. A genuine improvement, to be adopted before line one. | L | T1.5 |
| 11 | **The open-segment parameter gap.** The library's one-dimensional coordinate along a segment is distance from the left end (`segment_order.math`), deliberately; heights are affine in the PARAMETER and not in the distance. Do not route the parity argument through `distance_from_left`; add `Plane.openSegment_parameter`. Related: `Plane.levelMeet` is `between` at a parameter OUTSIDE [0,1], where every existing lemma carries `0 ≤ t ≤ 1`. | M | T1.1 |
| 12 | **Lemma 1.4 (a) is deferred and is real proof content.** `IsCompact.exists_thickening_subset_open` has no sequential twin here and `Plane.distanceToSet` was explicitly not built; the complement of `U` is closed but not compact, so the closing-pairs argument runs on the compact side. ~100 lines, a prerequisite, not a stub. | M | T1.2, T1.11 |
| 13 | **Sequential compactness — three genuine bites, everything else free.** (a) `IsCompact.prod` for the closest pair on the middle line (T1.11) — route via `distanceToSet` instead of building product metric spaces; (b) `MetricSpace.IsCompact.union` missing everywhere a finite union of segments must be closed/compact; (c) Lemma 1.4 (a) above. Every other use (extreme value, compact separation, uniform continuity on a compact set) is already sequential in `Metric/`. | M | T1.2, T1.4, T1.6, T1.7, T1.9, T1.11 |
| 14 | **Clopen connectedness is a net WIN but must be factored once.** Lean's `IsPreconnected` two-open-set applications (`parity_eq_of_isPreconnected`, `preconnected_subset_interior`, the closed-gap-cover step, `covered_by_two_of_local`) become "this trace is nonempty relatively clopen, hence everything". Written ad hoc at ~6 sites it becomes a time sink; write `IsConnected.lands_in_one_of_two_opens` and `lands_in_one_closed_piece` once, in `Metric/`. Also: our `IsConnected` is `IsPreconnected` (vacuous on ∅), so `IsSeparating` MUST carry nonemptiness of both halves explicitly — the likeliest way to get T1.3 subtly wrong. | L / M | T1.1, T1.3, T1.6, T1.12 |
| 15 | **Component recognition has the wrong front door.** Ours (`Plane.Component.recognize`) takes relatively open + relatively closed; every consumer in T1.3/T1.5/T1.7/T1.12 holds "the frontier misses the ambient set". One bridging lemma, cited 3–4 times per wave. Do not assume the existing one is a drop-in. | L | T1.3, T1.5, T1.7, T1.12 |
| 16 | **Absolute vs relative topology.** `IsFaceCycle.frontier_eq`, `ends_in_face_boundary`, `IsRegionOf.Boundary_equals` and the whole T1.12 side API speak the ABSOLUTE frontier; ours is relative-from-the-start with `region = universe` as the absolute case. Confirm on one statement that the absolute reading is a one-liner before the T1.3 API freezes around it. T1.10 recommends sidestepping entirely by defining `squareBoundaryAbout` as a sup level set. | L | T1.3, T1.5, T1.7, T1.10, T1.12 |
| 17 | **Complement spelling mismatch.** `Plane.Graph` speaks `Set.complement`; `Plane.Component_boundary_in_closed` and `Component_boundary_outside_region` speak `Set.universe ∖ S`, which is NOT definitionally interchangeable (the difference carries a vacuous conjunct). Only 4 sites use the `∖ universe` form — reconcile them first. | L | T1.3, T1.4 |
| 18 | **`Set` and `List` algebra are thinner than they look.** No distributivity, no `∪`-monotonicity, no `(T∖S)∪S=T`, no closure monotonicity, no `List.reverse`, no `flatMap`/`flatten`, no `List.append_of_mem`, no permutation congruences, no `range_up` split. Five of T1.3's ~35 statements bottom out in one of these; individually trivial, collectively invisible to any Lean-derived line estimate. | L | T1.3, T1.4, T1.5, T1.7, T1.8, T1.10 |
| 19 | **Only countable choice is available.** Lean's Proposition 8.5 picks a nearest point of `C` for EVERY point of the plane and then restricts to a countable dense subset; `Logic.countable_choice` is ℕ-indexed. The construction must be re-planned to select along the enumerating sequence — a mathematical restructuring, to be decided before writing. | M | T1.9 |
| 20 | **Countability and separability have no home.** No `Set.Countable`, no `Countable.image`/`.mono`, no dense countable subset of ℝ or ℝ² anywhere (`Real/density.math` is one-sided). Restating Proposition 8.5 over a SEQUENCE is cheaper and closer to how the construction consumes it — but it is an interface change relative to `main` and needs owner sign-off. | M | T1.9 |
| 21 | **`IsPolygonal` shape mismatch at step one.** Lean's unfolds to a vertex list and feeds `segsOf vs` straight to the overlay; ours is a nested `chainFrom` union with no piece list and no bridge. The bridge also needs the two-distinct-points hypothesis (to drop degenerate segments) — that hypothesis is not an artefact. | M | T1.6, T1.9 |
| 22 | **Cast-tower friction on `samplePoint`.** Every order fact about `index / count` is a mixed ℕ/ℝ inequality; this is the first wave that does it in bulk. Probe before committing to the `i/n` design (which is otherwise a clear win — the refinement clause becomes an identity). | L | T1.10 |
| 23 | **List-valued vs set-valued graph union.** Lean's set-valued `Graph.union` makes `chainUnion_le` / `le_chainUnion` / finiteness three-line inductions; ours must thread `Graph.IsWellFormed` at every step of the block recursion (though the shared ambient `ends` removes Lean's `Compatible` hypothesis). Friction lands in a different place than the Lean proof puts it. | L | T1.8, T1.10 |
| 24 | **Do NOT import `Set.ncard`.** Lean's descent measure is a finite-set cardinality; ours must be `List.filter` length, for which `List.filter_length_strict` already exists. Getting this wrong drags in a finite-cardinality theory with no other use in the wave. | L | T1.8 |
| 25 | **Correctness trap: parity does not transport across normalization.** Normalization merges collinear edges and keeps no record of the deleted points, so `parity_subdivide` has no subdivision to be fed. Re-derive the two values from separation, as `PrePolygonSep` does; "optimizing" this into a transport loses a day. | M | T1.6 |
| 26 | **Correctness trap: `CrosscutEncloses` is FALSE without `x ∈ exterior`** (Lean finding 19; counterexample = unit-square cycle cut at (0,0),(1,1), crosscut through (½,½), x = (2/5,2/5)). Put the counterexample in the docstring; the clause is free at the call site. | M | T1.8 |
| 27 | **Two blueprint hypotheses the Lean proof refutes — carry them.** In cor:alternating-crosscuts the second crosscut need NOT be polygonal or simple, and the four-endpoint distinctness is subsumed. Stating the blueprint's stronger version silently breaks the K₃,₃ argument two waves later. Likewise Lemma 2.6 is stated WITHOUT the arc hypotheses, and "Ω is the region containing P ∖ {p,q}" is dropped in favour of an inclusion — reintroducing either makes the lemma unusable at its call sites. | M | T1.3, T1.5 |
| 28 | **The corner hypothesis of `exists_closedPolygon_arcs` is not negotiable.** `ClosedPolygon.vertex_IsCornerAt` proves a cut point at which the curve runs straight is a vertex of NO realization. State the impossibility lemma beside the hypothesis, or T1.7 will try to drop it. `exists_prePolygon_split` is the corner-free alternative. | M | T1.6, T1.7 |
| 29 | **Adopt the named-hypothesis discipline; do not discharge inline.** `Jordan.lean` carries "every simple arc has connected complement" explicitly and `JordanClosed.lean` discharges it in one line — that split is what caught finding 19. Conversely, do NOT replicate Lean's `CrosscutSplitsRegion` hypothesis-then-primed-restatement in T1.7: build `crosscut_splits_region` first and state `face_cycles` unconditionally (the Lean integrator says so). | S | T1.7, T1.8, T1.11, T1.12 |
| 30 | **Interface risk with T1.7.** `alternating_meets_crosscut` was written against `IsK33Config.chords_alternate` and verified term by term; preserve the argument shape (`A`, `B`, `A ∩ B = {p,q}`, `w₁ ∈ A ∖ {p,q}`, `w₂ ∈ B ∖ {p,q}`) exactly. The piece missing at that seam on the Lean side was the hexagon REALIZATION step — most likely to come up one clause short. | S | T1.5, T1.7 |
| 31 | **Point/Vector split: mostly favourable, three rough spots.** Every one of T1.1's ~40 frame lemmas re-types (anchor at `origin` once, then use the difference lemmas and never mention it again); T1.2's `cone_eq_image` needs continuity of a TRANSLATION, which does not exist — prove sector connectedness directly instead; T1.4's `Plane.Point.equal_of_position` chains replace Lean's `module` (budget 3–5 lines each). T1.3, T1.5 and T1.8 have no exposure at all. | M | T1.1, T1.2, T1.4 |
| 32 | **Placement warts to flag upward.** `Plane.Segment` and `Plane.subdivide` live under `Plane/Graph/` though crossing parity has nothing to do with graphs (raise before T1.4 makes it load-bearing); `Plane.outside` collides with an unrelated local sense in `twoarcs.math`; `Plane/polygonal_jordan.math` must NOT import `Plane/Graph/` (the Lean side refuses the same import to keep the layering); Part I needs both `Plane/` and `Plane/Graph/`, so a new `Plane/Jordan/` area is proposed. | S | T1.1, T1.3, T1.4, T1.6 |
| 33 | **Redundancy-checker trap.** `crosscut_at_most_two` carries `IsPolygonal P` as a hypothesis its proof never uses (Lean marks it `_hPpoly`); it is the blueprint statement and what makes `HasArcCollars` dischargeable. The unused-name cascade will flag it — record it as a deliberate keep. | L | T1.12 |
| 34 | **Wave ordering is strict, and three waves cannot start.** T1.3 has no dependency on T1.1/T1.2 and should be built FIRST. T1.4 is strictly downstream of T1.1+T1.2+T1.3; T1.5 of T1.1+T1.3+T1.4; T1.7 of T1.3 (hard) plus T0/T1.4/T1.6 for its headline; T1.8 of T1.1+T1.3+T1.4+T1.6+T1.7; T1.11 of T1.9+T1.10; T1.12 of T1.2+T1.3. The arc half of T1.6 (`PolyArcRealize`) is blocked on T1.12. What CAN start immediately in parallel: all list/set/real infrastructure, the square geometry and mesh block of T1.10, the cone geometry of T1.9, and the combinatorial half of T1.8. | S | all |

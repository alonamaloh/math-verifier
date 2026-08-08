# Frictions found building `library/Plane/Graph/` (Layer 6)

Working notes in `QUIRK.md`'s style: symptom, minimal repro, root cause
where I found it, and what the library currently does about it.

Provenance: opening Layer 6 of the Jordan–Schönflies foundation
(`PLAN_JORDAN_SCHOENFLIES.md`) — `Plane/Graph/{basics,pointset}.math`, plus
`Lists/set_union.math` and `Metric/finite_union.math` underneath. This is the
first development that mixes the ambient edge triple of Layer 5 with the
plane's metric topology, and the first to live in a **nested** module
directory.

**Not a friction, but worth recording:** nested module directories work end
to end on the first try. `library/Plane/Graph/basics.math` declaring `module
Plane.Graph.basics` builds, caches, resolves imports, and passes
`make docs-check`; the Makefile's `find` is recursive and import resolution
maps dots to slashes (`modulePathWithExtension`, `src/main.cpp`). Nothing in
the build system had to change. This is the repo's first three-component
module name.

---

## L1 — DESTRUCTURING list membership is plumbing the prover doesn't do

**Scope, measured.** Only the *destructuring* direction. Building a
membership is already by-less: `head ∈ List.prepend(A, head, tail);` and
`item ∈ List.prepend(A, head, tail);` (from `item ∈ tail`) both close with no
citation — `--check-redundant-by` flagged the `List.member.here` /
`List.member.there` citations I first wrote as redundant, and both are now
bare in `Metric/finite_union.math`. It is reading a membership apart that
costs a citation.

**Symptom.** Two of them, in one twelve-line proof
(`List.unionOver_member`, `Lists/set_union.math`):

```math
case list = List.empty:
    done by List.no_member_empty                            -- (a)
case list = List.prepend(head, tail) for some head, tail:
    done by cases {
      case item = head: …
      otherwise: {
          item ∈ tail by List.member_of_prepend_not_head;   -- (b)
          …
        }
    }
```

- **(a)** goal `False` with `item ∈ List.empty(A)` in context. The prover
  reports "no in-scope contradiction lets us close it" and then offers
  `NaturalsBelow.zero_is_empty` plus four unrelated `→ False` lemmas from the
  conclusion-shape index — none of them about lists.
- **(b)** goal `item ∈ tail` from `item ∈ List.prepend(A, head, tail)` and
  `¬(item = head)`.

Both survive `--check-redundant-by`, so both are load-bearing.

**Why it is friction and not a missing lemma.** Both lemmas exist and are
correctly named; the objection is that citing them is what `docs/style.md`
forbids under *"Set-membership plumbing is not a citation"*. A mathematician
writing "the item is not the head, so it is in the tail" cites nothing, and
"nothing is a member of the empty list" is not a step at all. The rule was
written for `Set` and the auto-prover's battery was extended to match it
there; the same two rules for `List` were not added, even though the
construction direction was.

**What the natural form should be.** Bare steps:

```math
item ∈ tail;     -- from membership at a prepend plus `item ≠ head`
done             -- from `item ∈ List.empty(A)`, which is absurd
```

**Suggested fix.** Two rungs, mirroring the build direction that already
works: refute a membership whose list is `List.empty`, and split one whose
list is `prepend(head, tail)` on `head`-equality.
`List.no_member_empty` and `List.member_of_prepend_not_head`
(`Lists/list.math`) are already exactly those rules; they only need to be
reachable without being named. Worth measuring the blast radius first — the
library has many list inductions, so this should *remove* citations broadly
rather than only serve Layer 6.

---

## L2 — an equation case refines the GOAL but not the hypotheses

**Symptom.** In `Plane.segment_meet` the argument splits on whether the first
segment is degenerate:

```math
theorem Plane.segment_meet (a b c d : Plane.Point)
        (meets : Set.IsNonempty(Plane.Point,
            Plane.segment(a, b) ∩ Plane.segment(c, d)))
        : ∃ (p q : Plane.Point).
              Plane.segment(a, b) ∩ Plane.segment(c, d) = Plane.segment(p, q) :=
  done by cases {
    case a = b as endsEqual: …
```

Inside that arm the reported goal is

```
∃ p q. Set.intersection (Plane.segment b b) (Plane.segment c d) = Plane.segment p q
```

— `a` has been rewritten to `b` — while `meets` is still reported as
`Set.IsNonempty (Set.intersection (Plane.segment a b) (Plane.segment c d))`.
So the arm opens with two spellings of the same set, and every step that
feeds the hypothesis into a lemma about the goal has to bridge them by hand.

**Why it bites.** The refinement direction is not the one a reader picks. The
arm was written to reason about the *degenerate* segment, which reads
`segment(a, a)`; the elaborator produced `segment(b, b)`. A theorem
*parameter* is not refined at all, so the mismatch is not merely cosmetic —
it is between a rewritten goal and an unrewritten premise.

**What the natural form should be.** Either both refine or neither does. A
`case a = b` arm that rewrote the hypothesis too would let the arm be written
in one spelling throughout.

**What the library does about it.** Takes the degenerate case out as its own
theorem, `Plane.segment_meet_at_point`, stated in a single point name, so the
arm only has to transport `meets` once and then cite it:

```math
case a = b: {
    Plane.segment(a, b) = Plane.segment(b, b);
    Set.IsNonempty(Plane.Point, Plane.segment(b, b) ∩ Plane.segment(c, d))
        by substituting (Plane.segment(a, b) = Plane.segment(b, b));
    Plane.segment(b, b) ∩ Plane.segment(c, d) = Plane.segment(b, b)
        by Plane.segment_meet_at_point;
    witness b with witness b
  }
```

That is a good factoring on its own terms, so the cost here was small. It
would not be, in a proof whose degenerate case is not separable.

**Second occurrence, 2026-07-29** (`Plane.subdivide_avoids`, the
`case point = head` arm). Here the refinement went the useful way: the goal
became `¬(head ∈ …)` while the hypothesis stayed at `point`, and the arm was
simply written in terms of `head`, dropping a `by substituting` and a dead
label. So the asymmetry is not always a cost — but it is always a surprise,
and the error it produces when you write the arm the other way round
("this case's result has the wrong type for the function's declared return
type") does not mention the refinement at all. That message is the friction
as much as the behaviour is.

---

## Not frictions — two error messages that did their job

Recorded because they were the two places the build stopped, and in both the
message named the fix outright:

- ``field``: *"carrier `Real` uses the partial reciprocal
  `Real.reciprocal(b, proof)`, which carries its own nonzero proof — call
  `field` with no arguments (the proof rides on each `/`)"*. Written as
  `by field(gapNonzero)`, fixed to `by field`.
- A chain step that changed **two** subterms at once
  (`nearest` and `farthest` in one `Plane.between(…)`) with only one equation
  cited. Diff-inference wants one change per step; splitting it in two was the
  fix.

---

## L3 — `suppose x ∉ S for contradiction` is not recognised as a reductio — **FIXED 2026-07-30**

**Symptom.** `∉` is ordinary notation for `Not(x ∈ S)` — the lexer maps it to
`TokenKind::NotElementOf` and `Test/negated_relation_operators_test.math`
checks that `x ∉ s` and `Not(x ∈ s)` are interchangeable as *types*. But the
terminal reductio form does not see through it. In
`Plane.Component_boundary_in_closed`:

```math
        : x ∈ closedSet := {
  …
  suppose x ∉ closedSet for contradiction {   -- REJECTED
    …
  };
  done
```

fails with `claim 'Set.member Plane.Point x closedSet'` at the closing `done`
— i.e. the `suppose … for contradiction` did not register as discharging the
goal, so the goal was still open. Writing the same thing as

```math
  suppose ¬(x ∈ closedSet) for contradiction {   -- ACCEPTED
```

works. Found while sweeping `¬(a ∈ b)` → `a ∉ b` at the owner's request; that
one site is left in the `¬(…)` spelling because of this.

**Why it matters beyond the one site.** The sweep is now the house style, so
every future reductio whose goal is a membership hits this, and the error
message points at the closing `done` rather than at the `suppose` — nothing in
it suggests the negation spelling is the problem.

**Root cause, and the fix.** Re-tested before working around it, and the
symptom is narrower than recorded above: only the **forward** (braced) form
was affected. The terminal form accepts `∉` and always did — the entry's
repro is the forward form, and its diagnosis ("did not register as
discharging the goal") was wrong. What the forward form does depends on
whether the assumption is a negation: for `P = Not(X)` it eliminates the
double negation and establishes `X`, otherwise it establishes `Not(P)`. That
test (`parser.cpp`, `BlockWrapper::SupposeForContradictionForward`) knew the
`¬` prefix, a `Not(…)` application, and `≠` — and nothing else, so `x ∉ S`
established `Not(Not(x ∈ S))` and the goal stayed open.

Fixed by giving the negated relations one shared list,
`positiveRelationSymbol` in `syntax/surface.hpp`, used both by the
desugaring that turns `a ∉ b` into `Not(a ∈ b)` (`dispatch.cpp`, which had
the list inline) and by the reductio's negation test. Adding a negated
operator now cannot teach the desugaring about it and leave the reductio
behind — which is exactly how `≠` came to be handled and `∉` did not.

Pinned by six theorems in `Test/negated_relation_operators_test.math`, one
per operator plus the terminal form. Measured, while there: with the fix
reverted, the `≰` case fails outright, and the `∉` case still *verifies* —
the auto-prover's own reductio rung reproves the goal — but with the
"vestigial detour" warning, because the fact the block established was the
double negation and nothing consumed it. So the operator-specific pinning
lives in the `≰`/`∤`/`⊈` cases, and the real-world `∉` guard is
`Plane.Component_boundary_in_closed`, now written in the `∉` spelling.

Beyond this layer: `Metric/{sequence,real,compactness,separation,connected,
interval}.math` have six reductios spelled `¬(…)` that the negated operators
can now carry. Left alone — `Metric/` is not in `scripts/clean_manifest.txt`,
and style sweeps are manifest-scoped. `¬(∃ …)` sites stay as they are, and
`<` has no negated operator to move to.

---

## L4 — a disjunction goal makes the prover try the false side first

**Symptom.** Two shapes, both from the overlay, both cured the same way.

```math
-- (a) `Plane.splitSegmentAt_ends`, goal `point = cut ∨ Plane.IsEndOf(point, piece)`
--     with `Plane.IsEndOf(point, piece)` in context:
warning: expensive by-less proof step (80456 kernel-steps) — the auto-prover
closed it by search (via the disjunctionIntro strategy)

-- (b) `Plane.same_ends_of_meeting_interiors`, goal
--     `(A ∧ B) ∨ (C ∧ D)` between point equations, with `A` and `B` in context:
elaborate error: the auto-prover gave up after exhausting its effort budget
```

**Why it bites.** The style guide's rule is to state the true disjunct and
close bare — "the auto-prover's disjunction-introduction picks whichever
disjunct is in context". It does, but it tries the disjuncts in order, and
*failing* on the other one is what costs: in (a) 80k kernel-steps twice, in
(b) the whole budget in a context of twenty hypotheses about points. The
recommended form is the slow one, and nothing in the warning says which
disjunct was expensive.

**What the library does about it.** Two different answers, and the difference
is worth keeping:

- In (a) the disjunction was avoidable. `splitSegmentAt_ends` was restated in
  the negative — "an end of a half that is not the cut point was an end it
  inherited", `(notCut : point ≠ cut)` as a hypothesis and `Plane.IsEndOf` as
  the bare conclusion. That removed the disjunction from the goal, removed
  two case splits from the proof, and reads better than what it replaced. Its
  two consumers (`splitAllAt_ends`, `subdivide_ends`) then needed no case
  analysis at all.
- In (b) the disjunction IS the statement (two names for one segment, in one
  order or the other). There the fix is to name the injection —
  `done by Or.introduceLeft` — which the warning asks for and which reads as
  "this is the left case", at the cost of a mechanism name the style guide
  would rather not see.

**Suggested fix.** Try the disjuncts cheaply before committing: a disjunct
whose head is a constructor-shaped equation between distinct variables cannot
be closed from context by the equality battery, and a syntactic pre-check
would skip it in the cases above. Failing that, the warning should say which
side the search spent its budget on, so that the author can name the other.

## L5 — the matcher does not reduce a projection of a definition

**Symptom.** `Graph.vertices(Plane.overlayGraph(pieces, points))` is
definitionally `List.deduplicate(…)` — `overlayGraph` is a plain definition
whose body is `Graph.make(…)`, and `Graph.vertices` is the first projection —
but

```math
List.Distinct(Plane.Point, Graph.vertices(Plane.overlayGraph(pieces, points)))
    by List.deduplicate_distinct;
```

fails with *"the conclusion shape fits, but an argument could not be inferred
from the goal"*: matching `List.deduplicate(?list)` against
`Graph.vertices(overlayGraph(…))` needs one δ-step and one ι-step, and the
matcher does neither.

**What the library does about it.** States the fact at the reduced spelling
and transports it by the characterizing equation, which the definition
publishes anyway (`Plane.overlayGraph_vertices`):

```math
Graph.vertices(Plane.overlayGraph(pieces, points))
    = List.deduplicate(Plane.endsList(Plane.overlayPieces(pieces, points)))
    by Plane.overlayGraph_vertices as verticesAre;
List.Distinct(Plane.Point,
    List.deduplicate(Plane.endsList(Plane.overlayPieces(pieces, points))))
    by List.deduplicate_distinct;
List.Distinct(Plane.Point, Graph.vertices(Plane.overlayGraph(pieces, points)))
    by substituting verticesAre;
```

Three lines where one should do. Publishing the characterizing equations is
good practice regardless, so the cost is small — but the same shape will
recur at every graph a construction builds, and whnf-ing the goal's arguments
before matching would remove it.

## L6 — `let` in a proof abbreviates, but membership does not see through it twice

**Symptom.** With `let grown : List(Plane.Point) := List.prepend(P, u,
List.prepend(P, v, tail));`, the claim `u ∈ grown` closes by itself, and
`v ∈ grown` does not — the second needs the membership one level down, and
that is one ζ-step further than the prover takes. Stating the intermediate
(`v ∈ List.prepend(P, v, tail);` then `v ∈ grown;`) fixes it.

Recorded rather than worked around: the `let` is house style (it names the
object under construction, and the alternative is a three-line term repeated
at every membership claim), and one extra line per claim is a small price.
Related to L1 — building a membership is free only at the head.

## L7 — a `⊆`-on-lists citation needs its premise hoisted, and the error blames the wrong thing

**Symptom.** In `Plane.Graph.IsDrawing.path_IsArcBetween`, inside the step
case of an induction on a path derivation, with
`restPath : Graph.IsPath(graph, waypoint, rest, stepTarget)` among the case
binders:

```math
rest ⊆ Graph.edges(graph) by Graph.IsPath.edge_is_edge;   -- REJECTED
```

```
its conclusion is about `List.memberOf` but the goal is about `List.Includes`
  — this lemma does not target this goal (check the lemma name)
```

The lemma's conclusion *is* `List.Includes(edgeList, Graph.edges(graph))`,
which is what the goal is; the message is printed after the matcher has
δ-unfolded `List.Includes` on one side only and compared heads. Adding the
premise as its own line fixes it:

```math
Graph.IsPath(graph, waypoint, rest, stepTarget);
rest ⊆ Graph.edges(graph) by Graph.IsPath.edge_is_edge;   -- ACCEPTED
```

**Why it bites.** Hoisting the premise is the documented recipe
(`docs/style.md`, "hoist the premises, then cite bare"), so the *fix* is
house style and the cost is one line. The friction is the diagnosis: it says
the lemma is the wrong lemma and tells the author to check its name, when the
lemma is right and the missing thing is a premise the matcher could not
discharge. Nothing in the message mentions premises. Compare the message the
same matcher prints elsewhere — *"the conclusion shape fits, but an argument
could not be inferred from the goal or a premise discharged from context"* —
which is the accurate one; the `List.Includes` case takes a different branch
and prints the misleading one.

**Suggested fix.** Compare heads only after unfolding both sides, or not at
all when the lemma's conclusion is a transparent definition; and reserve
"check the lemma name" for a genuine head mismatch.

## L8 — disjunction-introduction does not walk a nested union

**Symptom.** With

```math
definition Plane.beyondSquare (radius : ℝ) : Set(Plane.Point) :=
  ((Plane.farRight(radius) ∪ Plane.farAbove(radius)) ∪ Plane.farLeft(radius))
      ∪ Plane.farBelow(radius)
```

and `x ∈ Plane.farRight(radius)` in context, the claim
`x ∈ Plane.beyondSquare(radius)` is not closed: the prover reports "no
in-scope hypothesis matches structurally" and offers `Set` lemmas about
complements and intersections. Spelling the two intermediate unions closes
it:

```math
x ∈ Plane.farRight(radius) ∪ Plane.farAbove(radius);
x ∈ (Plane.farRight(radius) ∪ Plane.farAbove(radius)) ∪ Plane.farLeft(radius);
done
```

**What the library does about it.** Four one-line theorems,
`Plane.farRight_beyondSquare` and its three siblings, so the walk is paid for
once. That is worth having anyway — the side names are what the argument
speaks — so the cost was small, but the shape recurs at every union of more
than two sets.

Same family as L4: the disjunction machinery is a single rung, and it neither
recurses nor reports which disjunct it tried.

**Not a friction, but worth recording.** A bare stated inequality can come
back wearing a local definition's clothes. `radius < -(-reach)`, stated in
`Plane.beyondSquare_IsUnbounded` to feed a `Plane.farLeft` membership, is
reported in a later context dump as
`Plane.HalfPlane Real.negate radius (-reach)` — the elaborator folded the
inequality into the definition that happened to match it. Harmless, and the
proof is unaffected, but a hypothesis list that renames the author's own
claims is hard to read.

## L9 — the expensive-step warning cannot see the layer's expensive declarations

**Symptom.** `Plane.IsEndOf.orientSegment` (191 s), `Plane.subdivide_common_segment`
(94 s) and `Plane.subdivide_separated` (40 s) are ~5.5 of the ~6 minutes
`Plane/Graph/` costs, and **none of them emits any warning**. Everything else
in the area is under 1.5 s.

Two independent reasons, both now understood:

- the warning's threshold was in **kernel steps**, and their cost is
  elaborator wall clock — defeq probes in `contextEqualityBridge`, which
  barely move the step counter;
- the warning fires only on a by-less claim that **succeeds** (`if (proof)`),
  and only ~0.7 s of `subdivide_separated`'s 40 s is in by-less claims. The
  rest is premise discharge for citations already written by hand.

**Partly fixed 2026-07-30.** The warning now names the winning fact's
PROPOSITION when the winner has no citable name (an anonymous claim or a
conjunction leg — `citableNameFromFactSource` returns empty for those, so the
message used to name only the strategy), names the dominant LOSING tactic and
what it cost, and fires on wall clock too (`MATH_AUTOPROVE_WARN_MS`, default
1500). Library-wide that went from ~35 to 47 expensive-step warnings, all
carrying a millisecond figure.

**Closed 2026-07-30 by `MATH_TIME_CLAIMS=1`**, which times every structured
claim — hinted, by-less, failed, speculative — and reports per declaration
sorted by self time. It localised all three immediately: each is ONE claim.
`Plane.IsEndOf.orientSegment` is 188 s in a single `by substituting` whose
REWRITE is the cost (its rewritten goal is closed by `localFactExactMatch`,
the cheapest rung there is); `Plane.subdivide_separated` is 39 s in the
disjunction goal this log already records as L4, closed not by the author's
cited lemma but by `contextEqualityBridge` reaching for
`Plane.segmentDrawing_arcFinish` — a lemma about drawings, in a claim about
endpoints. Full ledger, the wrong hypotheses it killed, and what to try next:
`PERF_EXPENSIVE_DECLARATIONS.md`.

## L10 — `suppose` does not destructure a goal spelled through a `let`-bound predicate

**Symptom.** Building B2 (`Plane/Graph/vertexsquares.math`), the property fed
to `Real.exists_common_positive_bound` is named by a `let`:

```math
let misses : Plane.Point → ℝ → Proposition :=
    (other : Plane.Point) ↦ (radius : ℝ) ↦
        (other ≠ vertex → other ∉ Plane.squareAbout(vertex, radius));
```

Inside the `Real.HoldsAtSmallerBounds(misses)` proof the goal after the
introductions is `misses(other, smaller)`. Supplying a type reduces fine —
`suppose other ≠ vertex → other ∉ Plane.squareAbout(vertex, larger);`
discharges the hypothesis `property(item, larger)` — but *destructuring* the
goal does not: `suppose other ≠ vertex;` fails with

```
bare `claim` / `done` needs an expected type from context (none available)
```

reported against the block's closing `done`. So the elaborator ζβ-reduces a
supplied type against the expected one, but does not ζβ-reduce the expected
type before asking whether it is an implication.

**Least-bad accepted phrasing.** One `change` line with the reduced spelling,
which is what `change` is documented for and which reads as "we need to show":

```math
change other ≠ vertex → other ∉ Plane.squareAbout(vertex, smaller);
suppose other ≠ vertex;
```

The same shape appears in the arms of a `by cases` whose goal is the
`let`-spelled property, and there the fix is to state the reduced proposition
outright rather than the `misses(item, bound)` spelling.

**Natural form.** `suppose` (and `take`, and the `by cases` arm) should WHNF
the goal — ζ through local `let`s included — before deciding what it is.
`Real.exists_common_positive_bound` itself is cited argument-free, so nothing
else about the `let` costs anything.

## L11 — `ordered_field` sees a division as an opaque product

**Symptom.** With `let gap : ℝ := Plane.distance(vertex, other) / 4;` in scope
and `Plane.distance(vertex, other) > 0`, the step `2 * gap < 4 * gap` is
refused:

```
Note that the goal is not linear: `(Real.reciprocal 4) * (Plane.distance vertex other)`
is an independent variable of the linear model, and nothing relates it to its factors.
```

The tactic does ζ-unfold the `let` — the message quotes the unfolded term —
but then treats `reciprocal(4) * d` as an atom instead of evaluating the
ground reciprocal to the rational `1/4` and scaling.

**Least-bad accepted phrasing.** State the defining equation once, in
multiplied form, and let every later step be linear in `gap`:

```math
let gap : ℝ := Plane.distance(vertex, other) / 4;
4 * gap = Plane.distance(vertex, other);
```

This is arguably better prose anyway ("four times the gap is the distance"),
so it is a small tax; but a mathematician would not have paused.

## L12 — the goal printer names a set-shaped definition instead of the relation

**Symptom.** Every error report in this file printed
`Plane.distance(vertex, other) > 0` as
`Plane.HalfPlane (Plane.distance vertex) 0 other`, and
`Plane.distance(vertex, other) < Plane.distance(vertex, other)` as
`Plane.Ball vertex (Plane.distance vertex other) other`. The printer is
folding the goal against any definition whose body matches — here the
half-plane and the open ball, neither of which the proof mentions.

Cosmetic, but it costs real reading time in exactly the situation where the
message matters. Same family as the recorded `Set.singleton`-instead-of-`=`
printer bug in the matrix error tests.

## L13 — `suppose ¬P` toward a positive goal needs `for contradiction`, and the error blames the closer

**Symptom** (B4, `cores.math`). Writing `Graph.Incident(…) by { suppose
¬Graph.Incident(…); …; done }` fails at the `done` with "bare `claim` /
`done` needs an expected type from context", pointing at the closer rather
than at the `suppose`. The adjacent shape `¬P by { suppose P; …; done }` —
where the goal already IS a negation — works without any keyword, which is
exactly why the mistake is easy to make.

**Natural form.** A diagnostic at the `suppose` itself: "the goal is `P`,
not a negation; did you mean `for contradiction`?" — landing on the line
the author has to change.

## L14 — overload dispatch reads argument heads before numeral coercion

**Symptom** (B4, `cores.math`, six sites). `distance(0, y)` with `y : ℝ`
is rejected — "no overload of `distance` matches arguments of types
(Natural, Real)" — and needs `distance((0 : ℝ), y)`. Bare numerals coerce
in ordinary argument positions, so the gap is specifically that overload
dispatch resolves before the coercion join runs on the operands.

## L15 — a hypothesis headed by a `let`-bound predicate cannot be applied

**Symptom** (B7, `tubes.math`). With

```math
let separated : E → E → ℝ → Proposition :=
    (edge : E) ↦ (other : E) ↦ (gap : ℝ) ↦ (other ≠ edge → ∀ …);
let separatedFromAll : E → ℝ → Proposition :=
    (edge : E) ↦ (gap : ℝ) ↦
        ∀ (other : E). other ∈ Graph.edges(graph) → separated(edge, other, gap);
```

a context fact `separatedFromAll(edge, epsilon)` is useless: the prover
instantiates it at `other` and reaches a term of type
`separated edge other epsilon`, which is an implication only after ζ, and
then the application is refused with

```
this is being applied to an argument, but it is not a function
  it has type:   separated edge other epsilon
```

The error is attributed to the `let` **binding line**, not to the step whose
proof search failed, so nothing in the message points at the fact being used.
Stating the proposition is fine everywhere — only *applying* it fails — so
the same `let` reads perfectly in the statement positions two lines above.

**Accepted phrasing.** Spell the inner predicate's body out inside the outer
`let`, so the hypothesis's type is an honest chain of `→`. The duplication is
the tax; the natural form is for the prover to ζ-unfold before deciding a
term is not a function.

## L16 — a vacuous `x ≠ x` reductio costs a second unless reflexivity is hoisted

**Symptom** (B7, `tubes.math`). In the `case other = edge` arm the separation
clause is vacuous, so it is discharged by `{ suppose edge ≠ edge; done }`.
That `done` is closed, but by a one-second reductio search:

```
warning: expensive by-less proof step (74607 kernel-steps, 1034 ms) —
  the auto-prover closed it by search (via the reductio strategy)
```

`done by Equality.reflexivity` is not available — `Equality.reflexivity` is
the constructor of `=`, not a citable declaration ("unknown lemma … no
declaration by that name is in scope"). The accepted phrasing is a bare
`edge = edge;` line ahead of the block, which drops the cost to nothing but
reads as pure plumbing. A citable reflexivity, or a cheap reflexivity rung
ahead of the reductio one, would remove both.

Also worth recording beside L2: in that arm the equation refines the **goal**,
so the vacuous clause has to be *stated* in the refined spelling (`edge`
everywhere, never `other`), or `witness` reports a conjunction it cannot
split.

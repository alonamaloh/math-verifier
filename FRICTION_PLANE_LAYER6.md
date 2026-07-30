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

## L3 — `suppose x ∉ S for contradiction` is not recognised as a reductio

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

**Suggested fix.** Wherever the reductio matches the supposed proposition
against `Not(<goal>)`, normalise the negated-relation notations first (`∉`,
`≠`, `≰`, `∤`) — they are the same term, so this is a matcher gap rather than
a semantic one. Worth checking `≠` in the same position while there: a goal
`a = b` with `suppose a ≠ b for contradiction` is the identical shape and
probably fails identically.

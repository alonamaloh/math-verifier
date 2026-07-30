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

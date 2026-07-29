# Frictions found building `library/Graph/` (Layer 5)

Working notes in `QUIRK.md`'s style: symptom, minimal repro, root cause
where I found it, and what the library currently does about it.

Provenance: opening Layer 5 of the Jordan–Schönflies foundation
(`PLAN_JORDAN_SCHOENFLIES.md`) — `Graph/{basics,walk,path,connected}.math`.
This is the first development in the library built over an **ambient
parameter triple** `(V, E, ends)` carried by `convention`, and the first
whose central objects are indexed inductive relations over that ambient.
Both of those are what the entries below are about.

---

## G1 — `choose … such that P` is unverified unless the source is a lemma

**Symptom.** The `such that` clause is silently discarded. The witness is
bound with whatever type the scanned existential happens to have, and the
condition the proof text claims is never checked.

**Minimal repro.**

```math
theorem ChooseProbe.unmatched (A B : Type(0)) (P : A → Proposition) (Q : B → Proposition)
        (only : ∃ (a : A). P(a))
        : True := {
  choose witnessValue such that Q(witnessValue);   -- Q is about B, not A
  sorry
}
```

`--goal-at` reports `witnessValue : A`. No error, no warning about the
mismatch — only the unrelated unused-name warning.

**Root cause — found.** `Elaborator::elaborateChoose`,
`src/elaborator/induction.cpp`. `choose.predicate` is consumed in exactly
one branch: *lemma source with `such that`*, which ascribes the citation
against the assembled `∃ (name : T). predicate`. The other three branches —
`from <hypothesis>`, `from <statement>`, and the no-`from` scan (which
takes the most recent binder whose type is `Exists`-headed) — build the
destructuring `cases` directly from the scrutinee and never look at the
predicate again.

**Why it matters.** `docs/style.md` sells `choose` as showing "— and the
kernel verifies —" what the witness satisfies, and the library has ~1465
`such that` sites. Most are honest; none of them are *checked* unless they
name a lemma. A mistaken one reads as verified mathematics.

**How it bit.** In `Graph/walk.math`, `choose farEnd such that
Graph.Joins(graph, usedEdge, vertex, farEnd)` was written with the
intended existential (`Graph.Incident`) sitting inside a conjunction and
behind a definition, so the scan reached past it to an unrelated `∃` over
the *edge* type and bound `farEnd : E`. The proof then failed a citation
several lines later, with nothing pointing at the real mistake. Fixed in
the library by naming the source: `from incidentAtVertex`.

**Suggested fix.** Assemble the nested `∃ (name : T). predicate` in every
branch, not just the lemma one, and ascribe the scrutinee to it — the code
that does this already exists a few lines above. Where no in-scope
existential matches the predicate, say so instead of taking the most
recent one.

---

## G2 — an inductive takes neither `convention` nor implicit binders, and
its applications get no leading-argument inference

**Symptom.** With

```math
convention V : Type(0)
convention E : Type(0)
convention ends : E → Pair(V, V)

inductive Graph.IsWalkOver (V : Type(0)) (E : Type(0)) (ends : E → Pair(V, V))
        (graph : Graph(V, E, ends)) : V → List(E) → V → Proposition where …
```

a statement `Graph.IsWalkOver(graph, source, edgeList, target)` fails with

```
this argument has the wrong type for the function it is given to
  the function expects: Type 0
  but this argument is: Graph V E ends
```

— the ambient triple has to be spelled at every occurrence. Declaring the
inductive's parameters as `{V : Type(0)} …` parses but changes nothing.

**Root cause.** Documented, in part: `docs/conventions/structures-and-inference.md`
says conventions "fire on `definition` and `theorem`. Inductive
declarations and axioms are not covered." The leading-argument inference
that makes `Graph.Joins(graph, edge, u, v)` work for a *definition* is the
same machinery, and it is likewise not reached for an inductive type
application.

**What the library does.** Every indexed inductive is declared with the
ambient spelled and immediately re-exposed as a transparent reader:

```math
definition Graph.IsWalk (graph : Graph(V, E, ends)) (source : V)
        (edgeList : List(E)) (target : V) : Proposition :=
  Graph.IsWalkOver(V, E, ends, graph, source, edgeList, target)
```

This is the `List.member` / `List.memberOf` pattern, and it works
completely — `by induction on <reader-typed hypothesis>` splits on the raw
constructors, and citations bridge the two spellings. The cost is a second
name per relation plus a wrapper theorem per constructor (G3).

**Suggested fix.** Let `convention` fire on `inductive`, or honour `{…}`
binders there. Either removes the reader for the common case.

---

## G3 — a constructor citation cannot recover a parameter that no index mentions

**Symptom.** `Graph.IsWalk(graph, target, List.empty(E), target) by
Graph.IsWalkOver.arrived;` fails with

```
could not infer hole(s) at position 2
```

position 2 being `ends`. The goal pins `V`, `E` and `graph`; `ends`
appears in the goal only inside `graph`'s *type*, and the unifier does not
read it back from there.

**What the library does.** Each constructor gets a one-line theorem
wrapper (`Graph.IsWalk.empty`, `Graph.IsWalk.extend`) whose ambient
arguments are convention-implicit and therefore solved from the graph.
Consumers cite the wrapper, which reads better anyway — "extend the walk"
rather than the constructor's name.

**Note.** This is not specific to inductives: any lemma with a parameter
occurring only inside another parameter's type will hit it. It bites here
because G2 forces those parameters to be explicit.

---

## G4 — a reader-form goal reduced to raw form defeats a citation

**Symptom.** Inside a `by cases` arm the goal printed as
`List.member V vertex (Graph.vertices …)` while the cited lemma concludes
`List.memberOf V u (…)` — the same proposition, one unfolded. The bare
citation `done by Graph.IsWellFormed.end_is_vertex` was rejected.

**Workaround.** State the fact in reader form first, then close:

```math
vertex ∈ Graph.vertices(graph) by Graph.IsWellFormed.end_is_vertex;
done
```

**Note.** This is the wrapper-vs-raw citation matching already recorded in
memory (`list_notation_ergonomics`); recorded here only as another sighting,
in a goal the elaborator itself produced by reduction rather than one the
author wrote.

---

## G5 — `choose … from <IH>` cannot read the witness type through a premise

**Symptom.** In an induction whose hypothesis was generalised over a
premise, `choose tailEdges such that … from IH` reports

```
could not read a simple (closed) witness type from the lemma's
existential conclusion (one ∃ layer per witness name)
```

**Workaround.** Annotate: `choose tailEdges : List(E) such that … from IH`.
The error message says exactly this, so the friction is small — but the
witness type is `List(E)`, not a bare constant, and that is the whole
reason the read fails (`witnessConstant` in `elaborateChoose` requires the
witness type to be a `Constant`). A generalised IH over a list-valued
existential is a common enough shape that reading applied types would pay.

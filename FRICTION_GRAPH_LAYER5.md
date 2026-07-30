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

**FIXED** (`chooseConditionType` / `checkChooseCondition` in
`elaborator/induction.cpp`). The condition is checked in every form, and with
`from` omitted it is the search key, so the walk-past that produced this entry
is now the behaviour rather than the bug. Measured over library + tests: no
partial restatements, no site whose scan result changed, and six that stated a
provable reformulation instead of the fact — all six restated. Fixtures:
`ErrorTest/choose_such_that_{unrelated,misstated}_condition`,
`Test/choose_condition_selects_source`.

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
several lines later, with nothing pointing at the real mistake. It was
worked around by naming the source, `from incidentAtVertex`; with the
condition now the search key, the `from` is gone again and the site reads
as first written.

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

**FIXED, by removing the requirement rather than widening the read.** An
unreadable witness type now falls back to the `such that`-less path — cite the
lemma argument-free, premises discharging from context — and the condition is
checked against the citation's own conclusion (G1's machinery) instead of
shaping the citation. So the condition no longer has to be readable *ahead* of
the citation, and no annotation is needed. This also retired the
`error_message_inbox` entry beside it: `choose y such that … from <a ∀-fact
whose body is an ∃>` elaborates now, and the two `Metric/compactness.math`
sites that restated the `∃` a line above the `choose` are written the natural
way. Lock: `Test/choose_condition_selects_source`, last theorem.

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

---

## G6 — naming an argument can BREAK a citation that works bare

**FIXED** (`elaborateArgumentAt` in `elaborator/inference.cpp`).
An argument is elaborated AGAINST its Pi domain, and a domain that still
carries the call's own unsolved holes cannot check anything: elaborating
`Graph.union(first, second)` against `Graph(V, E, ?ends)` pushes `?ends`
down into the sub-call, where `first`'s real type then fails to match it.
The argument's elaboration throws, it is deferred to the retry after the
context discharge — and by then nothing has pinned the holes, because the
argument that was named to pin them is the one that did not elaborate.
Bottom-up, `Graph.union(first, second)` needs no expected type at all: its
type is determined by `first`, and unifying that against the domain solves
all three holes at once.

So the shape is exactly "the named argument's domain still mentions
unsolved holes". `halves(cut := cut)` and `Reaches.transitive(middle := w)`
worked because their domain is `V`, which the goal pins first;
`drops(graph := …)` and `IsPath.reverse(edgeList := …)` failed because
`Graph(?V, ?E, ?ends)` and `List(?E)` do not.

**The fix.** When the domain still mentions this call's metavariables,
infer the argument bottom-up and let the existing unification read the
holes off its own type; the checked elaboration stays as the fallback, so
an argument that genuinely needs its expected type (a bare numeral) is
unaffected. Both reported spellings then verify, `library` + `tests` +
`error-tests` are unchanged (87/0), and the one deliberately-wrong probe —
`drops(graph := first)`, where no `IsWellFormed(first)` is in scope — now
reports `could not infer hole(s) at positions 4 7` instead of leaking
`unbound internal variable: _hole_2_Graph.deleteVertex.drops`.

**Left standing.** That leak is a separate defect: when the call fails, a
fallback path hands the kernel a term with the elaborator's internal hole
names still in it, and the user sees `_hole_2_<lemma>`. The fix above
removes the two known ways in, not the leak itself.

**Symptom.** `¬(target = deleted) by Graph.deleteVertex.drops(graph := Graph.union(first, second));`
fails with

```
unbound internal variable: _hole_2_Graph.deleteVertex.drops
```

while the same citation with no argument at all — `by Graph.deleteVertex.drops` —
succeeds. Seen again at `Graph.IsPath.reverse(edgeList := prefixEdges)`:
`could not infer hole(s) at positions 2 3 7`, where the bare citation had been
rejected only for ambiguity.

**Why it matters.** `named_arguments_over_positional` says to pass the one
un-inferable argument by name, and G8 below is exactly the situation that
calls for it — but the named-argument path solves *fewer* holes than the
bare one, so the documented escape hatch is sometimes unavailable. The
workaround is structural: put the competing fact inside a `by { … }` block
so it is not in scope at the citation, or factor the step into its own
lemma whose conclusion pins the arguments.

**Not always.** `Graph.IsPathGraph.halves(cut := cut)` and
`Graph.Reaches.transitive(middle := w)` both work. The failures are the
ones where the named argument is a *graph-valued* expression and other
arguments have to be solved from the goal at the same time.

---

## G7 — an implication as the last conjunct of an existential body

**Symptom.** With the conclusion

```math
∃ (prefixEdges : List(E)). ∃ (suffixEdges : List(E)).
    … ∧ (¬(vertex = source) → ¬(source ∈ Graph.walkVertices(graph, vertex, suffixEdges)))
```

every `witness A with witness B` in the proof fails with

```
`witness E with P` lost its expected type — P is a one-step relation chain,
so its `= … by …` was read as the enclosing statement's
```

which names a construct the proof does not contain. Parenthesising the
implication, braces around the inner witness, and `with done` all leave it
unchanged. Restating the clause as a disjunction —
`vertex = source ∨ ¬(source ∈ …)` — fixes it and reads better anyway.

**Guess at the cause.** The witness's expected type is derived by peeling
the existential; a trailing `→` in the body seems to be mistaken for the
statement-level implication that separates a claim from its proof.

---

## G8 — premise ambiguity is reported even when the goal pins the arguments

**FIXED** (`elaborateChoose` in `elaborator/induction.cpp`, plus one guard in
`inferCallWithHoles`). Locks:
`Test/choose_condition_selects_source`, last three theorems. The three
workarounds are out of `Graph/`: `twoconnected.math`'s two-step
`∃ … by Graph.edge_has_ends; choose …`, `pathgraph.math`'s
`halves(cut := cut)`, and the `¬(v = u)` that had been pushed past the
`choose` that would otherwise have captured it.

**Root cause — found, and not where the guess below points.** The
conclusion match already runs before the premise search; the trouble is that
in this layer the citation had no conclusion to match against. `choose … such
that P from <lemma>` shapes its citation by assembling `∃ (name : T). P` and
ascribing the citation to it — but only when it can read `T` off the lemma's
conclusion, and the read accepted a bare `Constant` only. Over an ambient
triple no witness type ever is one: `∃ (prefixEdges : List(E))` is an
application, and `∃ (u : V)` is one of the lemma's own parameters, which the
read saw as an unsolved hole because it looked at the conclusion AFTER
argument inference. Every `from` in the layer therefore fell back to the
argument-free citation, which has no goal at all — so the premise search was
left to guess arguments the stated condition had already named.

The read now peels the cited fact's OWN type, opening each Pi under its
binder name, and renders the witness type as surface text (constants, names
in scope, applications of those). `List(E)` and `V` are names the caller
shares, because both sides carry them by `convention`. A reading wider than
the old bare constant is probed before it replaces the argument-free
citation, so a name the caller happens to share for something else costs
nothing.

The premise-less sub-shape was a second, independent bug: a slot whose TYPE
is itself an unsolved metavariable (`edge : ?E`) is a data argument, not a
premise, and a bare pattern variable unifies with every hypothesis in scope
— which is why a lemma with no premises listed every binder in scope,
∧-legs included. Such a slot is now left to the conclusion.

**Symptom.** Recurring, roughly once per fifty lines in this layer:

```
ambiguous `by Graph.IsPathGraph.halves` citation: the premise
`List.memberOf @V ? (Graph.vertices @V @E @ends @pathGraph)` is matched by
several hypotheses that pin different arguments
```

with `cut ∈ vertices(pathGraph)` and `vertex ∈ vertices(pathGraph)` both in
scope. The conclusion often determines which is meant, but the matcher
decides on the premise first and gives up.

**What the library does.** Three workarounds, in order of preference:
factor the step into a lemma whose *conclusion* mentions the disputed
argument (this is why `Graph.IsPath.reaches_target_avoiding_source` exists
separately from the path-graph version); scope the competing fact inside a
`by { … }` block; or name the argument (G6 permitting).

**Suggested fix.** Try the conclusion match before the premise search, and
only report ambiguity for arguments the conclusion leaves open.

---

## G9 — `generalizing` silently drops every hypothesis about the scrutinee

**FIXED** (`scrutineeDependentBinders` in `elaborator/cases.cpp`, plus the
three dispatch points that let the listed names short-circuit it). The
user's list is now an ADDITIONAL set of roots for the same transitive
sweep, never a replacement — so a hypothesis mentioning the scrutinee, or
mentioning a loaded binder, is reverted alongside it. Locks:
`Test/auto_generalize_test`, last two theorems.
`List.length_le_of_distinct_inclusion` is written the natural way again,
with `big` and its inclusion premise back in the binder list.

**Symptom.** `by induction on <x> with IH generalizing <y>` produces an
induction whose motive has lost every premise. Auto-generalization — the
documented behaviour that a hypothesis mentioning the inducted variable is
reverted into the motive — does not happen at all once `generalizing` is
present. The arm then fails far from the cause, with the auto-prover
reporting "no in-scope hypothesis matches" for a fact the theorem assumed.

**Minimal repro.** The two differ only in `generalizing m`, and
`hypothesis` does not mention `m` at all:

```math
theorem Probe.generalizingWithScrutineeHypothesis (n m : ℕ) (hypothesis : n ≤ 0)
        : n ≤ m :=
  by induction on n with IH generalizing m {
    case n = 0: sorry
    case n = 1 + k: sorry
  }
```

`--goal-at` in the `1 + k` arm:

```
  IH : (m : Natural) → k ≤ m          -- the `k ≤ 0` premise is GONE
  m : Natural
  ⊢ 1 + k ≤ m                          -- and so is the arm's own
```

Without `generalizing m`, the same theorem reports what it should:

```
  IH : k ≤ 0 → k ≤ m
  hypothesis : 1 + k ≤ 0               -- refined, as documented
  ⊢ 1 + k ≤ m
```

So the loaded induction proves a strictly weaker — here false — statement.
It cannot be unsound (the arm goal is weakened in step with the IH, and the
kernel still checks the result against the real theorem), but it is
unusable: `generalizing` is exactly the tool for an induction that carries
hypotheses, and it works only when there are none.

**What the library did.** Put the generalized binder and the premises
that mention it in the CONCLUSION instead —
`(small : List(A)) (distinct : …) : ∀ (big : List(A)). … → …` — and opened
each arm with `take big; suppose …`. `List.permutation_of_distinct_inclusion`
is still written that way and can now be restated with ordinary
hypotheses.

**Suggested fix.** Run the same auto-generalization pass with
`generalizing` as without it, reverting the listed binders IN ADDITION to
the hypotheses that mention the scrutinee, rather than instead of them.

---

## G10 — `choose … such that P from <lemma>` can bind a proposition that is not P

**Symptom.** The witness is bound and the `such that` is accepted, but the
condition that joins the context is a *different* proposition — so every
later step about it fails with "no in-scope hypothesis matches
structurally" for a fact the `choose` line appears to have established.
This is G1's guarantee failing again, in the one branch G1 said was
covered ("the shaped-lemma branch states it as the ascription it builds,
so it is checked there").

It bites when the cited lemma states its conclusion through a **predicate
variable** and the stated condition needs the witness ABSTRACTED out of it.
`Natural.least_witness` concludes
`∃ minimum. predicate(minimum) ∧ ∀ k. predicate(k) → minimum ≤ k`; asking
for the least *shortfall* means solving
`?predicate := shortfall ↦ ∃ point. …  bound = shortfall + point`, which is
not a first-order match.

**Minimal repro.**

```math
theorem Probe.abstractedPredicate (predicate : ℕ → Proposition)
        (n bound shortfallAtN : ℕ) (witnessAtN : predicate(n))
        (seed : ∃ (point : ℕ). predicate(point) ∧ bound = shortfallAtN + point)
        : True := {
  choose leastShortfall such that
      (∃ (point : ℕ). predicate(point) ∧ bound = leastShortfall + point)
      ∧ ∀ (k : ℕ). (∃ (point : ℕ). predicate(point) ∧ bound = k + point)
          → leastShortfall ≤ k
      as leastProperties from Natural.least_witness;
  sorry
}
```

`--goal-at` on the `sorry`:

```
  leastProperties : And (predicate leastShortfall)
                        ((k : Natural) → predicate k → leastShortfall ≤ k)
```

— `?predicate` was solved to the theorem's own `predicate` (from the
`witnessAtN` premise, by match-and-unify), the stated condition was never
enforced, and no error was reported. Not unsound: what is bound is true.
But the proof text claims something else, which is exactly what G1 was
about.

**Contrast.** With the predicate a variable *applied to the witness*
(`predicate(minimum) ∧ ∀ k. …`) every leg is bound and usable, from a
lemma source and from a hypothesis source alike — four fixtures, all pass.
So the trigger is specifically the abstraction, not `choose`.

**What the library does.** Names the predicate, so the match is
first-order again: `Graph.HasPathOfLength(graph, edgeCount)` is a
definition, and `choose longest such that Graph.HasPathOfLength(graph,
longest) ∧ …` binds exactly what it says. Where naming it would be pure
machinery, restructure the proof to avoid the abstraction —
`Natural.greatest_witness` walks the bound down by induction rather than
taking a least shortfall, and needs no predicate of its own.

**Suggested fix.** Two parts, and the first matters more than the second:
enforce the ascription (a citation that resolves at a type other than the
`such that` existential must be an error, not a silent substitution), and
solve the predicate metavariable from the ASCRIPTION before the premise
discharge gets to guess it from `witnessAtN`.

---

## G11 — the layer had no vocabulary for "is contained in" (FIXED)

**Found by an external review, 2026-07-29**, and it is the root cause of most
of what made the hard files hard. `library/Graph/` contained **zero**
occurrences of `⊆`. Every inclusion was spelled
`∀ (x : T). x ∈ A → x ∈ B` and discharged with an inline
`by { take …; suppose …; done }` — 77 such blocks in the layer, the extreme
case being reflexivity written out in full:

```math
∀ (edge : E). edge ∈ Graph.edges(graph) → edge ∈ Graph.edges(graph)
    by { take edge : E; suppose edge ∈ Graph.edges(graph); done };
```

**Root cause: a library gap, not a proof defect.** `Set` has `Set.subset`
with `⊆`, `.reflexive` and `.transitive`, and `Plane/` uses it idiomatically.
`Lists/` had membership and nothing above it — no inclusion *relation* — so
for edge and vertex lists there was nothing to reach for.

**Fixed** by `List.Includes` in `Lists/list.math`, with `⊆` overloaded on
lists (`∈` was already overloaded that way, so this is the established
pattern), plus `.reflexive`, `.transitive`, `.prepend` and `.prepend_both`.
`Graph.IsSubgraph` is now two inclusions.

Worth knowing for the next such change: `List.Includes` is **transparent**, so
every consumer that projected an `IsSubgraph` leg as a ∀-fact — and every bare
`edge ∈ Graph.edges(whole);` step discharged from one — kept working with no
edit at all. The definition change and the consumer sweep were separable.

## G12 — `let` DOES abbreviate a graph term (measured, not a friction)

The same review flagged as unknown whether `by <Lemma>` citations unify
through a `let`-bound graph, and noted that if they do not, *that* is the
friction, since `docs/style.md` recommends the form. **They do.** Probed
directly:

```math
let combined : Graph(V, E, ends) := Graph.union(first, second);
Graph.IsSubgraph(first, combined) by Graph.union.IsSubgraph_left;
```

verifies, including when the theorem's own conclusion spells the term out —
ζ-reduction makes the two defeq. So the layer's total absence of `let` as an
abbreviation (three uses, all record destructures) was habit, not a language
limit. `Graph.IsTwoConnected.replace_edge_by_path` had respelled
`Graph.union(Graph.deleteEdge(graph, edge), pathGraph)` 33 times.

One trap when applying it in bulk: a search-and-replace of the long term will
also rewrite the right-hand side of the `let` that introduces it, producing
`let trimmed := trimmed;` and an `unknown identifier` at the first use.

## Note on the review that produced G11/G12

Two of its specific claims did **not** hold up, both worth recording because
they are the shape of mistake an outside reader makes here:

- *"`IsTree.has_leaf` re-derives positive degree over ~35 lines, which is what
  `Graph.IsConnected.degree_positive` proves."* It does not. `has_leaf` gets
  `1 ≤ degree(longestSource)` in three lines from the longest path's own first
  edge (`incidentEdges_member` then `length_positive_of_member`). The ~35 lines
  are the longest-path CONSTRUCTION — two distinct vertices, a path between
  them, its nonemptiness, a longest one — which `degree_positive` does not
  supply, and which itself costs 32 lines going the other way round (through
  connectedness, to another vertex). Citing it would replace three lines with
  one and add a dependency.
- *"the same eight lines, four times"* for the second-vertex block. Three
  times. The fourth site, `IsTree.delete_leaf`, wants only a SURVIVOR of the
  deletion, not a vertex distinct from a named one, so `Graph.other_vertex`
  is not what it needs.

Everything else the review asserted — the `⊆` count, the 77 inline
take-blocks, the term-occurrence counts, and all four `Natural` lemma names it
proposed — checked out exactly.


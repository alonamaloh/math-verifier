# Recommendations for the metric-space layer

This note consolidates my comments on the current versions of:

- `Metric/space.math`
- `Metric/topology.math`
- `Metric/continuity.math`
- `Metric/sequence.math`
- `Metric/compactness.math`

The recommendations are ordered by expected benefit. The first item is a semantic issue; most of the rest concern API shape and readability.

## Overall assessment

The recent visual changes are a large improvement. In particular:

```text
(m : MetricSpace) (x y : m)
distance(x, y)
```

now read naturally, and hide the dependent projection machinery from ordinary proofs. The new `Near` and `eventually` idioms also improve the proofs when a radius or threshold exists only to coordinate finitely many facts. `OpenIn.intersection`, uniqueness of limits, and compactness implying boundedness are good examples of the style the library should aim for.

The main arguments generally retain the mathematical proof spine. The remaining work is mostly about making the relative notions standard and then removing recurring proof-state bookkeeping without concealing mathematical choices.

---

## 1. Make all relative notions depend only on the trace on the relative region

This is the one foundational issue I would fix before extending the dependency cone substantially.

The current definitions do not consistently describe the topology of `subset ∩ region`. In particular, the present `ClosureIn` may use witnesses that lie in `subset` but outside `region`.

For example, in the usual metric on `ℝ`, let

\[
C=\{0\},\qquad S=\{1,1/2,1/3,\ldots\}.
\]

The present definition puts `0` in `ClosureIn(S, C)`, because every ball around `0` contains a point of `S`. But `S ∩ C` is empty, so its closure in `C` should be empty.

Likewise, with the current `InteriorIn`, if `region` is empty, every point of `subset` satisfies the ball condition vacuously, even though a relative interior should lie in the relative region.

I recommend keeping the useful design choice that callers need not provide `subset ⊆ region`, but defining the notions through the trace:

```text
definition MetricSpace.OpenIn {m : MetricSpace}
        (subset region : Set(m)) : Proposition :=
  ∀ (x : m). x ∈ subset → x ∈ region →
    ∃ (radius : ℝ). radius > 0 ∧
      ∀ (y : m). y ∈ region →
        distance(x, y) < radius → y ∈ subset
```

Equivalently, the first two hypotheses could be written as `x ∈ subset ∩ region`.

```text
definition MetricSpace.InteriorIn {m : MetricSpace}
        (subset region : Set(m)) : Set(m) :=
  (x : m) ↦ x ∈ region ∧ x ∈ subset ∧
    ∃ (radius : ℝ). radius > 0 ∧
      ∀ (y : m). y ∈ region →
        distance(x, y) < radius → y ∈ subset
```

```text
definition MetricSpace.ClosureIn {m : MetricSpace}
        (subset region : Set(m)) : Set(m) :=
  (x : m) ↦ x ∈ region ∧
    ∀ (radius : ℝ). radius > 0 →
      ∃ (y : m). y ∈ region ∧ y ∈ subset ∧
        distance(x, y) < radius
```

`ClosedIn(subset, region)` can continue to be defined by openness of `region ∖ subset` within `region`.

This gives standard subspace semantics while preserving the convenience of accepting arbitrary ambient sets as the first argument.

---

## 2. Use a noun for the relative set: preferably `region`

The word `within` describes the role well, but it is a preposition rather than a noun. Since the code expects an object name, I now prefer:

```text
OpenIn(subset, region)
ClosedIn(subset, region)
InteriorIn(subset, region)
ClosureIn(subset, region)
BoundaryIn(subset, region)
ContinuousWithinAt(f, region, x)
ContinuousOn(f, region)
```

`region` is already used successfully elsewhere in the library and is reasonably neutral. It avoids the current collision in which `carrier` means both:

1. the type carried by a `MetricSpace`; and
2. the subset relative to which topology or continuity is being evaluated.

I would reserve **ambient space** for the whole metric space `m`, or its carrier type. `ambient` is not wrong for the relative set, but it becomes ambiguous in a chain

\[
S \subseteq C \subseteq X,
\]

because both `C` and `X` can be called ambient relative to something smaller.

The word `within` remains useful in theorem names and surface syntax:

```text
ContinuousWithinAt(f, region, x)

for y sufficiently near x within region: {
  ...
}
```

Thus the identifier is a noun, while the API still uses the conventional English phrase.

---

## 3. Introduce `NearWithin`

The current expression

```text
MetricSpace.Near(x, (y : m) ↦ y ∈ region → P(y))
```

is useful but implementation-shaped. Give the relative notion a name:

```text
definition MetricSpace.NearWithin {m : MetricSpace}
        (x : m) (region : Set(m)) (P : m → Proposition) : Proposition :=
  MetricSpace.Near(x, (y : m) ↦ y ∈ region → P(y))
```

Then relative openness can be read as:

```text
∀ x. x ∈ subset → x ∈ region →
  MetricSpace.NearWithin(x, region, (y : m) ↦ y ∈ subset)
```

The ideal proof-language form would be:

```text
for y sufficiently near x within region: {
  ...
}
```

This removes repeated implications such as `y ∈ region → ...` from the visible mathematical statement.

---

## 4. Separate absolute continuity from continuity within a region

The current `ContinuousAt(f, region, x)` is what is conventionally called continuity **within** a set at a point. I recommend renaming it before the API grows:

```text
definition MetricSpace.ContinuousWithinAt {source target : MetricSpace}
        (f : source → target)
        (region : Set(source))
        (x : source) : Proposition :=
  ...
```

Then define the absolute notion as a wrapper:

```text
definition MetricSpace.ContinuousAt {source target : MetricSpace}
        (f : source → target)
        (x : source) : Proposition :=
  MetricSpace.ContinuousWithinAt(f, Set.universe(source), x)
```

`ContinuousOn(f, region)` can retain its existing name.

This improves terminology and removes repeated universe-membership noise from absolute results such as:

- openness of a ball;
- `ContinuousAt.near`;
- `ContinuousAt.of_near`;
- `Near.under`.

The current `.near` and `.of_near` theorems are already absolute in substance, despite being attached to a relative `ContinuousAt`; that is evidence that the distinction should be represented explicitly.

---

## 5. Let `choose` destructure and name conjunction components

A recurring pattern is:

```text
choose radius such that
    radius > 0 ∧
      ∀ y. ...
    from openInRegion;
radius > 0;
∀ y. ... as ballProperty;
```

The last two statements are projections from the chosen conjunction, not mathematical steps. A mathematician writes “choose `radius > 0` such that ...” and thereafter uses both facts.

A high-value language feature would allow something like:

```text
choose radius such that
    radiusPositive : radius > 0
    and ballProperty :
      ∀ (y : m). y ∈ region →
        distance(x, y) < radius → y ∈ subset
    from openInRegion;
```

The exact syntax is negotiable. The important capability is to bind the named legs of a flat conjunction while eliminating the existential.

This would reduce visual noise throughout topology, continuity, compactness, and sequence arguments without hiding any mathematics.

---

## 6. Continue using `Near` and `eventually` selectively

The new filter language is strongest when a radius or threshold merely coordinates several local or eventual facts. It should not automatically replace every explicit ε–δ argument.

### Good next conversions

#### `OpenIn.union`

Each case can obtain a nearby fact from the corresponding open set and then use inclusion into the union. No radius needs to be named.

#### The pasting lemma

`pasteRadius` could instead produce a `NearWithin` statement. Then `ContinuousOn.paste` could combine the two nearby properties directly, without naming:

```text
firstNearness
secondNearness
min(firstNearness, secondNearness)
```

This is exactly the same kind of bookkeeping that `Near` removed from `OpenIn.intersection`.

#### `ContinuousAt.along_sequence`

After continuity supplies a nearness condition, convergence should give an eventual source estimate, and the image estimate should follow “for sufficiently large `k`.” There is no need to unpack and repack the threshold explicitly.

#### `SequenceConverges.subsequence`

Add a general natural-number theorem of the form:

```text
eventually (n). P(n)
Natural.IsStrictlyIncreasing(index)
-----------------------------------
eventually (k). P(index(k))
```

Then subsequence preservation of convergence is nearly immediate.

#### `ContinuousOn.restrict`

The new pointwise theorem should be reused rather than reproving the ε–δ argument:

```text
take x : source;
suppose x ∈ smaller;
x ∈ larger by smallerInLarger;
MetricSpace.ContinuousWithinAt(f, larger, x) by continuousOnLarger;
done by MetricSpace.ContinuousWithinAt.restrict
```

### Arguments that should probably remain explicit

`ContinuousOn.compose` is clear in its current ε–δ form. The passage

1. target tolerance;
2. middle-space nearness;
3. source-space nearness

is the mathematical content, not incidental bookkeeping.

Likewise, the first proof that an open ball is open should probably display the radius

\[
r-d(c,x),
\]

because that is the idea of the proof.

---

## 7. Factor the shrinking-ball argument once

The same geometric calculation appears in:

- `Ball_IsOpen`;
- `openHull_IsOpen`;
- `InteriorIn_OpenIn`.

The core fact is:

\[
d(c,x)<r
\quad\Longrightarrow\quad
B\bigl(x,r-d(c,x)\bigr)\subseteq B(c,r).
\]

A useful theorem could expose either the explicit ball inclusion or its filter form.

### Explicit form

```text
theorem MetricSpace.Ball.shrink_inside ...
        (inside : distance(center, x) < radius)
        : MetricSpace.Ball(x, radius - distance(center, x))
            ⊆ MetricSpace.Ball(center, radius)
```

### Filter form

```text
theorem MetricSpace.distance_lt_near ...
        (inside : distance(center, x) < radius)
        : MetricSpace.Near(
            x,
            (y : m) ↦ distance(center, y) < radius)
```

Keep one full triangle-inequality proof visible near the definition of balls; use the helper elsewhere.

---

## 8. Hide the `openHull` / `BallWitness` scaffolding behind the textbook theorem

`BallWitness` and its four projection lemmas are reasonable elaborator-facing machinery, but they are not the mathematical API a reader is looking for.

The public result should be the characterization:

\[
S\text{ is open in }C
\quad\Longleftrightarrow\quad
S\cap C=U\cap C
\text{ for some open }U.
\]

With the naming discussed below:

```text
theorem MetricSpace.OpenIn_iff_cut_by_open ...
        : MetricSpace.OpenIn(subset, region)
          ↔ ∃ (cuttingSet : Set(m)).
              MetricSpace.IsOpen(cuttingSet)
              ∧ subset ∩ region = cuttingSet ∩ region
```

If `subset ⊆ region` is known, derive the cleaner corollary:

```text
subset = cuttingSet ∩ region
```

Recommendations:

1. Move `BallWitness`, its projections, and possibly `openHull` into an internal section or separate characterization module.
2. Expose one reader-facing equivalence theorem.
3. Keep `openHull` public only if later consumers need that particular witness, rather than merely the existence of some cutting open set.

---

## 9. Naming the set that cuts out a relatively open subset

For

\[
S=U\cap C,
\]

there are three different roles:

- `m`: the ambient metric space;
- `region` (`C`): the relative subspace being cut;
- `cuttingSet` (`U`): the open set performing the cut.

I recommend this signature for the characterization theorem:

```text
theorem MetricSpace.OpenIn_of_cut (m : MetricSpace)
        (subset region cuttingSet : Set(m))
        (cuttingSetOpen : MetricSpace.IsOpen(cuttingSet))
        (cut : subset = cuttingSet ∩ region)
        : MetricSpace.OpenIn(subset, region)
```

`cuttingSet` is a proper noun phrase and identifies the role accurately. It is preferable to bare `cut`, which sounds more like the equation or operation than the set.

I would avoid `cuttingOpenSet` in ordinary signatures. The hypothesis already records openness:

```text
(cuttingSet : Set(m))
(cuttingSetOpen : IsOpen(cuttingSet))
```

whereas

```text
(cuttingOpenSet : Set(m))
(cuttingOpenSetOpen : IsOpen(cuttingOpenSet))
```

repeats the same fact noisily.

For a theorem specifically explaining the construction, `cuttingSet` reads well. In routine local proofs, the shorter `openSet` may be enough because the equation already reveals its role.

I would reserve `ambient` for the whole surrounding metric space, not for the cutting set.

---

## 10. Make public theorem statements match their comments

Two sections currently advertise a textbook equality or equivalence but expose only directional implementation lemmas.

### Boundary of a relatively open set

The comment says:

\[
\partial U=\overline U\setminus U.
\]

The public theorem should state the equality:

```text
theorem MetricSpace.BoundaryIn_eq_ClosureIn_difference_of_OpenIn ...
        (openInRegion : MetricSpace.OpenIn(subset, region))
        : MetricSpace.BoundaryIn(subset, region)
            = MetricSpace.ClosureIn(subset, region) ∖ subset
```

The current one-way membership theorem can remain as a helper or receive a directional name.

### Relative openness as a cut by an open set

Expose an `iff` or existential characterization, rather than making the reader reconstruct it from two theorems involving the particular `openHull` witness.

Readers navigate a library primarily through theorem statements. The public statements should be the ones a textbook would name.

---

## 11. Resolve boundedness on an empty metric-space carrier

The current definition

```text
∃ (center : m). ∃ (bound : ℝ). ...
```

makes the empty subset of an empty metric space unbounded, because there is no center to choose. The same empty set is sequentially compact vacuously. This is why `IsCompact.bounded` currently needs an explicit `centre : m`, even though its conclusion existentially quantifies a center.

Coherent options include:

1. require metric-space carriers to be inhabited;
2. define boundedness as “the set is empty, or it is bounded about some center”;
3. define boundedness pairwise, by a uniform bound on distances between points of the set;
4. retain the present definition but add inhabitedness assumptions to the relevant theorems.

The least disruptive change is probably:

```text
MetricSpace.IsBounded(region) :=
  region = Set.empty(m)
  ∨ ∃ (center : m). ∃ (bound : ℝ).
      ∀ (x : m). x ∈ region → distance(center, x) ≤ bound
```

A pairwise definition is also mathematically clean and automatically handles the empty set, but it changes the working form of many proofs.

After this is settled, the expected theorem should not need a center argument:

```text
MetricSpace.IsCompact.bounded
    (compact : MetricSpace.IsCompact(region))
    : MetricSpace.IsBounded(region)
```

This is less urgent for concrete spaces such as `ℝ` and the plane, but worth deciding while the API is young.

---

## 12. Move generic set image out of `MetricSpace`

`imageSet` and `imageSet_union` do not use a metric. They are ordinary set-theoretic constructions and should live under `Set`, preferably with standard image notation if the language supports it.

This would make the compact-image theorem read more conventionally and keep `Metric.compactness` focused on metric concepts.

Also rename local witnesses currently called `source` in `imageSet_union`; that name shadows the source metric space. Prefer `x`, `preimage`, or `origin`.

A general convergence-congruence theorem based on pointwise equality would also avoid the explicit function-extensionality maneuver at the end of `IsCompact.image`.

---

## 13. Decide how explicitly the API acknowledges sequential compactness

The current `IsCompact` is sequential compactness. This is entirely appropriate inside a metric-space-only development, since the standard compactness notions agree there.

If the library may later introduce general topological spaces, consider either:

- naming the current notion `IsSequentiallyCompact`; or
- retaining `IsCompact` in the metric namespace but documenting clearly that this is the metric-space presentation, with an eventual equivalence theorem to open-cover compactness.

Renaming after many consumers exist would be expensive, so this is worth deciding early even though it does not affect the present proofs.

---

## 14. Preserve an explicit-metric escape hatch

Recovering `distance` from the point type is excellent for ordinary proofs. A single carrier type can nevertheless support several useful metrics, including equivalent metrics or bounded replacements of a metric.

The canonical-instance approach is fine provided there remains a pleasant explicit form for selecting a particular bundle. Wrapper types are another conventional solution.

This is an architectural constraint rather than a current readability defect.

---

## 15. Small API and presentation improvements

These are lower priority individually, but worthwhile after the semantic and structural work.

### Add a membership equivalence for balls

The natural public statement is:

```text
x ∈ MetricSpace.Ball(center, radius)
  ↔ distance(center, x) < radius
```

The two directional lemmas can remain as conveniences if elaboration benefits from them.

### Explain the carrier coercion once

Near the first occurrence of `x : m`, add a short comment such as:

```text
-- A metric space coerces to its carrier, so `x : m` means that `x`
-- is a point of the metric space `m`.
```

### Shorten implementation-heavy comments in mathematical files

The long overload-dispatch explanation is valuable institutional knowledge, but it interrupts the opening of a mathematical module. Keep a concise warning in the source and move the detailed δ-reduction discussion to a language-design note or regression test if practical.

### Prefer nested proof prose to long proof lambdas

For nontrivial nested implications, prefer:

```text
by {
  take y : m;
  suppose y ∈ region;
  suppose distance(x, y) < radius;
  ...
}
```

rather than a long multi-argument lambda. The new `ContinuousAt.restrict` proof is a good model.

### Remove unused proof labels

Names such as

```text
as xInCarrier
as tolerancePositive
as inEither
```

should be omitted when never referenced. A linter for unused `as` labels and hypothesis names would likely help across the library.

### Standardize names and spelling

- Choose either `center` or `centre` consistently.
- Rename `apart` in `equal_of_distance_zero`; it suggests positive separation. `distanceZero` is clearer.
- Rename “finite intersection” to “binary intersection” until the finite theorem exists.
- Avoid saying “the lattice laws” before arbitrary unions and the relevant full structure are present.
- Remove the duplicated section divider in `Metric/continuity.math`.
- Make theorem-name conventions consistent (`Ball_IsOpen`, `InteriorIn_OpenIn`, `openHull_IsOpen`, and so on).

### Consider implicit metric-space parameters in elementary lemmas

For example:

```text
theorem MetricSpace.distance_self {m : MetricSpace} (x : m)
```

may be slightly cleaner because `m` is determined by `x`. This is optional; the current explicit declarations are already readable.

---

## Suggested order of implementation

1. Fix trace semantics for `OpenIn`, `InteriorIn`, and `ClosureIn`.
2. Rename the relative-set parameter from `carrier` to `region`.
3. Introduce `NearWithin` and rename relative `ContinuousAt` to `ContinuousWithinAt`.
4. Add conjunction-destructuring support to `choose`, if feasible at the language level.
5. Convert the remaining pure radius/threshold bookkeeping to `Near` or `eventually`.
6. Factor the shrinking-ball lemma.
7. Hide `BallWitness`/`openHull` machinery behind a public cut-characterization theorem.
8. Add the promised boundary equality and other reader-facing `iff` theorems.
9. Resolve empty-space boundedness.
10. Move generic set image and perform the mechanical naming/lint pass.

## Bottom line

The visual layer is now strong. The ordinary proof bodies mostly read as mathematics, and the filter syntax is removing the right kind of bookkeeping. The relative-topology semantics are the one issue that can change mathematical meaning and therefore deserve first priority. After that, the best returns are likely to come from `NearWithin`, direct destructuring in `choose`, and hiding the `openHull` witness machinery behind the textbook characterization it proves.


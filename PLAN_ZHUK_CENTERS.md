# PLAN — Zhuk's centers and ternary absorption

Target: **the left center of a subdirect `R ≤ A × B` centrally absorbs `A`
when `B` is Taylor and has no nonempty proper binary absorbing subuniverse,
and the absorption is witnessed by a ternary term.** The blueprint is
`~/claude/zeb/zhuk_centers.tex` (24 pp, 51 labelled statements, Appendix A a
statement-level citation index, Appendix B a module order, Appendix C the
imported-background package, Appendix D a concordance with the source).
Published at <https://github.com/alonamaloh/csp-zhuk-centers>.

This file is the layer plan for the *foundation the library does not yet
have*, plus the milestones to steer by. It is not a proof outline — the
blueprint is that.

## Why this target

1. **The blueprint is unusually close to formal already.** Six review rounds
   across two independent reviewers went by without a mathematical objection;
   what they found were quantifier-shape defects, a missing substitution
   operation, and a type-level transport — precisely the failures a
   formalization would otherwise discover three weeks in. Appendix C is five
   items long, all finite combinatorics.
2. **The foundation is the one piece of general algebra the library lacks.**
   `Algebra/` has 100+ files and every one of them is *fixed-signature*:
   `Group`, `Ring`, `Field`, `VectorSpace`. Nothing in the library treats a
   signature as data, and nothing anywhere constructs a **generated**
   substructure as a least closed set. Both are reusable well beyond this
   theorem.
3. **It is a different stress test from Jordan–Schönflies.** That one is ε-δ
   geometry with configuration case analysis. This one is inductive types,
   substitution, and finite counting — the parts of the elaborator that
   `Lists/` and `Set/` exercise, pushed harder.

## What is missing (measured, 2026-07-30)

Library is 136,810 lines across 816 `.math` files.

| Needed by the blueprint | In library |
|---|---|
| `Set(T) = T → Proposition`, `∈`, `⊆`, `∪`, `∩`, `∖`, image, extensionality | ✅ `Set/basics`, `Set/algebra` |
| least-number principle, both forms | ✅ `Natural/least_number` |
| `inductive` with parameters and recursive constructors | ✅ `Lists/list`, `Algebra/group_bundle` |
| bundled structure + `IsSub…(G, subset)` idiom to imitate | ✅ `Algebra/group_bundle`, `Algebra/subgroup` |
| lists: membership, `map`, `filter` (on a `Proposition` predicate), `length`, `Distinct`, `range` | ✅ `Lists/` |
| strong induction / well-founded recursion | ✅ `Natural/strong_recursion`, `Logic/well_founded` |
| `HasSize(X, n)`, `NaturalsBelow`, pigeonhole, `HasSize.product` | ✅ `Set/finite*` — but on **types**, not subsets |
| signatures as data; algebras over a signature | — |
| terms over a signature; term operations; substitution + evaluation law | — |
| subuniverse; **generated** subuniverse `Sg` | — (`IsSubgroup` is the shape; no `Sg` anywhere, and `span` is by-combinations, not least-closed) |
| finite indexed product `∏_{i∈I} A_i`; projection, cylinder, reindexing | — (`Logic/product` is binary pairs) |
| cardinality of a **subset** as a natural; `S ⊆ T ⟹ ∣S∣ ≤ ∣T∣`; strict for proper | ✅ written — `Set/enumeration.math` |
| greatest element of a bounded nonempty set of naturals | ✅ `Natural.greatest_witness` — it was there all along |
| `Natural.minimum`, monotonicity, `min(N, min(N,x)+1) = min(N,x+1)` | ✅ written — `Natural/minimum.math` |

Estimated foundation: **~8k lines**. Blueprint content on top: **~15k**. Both
soft, and both smaller than Jordan–Schönflies by a factor of five; see
*Unknowns*.

---

## Layer 0 — `Universal/signature.math` : signatures, algebras, terms

Everything rests here, so the representation choices below are the ones worth
arguing about before any of it is written.

**Signature as a bundle carrying its arity function.**

```
inductive Signature : Type(1) where
  | Signature.make
      : (symbol : Type(0))
        → (arity : symbol → ℕ)
        → (∀ (f : symbol). 1 ≤ arity(f))
        → Signature
```

Putting *no nullary symbols* inside the signature rather than carrying it as a
side hypothesis is what makes `Sg(∅) = ∅` — blueprint Lemma 1.6(d), used in
the centrality theorem — a theorem with no hypotheses to thread. This is
Convention 1.2(a) of the blueprint, and it should be a field, not prose.

**Algebras bundled, subuniverses unbundled.** `Algebra(σ)` carries a `Type(0)`
carrier and
`interpret : (f : symbol(σ)) → (NaturalsBelow(arity(f)) → carrier) → carrier`.
Subuniverses are `Set(carrier)` with a closure predicate, exactly as
`IsSubgroup(G, subset)` is written. The blueprint has already made the
matching decision (Definition 2.1 defines absorption relative to a *pair of
subuniverses*, with the ambient algebra suppressed), so **no
"subalgebra as an algebra" construction is ever needed.** Do not build one.

### The one experiment that gates the layer

`Term` needs a constructor whose recursive argument is a **function**:

```
inductive Term (σ : Signature) (V : Type(0)) : Type(0) where
  | Term.variable : V → Term(σ, V)
  | Term.apply : (f : symbol(σ)) → (NaturalsBelow(arity(f)) → Term(σ, V)) → Term(σ, V)
```

**No inductive type in the library has a function-typed recursive argument.**
Whether the kernel's positivity check and the elaborator's recursor generation
accept this is unknown, and every line of the development sits on it. Test it
on day one, before anything else. If it is rejected, the fallbacks, in order
of preference:

1. `List(Term(σ, V))` plus a side condition `lengthOf(args) = arity(f)`, with
   the arity discharged at every use. Costs a hypothesis everywhere and makes
   the evaluation law uglier, but is plainly within what `Lists/` supports.
2. A `Vector` type — `NaturalsBelow(n) → A` wrapped — introduced first, if
   that changes the positivity analysis. Probably it does not.

Option 1 is a real tax: the blueprint's Lemma 1.14 (preservation) and
Lemma 1.11 (evaluation of a substitution) are both single structural
inductions in the function form, and both acquire arity bookkeeping in the
list form.

### Variables drawn from an arbitrary type, not from `[n]`

Write `Term(σ, V)` for `V : Type(0)`, not `Term(σ, n)` for `n : ℕ`. Three
payoffs, in increasing order of size:

- Substitution is `Term(σ, V) → (V → Term(σ, W)) → Term(σ, W)` — the monad
  bind — and the blueprint's `t[ρ]` for `ρ : [m] → [n]` is the special case
  `V := NaturalsBelow(m)`, `W := NaturalsBelow(n)`. One definition covers
  permutation, identification and dummy variables, which is exactly what
  Definition 1.10 asks for.
- The evaluation law (Lemma 1.11) is one induction with no index arithmetic.
- **The star powers stop needing Euclidean division.** See Layer 4.

`Clo_m(A)` is then the image of `Term(σ, NaturalsBelow(m))` under evaluation.

---

## Layer 1 — `Universal/subuniverse.math` : subuniverses and generation

**`Sg` is one line with predicate sets.** The library has no generated
substructure anywhere, and the instinct from `span` — define it by what its
elements look like — is the wrong one here. With `Set(T) = T → Proposition`,
the least closed superset is directly definable:

```
definition Sg (A : Algebra(σ)) (S : Set(carrier(A))) : Set(carrier(A)) :=
  (x) ↦ ∀ (T : Set(carrier(A))). IsSubuniverse(A, T) → S ⊆ T → x ∈ T
```

No completeness machinery, no transfinite construction. `Sg(S) ⊆ T` for any
closed `T ⊇ S` is immediate; that `Sg(S)` is itself closed is a two-line
argument. Blueprint Lemma 1.6 falls out.

**Main results.** `IsSubuniverse` closed under intersection; `Sg` monotone and
idempotent; `Sg(∅) = ∅`; singletons are subuniverses in an idempotent algebra;
term operations preserve subuniverses (Lemma 1.14, structural induction);
homomorphisms, images, preimages, and `h(Sg(S)) = Sg(h(S))`.

**The workhorse is generation by a fixed list** (Lemma 1.15):

> for `S = {s_1, …, s_N}`, `Sg(S) = { evaluate(t, s⃗) : t ∈ Term(σ, NaturalsBelow(N)) }`.

Both the centrality theorem and Step 1 of the doubling lemma consume it, and
the blueprint deliberately fixes the generator list once so that no
substitution over varying generator lists is ever needed. Prove it in that
form; do not generalize to arbitrary finite tuples.

---

## Layer 2 — `Universal/product.math` : finite indexed products

Index by a **type** `I` with a finiteness witness, carrier `I → carrier(A_i)`
for a family, `I → carrier(A)` for a power. The blueprint (Definition 1.8)
deliberately allows an arbitrary finite index set rather than `[m]`, because
the relational description of absorption forms `A^(A^m)` and projects onto a
subset of `A^m`; an initial-segment-only product forces a transport there that
an earlier draft got wrong.

**Main results — the five relational constructions of Lemma 1.19**, and
nothing else is needed: intersection, intersection with a box `∏ S_i`,
projection `π_J` for `J ⊆ I`, cylinder `π_J⁻¹`, and reindexing along a
bijection `I' → I`. All five are used; the blueprint says where.

`π_J(R)` for `J : Set(I)` lands in `Subtype(I, J) → carrier`. That subtype
indexing is the friction point of this layer and the thing to prototype
before committing.

---

## Layer 3 — cardinality of a subset — **done**

Landed as three files, none of them under `Universal/`: nothing in this layer
is universal algebra, so it went where it is reusable.

| File | Lines | Contents |
|---|---|---|
| `Natural/minimum.math` | 155 | `Natural.minimum`, the greatest-lower-bound facts, and the two Appendix C item 2 facts |
| `Lists/filter_length.math` | 168 | `List.filter_length_monotone` and `..._strict` |
| `Set/enumeration.math` | 128 | `Set.IsEnumeration`, `Set.IsFinite`, `Set.size`, and the three order facts |

The estimate was 300 lines and it came in at 451 — the closest any layer has
landed so far, and the enumeration-list representation never fought. Three
things made it cheap:

- `Set(A)` *is* `A → Proposition` and `List.filter` takes a `Proposition`
  predicate, so `size(enumeration, S) := length(filter(S, enumeration))`
  typechecks with no coercion and no decidability obligation at any call site.
- Every order fact reduces to a statement about lengths of filters, so the
  induction happens once, in `Lists/`, and `Set/enumeration.math` is pure
  translation.
- `min` needed no classical decision: `a ∸ (a ∸ b)` is the dual of
  `Natural.maximum`'s `a + (b ∸ a)`, so the characterising equations are monus
  arithmetic and everything past them is order reasoning.

`Natural.greatest_witness` — the greatest element of a bounded nonempty set,
which this section listed as missing — turned out to already exist in
`Natural/least_number.math`. Nothing was needed for it.

The original plan for this layer, kept for the record:

**It is where the estimate is least trustworthy.**

`Set/finite.math` gives `HasSize(X : Type(0), n)` — a *proposition* about a
*type*. The blueprint compares and increments the cardinalities of *subsets*
of a carrier (`|a+R|`, `|B|`, `|β(P)|`, `|I_j|`), and Step 0 of the doubling
lemma feeds `|β(P)|` to the least-number principle as a natural number. Three
ways to close the gap:

1. **Relational.** `HasSize(Subtype(A, S), n)` plus `HasSize.unique`. Every
   inequality becomes an existential dance; the enlargement induction, which
   is a chain of four comparisons, becomes unreadable. Rejected.
2. **Cardinality as a function via `Logic.the`.** Definite description on the
   `HasSize` predicate. Clean statements, but every rewrite has to re-derive
   the uniqueness side condition.
3. **Enumeration list** (recommended). A `FiniteAlgebra` carries a
   `List(carrier)` that is `Distinct` and covers; `size(S) := lengthOf(List.filter(S, enumeration))`.
   `List.filter` already takes a `Proposition` predicate and routes through
   `Natural.classical_decidable`, so no decidability obligation appears at
   call sites.

Option 3 makes the facts the blueprint needs into list lemmas —
`S ⊆ T ⟹ size(S) ≤ size(T)`, strict when `S ≠ T`, and
`size(S) = size(universe) ↔ S = universe` — and it matches the idiom next
door: `Graph/` represents a finite graph as two finite lists, for the same
reason.

**Also here:** `Natural.minimum` (only `maximum` exists), with the two facts
Appendix C item 2 names — monotonicity in the second argument, and
`min(N, min(N,x)+1) = min(N,x+1)` — and the **greatest** element of a
nonempty bounded set of naturals, which the maximal-arity argument needs and
which `Natural/least_number` does not supply.

---

## Layer 4 — absorption — **done**

| File | Lines | Contents |
|---|---|---|
| `Universal/absorption.math` | 312 | `Witnesses`, `Absorbs`, `BinaryAbsorbs`, the renaming bridge, Taylor identities, Lemma 2.6 |
| `Universal/star_power.math` | 297 | `StarIndex`, the block inclusion and its inverse, `starBase`, `starStep` and its evaluation law |
| `Universal/term.math` (added) | 39 | `Term.rename` and `evaluate_rename` — the blueprint's `t[ρ]` |
| `Set/finite_successor.math` (added) | 116 | the cons/uncons interface for `NaturalsBelow(1 + n)` |

Design question 3 is settled in favour of the index type, and the blueprint
was edited accordingly (eighth draft): terms range over an arbitrary variable
set, `Definition 2.8` indexes a star power by `[k]^{[ℓ]}`, the new Lemma 2.2
renames a witness onto a numeric arity, and Appendix C item 6 (Euclidean
division) is gone. The plan under-costed that edit — it also needed
Definitions 1.9, 1.10, Lemma 1.11, and preservation/idempotence generalized —
but Part II was untouched, which was the thing worth protecting.

Two frictions worth remembering, both new:

- **`Natural.add` is opaque, so `1 + rest` is never definitionally
  `successor rest`.** A dependent recursive definition on ℕ whose result type
  mentions the recursion variable therefore cannot be written: the `1 + rest`
  arm's body has the wrong type by exactly that non-reduction. `starPower` is
  published as `starBase` + `starStep` instead, and the iteration lives in a
  proof, where equation-shaped induction rewrites rather than reduces. Expect
  this again in Layer 6 and anywhere else a construction recurses on a numeric
  parameter that indexes its own type.
- **A conditional whose else branch uses the branch hypothesis needs
  `Logic.if_positive_dependent` / `if_negative_dependent`.** The plain
  `if_positive` takes constant branches, so it cannot see a branch that
  consumes the decision — which `starPrepend`'s does, since that is how it
  knows the index can be dropped. The diagnostic points at an uninferable
  argument, not at the dependence, so this costs a round trip if unexpected.

The original plan for this layer:

**Get the quantifier shape right, once.** Definition 2.1 constrains the tuple
`(z_1,…,z_m)` rather than quantifying over a list from `E` and overwriting an
entry. This is not a stylistic choice: the two readings differ exactly at
`E = ∅`, `m = 1`, `D ≠ ∅`, and only the tuple form makes the relational
description a true biconditional. Remark 2.2 of the blueprint records this,
and two separate review rounds were spent because the *proofs* had drifted to
the other form after the definition was fixed. Write the definition first,
then make every consuming statement match it verbatim.

### The star powers: an index type instead of arithmetic

Definition 2.7 defines `t^{*ℓ}` of arity `k^ℓ` and decomposes
`p ∈ [k^{ℓ+1}]` as `p = (j-1)k^ℓ + q` by Euclidean division — Appendix C
item 6.

With `Term(σ, V)` over an arbitrary variable type, take the variables of
`t^{*ℓ}` to be `NaturalsBelow(ℓ) → NaturalsBelow(k)`. There are `k^ℓ` of
them, and "block `j`, position `q`" is just *peeling off the first argument*
of a function. The division disappears, and so does the item in Appendix C.

**This changes the blueprint, not just this plan.** Definition 2.7 and
Appendix C item 6 both need editing in `~/claude/zeb/zhuk_centers.tex`, and
Appendix A regenerates with `python3 regen_appendix.py`. Settle it before
writing Layer 4.

---

## Layer 5 — `Universal/essential.math`

Essential relations for a product and for a partition, arity reduction,
regrouping (Lemma 3.7), `Clo_m(A)` as a subuniverse of `A^(A^m)`, and the
relational description of absorption (Theorem 3.10, Barto–Kazda).

**The single biggest milestone**, and the only one whose proof is a genuine
induction rather than a check.

### Represent a partition by its block function

The blueprint writes a partition as a tuple `(I_1, …, I_m)` of nonempty
blocks. Formally, prefer

```
block : I → NaturalsBelow(m)          -- surjective
```

with `I_j := { i | block(i) = j }`. Nonemptiness of every block is exactly
surjectivity, one hypothesis instead of `m`. Deleting an element from an
oversized block — which is the whole inductive step, since the rewrite over
arbitrary index sets removed the reordering — is then a statement about the
restriction of `block` to `I ∖ {u}`.

The payoff shows up immediately in Theorem 3.10: `X` is the set of tuples
with exactly one coordinate outside `S`, and its block function is literally
*which coordinate is free*. No partition needs to be constructed.

---

## Layer 6 — `Universal/center.math`

Neighborhoods `a + R`, left and right centers, the enlargement step
(Theorem 5.1), and the star-power iteration (Theorem 5.2).

Both theorems are stated over tuples constrained coordinatewise, matching
Definition 2.1. Theorem 5.2's induction `(∗_ℓ)` is stated in that shape
deliberately — see Remark 5.3 — and the degenerate cases `C = ∅` and `|B| = 1`
dissolve rather than needing a split. Do not "simplify" the statement back to
the overwrite form; that reintroduces the gap.

---

## Layer 7 — `Universal/doubling.math`

Central absorption, the Zhuk–Kozik doubling trick (Lemma 7.1), the ternary
collapse (Corollary 8.1), and the main theorem.

**Step 1 must be a standalone universally quantified lemma**, before the
element `b` of Step 2 is fixed:

> for all `b₁, b₂ ∈ B'`, `b₂ ∈ Sg(C' ∪ {b₁})`.

Step 3 instantiates it twice, the second time at an element the first
instantiation produced. Remark 7.2 spells this out; it is the only argument in
the document that doubles back on itself, and the only place a reviewer had to
draw the dependency by hand.

Note that Lemma 7.1 requires **only `A_{n+1}` finite** — the other factors are
arbitrary. An earlier draft strengthened this to all-finite and thereby
imported, silently, that a finite algebra has finitely many subuniverses. The
weaker hypothesis is both correct and cheaper: the minimization needs the
least-number principle and nothing else.

---

## Design questions to settle before writing

1. **`Term`'s recursive argument** — function-typed, or list-plus-arity?
   Decided by the day-one experiment, not by preference. Everything else waits
   on it.
2. **Cardinality representation** — recommendation is the enumeration list
   (Layer 3, option 3). The alternative worth a second look is `Logic.the` on
   `HasSize`, if `List.filter` reasoning turns out to fight.
3. ~~**Star-power variables** — index type or Euclidean division?~~ **Settled:
   the index type.** The blueprint's eighth draft carries it — Definition 2.8,
   the new Lemma 2.2, and Appendix C item 6 deleted — and `Universal.StarIndex`
   implements it. Note the Lean formalization had already made this choice
   (`Fin ℓ → Fin k`, `Fin.cons`, `Absorbs.of_finite`); the blueprint was behind
   both.
4. **Partition representation** — block function or tuple of subsets?
   Recommendation is the block function; this does *not* edit the blueprint,
   since Definition 3.2 is already stated over an arbitrary finite index set
   and the block function is a faithful encoding of what it says.
5. **Is `Algebra(σ)` bundled?** The library's fixed-signature structures all
   are (`Group`, `VectorSpace`), and `Metric/space.math` shows the pattern for
   a `Type(1)` bundle over a `Type(0)` carrier. Recommendation: bundle, and
   follow `Algebra/group_bundle.math`'s projection style. The one thing to
   check early is whether the dependent motive in
   `interpret : (f : symbol) → (NaturalsBelow(arity(f)) → carrier) → carrier`
   trips the same pattern-match codegen limitation that
   `group_bundle.math` documents for `Group.operation`; if so, use the
   `let ⟨…⟩ :=` destructuring form it fell back to.

## State, and where to pick up

Layers 0–4 are done, sorry-free, and in the library build. Blueprint at the
eighth draft; Lean version unchanged and complete.

| | Lines here |
|---|---|
| Layers 0–2 (signatures, terms, subuniverses, generation, products) | ~510 |
| Layer 2 relational constructions (`Universal/relation.math`) | 240 |
| Layer 3 (`Natural/minimum`, `Lists/filter_length`, `Set/enumeration`) | 451 |
| Layer 4 (`Universal/absorption`, `Universal/star_power`, + `term`, + `Set/finite_successor`) | 764 |
| Layer 5 so far (`Universal/essential.math`) | 534 |
| Dependent product (`Universal/dependent_product.math`) | 152 |
| **Total** | **~2650** |

**The remaining estimate, recalibrated.** The plan's "~15k lines of blueprint
content" was a guess made before anything was measured, and it is about 4× too
high. Lean's remaining files — Essential 112, Regrouping 135, Relational 95,
Center 139, Step 93, Absorbs 103, Central 179, Doubling 289, Ternary 71 — total
1216 lines. At Layer 4's measured 3.3:1, the only fair-fight ratio available and
the same kind of content (real proofs, not library lookup), that is **~4000
lines here**. Layer 5's opening came in at 187 against Lean's `Essential.lean`
112, a ratio of 1.7:1, so 3.3:1 may even be pessimistic for the transcription-
heavy parts.

**Layer 5 is opened.** `Universal/essential.math` (187 lines) has
`Universal.IsEssential` in the two-clause form of Definition 3.1, Lemma 3.4
(essentiality forces the parts nonempty), and — the item that showed the layer
will work — Proposition 3.6: a witnessing term forbids an essential relation on
the same index. The proof is the one move Part II turns on, and it transcribed
almost directly: evaluate the witnessing term *in the power* at the tuple of
witnesses, and preservation plus `Universal.Witnesses` put the result inside the
box, contradicting the second clause. Stated at `index = NaturalsBelow(m)`,
since it chooses one witness per coordinate and `NaturalsBelow.choice` is the
choice principle available.

Proposition 3.5 (arity reduction) is done too, as
`Universal.IsEssential.deleteFirst` — the first consumer of
`Universal/relation.math`, built as `project` of `relation ∩
firstCoordinateIn`. It deletes the *first* coordinate rather than the
blueprint's last, since `NaturalsBelow.shiftUp` makes that one cheap and which
goes is immaterial. Corollary 3.7 follows: `HasEssential.descend` and
`HasEssential.bounded_of_witnesses`.

**The dependent product is built** (`Universal/dependent_product.math`, 152
lines): the definition, coordinatewise evaluation, the box, and the fact that
the power *is* the constant family — `power_eq_dependentProduct` is `done`,
since a non-dependent function type is the dependent one at a constant motive.
`restrict`/`project`/`cylinder` stay in their power form until Layer 7 names the
dependent counterparts it wants.

**What is left in Layer 5:** Lemma 3.7 (regrouping), which the plan has always
called the single biggest milestone and which settles design question 4;
Lemma 3.9 (`Clo_m` as a subuniverse of `A^(A^m)`); and Theorem 3.10, which
assembles them. Then Layers 6–7.

### The trick that makes arithmetic-indexed induction work

`Natural.add` is opaque, so `NaturalsBelow(gap + lower)` never reduces to the
shape an induction step wants, and a descent stated directly on those types
needs a type-level transport at every level. Wrapping the whole statement in a
predicate on ℕ — `Universal.HasEssential(a, subset, arity)` — moves the same
arithmetic to the propositional level, where `by substituting` handles it and
the induction is ordinary. This is the counterpart to the star-power finding: do
not induct on a numeral that indexes a type; induct on a numeral that indexes a
proposition *about* the type.

Note also that `by induction on x` needs `x` to be a **parameter**, not a
binder of a `∀` in the statement. `descend` takes `gap` as a parameter and
quantifies over `lower` in the conclusion, the shape `Natural.monus_add_left`
uses.

## Milestones

- **M0 — the positivity experiment.** `Term` with a function-typed recursive
  argument, its recursor, and one structural induction over it. Half a day, or
  the plan changes.
- **M1 — Layer 0 complete.** Signature, algebra, terms, substitution, the
  evaluation law, idempotence of term operations. The first honest measurement
  of the line-count estimate.
- **M2 — Layers 1–2. Done** except the dependent product, which only Layer 7
  needs. Subuniverses, `Sg`, preservation, generation by a fixed list, powers
  and binary products, the five relational constructions.
- **M3 — Layer 3. Done.** Subset cardinality and its three order facts,
  `minimum`, greatest element of a bounded set. 451 lines against an estimate
  of 300; the enumeration-list representation held and no switch was needed.
- **M4 — Layer 4. Done.** Absorption and the Taylor lemma. 764 lines. The
  first point where a blueprint statement transferred verbatim — and the first
  where the formalization sent an edit back to the blueprint.
- **M5 — Layer 5.** Regrouping and the relational description. The one that
  will take longest and the one worth reporting frictions from.
- **M6 — Layers 6–7.** Centers, doubling, ternary, main theorem. Mostly
  transcription if M1–M5 held.

## Unknowns, honestly

- **M0 gates everything and has no precedent in the library.** A function-typed
  recursive argument is standard in other systems and absent here. If it is
  rejected and option 1 is taken, add ~20% to every later estimate for arity
  bookkeeping.
- **Appendix C's exhaustiveness is an empirical claim.** Both reviewers said
  so explicitly and neither would certify it. Expect one or two further silent
  uses of `B ≠ ∅` beyond the three audited in Convention 1.2, and a handful of
  finiteness obligations that the prose leaves implicit. Log them; each is a
  blueprint edit.
- ~~**Cardinality is the estimate most likely to be wrong.** Layer 3 looks like
  300 lines and could be 1500 if subset-vs-type counting fights.~~ Settled: 451
  lines, no fight. See Layer 3 above.
- **The rate to plan with is ~1k lines/day on foundational material**, the
  same figure `PLAN_JORDAN_SCHOENFLIES.md` settled on. Nothing here bulk
  generates; the regrouping induction and the doubling construction need
  design, not pattern-following.
- **This development touches no existing area.** It imports `Set/`, `Lists/`,
  `Natural/`, `Logic/` and nothing else, and nothing existing imports it. That
  makes it unusually safe to build in parallel with the Jordan–Schönflies
  layers, and it means a narrow build target is worth adding on day one.

## Building while working here

Add `make -j 16 universal`, naming `library/Universal/*.math`, on the model of
the `plane` and `graph` targets in the Makefile. The transitive closure is
`Set/`, `Lists/`, `Natural/`, `Logic/`, `Equality/` — a small fraction of the
library, so warm runs should be seconds. Reserve `make -j 16 library` for
pre-commit checks.

## Suggested first move

**M0, today, in a scratch file.** Write the `Term` inductive with the
function-typed recursive argument, generate its recursor, and prove one
statement by structural induction over it — the evaluation law for
substitution is the right test, since it is the induction every later proof
imitates. Nothing else in this plan is worth writing until that either
compiles or is known not to.

Then settle design questions 3 and 4 before Layer 4, and edit the blueprint
for question 3: Definition 2.7 and Appendix C item 6 in
`~/claude/zeb/zhuk_centers.tex`, then `python3 regen_appendix.py` and rebuild.

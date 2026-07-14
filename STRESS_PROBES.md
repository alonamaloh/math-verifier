# STRESS_PROBES.md — goals that probe the limits of the approach

A working roadmap of library extensions chosen **not** for their own sake but
because each one isolates a different layer of the system and tells us whether
that layer holds up. Meant to sit alongside `TODO.md` and the `PLAN_*.md`
files. Use it with Claude Code as a menu of self-contained probes.

The point of every goal below is diagnostic: when it goes smoothly that is
evidence *for* the design; when it groans, the *way* it groans names a concrete
limit. Prefer finishing one probe and writing down what broke over starting
several.

---

## The diagnostic frame

Three layers can fail, and they have completely different verdicts. Every goal
is tagged with the layer it loads hardest.

- **[PROVER]** — the auto-prover (the thing behind `by`-less steps, `done`,
  bare `claim`). Today it does one library lookup, discharges against
  *in-scope* hypotheses, runs `ring`, and does **no** backward chaining.
  (Under the planned Lux cite-only prover — `PLAN_LUX_TRANSITION.md` — global
  lookup goes away entirely; this probe's verdicts still apply to the
  local-context + tactics core.) If a probe balloons here, the approach is fine and the
  prover is just immature — and the fix (e.g. `linarith`) is known.
- **[SURFACE]** — the surface language's readability under binders,
  abstraction, and higher-order objects. If a probe degenerates into
  bookkeeping that no amount of `claim`-staging hides, that is closer to a
  real design limit.
- **[FOUNDATION]** — the kernel / instance / quotient machinery. If a probe
  can't even be *stated* cleanly, that's an architecture question.

A probe is most valuable when it loads exactly **one** of these, so a failure
localizes.

---

## Repo facts this plan assumes (verify before trusting)

Snapshot taken while writing this; re-check with a build, since the library
moves fast.

- Library verifies essentially completely (269/270 non-test files on a
  foreign g++ build; the lone failure is one calc step with an explicit `by`,
  consistent with compiler-dependent ordering in the elaborator, not a broken
  proof). Real math is `sorry`-free.
- **Already done — do not re-attempt:** Cauchy-completeness of ℝ
  (`Real.cauchy_sequence_converges` in `Real/cauchy_complete.math`),
  Cauchy–Schwarz (`Real/cauchy_schwarz.math`), IVT
  (`Real/intermediate_value.math`), derivatives (`Real/derivative.math`),
  supremum/completeness (`Real/supremum.math`).
- **Genuinely absent:** any integration theory, Bolzano–Weierstrass, and the
  entire metric-space / topology stack (no metric, open set, or cover anywhere).
- **Finiteness is type-level:** `Set/finite.math` defines `HasSize (X : Type(0)) n`
  via `NaturalsBelow(n)`. There is **no** notion of "a finite subset of a set"
  or "a finite subfamily of a family." This is a hard prerequisite for the
  topology stretch goal (see PROBE-T0).
- Algebra bundles exist and are the model to imitate for any new structure:
  `Algebra/{group_bundle,ring_bundle,commutative_ring_bundle}.math`,
  `Algebra/field.math`, with field instances at `IntegerMod/field.math` and
  `FiniteField/field.math`. Abstract `ring` behaviour is probed in
  `Test/abstract_ring_ac_test.math`.
- Highest-value *infrastructure* work, independent of any probe: a
  `linarith`-style linear-arithmetic procedure. It is the most likely practical
  ceiling on naturalness everywhere and the thing the analysis probes will keep
  voting for.

---

## Recommended order (information per unit effort)

1. **PROBE-A** — analysis depth. Cheap, isolates [PROVER], teaches the
   practical ceiling fast.
2. **PROBE-G/T** — geometry → topology. The untested frontier; loads
   [FOUNDATION] then [SURFACE]; do the warm-ups first.
3. **PROBE-M** — metatheory (STLC). The real [SURFACE] verdict.
4. **PROBE-L** — abstract linear algebra. The flexibility headline, most work.
5. **PROBE-Q** — a new quotient construction. Targeted [FOUNDATION] probe on
   the biggest source of CIC leakage.

---

## PROBE-A — Analysis depth  · [PROVER]

**Flagship:** Bolzano–Weierstrass (every bounded real sequence has a convergent
subsequence). **Stretch:** Riemann integration and the Fundamental Theorem of
Calculus.

**Why interesting.** Analysis is where a shallow prover hurts most: the proofs
are dense with "obvious" inequality manipulation a human expects to vanish.
This is the cheapest way to measure the practical ceiling of the current `by`-less
machinery. Completeness and the sup are already available, so Bolzano–Weierstrass
is reachable without rebuilding foundations.

**Check first.** Is there a subsequence / monotone-subsequence notion? If not,
defining it (an index map `Natural → Natural` that is strictly increasing) is
step one.

**Predicted informative failure.** Estimate-juggling that should be one line
turns into many staged `claim`s. If so, you've made the empirical case for
`linarith`. Capture a representative ε-chasing step that *should* have been
automatic — that snippet is the spec for the procedure.

**Done =** Bolzano–Weierstrass verified for ℝ; a note in `TODO.md` (or a new
`PROVER_GAPS.md`) recording every step that needed manual estimate work.

**Stretch note.** FTC needs integration built from scratch (derivatives exist,
integrals do not). That is a substantial build, not a polish task; treat it as
a separate milestone and expect it to also stress [SURFACE] via the partition
machinery.

---

## PROBE-G — Geometry warm-up  · [FOUNDATION]

**Flagship:** define ℝ² with the Euclidean metric and prove it is a metric
space (a structure bundle: carrier + distance + the three axioms).

**Why interesting.** Forces the bundle/instance story *outside algebra* for the
first time. The diagnostic question: does the abstraction that carries
`IsCommutativeRing`/`IsField` generalize to "geometric structure," or was it
quietly specialized to rings? Cheap, genuinely geometric, and a fast read on
whether the metric bundle instantiates pleasantly before topology is stacked on
top.

**Reuse.** The triangle inequality for the Euclidean metric falls out of
`Real/cauchy_schwarz.math`. Pythagoras in ℝ² is then a one-line corollary —
a nice free Freek-list item and a sanity check that the instance is usable.

**Done =** a `MetricSpace` bundle definition; ℝ and ℝ² as instances; triangle
inequality discharged from Cauchy–Schwarz; Pythagoras as a corollary.

---

## PROBE-T — Topology: the continuity bridge  · [SURFACE]

**Flagship:** for a map between metric spaces, ε–δ continuity ⟺ the preimage of
every open set is open. State it for arbitrary metric spaces; instantiate at
ℝ→ℝ **and** ℝ²→ℝ.

**Why interesting.** The canonical first theorem of topology, and it loads the
two things the library has never done while reusing `Real/continuity.math` and
the ball definitions from PROBE-G. The real signal is the second load below.

**The two new loads:**

1. Space-with-structure abstraction outside algebra (shared with PROBE-G).
2. **Quantification over collections of sets.** Since `Set(X) = X → Proposition`,
   "open set" and especially "family of open sets" land you in
   `Set(Set(X)) = (X → Proposition) → Proposition`. Nothing in the library
   quantifies at that height today. The question: does the surface stay
   prose-like when objects are *families of sets*, or does it degenerate into
   higher-order bureaucracy? That is the limit signal.

**Predicted informative failure.** Manipulating `Set(Set(X))` membership and
the open-cover predicate makes the proof unreadable in a way ε–δ never did. If
so, that's a concrete, nameable [SURFACE] wall and a candidate for new sugar.

**Done =** the iff verified generically over `MetricSpace`, instantiated at the
two stated maps.

### PROBE-T0 — Prerequisite (do before the stretch)  · [FOUNDATION]

Confirm or build a clean **"finite subfamily of an arbitrary family"** notion.
Today finiteness is `HasSize (X : Type(0)) n` over `NaturalsBelow(n)` — type-level,
not subset-level. Heine–Borel's "finite subcover" needs finiteness of a *subset
of a possibly-infinite family*. If `Set/finite.math` + `Set/subtype.math` can't
express this cleanly, that gap is itself the first interesting finding — record
it before writing any compactness proof.

### PROBE-T1 — Heine–Borel (the actual limit test)  · [SURFACE]+[FOUNDATION]

**Flagship:** a closed interval `[a,b] ⊂ ℝ` is compact — every open cover has a
finite subcover.

**Why this is the real test.** Compactness proofs are quantifier-dense; the
standard sup/bisection argument over the cover is exactly where a declarative
surface either shines or drowns, and it depends entirely on PROBE-T0. If
Heine–Borel comes out readable, that is a far stronger claim for the design than
any algebra theorem. If it doesn't, you've found the wall — and you'll know
whether it was the finite-subfamily machinery or the higher-order quantification
that broke.

**Done =** Heine–Borel for `[a,b]`; a written verdict on whether the finite-
subcover bookkeeping stayed prose-like.

---

## PROBE-M — Metatheory: STLC type safety  · [SURFACE]

**Flagship:** progress + preservation for the simply-typed lambda calculus.
**Warm-up:** propositional-logic completeness (induction on syntax with less
substitution pain).

**Why interesting.** A *different flavor* from everything in the library: all
current content is ordinary mathematics over first-order objects, whereas
metatheory makes the **objects themselves carry binders and substitution**.
This is the classic place declarative surface languages either shine or drown,
and it loads [SURFACE] rather than the prover.

**The crux.** You immediately confront the representation choice (de Bruijn vs.
locally nameless vs. named) and the substitution lemmas. The question: does
`cases` / `by_induction on` over syntax trees with side conditions stay
prose-like, or degenerate into variable-binding bureaucracy that `claim`-staging
can't hide?

**Done =** progress and preservation verified for STLC; a note on which term
representation kept the proofs legible and where binding bureaucracy leaked.

---

## PROBE-L — Abstract linear algebra  · [FOUNDATION]

**Flagship:** `det(A·B) = det(A)·det(B)` for matrices over an abstract
commutative ring / field, instantiated at ℝ **and** ℤ/p.

**Why interesting.** The best *breadth/integration* test rather than more of the
same algebra. It makes the instance story carry real weight — prove generically
over an abstract carrier, then instantiate and expect it to just work — and it
joins two currently-separate subsystems: matrices indexed by finite sets and the
**sign of a permutation** (`Lists/permutation.math`). The sharpest sub-question:
does `ring` fire when the carrier is an opaque `IsCommutativeRing` *instance
hypothesis* rather than a concrete type? (`Test/abstract_ring_ac_test.math`
probes this small; a determinant proof probes it at scale.)

**Predicted informative failure.** Finding yourself re-proving per carrier, or
fighting projection/coercion ergonomics every time you go from "abstract field
F" to "ℝ as a field." If that happens, the abstraction is more decorative than
real. If it's clean, that's strong evidence the instance layer is genuine.

**Check first.** Is there a finite-indexed matrix type and a determinant
(sum over permutations of signed products)? Both likely need building on
`Set/finite.math` + `Lists/permutation.math`.

**Done =** `det(AB) = det(A)det(B)` over an abstract ring, instantiated at two
concrete carriers, with `ring` doing the per-entry algebra under the abstract
instance.

---

## PROBE-Q — A new quotient construction  · [FOUNDATION]

**Flagship:** localization of a commutative ring (or: completion of a metric
space, or free groups) — a quotient of a *new kind*, not another number tower.

**Why interesting.** Explicit `Quotient.{mk,sound,lift,induct}` is the single
biggest source of CIC leakage (~283 occurrences in the leak census). Every
existing number type is a quotient, so this cost has been paid once per carrier
already. A genuinely new quotient reveals whether that leakage is **structural**
(quotients are simply where the prose breaks) or **unpolished** (better
`cases`-on-quotient sugar can drive it toward zero). Either answer is useful and
feeds directly back into the leak-reduction campaign.

**Done =** the construction verified; a count of how many `Quotient.*` tokens it
took and a judgment on whether new sugar would remove them.

---

## PROBE — Steinitz exchange lemma · [SURFACE + PROVER] verdict (2026-07-14)

**What was built.** `Algebra/exchange_lemma.math`: the Steinitz inequality
`independent_le_spanning` (an independent family is ≤ a spanning one, hence
`m ≤ n`), proven by the classical one-swap-at-a-time argument — the first
genuine use of `Field.reciprocal` (dividing by the pivot coefficient in
`InSpanOf.scale_cancel`). Supporting bricks: a canonical-coordinate layer
(`standardCombination` + peel/congruence/bump), combination normalisation
(any combination of a family that vanishes past `n` → canonical coordinates),
pivot extraction from independence, `swapIn` + `exchange_step`, the
`exchange_build` induction.

**Verdict — two friction sources, both naming a concrete tool.**

1. **No additive/linear-combination normaliser over `VectorSpace.carrier`
   [PROVER].** `ring`/`field` run only over commutative-ring carriers; over a
   vector carrier the *only* automation is the fixed `automatic` flattened-law
   rewrite set, which is not a decision procedure. So group-arithmetic
   identities that a normaliser would close in one step had to be hand-proven:
   `add_subtract_cancel_left` ((a+b)−a=b), `add_pair_interchange` (the medial
   law, already in `linear_combination.math`), and the scattered assoc/comm
   chains in every `standardCombination_*` proof. **Two-tier fix, in order of
   power:** (a) an *additive-group normaliser* — the sound additive fragment of
   `ring` (assoc/comm/inverse/`0`, pushing `•` through `+`/`−`) over any
   `IsAbelianGroup`/`VectorSpace.carrier`; (b) a *`linear_combination` / free-
   module normaliser* that treats each distinct vector as an atom, normalises
   both sides to a canonical `Σ cᵢ • vᵢ` by collecting like terms — where
   collecting means **adding coefficients in the field, discharged by
   `ring`/`field`** — then compares atom-by-atom. Tier (b) subsumes (a) and
   would collapse most of `linear_combination.math` and the coordinate algebra
   in this file to one-liners (it closes `a•v + b•v = (a+b)•v`,
   `a•(u+v)=a•u+a•v`, etc.). This is the highest-impact automation the linear-
   algebra branch has surfaced.

2. **`NaturalsBelow(m)` ⇄ `Natural` transport at the boundary [SURFACE].** The
   proof runs entirely on `Natural`-indexed families with bounded predicates
   (`StandardIndependentBelow`, `Spans` + a "vanishes past n" clause), which
   kept the guts free of `NaturalsBelow.make` gymnastics — the reindexing pain
   the plan warned about *did not* materialise inside the argument (delete/
   insert/swap became point-updates via `Function.updateAt`/`swapIn`, no
   subset representation needed). The friction is confined to the **bridge** to
   the index-generic `LinearlyIndependent`/`Spans`: extending a
   `NaturalsBelow(m) → V` family to `Natural → V` needs a value-level
   *dependent* conditional (`if i<m then u(make(i, proof)) else zero`, i.e. a
   `Logic.classical_decidable(i<m)` pattern-match binding the proof, à la
   `Rational.minimumWithDecision`), the *selection* into `NaturalsBelow(m)`
   needs the same total extension (with an `m=0`/`len=0` trivial split for the
   empty index type), plus a `linearCombination_congruence`. That bridge is a
   self-contained transport package — **deferred as the documented next step**;
   the measurement itself is the finding (the encoding choice moved the cost
   entirely to the boundary, which is the right place for it).

**Done =** core theorem verified library-green (canonical-coordinate form);
official-`IsBasis` bridge is the next step; both tactic tiers filed below.

---

## PROBE — Dimension invariance (Stage F, finite) · [SURFACE + FOUNDATION] verdict (2026-07-14)

**What was built.** `Algebra/dimension.math`: a well-defined `dimension : Natural`
for finite-dimensional spaces and its invariance. `basis_size_unique` (two finite
bases of a fixed space have equal size), `dimension_unique`, `bases_equinumerous`
(the invariance through `Equinumerous`), `dimension` via `Logic.the` over the
invariance (+ `dimension_has_basis`/`dimension_equals`), `Field.vector_space_dimension`
(a field is 1-dimensional over itself), and the general index-agnostic
`SameDimension` relation with the finite bridge `same_dimension_of_equal_dimension`.
All choice-free (export-check axiom inventory unchanged).

**Verdict — the transport crux the branch was built to measure did NOT bite here;
the cost was pre-paid at the exchange bridge.** This is the single most important
finding for the branch's thesis.

1. **`n = m` transport was trivial [SURFACE].** The plan flagged finite dimension
   as "the transport crux — a propositional `n = m` you transport bundled data
   along; record how heavy it is." In the event it was one line each:
   `basis_size_unique` is `VectorSpace.exchange` applied both directions +
   `Natural.le_antisymmetric` (three cited steps); and turning the resulting
   `m = n` into `Equinumerous(NaturalsBelow(m), NaturalsBelow(n))` is a single
   `done by substituting` over `Equinumerous.reflexive`. No `cast`, no dependent
   motive, no elaborator help. The reason: the earlier architectural choice
   (Steinitz proven over `Natural`-indexed families with bounded predicates, all
   `NaturalsBelow.make` reindexing confined to `VectorSpace.exchange`) means every
   consumer of exchange — dimension included — receives a clean `m ≤ n` /
   `IsBasis`-level interface and never touches the index gymnastics. The transport
   cost is real but was localised once, at the right boundary, and does not smear
   into the invariance proof.

2. **`Logic.the` for a value-out-of-a-relation was frictionless [FOUNDATION].**
   `dimension` is definite description over the invariance, structurally identical
   to `Field.reciprocal` (existence from `FiniteDimensional`, uniqueness from
   `dimension_unique`); `dimension_has_basis` is the paired `Logic.the_satisfies`.
   `FiniteDimensional(V)` being *definitionally* `∃ n. HasDimension(V, n)` meant the
   existence argument to `Logic.the` typechecked with no restatement. The
   unique-choice wall the plan worried about is simply not present for a
   `Natural`-valued invariant.

3. **General `SameDimension` needed universe-polymorphic `Exists` — and had it
   [FOUNDATION].** Stating "a basis of one is equinumerous to a basis of the other"
   index-agnostically requires `∃ (I : Type(0)). …`, i.e. an existential quantifier
   over a `Type(1)` type. `Logic/exists.math`'s `Exists` is universe-polymorphic
   (`Exists.{u}`, auto-generalised from `A : Type`), so this elaborated as
   `Exists.{1}` with no change — a latent capability confirmed. Had `Exists` been
   monomorphic at `Type(0)` the general relation would have been inexpressible and
   forced a `Natural`-only fallback; worth noting as a capability the design
   already has.

**Done =** `dimension` well-defined and choice-free; finite invariance verified
library-green; the transport measurement is the finding — the exchange-bridge
encoding moved the cost off the invariance entirely.

---

## PROBE — Rank–nullity (Stage G) · [SURFACE + FOUNDATION] partial verdict (2026-07-14)

**What was built (`Algebra/rank_nullity.math`, bricks 1–2, library + export green,
choice-free).** The two bricks the plan named as the `Subtype`/`Subspace` boundary
measurement:

- **Brick 1 — the subtype-transport bridge, `Subspace.linearCombination_value`.**
  `Subtype.value(linearCombination_S(fam, c, sel, k)) = linearCombination_V((i)↦value(fam(i)), c, sel, k)`.
  Its two corollaries `Subspace.value_linearlyIndependent` (a subspace family's
  value-image is independent in `V`) and `Subspace.spans_of_value_covered` (a
  subspace family spans when every subspace vector's value is `0` or a `V`-combination
  of the family values).
- **Brick 2 — `LinearMap.image_finite_dimensional`**, on the linearity/combination
  interchange `LinearMap.apply_linearCombination` (`T(Σcᵢbᵢ)=ΣcᵢT(bᵢ)`): the images
  of a basis of `V`, lifted into the image subtype, span the image subspace ⟹
  finitely generated ⟹ finite-dimensional by pruning.

**Verdict, part 1 — the `Subtype`/`Subspace` value boundary the branch was built to
measure is FRICTIONLESS [SURFACE, confirming the Stage F thesis].** Brick 1 compiled
first try. `Subspace.add`/`scale`/`zero` are *defined* so their `Subtype.value` is the
corresponding `V` operation, so every value-of-a-subspace-operation step is
definitional; the only non-defeq steps in the whole induction are the two
`linearCombination_add_one` peels. `Subtype.equal_of_value_equal` then discharges every
"equal values ⟹ equal subtype elements" obligation in the corollaries with proof
irrelevance carrying the membership witnesses silently. The design decision that
`Subspace.carrier` carries the `IsSubspace` proof so `+`/`•` recover it (Stage C) is
exactly what makes the operators resolve on the subspace side with zero annotation.
**This confirms the plan's bet: one reusable transport lemma confines the entire
subtype boundary cost, and it is cheap.**

**Verdict, part 2 — the real Stage-G cost is NOT the subtype boundary but the
`NaturalsBelow` FAMILY-MANIPULATION for bricks 3–5 (append / concatenate a basis and
prove the result independent). This infrastructure does not yet exist, and building it
is a project on the scale of `exchange_lemma.math`/`basis_pruning.math` (~900 lines
each).** Concretely:

1. **Both remaining routes need a size-`k+r` `NaturalsBelow`-indexed basis of `V`.**
   `HasDimension(V, n)` is `∃ basis : NaturalsBelow(n) → carrier(V). IsBasis(basis)`,
   so to conclude `dim V = dim ker + dim im` one must *exhibit* a `NaturalsBelow(k+r)`
   basis (the ker-basis concatenated with the extension) and prove `IsBasis`. There is
   no way to read the equality off inequalities alone.

2. **The blocker is `LinearlyIndependent` of an appended/concatenated family.**
   `LinearlyIndependent(family)` quantifies over an *arbitrary injective* selection
   `Natural → I`. To prove `appendVector(e, x)` (an `e`-basis with one vector added)
   independent, a vanishing combination must be reduced to a pure `e`-combination — but
   the (at most one) position selecting the new index clamps, under any
   `NaturalsBelow(1+m) → NaturalsBelow(m)` reindex, onto a value already used by another
   position, so the reduced selection is **not injective** and `LinearlyIndependent(e)`
   cannot be applied. Escaping this needs a *position-level* skip (drop the zeroed
   position from the combination range) — the mirror of `basis_pruning`'s
   `NaturalsBelow.skip` but on the fold's position index rather than the family index.
   That machinery is what bricks 3 (subspace of f.d. is f.d., via a maximal-independent
   family — `Natural.least_witness` is available and the exchange bound
   `k ≤ dim V` transports cleanly through brick 1's corollary) and brick 4 (extend the
   ker-basis, e.g. by sifting `concat(e, basisV)`) both require, and it is genuinely new.

   **This is the honest measurement: the dependent-index story stays ergonomic for
   *reading a scalar out of* a `NaturalsBelow`-indexed structure (Stage F) and for
   *pushing values across a subtype boundary* (Stage G bricks 1–2), but *building a new
   finite family by append/concatenate and re-establishing independence* reloads the
   full `NaturalsBelow.make`/position-reindex cost that exchange and pruning each paid
   once. The cost did not disappear; it reappears wherever a proof constructs, rather
   than consumes, a finite-indexed basis.** The right fix is an infrastructure module
   (an `appendVector`/`mergeFamilies` layer with independence + spanning transport, and
   a position-skip fold lemma), not a proof hack — filed below.

**Elaborator finding (filed).** `by <Lemma>` citation fails when the lemma's conclusion
is a `definition` that δ-unfolds to `Or`/`∀` — `VectorSpace.Spans(family)` desugars to
`∀ v. v = 0 ∨ …`, and the dispatch compares the *unfolded* lemma head (`Or`) against the
*folded* goal head (`Spans`), reporting "conclusion is about `Or` but the goal is about
`Spans`" even though the fully-applied term has exactly the goal type. Workaround used in
brick 2: feed the fully-applied lemma term into a `witness … with <term>` position, which
type-checks against an expected type instead of running the citation heuristic. Root fix:
the citation head-comparison should unfold both sides (or neither) consistently.

**Done (partial) =** bricks 1–2 green, choice-free, export-check 2861 / axioms
unchanged; the subtype-boundary measurement (frictionless) recorded; bricks 3–5 scoped
with the precise blocker identified (append/concat-independence + position-skip infra).

## Side quests / infrastructure (not blocked on any probe)

- [x] **Tier (a) — additive-group normaliser over `VectorSpace.carrier` — DONE
  (2026-07-14).** The `group` tactic now runs in abelian mode over a vector
  space's additive group: it sorts the reduced word (via `add_commutative`) and
  re-cancels, closing the medial law, `(a+b)-a=b` (subtract unfolds to
  `add∘negate`), and every additive rearrangement — by `group` and as a bare
  calc step (`src/elaborator/group.cpp`, `Test/vector_group_test.math`). Retired
  `VectorSpace.add_pair_interchange` and `add_subtract_cancel_left` (deleted) and
  collapsed the assoc/comm chains in `exchange_lemma`/`basis_pruning`/
  `linear_combination` to single `by group` steps. `a•v` stays an opaque atom.
- [x] **Tier (b) — free-module normaliser (`module`) — DONE (2026-07-14).**
  New `module` decision tactic (`src/elaborator/module_normalise.cpp`, keyword
  reuses the module-declaration token in expression position). Closes an `=`
  goal over `VectorSpace.carrier(V)` by normalising both sides to a canonical
  `Σ cᵢ • vᵢ`: distribute `•` over `+`/`−` (`scale_vector_add`), collapse nested
  scales (`scale_scalar_multiply`), negate → `(−1)•` (`negate_one_scale`),
  subtract → `add∘negate`, bare `v → 1•v` (`one_scale`); then sort by atom
  (`add_commutative`), merge like atoms by adding field coefficients
  (`scale_scalar_add`), and drop coefficients the `ring` prover shows are zero
  (`zero_scale`); compare atom-by-atom with each coefficient equality discharged
  by `ring` (close goal over binders → `elaborateRing` in try/catch → reopen).
  Every step emits a kernel-checked certificate (reuses the group.cpp
  congruence/transitivity pattern). Wired into the calc-step auto-prover
  (cheap no-op off vector carriers) so it fires as a bare step too. Closes
  `a•v+b•v=(a+b)•v`, `a•(u+v)=a•u+a•v`, `a•(b•v)=(a*b)•v`, reorderings,
  `a•v−a•v=0`, and combined rearrangements (`Test/module_tactic_test.math`).
  Validated on a real proof: `linearCombination_scale`'s inductive step
  (`scale_vector_add` + `scale_scalar_multiply`) is now one `by module`. Does
  NOT reach inside an opaque atom (a `linearCombination`/`sum` head stays an
  atom), so inductions still peel + apply the IH by hand around it. Gates: full
  tests + export-check 2861 green, axioms unchanged. Docs:
  `docs/conventions/algebra-tactics.md`.
- [ ] **Finite-family construction layer (`appendVector` / `mergeFamilies` +
  independence/spanning transport + a position-skip fold lemma).** Surfaced by
  Stage G (rank–nullity) bricks 3–5: `basis_pruning`/`exchange` gave the tools to
  *consume* and *shrink* `NaturalsBelow`-indexed families, but *growing* one
  (append a vector, concatenate two bases) and re-proving `LinearlyIndependent`
  reloads the full reindex cost. The specific missing primitive is a
  **position-skip**: dropping a zero-coefficient position from a
  `linearCombination`'s `0..len-1` range (mirror of `NaturalsBelow.skip`, which
  skips a *family* index, on the *fold position* index) — needed because
  `LinearlyIndependent` demands an injective selection, and the one position that
  selects an appended vector clamps onto an already-used index under any
  `NaturalsBelow(1+m)→NaturalsBelow(m)` reindex. With that lemma,
  `independent_append_outside_span` (append a not-in-span vector keeps
  independence) and its concatenation cousin fall out, unblocking "subspace of a
  f.d. space is f.d." (brick 3), basis extension (brick 4), and the final count
  (brick 5). Estimated scope: comparable to one of `exchange_lemma.math` /
  `basis_pruning.math`.
- [ ] **Citation head-comparison unfolds inconsistently (fold-level desync).**
  `by <Lemma>` fails when the lemma's conclusion is a `definition` that δ-unfolds
  to `Or`/`∀` (e.g. `VectorSpace.Spans(family)` → `∀ v. v = 0 ∨ …`): dispatch
  compares the unfolded lemma head (`Or`) to the folded goal head (`Spans`) and
  rejects a term that in fact has the goal's exact type. Reproduced in
  `rank_nullity` brick 2; worked around by supplying the term in a `witness … with`
  position. Fix: unfold both sides (or neither) before the head comparison.
- [ ] **`linarith`.** A linear-arithmetic procedure over ordered fields. The
  analysis probes will keep generating its spec; build it from the captured
  ε-chasing snippets. Highest expected impact on naturalness library-wide.
- [ ] **Elaborator determinism.** Track down the compiler-dependent ordering
  that made one calc step fail under g++ but (presumably) pass under clang —
  likely `std::hash` / `unordered_map` iteration order in the lemma index or
  auto-prover. Soundness is safe (the kernel re-checks), but a prover whose
  *success* depends on hash order is a reproducibility smell worth fixing,
  especially for a small-trusted-base project.
- [ ] **Keep the leak ratchet honest.** Run `scripts/cic_leak_report` before/
  after each probe and record deltas in `TODO.md`. New subsystems are the
  moment leakage creeps back in.

---

## How to use this with Claude Code

- Pick **one** probe; read its "Check first" line and confirm prerequisites
  before writing proofs.
- Build the warm-up before the flagship (PROBE-G before PROBE-T; the
  propositional-logic warm-up before STLC).
- When something is hard, follow the project's own rule: find the *math-level*
  reason it's hard, decide which layer ([PROVER]/[SURFACE]/[FOUNDATION]) it
  loads, and record the finding — the failure is the result.
- After each flagship, run the full library build and the leak report, and
  write the one-paragraph verdict the probe was designed to produce.

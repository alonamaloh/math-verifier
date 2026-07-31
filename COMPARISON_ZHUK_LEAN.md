# Comparison log — Zhuk's centres, this system vs Lean 4 / Mathlib

The same theorem is being formalized twice: once in Lean 4 with Mathlib
(<https://github.com/alonamaloh/zhuk-lean>, complete, 1593 lines) and once here
under `library/Universal/` (in progress). Both follow the same blueprint
(<https://github.com/alonamaloh/csp-zhuk-centers>), so differences are
attributable to the systems rather than to the mathematics.

This file records what each system supplied, what each cost, and the design
lessons that transfer. It is a running log, appended as the second formalization
proceeds — not a verdict.

---

## 1. What the library supplied, per layer

`PLAN_ZHUK_CENTERS.md` budgets Layers 0–3 as foundation. Measured against what
each system actually gave for free:

| Blueprint item | Mathlib | Here |
|---|---|---|
| Signature (Def 1.1) | `FirstOrder.Language` ✅ | written (~10 lines) |
| Terms (Def 1.9) | `FirstOrder.Language.Term` ✅ | written (~10 lines) — **and an elaborator fix** |
| Substitution + evaluation law (Def 1.10, Lemma 1.11) | `Term.subst`, `realize_subst` ✅ | written (~50 lines) |
| Subuniverse (Def 1.4) | `Substructure` ✅ | written (~8 lines) |
| Generated subuniverse (Lemma 1.6) | `Substructure.closure` + `GaloisInsertion` ✅ | written (~40 lines) |
| Preservation (Lemma 1.14) | `Term.realize_mem` ✅ | written (~25 lines) |
| Generation by terms (Lemma 1.15) | `mem_closure_iff_exists_term` ✅ | written (~90 lines) |
| Finite choice | `choose` (one word) | **derived, ~60 lines** |
| Products of structures (Def 1.8) | ❌ absent — written (~30 lines) | ❌ absent — written (~180 lines) |
| Subset cardinality + its order facts (App. C 1) | `Set.ncard`, `Finset.card_lt_card`, `Set.eq_of_subset_of_ncard_le` ✅ | written (~300 lines) |
| `min` arithmetic (App. C 2) | `omega` ✅ | written (~155 lines) |
| CSP content (Parts II–III) | ❌ absent | ❌ absent |

The honest summary of Part I: Mathlib supplied nearly all of it; here all of it
is being written. Parts II and III are new in both.

---

## 2. Where the two systems genuinely differ

### 2.1 The M0 gate — a fix, not a workaround

The plan called out one experiment as gating everything: an inductive whose
recursive argument is a **function**,
`arguments : NaturalsBelow(arity) → Term(…)`.

In Lean this is not a question — Mathlib's `Term.func` has exactly that shape.

Here the *type* was accepted but structural recursion through it was not:
`Probe.depthAtZero(branches(0))` reported the definition's own name as an
undefined constant. Isolating it took two control probes (ordinary recursion:
fine; recursion under a lambda: fine), which located the gap precisely in
`rewriteRecursiveCalls`, which required a self-call's scrutinee to be a bare
identifier.

**Resolved by fixing the elaborator** (commit `4a76a4e7`), not by taking the
plan's list-plus-arity fallback. The induction hypothesis for a higher-order
field was already being built correctly as `Π telescope. motive(field telescope)`;
only the rewrite was missing. This is a case where the second formalization
improved the system rather than merely exercising it — and it saved the ~20%
bookkeeping tax the plan had costed for the fallback.

### 2.2 Finite choice — invisible there, 60 lines here

Closure of the term values under an operation needs, from
`∀ index. ∃ t. evaluate(t) = arguments(index)`, a *function* `index ↦ t`.

Lean: `choose`, one word, backed by `Classical.choice`.

Here: `Logic.the` is unique choice (doesn't apply — nothing distinguishes the
terms) and `Logic.countable_choice` indexes by all of ℕ. `NaturalsBelow.choice`
had to be derived (commit `4cbfaa4f`), and the derivation is not routine: the
family must be extended to every natural, which needs an option to return out of
range, and there need not be one.

The blueprint's Appendix C predicted this exactly, listing finite choice as an
import. It is the clearest instance of an "invisible" import in one system being
real work in another.

### 2.3 Products — the first head-to-head, and the ratio is ~6:1

Neither library has products of structures: Mathlib's `Ultraproducts` goes
straight to the quotient via `Prestructure`, and there was nothing here either.
So this is the first item both systems had to build from nothing.

Lean: ~30 lines for the dependent product, the binary product, coordinatewise
realization, and the reindexing and evaluation homomorphisms.

Here: ~180 lines for powers, binary products, and the three coordinatewise
evaluation lemmas.

The gap is not the definitions — those are comparable — it is the evaluation
lemmas. In Lean each is

```lean
induction t with
| var a => rfl
| func f ts ih => simp [Term.realize, ih]
```

three lines, because `simp` closes the constructor case from the induction
hypothesis and the definitional unfoldings together. Here each needs the
pointwise tuple equality by `Function.extensionality` AND an explicit four-step
chain spelling out the two definitional unfoldings, because citing a hypothesis
whose conclusion differs from the goal by an unfolding does not fire. That is
~25 lines per lemma against three, and it is the single largest per-item ratio
seen so far.

Worth noting the chain is not *worse* to read — it says exactly what happens —
but it is written by hand where `simp` finds it.

### 2.4 Generation: predicate sets beat a complete lattice

Mathlib builds `Substructure.closure` as `sInf {S | s ⊆ S}` over a complete
lattice of substructures, with a `GaloisInsertion` on top.

Here, because `Set(T) = T → Proposition`, the least subuniverse containing
`base` is **directly definable**:

```math
definition Universal.generated (a) (base) : Set(carrier(a)) :=
  (subject) ↦ ∀ (subset). Universal.IsSubuniverse(a, subset) → base ⊆ subset → subject ∈ subset
```

`contains_base`, `least` and `is_subuniverse` then each take three or four
lines, and after polishing two of them are pure `take`/`suppose` + bare `done`.
No lattice, no adjunction. This is the one place so far where this system's
foundations are *lighter* than Mathlib's, and the plan predicted it.

---

### 2.5 Layer 3 — the widest gap so far, and the least interesting one

The plan called subset cardinality the estimate most likely to be wrong, and
warned it could be 1500 lines. It came in at 451, split three ways: `min`
arithmetic (155), the two filter-length inductions (168), and the translation
into set language (128).

Against Lean the ratio is not measurable, because Lean wrote **one line**:

```lean
theorem min_min_add_one (N x : ℕ) : min N (min N x + 1) = min N (x + 1) := by omega
```

and everything else — `Set.ncard`, `Finset.card_lt_card`,
`Set.eq_of_subset_of_ncard_le`, monotonicity of `min` — came from Mathlib or
from `omega` inline at the use site. Blueprint Appendix C items 1 and 2 are, in
Lean, entirely invisible.

Two observations that are not just "Mathlib is big":

- **`omega` is doing the work, not the library.** The `min` facts are not
  Mathlib theorems being cited; they are decided. A linear-arithmetic decision
  procedure over ℕ collapses an entire module here to nothing there, and it is
  the single cheapest thing this comparison has found that this system lacks.
  Nothing about the 155 lines is *hard* — they are `a ∸ (a ∸ b)`, two
  characterising equations, and greatest-lower-bound reasoning — which is
  exactly the profile a decision procedure erases.
- **Predicate sets paid again.** `Set(A)` *is* `A → Proposition` and
  `List.filter` takes a `Proposition` predicate, so a subset can be filtered by
  directly: `size(enumeration, S) := length(filter(S, enumeration))` needs no
  coercion, no `Fintype` instance, and no decidability obligation at any call
  site. Mathlib pays for the same generality with `Set.ncard` (a
  `Nat.card` of a coercion to a type) alongside `Finset.card`, and with the
  `Set.toFinite _` arguments visible at `Doubling.lean:109`. Here there is one
  notion and it is a natural number.

The layer also retired an item from the plan's missing list without writing
anything: `Natural.greatest_witness` — a bounded nonempty predicate on ℕ has a
greatest witness — was already in `Natural/least_number.math`. The plan said
`Natural/least_number` does not supply it. It does.

### 2.6 Layer 4 — the first fair fight, and the ratio drops to ~3:1

Absorption is Part II, so **neither library supplies any of it**. Both
developments wrote the same four things from nothing, and this is the first
place the comparison measures the two systems rather than the two libraries.

| | Lean | Here |
|---|---|---|
| `Witnesses` / `Absorbs` / `BinAbsorbs` | `Absorption.lean`, 178 | `absorption.math`, 312 |
| Star powers | `StarPower.lean`, 54 | `star_power.math`, 297 |
| `t[ρ]` and its evaluation | `Term.relabel` (Mathlib) | `term.math` +39 |
| cons/uncons of `Fin (n+1)` | `Fin.cons`, `fin_cases` (Mathlib) | `finite_successor.math` +116 |
| | **232** | **764** |

Three things are worth separating out of that 3.3:1.

**The definitions are the same.** Lean's

```lean
def Witnesses (E D : Set M) {V : Type*} (t : L.Term V) : Prop :=
  ∀ (i : V) (z : V → M), z i ∈ D → (∀ j, j ≠ i → z j ∈ E) → t.realize z ∈ E
```

and `Universal.Witnesses` are the same proposition, binder for binder, and both
range over an arbitrary variable type. The *proof* of Lemma 2.6 is the same
proof too — same preamble ("every coordinate lies in `D`"), same split on which
of the two variables is free, same "switch to the `v` side" in the first arm.
Where a blueprint statement is precise, both formalizations transcribe it and
neither gets to be clever. That is the encouraging half.

**Mathlib's `Fin` API is most of the gap.** `fin_cases i₀` splits a `Fin 2`
into its two elements and `by decide` discharges `0 ≠ 1`; here the split is on
`NaturalsBelow.value(free) = 0` and the disequality is an explicit
value-level chain. Similarly `Fin.cons` and `Fin.elim0` are Mathlib primitives,
where `NaturalsBelow.first` / `.shiftUp` / `.dropFirst` / `.first_or_shift` had
to be written — 116 lines that are genuinely reusable and genuinely absent.
None of this is deep; all of it is typing.

**One difference is structural, not library depth.** Lean writes the star power
as a dependent recursive definition and gets its unfolding for free:

```lean
def starPower {k : ℕ} (t : L.Term (Fin k)) : (ℓ : ℕ) → L.Term (Fin ℓ → Fin k)
  | 0 => var Fin.elim0
  | ℓ + 1 => t.subst fun j => (starPower t ℓ).relabel fun q => Fin.cons j q

theorem starPower_succ … := rfl
```

That `rfl` is available because in Lean `ℓ + 1` is definitionally `Nat.succ ℓ`.
Here `Natural.add` is **opaque**, so `1 + rest` and `successor rest` are not
definitionally equal, and the recursive definition does not typecheck at all —
its `1 + rest` arm must produce a `StarIndex(arity, successor(rest))` where it
has a `StarIndex(arity, 1 + rest)`. There is no arrangement of the arithmetic
that fixes this; opacity is the point of the seal.

The fix is not a workaround so much as a relocation: publish `starBase` and one
level `starStep`, and iterate inside a *proof*, where an equation-shaped
`by induction on depth` **rewrites** the goal to the `1 + rest` form instead of
needing it to reduce. That is where the centrality argument wants the iteration
anyway, since it carries an invariant up the levels rather than just a term.
The cost is that `star_power.math` cannot name `t^{*ℓ}` as a function of `ℓ`.

This is the sharpest system-level difference the comparison has found so far,
and it is a real trade: the `Natural` seal buys a `ℕ` whose representation
never leaks, and charges for it exactly here.

**A footnote on the blueprint.** Lean had already indexed star powers by
`Fin ℓ → Fin k` and already had `Absorbs.of_finite` transporting a witness off
an arbitrary finite variable type. The blueprint was behind *both*
formalizations; the eighth draft catches it up. Two independent formalizations
converging on a representation the prose had not chosen is about as strong a
signal as this exercise produces.

### 2.7 Layer 5 — where Lean's proof was *mathematically* better

Layer 5 is regrouping (Lemma 3.7) and the relational description of absorption
(Theorem 3.10). Neither library supplies any of it, so this is the second fair
fight.

| | Lean | Here |
|---|---|---|
| Regrouping (Lemma 3.7) | `Regrouping.lean`, 135 | `regrouping.math`, 817 |
| `Clo_m` + Theorem 3.10 | `Relational.lean`, 95 | `clone.math` 118 + `relational.math` 349 |
| | **230** | **1284** |
| Indexing a subset by an initial segment | `Finset` + `Finset.card` ✅ | `subset_indexing.math`, 458 |
| A finite power of a finite type is finite | `Fintype` instance ✅ | `finite_function.math`, 191 |

The two library rows are the familiar story — `Finset` and the `Fintype`
instance graph collapse 649 lines to nothing. The two proof rows come in at
5.6:1, noticeably worse than Layer 4's 3.3:1, and the reason is visible in the
proofs: `Finset.card_lt_card` supplies the induction measure and `Finset`'s
membership algebra is used at every step of both branches, where here each of
those is a stated fact over `NaturalsBelow.IndexesSubset`.

**The interesting difference is not a ratio.** Lean's Theorem 3.10 has *no
degenerate cases*, where the blueprint's proof spends three paragraphs on
`S = A`, `S = ∅` with `m ≥ 2`, and `S = ∅` with `m = 1`. The plan here had
budgeted for those, and the first version written here had them: the blocks of
the partition of `X` are nonempty because `S` and `A ∖ S` are, so both have to
be inhabited, so the two extremes are peeled off first — and the statement was
restricted to `2 ≤ arity` to drop the third.

Lean does not need any of it, because `IsEssentialOn.exists_mem` derives
"every block meets the live set" **from block essentiality itself**: if some
block were empty, condition (B1)'s witness freed at that block would lie inside
`S` at every live coordinate, which is exactly what (B2) forbids. Four lines.

That fact is available here just as much as there, and it was simply not seen
when the plan was written. `Universal.IsBlockEssential.blocks_populated` is the
same argument, and with it Theorem 3.10 discharges regrouping's surjectivity
premise inside the very branch where (B2) is assumed. `relational.math` came
down from 537 lines to 349 (144 net, counting the new lemma), has no case split
anywhere, and holds at **every** arity — no `2 ≤ arity`, no `S ≠ ∅`, no
`S ≠ A`.

Two things worth separating out.

- **This is a blueprint edit, and the blueprint is behind both formalizations
  again.** Definition 3.2 builds nonemptiness into the word "partition", so
  Lemma 3.7 carries it as a hypothesis and Theorem 3.10 has to check it. Drop it
  from the definition, prove it as a remark, and Theorem 3.10's preamble deletes
  itself. Same shape as the star-power finding of §2.6: a representation the
  prose had not chosen, which one formalization found and the other confirms.
- **The mechanism of the discovery is worth recording.** Nothing about the
  formalization forced this; the first version here typechecked, and was
  complete and correct. What surfaced the redundancy was reading the *other*
  system's proof of the same theorem and noticing it did less work. A second
  formalization catches errors, which is its advertised value; catching
  *unnecessary hypotheses* is a distinct and less obvious one, and it only
  works if the two are read against each other rather than merely both
  completed.

### 2.8 Layer 6 — the cardinality representation shows its bill

Layer 6 is the centre argument: neighbourhoods and the left centre (Lemma 4.3),
the enlargement step (Theorem 5.1), and its iteration (Theorem 5.2). Part III,
so again neither library supplies any of it.

| | Lean | Here |
|---|---|---|
| Centres and neighbourhoods | `Center.lean`, 139 | `center.math` §1, ~300 |
| Enlargement step | `Step.lean`, 93 | `center.math` §2, ~300 |
| Star-power iteration | `Absorbs.lean`, 103 | `center.math` §3, ~570 |
| Term operations fix constants | `IsIdempotent.realize_const` (written) | `term.math` +45 |
| A nonempty subset is counted ≥ 1 | `Set.ncard_pos` ✅ | `enumeration.math` +21 |
| | **335** | **~1230** |

3.7:1, in line with the other fair fights. Three observations.

**The cardinality representation is what costs here, and it is not the count —
it is the enumeration.** `Set.ncard` is a function of a set alone, so Lean's
statements never mention finiteness; ours are `Set.size(enumeration, subset)`
against a fixed enumeration of `B`, so every statement in the layer carries
`enumeration` and `isEnumeration` as parameters and every call site threads
them. Layer 3 chose that representation and it held with no fight (see §2.5) —
the bill arrives here, as parameter plumbing rather than as proof difficulty.
Nothing was harder to prove; everything was longer to say.

**`omega` again, and again it is cheap to name.** Lean's `min_min_add_one` is
`by omega`. Here it is `Natural.minimum_absorbs_one_plus`, one of the two facts
Layer 3 built for exactly this consumer — so the *use* site is the same length
in both, and the difference stayed in Layer 3's 155 lines. This is the pattern
worth noting: a decision procedure's advantage shows up once, in the layer that
would have to prove the lemma, not repeatedly at every use.

**The star-power decision was vindicated.** §2.6 recorded that `Natural.add`'s
opacity makes `t^{*ℓ}` unnameable as a function of `ℓ`, and that the iteration
would have to happen inside a proof. It did, and the shape it forced —
`center_star` asserts *there exists* a term of the right index type satisfying
`(∗_ℓ)`, with the induction producing term and bound together — turned out to
be the natural statement rather than a concession: the invariant is what the
argument carries up the levels, and the term rides along. The final theorem
still names the blueprint's depth, `|B| ∸ 1`, in the type of the term it
produces. Lean, which *can* define `starPower t ℓ` and prove
`realize_starPower_succ` by `rfl`, states the two separately and needs no such
existential; that is a genuine convenience, and it is the only place in this
layer where the `Natural` seal is visibly charged for.

### 2.9 Layer 7 — the last layer, and what the blueprint over-specified

Layer 7 is centrality (Theorem 6.1), central absorption (Definition 6.2 and
Corollary 6.3), the Zhuk–Kozik doubling trick (Lemma 7.1), the ternary collapse
(Corollary 8.1) and the main theorem.

| | Lean | Here |
|---|---|---|
| Centrality, central absorption | `Central.lean`, 179 | `central.math`, 802 |
| Doubling, ternary, main theorem | `Doubling.lean` 289 + `Ternary.lean` 71 | `doubling.math`, 2128 |
| Reindexing essentiality along a bijection | (in `Regrouping.lean`) | `essential.math` +105 |
| | **539** | **3035** |

5.6:1 — the same as Layer 5, and for the same reason: `Finset`, `Set.ncard` and
`Nat.find` do in one token each what is a stated fact here.

**Both formalizations found the same two simplifications, independently of the
blueprint.**

- *Theorem 6.1 needs no sorted enumeration.* The blueprint enumerates the
  generators so the three blocks are consecutive, extracts indices `p ≤ q` and
  picks `m` between them — an apparatus that exists only to index a sorted list.
  Both formalizations make the variable type of the realising term *be* the
  generating set, so each variable already knows its block and the selector is
  "is this generator's second coordinate the point". Blueprint Lemma 1.20, the
  block-respecting enumeration, is used nowhere; it was written for this proof
  and this proof does not want it.
- *Lemma 7.1 does not need mixed factors.* The blueprint states it over
  `A₀ × ⋯ × A_{n+1}` with designated subuniverses `C, B₁, …, B_n, C'`; its only
  consumer, Corollary 8.1, applies it with everything equal. Specialized, every
  relation is a subset of a power, the statement is literally `HasEssential`,
  and neither formalization ever built a dependent product for it. Here that
  retires `PLAN_ZHUK_CENTERS.md`'s prediction that Layer 7 would need
  `dependent_product.math`, which remains built and unused.

That is two blueprint over-specifications caught by *agreement between two
formalizations* rather than by either one alone — the same mechanism as the
`blocks_populated` finding of §2.7, and now the clearest recurring value this
exercise has produced.

**Where the two diverge.** Lean reaches for `Fin (n+1) ⊕ Fin (n+1)` as the
doubled index and transports with `finSumFinEquiv`; here the same move needed
`Universal.IsEssential.reindex` to be written first (105 lines — blueprint
Lemma 1.19(e), which nothing earlier had consumed) and `NaturalsBelow.sum_out_of`
from Layer 3's `finite_sum.math`. Building `R'` the way the blueprint describes
it — an intersection of cylinders, then a projection — paid for itself
immediately: closure is `IsSubuniverse.project`/`.cylinder`/`.intersection` and
nothing is checked by hand, where Lean's `doubled` proves `fun_mem` directly.

**A loose end this layer exposed.** `Set.IsEnumeration` (Layer 3, subset
cardinality) and `HasSize` (Layer 5, type cardinality) are independent notions
here with no bridge, so the main theorem carries both finiteness hypotheses for
the same carrier. Mathlib has one `Finite` and derives what it needs. A lemma
`Set.IsEnumeration(A, e) → HasSize(A, length(e))` would collapse them; it needs
an "index of an element in a distinct list" construction the library does not
have.

### 2.10 The notation experiment — 14% of lines for a day's work

An outside reviewer measured this tree and found that three token substitutions
removed 24% of its characters. That prompted an audit of what the language
already offers, and most of the answer was: more than the development was using.

| lever | status | effect |
|---|---|---|
| `convention signature : Universal.Signature` | **already existed** | removes a binder from 150 of 174 declarations |
| `operator (^)` for the power, `(×)` for the product | operators existed; `×` needed one lexer entry | 237 + 177 call sites, and it is the blueprint's own notation |
| `Universal.carrier`, `Universal.universe` aliases | ordinary definitions | 673 + 117 call sites |

Net: **14.3% fewer lines and 9.7% fewer characters**, no mathematics touched.
`center_central`'s signature went from 13 lines to 11 and now reads
`(closed : Universal.IsSubuniverse(a × b, relation))` where it read
`(closed : Universal.IsSubuniverse(Universal.Algebra.product(a, b), relation))`.

Three findings worth keeping:

- **`convention` is the feature Lean calls `variable`, and it was in the tree
  the whole time** — `Graph/` uses it for exactly this. The development simply
  never opened the door on it. That is a documentation failure more than a
  language gap.
- **Adding a lexer token is cheap.** `×` cost five lines of C++ (a `TokenKind`,
  a table entry, a diagnostic string, an `isOperatorSymbolToken` case, and a
  `parseMultiplicative` case). If notation is what makes a development readable,
  the barrier to new notation should be this low, and it is.
- **An alias can push the auto-prover off a fast path.** After `a ^ N` replaced
  `Universal.Algebra.power(a, N)`, one bare conjunction-projection in
  `doubling.math` went from silent to a 70k-step, 626 ms search, because the
  prover's structural match no longer saw through the operator. Notation is not
  free at the prover level, and that is worth knowing before a library-wide
  sweep.

**Coercion to sort, and the rest of the sweep.** Four further levers, measured
on top of the above:

| lever | effect |
|---|---|
| coercion to sort — `Set(a)`, `(x : a)`, `a → a` | 673 sites |
| `≠` for `¬(x = y)`, `∉` for `¬(x ∈ S)` | 217 + 19 sites |
| deleting the hand-rolled `1 ≠ 0` derivations | 4 sites, 32 lines → 6 |
| five `let`s for repeated compound terms | 82 sites |

Running total against the pre-notation tree: **15.7% fewer lines, 14.9% fewer
characters**, and the two proofs the reviewer named as unreadable now read as
`(relation : Set(a × b))`, `(closed : Universal.IsSubuniverse(a × b, relation))`,
`(element : a)`.

Three things learned doing it:

- **Coercion to sort was half-built.** `coerceBundleValueToCarrier` already
  fired wherever a type was wanted, applying `<Structure>.carrier` by naming
  convention. Two gaps kept it from this development: it did not solve the
  projection's leading implicits (so a signature-parametrised carrier was
  mis-applied), and a declaration's *return type* was not routed through it.
  Both are a few lines. Its one real limit: a pattern-match definition's return
  type cannot use it, because the recursor's motive must syntactically end in a
  Sort — hit exactly twice.
- **The `1 ≠ 0` ceremony was self-inflicted.** The reviewer read six lines of
  value-chasing as a missing decision procedure. It is not: `by
  NaturalsBelow.ne_of_value_ne` alone closes the goal, and always did. Four
  copies of a hand-rolled derivation existed because nobody tried the one-liner.
  A cheap tactic would have hidden the same mistake.
- **The `let` traps are narrower than they looked.** Three of five attempted
  abbreviations took, at 82 sites; the two that failed are the documented shape
  — a `let`-bound set that a later `witness` must unfold. Abbreviating a
  compound term used as an *argument* is safe; abbreviating one that has to be
  seen through is not.

**Lifting the algebra too.** A follow-up review pointed out that removing the
`{signature}` binder left 139 declarations still spelling
`(a : Universal.Algebra(signature))`, and that `Algebra/group.math` lifts a
whole structure — carrier, operations, and the `IsGroup` proof — into chained
conventions. It does, and `convention a b : Universal.Algebra(signature)` under
`convention signature` works: 70 theorem binder lines gone, 21 left.

The split that matters is theorem versus definition. A theorem's algebra is
ambient and its citations are argument-free, so lifting it is free. A
definition's is often what a reader needs to see, and making it implicit only
pays where it is *inferable from another argument*: `Universal.leftCenter(relation)`,
`Universal.betaSet(subset, relation)` and `Universal.doubledRelation(relation, link)`
took (75 + 57 + 15 sites, the last turning a 103-character term into 40), while
`Universal.pair` and `Universal.neighborhood` did not — the second algebra is not
determined by the arguments the elaborator sees first.

Two wrinkles found in the convention mechanism, both worth a diagnostic:

- **A convention binder is prepended ahead of *all* user binders.** So a
  convention whose type references a name the declaration also binds explicitly
  dangles — `{a : Universal.Algebra(signature)}` in front of a user's
  `(signature : Universal.Signature)`. The error points at the convention's
  declaration line, several files away from the declaration that triggered it.
  The fix at the use site is to drop the redundant explicit binder.
- **A convention that is never mentioned is not free.** Adding
  `convention a b` to a file that uses neither still tripped the above, because
  another declaration bound `signature` explicitly. Declare conventions only in
  the files that use them.

What did **not** work: `Universal.Tm(V)` for `Universal.Term(signature, V)`. The
convention makes `signature` implicit, and an implicit that appears only in a
pattern-match definition's *return* type cannot be inferred. The same shape is
why a coercion-to-sort is the remaining prize: `Universal.carrier` is still 3.2%
of all characters, `NaturalsBelow` 7.5%, and the `Universal.` prefix 11.3% —
the last needing a namespace mechanism the language does not have.

---

## 3. Design lessons that transfer

These came out of one system and improved the other, or improved the blueprint.

1. **Index the signature by arity.** `signature : ℕ → Type(0)`, as Mathlib does,
   rather than `symbol : Type` plus `arity : symbol → ℕ` as the plan first
   proposed. The arity becomes definitional, so the argument tuple's type carries
   no dependency on the symbol. Adopted here; it is why the constructor
   typechecked first try.

2. **Variables from an arbitrary type.** Then substitution is
   `(source → Term(target)) → Term(source) → Term(target)` — one operation
   covering renaming, identification and dummy variables — and the generating
   set can *be* the variable type, so `Universal.generated_eq_termValues` needs
   no enumeration of the generators. Blueprint Lemma 1.15 and Lemma 1.20
   (block-respecting enumeration) both simplify as a result.

3. **State a vanishing condition as a bound on what you hold.** This has bitten
   three times, in both directions:
   - `HasNoConstants` as "every symbol has positive arity", not "`signature(0)`
     is empty";
   - `NaturalsBelow.choice` splitting on whether the *index set* is inhabited,
     not on whether the bound is zero.

   The underlying fact: **an equation-shaped case split on a natural does not
   refine the types of other things in scope that mention it.** Splitting on
   `bound` leaves `property : NaturalsBelow(bound) → …` untouched, so the arm
   needs a hand-written transport. Choosing a formulation where the split never
   has to reach into another binder's type avoids this entirely. This is a
   dependent-types lesson, not a quirk of either system.

---

## 4. Frictions, by system

### Lean / Mathlib

- Tactic imports are not transitive: `fin_cases`, `ring` and `norm_num` each
  need their own import even with `Mathlib.ModelTheory.*` in scope. `omega` is
  available and handles `min`/`max` on `ℕ`.
- `Structure` bundles `funMap` and `RelMap`, so every product instance must
  supply a `RelMap` even for a purely algebraic signature.
- Binder-type inference on subtype coercions: `fun g => (g : A × A).1`
  elaborates `g : A × A` rather than coercing from `↥S`. Naming the valuation
  fixes it.

### Here

- **`Natural.add` is opaque, so `1 + k` is never definitionally `successor k`.**
  A dependent recursive definition on ℕ whose result type mentions the
  recursion variable cannot be written at all. See §2.6; the workaround is to
  publish the base and one step and iterate inside a proof.
- **A conditional whose branch *uses* the branch hypothesis needs
  `Logic.if_positive_dependent` / `if_negative_dependent`.** `if_positive`'s
  branches are constants, so it silently fails to match — reported as an
  uninferable argument rather than as the dependence. Both variants are
  documented side by side in `Natural/classical_decidable.math`; the trap is
  reaching for the more familiar one.

  **This is a fixable leak, not a fact of life.** `if_positive` *is*
  `if_positive_dependent` at a constant branch, so the choice the author is
  being asked to make carries no mathematical content — it is about how the
  branch was written. Publishing only the dependent forms, with the plain ones
  as `automatic` corollaries, would remove the decision entirely. The same goes
  for the module name: a file that wants `if P then a else b` must
  `import Natural.classical_decidable`, which tells the author about a
  decidability mechanism when what they wrote was "by cases on whether P".
  Worth an issue against the library, independent of this development.
- **Implicit arguments are not inferred in a theorem *statement* with no outer
  expected type.** `Universal.starPrepend(block, position, …)` with implicit
  `{arity depth}` put `block` in the `arity` slot — via the
  `NaturalsBelow → ℕ` coercion, so the error surfaced as a type mismatch two
  arguments later. Making the numeric parameters explicit fixed it; so did a
  `(… : T)` ascription where a bare `NaturalsBelow.first` appeared. Same root
  cause as the `Set.IsNonempty` note in `Set/basics.math`.
- **A `let`-bound set blocks the unfolding that `witness` needs.** Binding the
  long `Universal.project(a, …, clone(a, m))` as `let restrictedClone := …` and
  then proving `restrict(…) ∈ restrictedClone` by `{ witness p }` fails with
  "expected type does not have an inductive head": the goal does not reduce past
  the `let` to the `∃` that `project`'s body is. Spelling the projection out at
  every use fixes it. This is the second `let` trap — the first being that an
  equation about a `let`-bound function has no occurrence left to rewrite — and
  the shared lesson is that a `let` is fine for a value only *read*, and wrong
  for one whose definition a later step must see through.
- **Named arguments work only for globally declared functions, not for a local
  hypothesis.** `by innerBound(values := …)` reports "function 'innerBound' is
  not in scope" — `innerBound` being a hypothesis of the theorem being proved.
  So instantiating an induction hypothesis at a higher-order argument the goal
  cannot determine has to be a positional call supplying *every* argument,
  including the premise, which then has to be named. Lifting the named-argument
  form to local binders would remove the only direct lemma call in Layer 6.
- **`choose x such that P as name from source;`** — the `as` clause comes
  *before* `from`, not after. Easy to get backwards, and the parse error points
  at the `as`.
- **A lambda on the right of a claim, or after `witness`, needs parentheses.**
  `arguments = (i : T) ↦ e;` is a parse error at the `↦`. Cost a round-trip
  three times.
- **Multi-statement case bodies need `{ }`,** and `for some` binders need
  explicit types. Neither is visible in the reference's examples, which are all
  single-expression cases.
- **"Implicit binders must precede all explicit binders"** — a real constraint,
  hit twice, and it fights the reading order one would choose at call sites.
- **Parse errors report `file:1:1:`** with the true position in the message
  prose. Logged in `docs/error_message_inbox.md` with the three code sites.
- **A `by cases` on a proposition needs the disjunction brought into scope
  first.** The diagnostic says so clearly, which is good; the requirement is
  still a step.
- Citing a hypothesis whose conclusion differs from the goal by a definitional
  unfolding fails. State the operative fact and let `done` bridge — which reads
  better anyway.
- **A chain step's `by` must prove that step's relation exactly.** `≤ 1 + f(y)
  by IH` is rejected where `IH : f(x) ≤ f(y)` — "this step's justification
  proves a different relation than the step claims" — even though the step
  follows from `IH` by one monotonicity move the prover makes unaided. The fix
  is to drop the `by` and let the by-less step pick `IH` out of context, which
  costs the reader the one citation the style guide most wants kept. Hit three
  times in `Lists/filter_length.math`. The diagnostic is excellent; the
  asymmetry (a cite is *narrower* than no cite) is the surprise.

---

## 5. Line counts

Both formalizations are now complete.

| | Lean | Here |
|---|---|---|
| Part I foundation | ~200 (products + inventory) | ~510 |
| Finite choice | 0 (a tactic) | ~60 |
| Subset cardinality + `min` (App. C 1–2) | 1 (`by omega`) | 451 |
| Absorption + star powers (Part II, Layer 4) | 232 | 764 |
| Subset indexing + finite powers (Layer 5 support) | 0 (`Finset`, `Fintype`) | 649 |
| Regrouping + relational description (Part II, Layer 5) | 230 | 1284 |
| Centres, enlargement step, iteration (Part III, Layer 6) | 335 | ~1230 |
| Centrality, doubling, ternary, main theorem (Layer 7) | 539 | 3035 |
| | **1591** | **~8900** |

The Lean figure for Part I is small because Mathlib supplied the rest; the
figure here is the true cost of the same content. The Parts II–III rows are the
ones that measure the two systems on equal footing, since neither library
supplies any of it — and the first of them, Layer 4, came in at 3.3:1 against
the 6:1 of the products and the unbounded ratio of Layer 3. See §2.6.

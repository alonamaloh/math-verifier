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

Not comparable yet — Lean is complete, this is through Layer 3 — but recorded
as they land.

| | Lean | Here |
|---|---|---|
| Part I foundation | ~200 (products + inventory) | ~510 |
| Finite choice | 0 (a tactic) | ~60 |
| Subset cardinality + `min` (App. C 1–2) | 1 (`by omega`) | 451 |
| Parts II–III | ~1400 | not started |

The Lean figure for Part I is small because Mathlib supplied the rest; the
figure here is the true cost of the same content. The Parts II–III comparison,
when it comes, is the one that measures the two systems on equal footing, since
neither library supplies any of it.

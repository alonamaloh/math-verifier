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
| Products of structures (Def 1.8) | ❌ absent — written (~30 lines) | not yet reached |
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

### 2.3 Generation: predicate sets beat a complete lattice

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

---

## 5. Line counts

Not comparable yet — Lean is complete, this is mid-Layer-1 — but recorded as
they land.

| | Lean | Here |
|---|---|---|
| Part I foundation | ~200 (products + inventory) | ~330 so far |
| Finite choice | 0 (a tactic) | ~60 |
| Parts II–III | ~1400 | not started |

The Lean figure for Part I is small because Mathlib supplied the rest; the
figure here is the true cost of the same content. The Parts II–III comparison,
when it comes, is the one that measures the two systems on equal footing, since
neither library supplies any of it.

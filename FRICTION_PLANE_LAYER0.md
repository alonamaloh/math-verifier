# Frictions found building `library/Plane/` (Layer 0)

Working notes in the style of `QUIRK.md`, kept separate only because that
file was open in another session when these were written — fold them in
when convenient. Each entry: symptom, minimal repro where I have one,
root cause where I found it, and the workaround the library currently
uses.

Provenance: writing Layer 0 of the Jordan–Schönflies foundation
(`PLAN_JORDAN_SCHOENFLIES.md`) — 81 theorems across
`Plane/{vector,point,bilinear,direction,norm}.math` plus
`Real/maximum.math`. This is the first geometry the library has ever
carried, so it exercises ε-δ and ordered-field reasoning far harder than
the algebra does.

**The headline: section I. Every entry there is a step a mathematician
writes without pausing.**

**Status 2026-07-25.** I2, I3, I5 and I6 are closed — four missing
lemmas and one missing `automatic` tag, no tactic work. Retiring them
also confirmed the division of labour proposed by the elaborator session:
with the lemmas in place, **I4 is the only entry that genuinely needs a
decision procedure.** The evidence is concrete — `add_preserves_LessOrEqual_both`
retires every *syntactic* sum-of-two-bounds, and what it cannot touch is
exactly the shape (`a - b ≤ (c - a) + (c - b)`) where the rearrangement
is the content. I1, I7 and I8 are the elaborator session's.

Measured after the three new `automatic` tags, against the numbers in
this file: `Real/supremum` 3.37s (was 3.35–3.38), `Algebra/ring_lemmas`
1.37s (was 1.55–1.57), `Algebra/residue_arithmetic_generated` 132.5s
(was 144.5). No regression from the larger candidate pool.

---

## I. Inequalities

### I1 — the sign battery cannot see zero on the right

**Symptom.** `0 ≤ 2 * (c - a)` closes by itself. `2 * (b - c) ≤ 0` does
not, and reports the full "no in-scope hypothesis matches structurally…"
failure.

**Root cause — found.** `Elaborator::parseSignJudgment`,
`src/elaborator/lemma_index.cpp`:

```cpp
if (arguments.size() == 2) {
    bool weak = endsWith(head, ".LessOrEqual");
    bool strict = endsWith(head, ".LessThan");
    if (!weak && !strict) return false;
    auto leftNumeral = asNumeralLiteral(arguments[0]);
    if (leftNumeral && leftNumeral->second == 0) {
        out = {weak ? "zle" : "zlt", head, arguments[1]};
        return true;
    }
    return false;                 // ← `e ≤ 0` falls off the end
}
```

Only `0 ≤ e` / `0 < e` parse as sign judgments. For `e ≤ 0` the subject
would be the literal `0`, so it bails and the goal never enters the
battery at all.

**Not a one-line fix.** `parseSignJudgment` only computes an *index key*;
the proof itself comes from `matchAgainstPattern(rule.conclusion,
goalClosed, …)`. Recognising `e ≤ 0` gets goals *in*, but every existing
rule is stated `0 ≤ …` and will not match. It also needs a form bridge
`e ≤ 0` ⟼ `0 ≤ -e`, and the bridge machinery is adjacent to
`collectContextFacts` / `tryContextFactMatch`.

**Workaround.** Phrase every bound as a nonnegative increment
(`Real.less_or_equal_add_of_nonneg`) so the zero stays on the left. See
`Real.maximum_LessOrEqual`.

### I2 — CLOSED 2026-07-25 — strict/non-strict asymmetry, in both directions

Two separate gaps that point opposite ways, so neither "the strict forms
are weaker" nor the converse is the right summary.

- ~~`-x ≤ c` from `-c ≤ x` needs `Real.LessOrEqual.negate` cited.~~
  **Fixed:** `Real.LessOrEqual.negate` is now `automatic`, matching its
  strict twin.
- ~~`0 < c - a` from `a < c` is **not** automatic, while `0 ≤ c - a` from
  `a ≤ c` **is**.~~ **Fixed 2026-07-25 (second pass):** it bit a *second*
  independent site — `Plane.Ball_IsOpen` — which is what earned it a
  lemma rather than another hand-bridge.
  `Real.subtract_positive_of_LessThan`, `automatic`, in
  `Real/order.math`; both bridges retired.

### I3 — CLOSED 2026-07-25 — adding two inequalities is not a step

**Symptom.** From `x₁ ≤ y₁` and `x₂ ≤ y₂`, the goal `x₁ + x₂ ≤ y₁ + y₂`
does not close.

`Real.add_preserves_LessOrEqual : x ≤ y → x + z ≤ y + z` adds on the
**right only**. There is no left form, and no
`a ≤ b → c ≤ d → a + c ≤ b + d`.

**Workaround.** Route through right-addition twice with a commute in
between:

```math
x₁ + x₂ ≤ y₁ + x₂   by Real.add_preserves_LessOrEqual
        = x₂ + y₁
        ≤ y₂ + y₁   by Real.add_preserves_LessOrEqual
        = y₁ + y₂;
```

This was the **most frequent** friction in the whole batch.

**Fixed:** `Real.add_preserves_LessOrEqual_both`
(`a ≤ b → c ≤ d → a + c ≤ b + d`), `automatic`, in `Real/order.math`. The
workarounds in `Plane/norm.math` collapsed to single steps.

**Caveat found while retiring it:** the lemma matches only when both
sides are *syntactically* sums. `a - b ≤ (c - a) + (c - b)` is not, so
`Real.maximum_LessOrEqual` still routes by hand — that residue is I4, not
I3.

### I4 — CLOSED 2026-07-25 — linear arithmetic over an ordered field

**Symptom.** `a - b ≤ (c - a) + (c - b)` from `a ≤ c` and `b ≤ c` is
declined. It is a pure linear consequence.

**Workaround (retired).** Hand-route as a nonnegative increment:
`a - b ≤ (a - b) + 2*(c - a) = (c - a) + (c - b)`. Every such step in
`Real/maximum.math` had to be written this way.

**Fixed:** the `ordered_field` tactic
(`PLAN_ORDERED_FIELD_TACTIC.md`, `src/elaborator/ordered_field.cpp`),
named for the theory the way `ring` is. Both proofs in
`Real/maximum.math` now say
`a - b ≤ (c - a) + (c - b) by ordered_field;` and the `-2c`
scaffolding is gone.

Two things the fix taught, worth keeping:

- **The gap was two-layered.** Even handed the difference in the goal's
  own spelling, `0 ≤ ((c - a) + (c - b)) - (a - b)` from `a ≤ c`
  exhausts the auto-prover budget: the sign battery does not
  ring-normalise its subject, AND nothing bridges `0 ≤ D` to `L ≤ R`
  when `D` merely ring-equals `R - L`. Both had to be covered.
- **The corpus was smaller than this section looks.** `x ≤ x + y` from
  `0 ≤ y` already closed bare, so the `Plane/bilinear.math` and
  `Plane/norm.math` sites were never I4 — their
  `by Real.less_or_equal_add_of_nonneg` is a redundant hint. Measuring
  each shape in isolation before building is what caught that.

### I5 — CLOSED 2026-07-25 — missing strict counterparts

- `Real.LessOrEqual.multiply_cancel_left_positive` exists;
  **`Real.LessThan.multiply_cancel_left_positive` does not.**
- `x / 2 < y / 2` from `x < y` does not close, though `minimum_positive`
  gets away with the analogous divided form.

**Fixed**, and it took *three* lemmas rather than two — the second
depended on a third that was also missing:

- `Real.LessThan.multiply_cancel_left_positive` (`order_field.math`)
- `Real.positive_of_multiply_positive` (`order_field.math`) — the strict
  twin of `nonneg_of_multiply_nonneg`, which the above needs

`Real.maximum_LessThan` is now **proved and unparked**, with the parked
proof unchanged apart from its closer. The division friction (`x/2 < y/2`
from `x < y`) was never needed once the cancellation lemma existed.

### I6 — CLOSED 2026-07-25 — two spellings of one fact: `0 ≤ x` vs `Real.IsNonneg(x)`

`Real.multiply_nonneg` does not exist; the lemma is
`Real.IsNonneg.multiply`, stated in the predicate form. So a proof that
reasons in `≤` has to translate at every use:

```math
Real.IsNonneg(a);
Real.IsNonneg(b);
Real.IsNonneg(a * b) by Real.IsNonneg.multiply;
0 ≤ a * b;                       -- translate back
```

Four such adapter blocks in `Plane/norm.math` alone.

**Fixed:** `Real.multiply_nonneg`, `automatic`, stated in `≤` beside
`Real.IsNonneg.multiply` in `order_multiplication.math`. All four adapter
blocks collapsed to one line each.

### I7 — `0 ≤ x * x` is known, `x * x ≤ y * y` from `x ≤ y` is not directly

The prover closes `0 ≤ x*x` unaided (pleasantly — it made
`innerProduct_self_nonneg` a one-liner). But square monotonicity needs
`Real.LessOrEqual.multiply_monotone_nonneg` with four arguments, and it
does not surface from a goal-shape search for the square case.

### I8 — lemma search ranks against you on inequality goals

`kernel search --goal "(a b : Real) → 0 ≤ a → 0 ≤ b → a + b = 0 → a = 0"`
returns `Real.eq_of_absolute_value_less_than_all_positive` at the top.
Ranking is by *fewest remaining hypotheses*, so generic conclusions
(`x = y`, `x ≤ y`) dominate and the hypothesis shape is ignored. For
inequality goals the search is close to useless; I fell back to `grep`
every time.

### The pattern underneath I1–I8

The order API is split three ways at once — `≤` vs `<`, `0 ≤ x` vs
`IsNonneg x`, left- vs right-addition. A single obvious step needs the
right one of eight variants named. Each variant is fine on its own; the
product is what bites. Two combinations are simply missing (I5), and one
whole quadrant is unreachable (I1).

---

## II. Elaborator

### E1 — CLOSED 2026-07-25: Or-injection missed all but the first disjunct

Fixed in `coercion.cpp`, locked by `library/Test/or_injection_test.math`.
Recorded because the *diagnosis* was wrong twice before it was right.

`A ∨ B ∨ C` is `Or(A, Or(B, C))`, and `disjuncts()` collected top-level
application arguments under a `size == 2` guard, so a term proving `B` or
`C` matched neither. Separately, `expectedIsOr` read the **folded** head,
so a definition unfolding to `Or` skipped the block entirely. Minimal
repro needed neither a `by cases` arm nor a definition:

```math
theorem pos1 (a b c : ℕ) (p : a ≤ b) : a ≤ b ∨ b ≤ c ∨ c ≤ a := p   -- passed
theorem pos2 (a b c : ℕ) (p : b ≤ c) : a ≤ b ∨ b ≤ c ∨ c ≤ a := p   -- failed
```

**Lesson for future diagnosis:** the printer folds a spelled-out
disjunction back to the definition name, so "the goal prints as
`Foo a b c`" is *not* evidence that the goal is unfolded-shaped. That
false signal is what made my second wrong hypothesis look confirmed.

### E2 — `ring` treats a projection of a compound as an opaque atom

**Symptom.** `Plane.Vector.first(u + v) = Plane.Vector.first(v + u)` is
declined by `ring`, which reports that a non-variable application was
treated as an opaque atom.

The diagnostic is **excellent** — it says exactly this and names both
fixes. But the consequence propagates: any identity about
`innerProduct(u + v, u + v)` has to be stated in a file where the
coordinates can be expanded first, not at the use site. See
`Plane.Vector.innerProduct_add_self`, which exists only for this reason.

**Workaround.** Expand into coordinates first. It turns out to read
*better* — "expand, commute, reassemble" is what a mathematician writes —
so this one may be fine as it is.

### E3 — a calc step cannot rewrite the same lemma at two positions

**Symptom.** One step citing `norm_squared` where both `u` and `v` need
rewriting fails; diff inference wants one occurrence per step.

**Workaround.** Split into two steps. Cheap, but the failure message
points at the step rather than at the multiplicity, so it costs a
round-trip to work out.

### E4 — a bare relation statement as a whole theorem body is a *proposition*

```math
theorem f : 0 ≤ e := 0 ≤ e'
```

reports "this proof has type `Set Plane.Vector`". A relation **chain** in
the same position works, so the one-step and two-step cases differ. Fix
is the block form `:= { 0 ≤ e'; done }`.

### E5 — an ascription inside an argument list needs its own parens

`Real.IsNonneg(2 : ℝ)` is a parse error at the `:`;
`Real.IsNonneg((2 : ℝ))` is not.

---

## III. Library gaps found and filled

Proved on the way; all now in the library.

| Lemma | Where it landed |
| --- | --- |
| `Real.maximum` + bounds + `maximum_LessOrEqual` | `Real/maximum.math` (new file — only `minimum` existed) |
| `Real.absolute_value_LessOrEqual_of_bounds` | `Real/absolute_value_order.math` (only the strict form existed) |
| `Real.zero_of_nonneg_sum_zero` | `Plane/direction.math` — belongs in `Real/` |
| `Real.zero_of_square_zero` | `Plane/direction.math` — belongs in `Real/` |
| `Real.equal_of_square_equal_nonneg` | `Plane/norm.math` — belongs in `Real/` |

The three sitting in `Plane/` are general facts about ℝ and should be
relocated; they are there only because that is where they were needed.

**Relocated 2026-07-25** — the three general facts about ℝ that had been
sitting in `Plane/` now live where they belong:
`zero_of_nonneg_sum_zero` → `Real/order.math`, `zero_of_square_zero` →
`Real/division.math`, `equal_of_square_equal_nonneg` →
`Real/square_root.math`.

**Still missing:** the
`componentwise` tactic that would collapse the duplicated coordinate
chains in `Plane/vector.math` — roughly two thirds of that file is the
same proof written once for `first` and once for `second`.

---

# Frictions found building Layer 2 (sequences and extraction)

Added 2026-07-25, same conventions as above.

### I9 — ground numeral comparison on ℝ is decided for `≤` but not `<`

```
theorem T : Real.LessOrEqual(2, 4) := done   -- verifies
theorem T : Real.LessThan(2, 4)    := done   -- "no library theorem
                                             --  with this conclusion
                                             --  shape applies"
```

Same two numerals, same embedding chain
`Rational.to_real(Integer.to_rational(Natural.to_integer n))`. The `≤`
side reaches a decision procedure; the `<` side reaches nothing, and
there is no lemma to cite either — `Rational.to_real.LessThan_preserves`
exists but the elaborator does not find it, and reaching it by hand
means descending three embeddings.

Cost: `Plane.rootTwo < 2` had to be weakened to `Plane.rootTwo ≤ 2`,
and the ε/2 estimate reworded to only need the non-strict form. That
happened to be free here, but it is luck, not design.

### E6 — a `case` pattern cannot have a top-level `∧`

```
done by cases on aIsLeast {
  case P(a) ∧ (∀ (k : ℕ). P(k) → a ≤ k) as aWitnesses: { … }
```
→ `parse error: expected ':' between case pattern and body (got '∧')`

A top-level `∃` in a case pattern parses fine (`Natural/least_number.math`
does it), and `∧` *under* the `∃` parses fine too — it is only `∧` at the
top of the pattern that stops the parser. Parenthesizing works.

Worth fixing at the parser: case patterns should accept a full
proposition. In the meantime the workaround that is actually *better*
style is to phrase the disjunction as a conjunction of two implications
(`(H → A) ∧ (¬H → B)` rather than `(H ∧ A) ∨ (¬H ∧ B)`), which is what
`Natural.IsLeastWitness` now does — consumers apply instead of
case-splitting.

### E7 — a theorem body cannot be a bare `by cases`

```
theorem T … : G :=
  by cases { … }        -- parse error at the first `case`
```
must be written

```
theorem T … : G := {
  done by cases { … }
}
```

`by induction on …` has the same shape restriction. This is a small
thing but it costs a re-read of the error every time, because the
reported position is the first token *inside* the block, not the `by`.

### E8 — a cited `∀`-fact is not applied to hypotheses already in scope

```
choose threshold such that
    ∀ (m : ℕ). threshold ≤ m → abs(…) < tolerance / 2 as close from …;
…
threshold ≤ m;                       -- in context, anonymous
… < tolerance / 2 by close;          -- "its arguments could not be
                                     --  inferred from the step"
```

The index `m` is inferable from the conclusion, but the proof of
`threshold ≤ m` is not, even though it is sitting in the context — so the
citation has to be spelled `close(m, pastThreshold)`, which forces naming
the threshold fact. Without the citation the auto-prover *does* find it,
but at 60k kernel-steps and an expensive-step warning. So the choice is
between a slow proof and a noisy one.

## Architectural: Layer 2 needs a choice principle, or careful avoidance

The only selection axiom in the system is `Logic.the` — definite
description, which demands uniqueness. There is no countable choice.

For *index* selection that is fine, and `Natural/frequently.math` shows
why: "choose n_k > n_{k-1} with P_k(n_k)" becomes "take the LEAST such
n_k", which is canonical, so `Logic.the` applies and subsequence
extraction is choice-free.

For *point* selection it is not fine. Three standard Layer 2 arguments
each begin by building a sequence of points from `∀ n. ∃ x. …`:

- compact ⟹ closed (`p ∈ closure(K)` ⟹ pick `x_n ∈ K` with
  `d(p, x_n) < 1/(n+1)`)
- a continuous function on a compact set attains its minimum (pick
  `x_n` with `f(x_n) → inf`)
- uniform continuity by contradiction (pick `x_n, y_n` close but with
  `|f(x_n) − f(y_n)| ≥ ε`)

None of these has a canonical choice available, so `Logic.the` does not
reach them. Each *can* be replaced by an explicit bisection — halve the
square, keep the half where the obstruction survives, which is a
canonical binary choice — but that is a different proof from the one in
the textbook, and it is the textbook proof we said we wanted to be able
to write.

The two options are (a) add countable choice, or full choice, to
`axioms.math` — Lean carries `Classical.choice` for exactly this reason —
or (b) accept bisection rewrites at each of the three sites. This is a
decision about the system, not about `Plane/`, so it is recorded here
rather than worked around silently.

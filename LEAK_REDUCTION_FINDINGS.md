# Proof-style leak reduction — findings log

Running notes from the campaign to drive `scripts/cic_leak_report` to zero.
Purpose: capture what transforms work, what don't, and **what the
elaborator / error messages / tooling could do better** so the system
improves, not just the corpus.

## Categories (as of baseline reset)

The linter now counts three families (see `scripts/cic_leak_report`):
1. CIC vocabulary: `Quotient.` (107), `Equality.symmetry` (98),
   `congruenceOf` (23), `transport_proposition` (14),
   `False.eliminate_proposition` (8), `Equality.transitivity` (1).
2. Structural: `claim-by-calc` (was 73, now 0).
3. Positional lemma calls (`theorem` applied with ≥3 positional args):
   started 1022.

Baseline after promoting categories: **1346**. Two-arg positional calls
(367) are reported advisory-only.

## What works (mechanical, high-confidence)

### claim-by-calc → `calc … as NAME`  ✅ (73 → 0)
`claim NAME : T by calc <steps>` just restates the calc's endpoints.
Rewrite to `calc <steps> as NAME` (bare `calc <steps>` when anonymous).
- Fully automatable with a comment-aware rewriter (`/tmp/rewrite_cbc.py`):
  scan to the statement's terminating `;` tracking `()[]{}⟨⟩` depth,
  detect `claim IDENT :` for the name, strip `claim … by `, append `as NAME`.
- Gotcha: a first pass missed claims **nested inside `by { … }` blocks**
  because the outer non-cbc statement was consumed whole. Fix: when a
  `claim` is non-cbc, emit only the `claim` keyword and keep scanning
  inside it, so nested cbc claims are still found.
- Net: kernel verification is a strong safety net — a wrong rewrite or a
  dropped-but-referenced `as NAME` fails to verify.

### Positional transitivity → calc  ✅
`LessOrEqual.transitive(a, b, c, p_ab, p_bc)` → `calc a ≤ b ≤ c`.
Works cleanly when each step is discharged by a **named hypothesis in
scope** or a **library lemma found by conclusion shape** (e.g.
`a ≤ max(a,b)` via `left_le_max`). Example: `Natural.le_through_max_left`.

### Nested-premise hoist → argument-free `by Lemma`  ✅ (the key method)
A positional call whose premise argument is itself a nested lemma result
is NOT argument-free as-is, but becomes so after **claiming the nested
result into context first**:
```
-- before (2 positional calls, nested):
claim N_s_bound ≤ m by le_through_max_left(N_s_bound, N_t_bound, m,
    le_through_max_left(maximum(N_s_bound, N_t_bound), maximum(N_s,N_t), m, m_ge));
-- after (0 positional calls):
claim maximum(N_s_bound, N_t_bound) ≤ m by Natural.le_through_max_left;
claim N_s_bound ≤ m                  by Natural.le_through_max_left;
```
The data args (subjects) come from the goal; the remaining premise, now a
context fact, is found by match-and-unify + context discharge.
- Validated on `Real.multiplication` (the six `m,n ≥ witness` bounds:
  12 positional calls → 0).
- **Not automatable by regex** — hoisting needs the nested premise's
  *type* (the sub-lemma's conclusion with unified indices), which only the
  elaborator knows. Done by hand.

## What does NOT work

### Blind argument-drop on nested-premise citations  ❌
Dropping all args from `by Lemma(args)` → `by Lemma` without hoisting
fails when any premise is a derived (non-in-scope) fact.
- Measured: `Real.multiplication` converted **0 of 12** this way.
- The auto-prover's context discharge only searches *in-scope
  hypotheses*; it does not synthesise a missing premise by applying
  another lemma (no backward chaining beyond one library lookup).

### Term-position helper applications  ❌ (largely irreducible)
Big multi-arg helper calls used as a *term* — definition bodies, `witness`
payloads, `obtain … from <call>`, tuple components — have no `by`/claim to
host an argument-free citation. E.g. `obtain ⟨c,eq⟩ from
Natural.subtraction_witness(a,b,aLeqB)`, or a theorem body that *is*
`Helper(24 args)`. Reducing these means inlining/restructuring the helper,
not a citation change. These form a large irreducible-ish tail of the 1022.

## Ideas for system improvement (the real payoff)

1. **Backward-chaining in `by Lemma` (argument-free).** Today the prover
   discharges premises only from in-scope hypotheses. If it could attempt
   one more level — discharge a premise by *another* argument-free library
   lemma — the nested-premise case would need no manual hoisting. Bounded
   depth (1–2) would already kill most of the positional-call tail.
2. **Better failure message for argument-free `by Lemma`.** When it fails,
   say *which premise* it couldn't find and its expected type (so the user
   knows exactly what to `claim` into context). Right now the failure is
   the generic "no in-scope hypothesis / no library lemma" message.
3. **`obtain … from (by Lemma)` / argument-free in term position.** Allow a
   goal-driven citation where a *term* of a known type is expected (the
   expected type is available there), so existential-elimination and
   witness payloads can drop their positional args too.
4. **Auto-hoist suggestion.** The linter or elaborator could suggest the
   exact `claim <premise-type> by <SubLemma>;` lines to insert, computed
   from the call's elaboration — turning the manual hoist into an applied
   fix.

## Per-file progress

- `Real/multiplication`: claim-by-calc (1) cleared; le_through_max block
  hoisted (−12 positional). Remaining: term-position helper calls + a few
  `multiply_by_nonneg` (need cascading nonneg hoists).
- `Natural/maximum`: both `le_through_max_{left,right}` → ≤-calc (−2).
- `Rational/order_arithmetic`: two `LessThan` transitives — `x ≤ z` by
  the transitivity bridge (by-less `claim`), `x = y` by antisymmetric
  found by conclusion shape (−3). Remaining: term-position `IsNonneg`
  with `?`-holes and `LessThan.lift` bodies.
- `Real/order`: two `LessThan` transitives fully de-positionalized
  (−8): see the "dense order theorem" pattern below.

## Pattern: dense order theorem (transitive + weaken + distinct + antisym)

`Real.LessThan.transitive_{left,right}` packed FOUR positional calls into
one nested term. The de-positionalized block:
```
theorem … : x < z := {
  claim yLeqZ : y ≤ z by Real.LessThan.weaken;     -- arg-free: premise y<z in scope
  claim xLeqZ : x ≤ z;                              -- transitivity bridge (by-less)
  claim yNotZ : ¬(y = z) by Real.LessThan.distinct; -- arg-free
  And.introduction(xLeqZ,
      (xEqualsZ : x = z) ↦ {
        calc y ≤ z = x as yLeqX;                    -- bare calc binds yLeqX
        claim xEqualsY : x = y by Real.LessOrEqual.antisymmetric;  -- arg-free
        yNotZ(calc y = x = z) }) }
```
Findings:
- **Argument-free `by Lemma` works even for ¬-goals** (`by …distinct`
  where distinct : … → ¬(y=z)) — the premise `y < z` is in scope.
- **Transitivity bridge fires by-less** for any relation R with
  `R.transitive` in scope and both edges as hypotheses (Real/Rational
  `LessOrEqual`, not just `=`).
- Net: a dense 4-call term becomes a 0-call block that reads as the
  textbook argument. This is the highest-value shape — order/arithmetic
  preambles are full of them.

## Progress + the plateau (positional calls)

Total **1346 → 1234** so far (claim-by-calc 73→0; positional 1022→983;
CIC tokens steady at 251). The cleanly-reducible positional shapes are
now largely harvested:
- nested-max preamble hoist: `Real.multiplication`, `PAdic.multiplication`
  (−12 each).
- dense order theorems: `Real.order`, `Rational.order_arithmetic`.
- scattered transitivity bridges: `Natural.maximum`, `Polynomial.degree`.

**Plateau reached.** The remaining ~983 are dominated by **deep
term-position nests** — `le_through_max` buried inside a calc-step's `by
add_strict_strict(…)` argument (`PAdic/addition`), `?`-hole `IsNonneg`
trees, big helper-application theorem bodies, `obtain … from`. Each needs
a risky multi-line restructure for a small per-site gain. **The
high-leverage move for this tail is the elaborator change (backward-
chaining argument-free `by`, idea #1): it would let the nested premises be
discharged without hand-hoisting, collapsing a large fraction
automatically.** Recommend doing that before grinding the term-position
tail by hand.

## CIC tokens

### False.eliminate_proposition → absurd  ✅ (8 → 0)
`False.eliminate_proposition(GOAL, fp)` → `absurd(fp)`. `absurd` infers
the goal from the surrounding expected type, so the explicit `GOAL`
argument was pure plumbing. Fully mechanical; all 8 user-space sites
converted (the `Logic/excluded_middle` uses are foundational, excluded).

### Still open
- `Equality.symmetry` (98): mostly `rewrite(Equality.symmetry(eq), x)`
  (reverse rewrite) and calc-flips. Needs case-by-case (calc /
  `substituting` / `linear_combination`); some are genuinely a flip.
- `congruenceOf` (23): → one-step `calc … by <eq>` or element interface.
- `transport_proposition` (14): → `substituting` / `rewrite`.
- `Quotient.` (107): biggest; needs `construction` / `by_representatives`
  intro sugar — the deepest rewrite.

LEAK_BUDGET ratcheted 1346 → **1226**.

## Reducible fraction (running estimate)

Of the ~1000 positional calls, the readily-reducible shapes are:
nested-premise hoists, dense order/arith theorems, positional
transitivity, and named-premise citations. A large minority are
**term-position helper applications** (definition bodies, `witness`
payloads, `obtain … from`, `?`-hole IsNonneg trees) that need real
restructuring or an elaborator change (backward-chaining `by`) — these
are the long tail and may not be worth hand-rewriting.

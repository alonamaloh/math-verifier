# PLAN_ORDERED_FIELD — a tactic for linear arithmetic over an ordered field

## Goal

A step that follows from the ordered-field axioms alone should close with
`by ordered_field`, the way a commutative-ring identity closes with
`by ring`:

```math
a - b ≤ (c - a) + (c - b) by ordered_field;
```

Given the in-scope hypotheses and the goal, the tactic searches for a
**nonnegative rational combination** of the hypotheses that yields the
goal, and then emits that combination as a kernel-checkable term. The
search is never trusted: the certificate is assembled from real proof
terms and a `ring`-checked bridge, so a wrong coefficient vector fails
typechecking rather than producing a bad proof.

## Why `ordered_field` and not `linarith` / `combining`

The tactic family is `ring`, `field`, `group`, `monoid`, `module`
(`src/syntax/lexer.cpp:67-70`, `docs/reference.md:368`). Every one names
**the theory whose axioms suffice**, not the procedure that decides it —
`by ring` does not mean "normalise to a polynomial normal form", it means
"this holds in any commutative ring". `ordered_field` is the next member
of that sequence and is literally true of the goals in scope: they follow
from the ordered-field axioms.

Two rejected alternatives, recorded so they are not relitigated:

- `combining` names the *method*, and every existing gerund in `by`
  position (`by substituting`, `by unfolding`, `by dividing`) takes an
  argument naming what to transform. An argument-free gerund would be the
  odd one out twice over.
- `linear_arithmetic` names the *fragment*. Discoverable for anyone
  arriving from Lean or Coq, but it breaks the theory-naming pattern, and
  the fragment is the implementation's business, not the reader's.

The name also documents the boundary: if a goal needs two unknowns
multiplied, it is not an ordered-field-linear fact, and the tactic name
already said so.

## What it decides

**In scope.** Goals `L ≤ R`, `L < R`, `L = R`, and `False`, over a carrier
with the order API (ℝ first, ℚ second), where every hypothesis and the
goal are **linear in the atoms**. An atom is any maximal subterm that is
not a `+`, `-`, unary `-`, or multiplication/division by a rational
numeral. So `abs(a - b)`, `Plane.Vector.supNorm(v)`, `f(x)`, and
`innerProduct(u, v) * innerProduct(u, v)` are all perfectly good atoms —
this is what makes the tactic reach the `Plane/` sites, where the content
is linear over compound terms.

**Out of scope, deliberately.**

- Nonlinear facts. I7 (`x * x ≤ y * y` from `x ≤ y`) stays a cited lemma:
  the two squares are unrelated atoms.
- Integer reasoning that needs rounding (`2 * n ≥ 1 → n ≥ 1` over ℕ/ℤ).
  That is `omega`'s fragment, not an ordered field's. If ℤ support is
  added later it is Farkas-only, and the name stops being honest at
  exactly the point the procedure stops being complete — which is the
  right place for the boundary.
- Case splits on `≠` or disjunctions. One conjunctive system per call.

## The certificate, and the term it becomes

The template already exists: `linear_combination` proves an equality from
a known equation plus a `ring`-checked bridge, assembled through one
library lemma (`Ring.equal_of_linear_combination`,
`library/Algebra/ring_lemmas.math:92`, emitted in
`src/elaborator/ring.cpp:700-757`). The inequality version is the same
shape with the order lemmas doing the assembly.

For a goal `L ≤ R` with hypotheses normalised to `0 ≤ eᵢ` (weak) and
`0 < fⱼ` (strict), Farkas gives: the goal follows linearly iff there are
nonnegative rationals with

```
R - L  =  Σ cᵢ·eᵢ  +  Σ dⱼ·fⱼ  +  s        (cᵢ, dⱼ, s ≥ 0)
```

as a **polynomial identity in the atoms**. The emitted term walks that
equation right to left:

1. Each hypothesis is brought to `0 ≤ e` / `0 < f` form (one bridge lemma
   per input relation shape — see O1).
2. Each is scaled: `0 ≤ c · e` from `Real.multiply_nonneg`
   (`library/Real/order_multiplication.math:161`), with `0 ≤ c` for the
   rational numeral discharged by the existing ground-relation tier.
3. The scaled terms are summed with `Real.IsNonneg.add` /
   `Real.add_nonneg_positive` / `Real.add_positive_positive`
   (`library/Real/order.math:251,579,572`), the strict variants chosen
   when any `dⱼ > 0`.
4. The bridge `R - L = Σ …` is proved by
   `elaborateRingByNormalisation` — reused verbatim, it is a pure ring
   identity with no hypotheses.
5. `0 ≤ R - L` becomes `L ≤ R` through the concluding lemma (O1).

Two properties fall out of doing it this way. The proof is a **direct**
one, not a reductio, so the exported term reads as the mathematician's
"adding the two bounds and rearranging" rather than as a contradiction.
And step 4 means an incorrect coefficient vector is caught by the ring
normaliser, so the LP is a *heuristic* in the soundness argument, not a
trusted oracle. That is the property to preserve under every later
optimisation.

## Regression corpus

Provenance: `FRICTION_PLANE_LAYER0.md`, written while building Layer 0 of
the Jordan–Schönflies foundation. Its section I is the specification.
**Four of its nine entries were absorbed by library lemmas on 2026-07-25
and must not be re-solved by the tactic** — that is what leaves I4 as the
one entry needing a decision procedure, and the corpus below is
correspondingly smaller than section I looks.

| Entry | Status | Bearing on this plan |
| --- | --- | --- |
| I2 | CLOSED — `automatic` tag + `Real.subtract_positive_of_LessThan` | none |
| I3 | CLOSED — `Real.add_preserves_LessOrEqual_both` | none; it retires every *syntactic* sum-of-two-bounds |
| I5 | CLOSED — three strict counterparts | none |
| I6 | CLOSED — `Real.multiply_nonneg` in `≤` spelling | supplies the scaling lemma in step 2 above |
| **I4** | **OPEN** | the target |
| I1 | OPEN, elsewhere | the sign battery cannot parse `e ≤ 0`; see "Interactions" |
| I7 | OPEN, out of scope | nonlinear |
| I8 | OPEN, elsewhere | lemma-search ranking |
| I9 | OPEN, elsewhere | ground numeral `<` on ℝ; see "Interactions" |

I3's closing note is the precise statement of what is left: the lemma
matches only when both sides are syntactically sums, and
`a - b ≤ (c - a) + (c - b)` is not, so the rearrangement is the content.

**The corpus itself** — each site currently carries a hand-routed
nonnegative increment, and each should collapse to one `by ordered_field`:

| Site | Shape |
| --- | --- |
| `library/Real/maximum.math:59-67` (`maximum_LessOrEqual`) | two blocks: `a - b ≤ (a-b) + 2(c-a) = (c-a)+(c-b)` and its mirror. The canonical I4 |
| `library/Real/maximum.math:93-101` (`maximum_LessThan`) | the strict twin of the same two blocks |
| `library/Plane/bilinear.math:201` (`cauchy_schwarz`) | `X ≤ X + Y` from `0 ≤ Y`, atoms = products |
| `library/Plane/norm.math:60` and its second-coordinate twin | same shape, four sites across the two theorems |
| `library/Real/derivative.math:303,305` | `X ≤ abs(X) + 1` style bounds |
| `library/Plane/sequence.math:146-155` | `< ε/2 + ε/2 = ε` — currently three cited steps; rational constants make it one |

**Measured 2026-07-25, after O1.** Each shape was probed in isolation.
The corpus is smaller and sharper than the table above:

- **`Real/maximum.math` is the real target, and it is worse than I4
  claimed.** The bare goal declines (expected). Stating the certificate's
  nonnegative term first (`0 ≤ 2 * (c - a);`) does not help. Stating the
  difference in the goal's own spelling
  (`0 ≤ ((c - a) + (c - b)) - (a - b)`) does not help either — that claim
  *exhausts the auto-prover budget*. So the gap is two-layered: the sign
  battery does not ring-normalise its subject, and there is no bridge
  from `0 ≤ D` to `L ≤ R` when `D` merely ring-equals `R - L`. Steps 4
  and 5 of the emission cover both, which is a good sign for the design.
- **The two `Plane/` sites leave the corpus.** `x ≤ x + y` from `0 ≤ y`
  closes bare — the `by Real.less_or_equal_add_of_nonneg` at
  `Plane/bilinear.math:201` and `Plane/norm.math:60` is a redundant hint,
  not an I4 workaround. Whether to strip it is a per-site readability
  call under the redundant-`by` rule, and it is not this plan's business.
- **The `Real/derivative.math` sites stay, but their `by` is
  load-bearing**: `abs(x) ≤ abs(x) + 1` declines bare, because the
  numeral's `0 ≤ 1` is not discharged in that position. Linear over atoms
  once it is, so the tactic should reach them — a useful second test
  case, since it exercises the constant row.

Acceptance for the corpus is not "the tactic closes them" but "the file
reads better afterwards" — judged by reading the proofs, per
`docs/style.md`, not by counting hints. `Real/maximum.math` is the file to
judge on: if `maximum_LessOrEqual` does not become obviously more
readable, the tactic is not earning its keep.

Lock the corpus as `library/Test/ordered_field_test.math` before touching
the library files, so the rewrite is an acceptance test rather than the
specification.

## Stages

### O1 — DONE 2026-07-25 — the concluding lemmas (library only)

Probed before writing anything, and the guess was wrong in both
directions. **Both weak bridges already close unaided** at ℝ and at ℚ —
`0 ≤ b - a` from `a ≤ b` (as `Real/order.math:511` already claimed) and,
unrecorded until now, the converse `a ≤ b` from `0 ≤ b - a`. What was
missing is the *strict* side, and ℚ was missing more of it than ℝ:

| Bridge | ℝ | ℚ |
| --- | --- | --- |
| `a ≤ b → 0 ≤ b - a` | automatic already | automatic already |
| `0 ≤ b - a → a ≤ b` | automatic already | automatic already |
| `a < b → 0 < b - a` | `subtract_positive_of_LessThan` (I2's fix) | **added** |
| `0 < b - a → a < b` | **added** | **added** |

Landed: `Real.LessThan_of_positive_subtract`
(`library/Real/order.math`), `Rational.subtract_positive_of_LessThan` and
`Rational.LessThan_of_positive_subtract`
(`library/Rational/order_arithmetic.math`). All three in the natural
spelling (`a = a + 0 < a + (b - a) = b`), first try, no hints.

Deliberately **not** `automatic`: the tactic cites them by name, so
marking them would widen the candidate pool for zero benefit here. That
is a separate decision requiring its own canary measurement.

Open question 1 is answered by this: ℚ is in from the start, and its
lemmas cost nothing extra.

### O2–O6 — DONE 2026-07-25

Landed as `src/elaborator/ordered_field.cpp` plus the surface plumbing
(`KeywordOrderedField`, `SurfaceOrderedField`, one dispatch case). What
the stages below specified, and what actually happened, in one place:

- **O2.** The linear model turned out to need no atom extraction of its
  own. `normaliseToRingPolynomial` already returns
  `map<monomial signature, coefficient>`; taking the SIGNATURES as the
  linear-model variables makes "linear in the atoms" true by
  construction, with the empty signature as the constant term. Products
  are ordinary variables for free, and there is exactly one notion of
  "same subterm" in the elaborator — the constraint the stage was
  written to enforce.
- **O3.** Fourier–Motzkin with multiplier tracking, ~120 lines, caps at
  512 rows / 32 eliminations, both reported by name when they trip.
- **O4.** Emission as designed: hypothesis bridges → repeated addition
  folded with the four `add_*` lemmas → `ring`-checked bridge → one
  concluding lemma. Repeated addition rather than scalar multiplication
  is what keeps `0 ≤ c` proofs for coefficients out of the emitter
  entirely; the price is a 64-copy cap.
- **O5.** Four distinguished failures, two locked in `ErrorTest/`
  (`ordered_field_not_linear`, `ordered_field_wrong_goal_shape`).
- **O6.** `Real/maximum.math` rewritten — the two hand-routed
  nonnegative-increment blocks in `maximum_LessOrEqual` and
  `maximum_LessThan` became one `by ordered_field` line each, and the
  `-2c` scaffolding is gone. That is the whole corpus rewrite: the
  measurement had already removed the `Plane/` sites, and the
  `Real/derivative.math` citations read better than `ordered_field`
  would. Docs: `docs/reference.md`, `docs/conventions/algebra-tactics.md`.

**Three things worth carrying forward.**

1. `weakHeadNormalForm` on the goal was exactly the wrong first move:
   `Real.LessOrEqual` is a `definition`, so WHNF unfolds the head the
   parser is trying to read and the relation disappears into its
   representative-level body. Read the FOLDED form first, WHNF only as
   a retry. This is QUIRK E1's lesson from the other direction — there
   the printer folded and made an unfolded goal look folded.
2. Emitting the certificate as repeated addition instead of scaled
   terms removed a whole class of work (numeral-nonnegativity proofs)
   at the cost of one cap. Worth remembering as a shape.
3. The witness valuation is what makes the decline useful, and it is
   nearly free: FM already has the elimination history, so
   back-substituting in reverse order gives a satisfying assignment.

### O7 — ℚ: NOT BUILT, by measurement (2026-07-26)

Open question 1 asked whether ℚ ships in the first cut. The O1 probe
said yes on the strength of the bridge lemmas; the emission lemmas are
the thicker requirement, and ℚ turns out to need **seven**:
`add_nonneg`, `nonneg_subtract_of_LessOrEqual`,
`nonneg_subtract_of_equal`, `nonneg_of_multiply_nonneg`,
`positive_of_multiply_positive`, both `multiply_cancel_left_positive`
strengths, and then the two combination lemmas on top.

Before writing them, the demand was measured. **There is none.** No site
in `Rational/` uses a nonnegative-increment workaround, and the ℚ order
by-hints in the whole library are transitivity (8), antisymmetry (3),
weakening (2) and multiplicative cancellation (3) — single-lemma steps
the tactic would not improve. Not one is a nonnegative-combination
shape.

So ℚ stays unbuilt, and this is a *measurement*, not a backlog item.
The carrier name table is the extension point: when a ℚ site appears
that wants it, the work is those seven lemmas plus one table entry, no
new machinery. Do not build it speculatively.

### O8 — DONE 2026-07-26 — equality hypotheses as rows

An `a = b` hypothesis now contributes BOTH `b − a ≥ 0` and `a − b ≥ 0`,
so a proof may mix equations with inequalities without converting them
by hand. One new lemma (`Real.nonneg_subtract_of_equal`) serves both
directions: the second row is built on `buildEqualitySymmetry` of the
same proof.

This also closes an honesty gap left by O5. Equality hypotheses were
previously dropped *silently* — not even named in the "not read as
rows" list, which the O5 spec required — so a proof could fail with a
message that never mentioned the fact it most needed.

### O9 — DONE 2026-07-26 — `False` goals, so the tactic reaches reductio

`done by ordered_field` now closes a `False` goal from contradictory
order hypotheses, which is the idiom this library actually writes
(`suppose … for contradiction { …; done }`).

It needed almost no new machinery, because the contradiction can be
routed through the *existing* concluding lemma: retarget the goal at
`0 < 0`, let the certificate and the `ring`-checked bridge run
unchanged (the combination sums to zero by construction), then hit the
result with `LessThan.irreflexive`. The only structural differences are
that no negated-goal row is added and there is no multiplier to divide
through by.

The carrier for a `False` goal comes from the first order hypothesis in
scope — there is no goal to read it off. When no hypothesis supplies
one, the decline says exactly that. When the hypotheses are merely
consistent, the message says *that* and shows a satisfying valuation,
rather than reporting a failure to prove some goal the author never
wrote.

### O2 — atom extraction and the linear model (as specified)

Walk goal and hypotheses into `Σ qₖ · atomₖ + q₀` over ℚ, with atom
identity by the same term-equality the ring normaliser uses (reuse
`src/elaborator/ring.cpp`'s atom handling rather than writing a second
notion of "same subterm" — Q5 and Q14 are both records of the ring side
learning to see through spellings, and a divergent atom notion would
re-earn those bugs). Numerals go through the coercion registry, which is
exactly the Q14 lesson: `linear_combination` treated a bare numeral
coefficient as an atom and reported a true identity as false.

Carrier: there is no `IsOrderedField` bundle in the library today (grep
finds none), so the carrier enters as a name table the way `RingScheme`
does — `Real.*` and `Rational.*` prefixes over one code path. Say so in
the code: the *name* is the theory, the *implementation* is a per-carrier
table until a bundle exists.

Acceptance: a debug dump of the parsed system for each corpus site,
eyeballed once.

### O3 — the search

Fourier–Motzkin with certificate tracking over the negated goal. The
systems here are tiny (the corpus maxes out around six rows and four
atoms), FM is thirty lines, and it produces the multipliers directly. The
negated goal appears in the refutation with some coefficient λ₀ > 0;
dividing through by λ₀ and dropping that row gives the **direct**
coefficients the O4 assembly wants.

Keep a row cap and a coefficient-bound cap, and when either trips, say so
in the failure message rather than silently declining (per
`no_silent_caps` thinking: a bounded search that reads as "no certificate
exists" is a lie). Simplex is the upgrade path if a real site ever blows
the cap; do not write it first.

### O4 — emission

As "The certificate, and the term it becomes" above. Mirror
`Elaborator::buildLinearCombinationProof` /
`assembleLinearCombination` (`src/elaborator/ring.cpp:660-770`),
including `closeOverLocalBinders`. New file
`src/elaborator/ordered_field.cpp`; keep it out of `ring.cpp`, which is
already 8565 lines.

Surface plumbing: `KeywordOrderedField` in `src/syntax/lexer.cpp`,
`SurfaceOrderedField` in `src/syntax/surface.hpp` beside `SurfaceField`,
the parse site beside `src/syntax/parser.cpp:3793`. Argument-free, like
`ring` — the hypotheses come from the context, and if a fact needs
naming to be found, that is a bug in context collection, not a reason for
an argument list.

### O5 — the failure message

`prover.cpp:3747-3758` is the bar, and it is high: it enumerates every
strategy that ran. The `ordered_field` failure should say what certificate
it looked for and why there is none. Farkas duality makes this unusually
good — when the system is infeasible, the dual gives a **witness
valuation**: rational values for the atoms satisfying every hypothesis
while violating the goal. Report it.

```
`ordered_field`: no nonnegative combination of the hypotheses yields
`a - b ≤ (c - a) + (c - b)`. Treating `a`, `b`, `c` as independent, the
hypotheses `a ≤ c` hold at a = 0, b = 0, c = 0 while the goal fails —
the goal is not a linear consequence. (`b ≤ c` was not used: it is not
in scope here.)
```

Three cases to distinguish, because they call for different fixes:

- **not a linear consequence** — emit the witness valuation as above;
- **dropped rows** — a hypothesis was skipped as nonlinear or at the
  wrong carrier; name it and say which, since "I never saw your
  hypothesis" and "your hypothesis does not suffice" are different bugs;
- **cap tripped** — say which cap and what the system size was.

Lock all three in `ErrorTest/`, matching the existing convention.

### O6 — corpus rewrite and docs

Rewrite the corpus sites, read the results, and keep only the ones that
improve. Then `docs/reference.md:368` (the tactic list),
`docs/conventions/algebra-tactics.md` (the depth: fragment, atom notion,
carrier table, what to do when it declines), and a line in
`FRICTION_PLANE_LAYER0.md` retiring I4.

## Constraints

**Do not cold-build `library/`.** The fifteen-theorem files dominate the
wall clock (`Algebra/residue_arithmetic_generated` alone is ~132 s).
Iterate with `make -j 16 plane`, which is exactly this: `PLANE_CONE_MATHV`
in `Makefile:188-192` uses `scripts/module_cone.py` to request the cone's
proofs, so the narrow target is correct as well as fast.

**The final gate is `make -j 16 tests`, and it is run ONCE, at the end of
the elaborator work — not per stage.** Every `.mathv` depends on the
`kernel` binary, so an elaborator change invalidates the whole cache. But
the full run is dominated by the Python-generated fifteen-theorem files
(one is ~15 minutes), and those are the *least* informative files in the
library for this purpose: they are long, repetitive and structurally
simple, so they almost never catch an elaborator mistake that
`make plane` and `Test/` did not. Pay for it before declaring O4 done;
do not pay for it after each edit. Library-only stages (O1) need only
`make -j 16 plane`.

**Cap memory** on every kernel/make invocation (`ulimit -v`) — a runaway
allocation OOM-kills the session.

**Do not trim the auto-prover's candidate pool without measuring.** The
canaries and their current numbers, from
`FRICTION_PLANE_LAYER0.md:28-31`: `Real/supremum` 3.37 s,
`Algebra/ring_lemmas` 1.37 s, `Algebra/residue_arithmetic_generated`
132.5 s. Use `scripts/time_verify.sh`.

This plan should not touch the pool at all, and that is a design
property worth stating: **`ordered_field` is explicitly invoked, so it
costs nothing on any goal that does not name it.** Adding it as a prover
tier is a separate decision requiring its own measurement against those
canaries — do not fold it in as a "while we are here".

## Interactions with open work

- **I1** (`e ≤ 0` does not parse as a sign judgment,
  `parseSignJudgment` in `src/elaborator/lemma_index.cpp`) is
  independent, and the tactic is not a substitute for fixing it: a
  one-hop sign fact should not need a decision procedure. But O2's
  normalisation has to handle `e ≤ 0` regardless, so the form bridge
  `e ≤ 0 ⟼ 0 ≤ -e` that I1 needs gets written here anyway. Coordinate,
  do not duplicate.
- **I9** (ground `2 < 4` at ℝ decides for `≤` but not `<`) would be
  incidentally absorbed, since ground numerals are just the constant
  row. Do **not** treat that as the fix — the ground-relation tier should
  decide it directly, and `Plane.rootTwo ≤ 2` should not have to invoke a
  tactic.
- **I8 / QUIRK Q15** (lemma search ranks by fewest remaining hypotheses,
  so inequality goals return nonsense) is the friction that made this
  work hard to *find* lemmas for. Unaffected by the tactic, still worth
  fixing; Q16 records the shape-fingerprint measurement that applies
  there without reservation.
- **QUIRK Q14** is the direct precedent for O2's numeral handling, and
  its failure mode — "the identity is FALSE as a polynomial" on a true
  identity — is the one to avoid re-creating in the O5 message.

## Open questions

1. **ℚ in the first cut, or ℝ only?** ℚ costs one name table entry, and
   `Rational/order_arithmetic.math` already has the parallel lemmas. Lean
   toward both, but only if O1's ℚ twins are free.
2. **Equality goals.** `L = R` from `L ≤ R` and `R ≤ L` is antisymmetry
   plus two searches. Cheap, but is it wanted, or does it overlap
   `linear_combination` confusingly? Defer until a corpus site asks.
3. **Should the certificate be printable?** A `--explain` mode emitting
   the combination as a relation chain would turn the tactic into a proof
   *generator* the reader can paste and edit. Attractive for the style
   goal — a tactic that shows its work is more in keeping with this
   library than one that closes the goal opaquely — but out of scope
   until the tactic exists.

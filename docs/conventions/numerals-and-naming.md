# Naming, line width, numerals, and casts

No abbreviations; the 140-column rule; arithmetic Natural notation; binding a repeated cast with `let`.

*(Part of the project conventions; see `CLAUDE.md` for the index.)*

## Naming

- **No abbreviations in identifiers.** `representative`, not `rep` (in
  declaration names). Local-variable `rep` is fine.
- Long fully-qualified names (`Rational.padic_absolute_value`) are
  searchable. Don't shorten.
- `IsX` (predicate) and `X_is_Y` (witness) conventions match the
  algebraic-instance pattern in `library/Rational/instances.math`.

## Line width

Don't wrap until column 140. Wrapped lines hurt readability — the
extra vertical sprawl from a wrapped `Rational.absolute_value(...)`
or `Rational.halve(epsilon)` chain is its own readability cost, and
modern screens display 140-column lines without effort. Wrap when
the line genuinely needs it (a multi-argument function call where
each arg is itself complex), not because of a column limit.

## Natural successors: use arithmetic outside `Natural/`

Modules outside `library/Natural/` treat `Natural` as a sealed arithmetic
type. Write `n + 1` or `1 + n`; do not write `successor(n)`, pattern-match on
`successor`, cite successor-facing boundary lemmas, or unfold
`Natural.add`/`Natural.multiply`. Use ordinary arithmetic theorems, `ring`,
and arithmetic case or induction arms such as
`case n = 1 + k for some k:`.

Choose between `n + 1` and `1 + n` for mathematical readability. They are
equal by the public arithmetic laws, but they need not be definitionally
equal because `Natural.add` is opaque. A consumer proof must not depend on
which argument the hidden implementation recurses over.

Constructor spellings are confined to the implementation of the Natural
boundary itself. Code there may need `Natural.Raw.successor`, the temporary
`successor` wrapper, or explicit unfolding to prove the arithmetic-facing
interface. That is representation-level machinery, not a general proof
style or an exception available to downstream modules.

## Numeral coercion: argument positions, and why `0`/`1` differ from `2`

A bare numeral parses as a `Natural` (the literal default never changes). What
varies is whether the *position* lifts it up the coercion tower:

- **Function-argument and operator-operand positions DO coerce.** When the
  expected type is a registered coercion target, a bare numeral (or a bare
  `Natural` variable) is lifted automatically. So `Real.power(2, m)` and
  `Real.power(m, m)` need no ascription — the base `2` / `m` is `Natural`,
  lifted to `Real` exactly as `(2 : Real)` / `(m : Real)` would be. **Prefer
  the bare form.** Likewise prefer real division `(x + y) / 2` over
  `(x + y) * (Rational.one_half : Real)` — it reads as the mathematics, and
  `field` proves identities over it directly (see `algebra-tactics.md`).
- **All-numeral chain heads do not.** A chain beginning `0 = 0 + 0 ≤ …`
  can't pin a carrier from `0 = 0 + 0`, so it defaults to `Natural`; seed it
  with one cast—`(0 : Real) = 0 + 0 ≤ …`. A first relation with a non-numeral
  operand (`0 ≤ abs(x)`) seeds fine—only the all-numeral case needs the
  ascription. (The C++ `std::string("a") + "b"` situation: you seed the first
  operation, and a typed operand appearing *later* in the chain can't reach
  back to fix it.)

**`0` and `1` are special; `2` and `4` are not.** The prover canonicalises bare
`0`/`1` against `Real.zero`/`Real.one` (and the other carriers' constants), so
they are interchangeable EVERYWHERE — relations, `ring`, citations. But
`(2 : Real)` is the coercion tower `tower(2)`, which is **not** definitionally
equal to `Real.one + Real.one` (real addition) — only ring-equal. Consequences:

- `2` works in an `=` goal/step (the by-less prover runs `ring`, which bridges
  `2 ↔ 1 + 1`), but **not** in non-`=` *matching* — a `≤` step or a lemma
  citation against a `1 + 1`-producing lemma compares structurally and fails.
- To use `2` where a proof otherwise carries `1 + 1`: make the WHOLE proof use
  `2` (so nothing has to match `1 + 1` against `2`), with ONE bridge at the spot
  a lemma forces the `1 + 1` form—`… ≤ Real.one + Real.one = 2`. (AGM's
  `means_inequality_double` does exactly this for its doubling factor.)
- An ALL-numeral product keeps at least one ascription: `(2 : Real) * (2 : Real)`,
  never bare `2 * 2` (which elaborates as the `Natural` literal `4`).

## Bind a repeated cast with `let`, don't re-ascribe it

A coercion is shown at one syntactic site by design (see the
coercion-registry principle). In a relation chain that lives entirely in one
carrier, that principle backfires: the same ascription
`((1 + d) : Integer)` gets re-typed at every term — eight times
in a Rational cross-multiplication is common. The fix is NOT to hide
the cast (a carrier-scoped region would move it off-screen and weaken
"coercions visible at one site"); it is to **name it once** with a
`let` and reuse the name:

```math
-- Noisy: the cast is re-ascribed on every line.
((1 + d_x) : Integer) * n_y + ((1 + d_y) : Integer) * n_x
   = …((1 + d_x) : Integer)…((1 + d_y) : Integer)…

-- Clean: bind each positive denominator once, reuse the name.
let dx : Integer := ((1 + d_x) : Integer);
let dy : Integer := ((1 + d_y) : Integer);
dx * n_y + dy * n_x
   = …dx…dy…
```

The kernel ζ-unfolds the `let` whenever def-eq is needed (see the
`let` and ζ section), so the auto-prover and `rewrite` still see
through `dx` to `((1 + d_x) : Integer)`. The cast appears
exactly once — at the binding — which is *more* faithful to "one
visible site" than the inline form, not less. Reach for this
whenever a single coercion appears 3+ times in one proof.

**Same move for any long repeated subexpression, not just casts.** A proof
that spells `Real.partialSum((j : Natural) ↦ s(m + j), m)` (44 chars) at thirty
sites is forced to chop every expression across four lines; binding
`let secondSum : Real := …` collapses each to one readable line. AGM's
`means_inequality_double` (`firstSum`/`secondSum`/`firstProduct`/`secondProduct`)
and its base case (`let mean := (x + y) / 2; let halfDiff := (x - y) / 2`) read
as the mathematics — `(firstSum - secondSum) * (firstSum - secondSum)`,
`mean < g → g * g < g * g` — and the file shrank ~25%.

**Caveat — `let` is ζ-transparent *except to `linear_combination`*.** The
kernel unfolds the `let` for def-eq, the matcher unfolds it (so `by <lemma>`,
`IsNonneg(…)` decomposition, relation steps, and `by substituting` all see
through the name to its value), `ring` and `field` ζ-unfold the goal (and
`field` reads its nonzero hypotheses at the same let-free spelling), and the
sign battery retries a declined sign/positivity goal at the ζ-unfolded
spelling — so `mean * mean - x*y = halfDiff * halfDiff by field` with
`let mean := (x + y) / 2` and bare `tolerance > 0` facts over a `let` both
work as written (pinned by `Test/zeta_let_test.math`). The one remaining atom
treatment is `linear_combination`, whose cited hypothesis equations feed its
coefficient bookkeeping at their stated spellings — keep explicit forms
there. The dual caveat is reduction: a `cases`/`if` refinement won't compute
*through* a `let`, so when a goal `P(augmentedRow(k))` must ι-reduce as `k`
is refined, keep the full application `P(augmentedScaledRow(s, m, k))` in the
fact's *type* (only the `let` name in the surrounding prose).

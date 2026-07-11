# Naming, line width, numerals, and casts

No abbreviations; the 140-column rule; `1 + n` vs `successor(n)`; binding a repeated cast with `let`.

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

## `successor(n)`, `1 + n`, and `n + 1`

`successor(n)` is the Peano constructor; `1 + n` and `n + 1` are the same
value written with the carrier's `+`. **There is no house preference among
them** — write whichever reads most naturally (mathematicians usually write
`n + 1`). The points below are about *mechanics*, not style.

**They are only propositionally equal, not defeq.** `Natural.add` is
`opaque`, so the kernel does NOT silently reduce `1 + n` to `successor(n)`.
The bridge is the lemma `Natural.one_add : 1 + n = successor(n)` (and
`ring` / `add_commutative` to move between `1 + n` and `n + 1`). Under an
explicit `unfold Natural.add`, `1 + n` *does* reduce to `successor(n)` —
but `n + 1` does not, because `add` recurses on its FIRST argument.

This left/right asymmetry is intrinsic to structural recursion and is the
thing to actually watch: `0 + a ≡ a` is one ι-step but `a + 0 = a` needs
induction; `successor(k) + b` and `1 + k` reduce, `k + 1` is stuck. **Keep
any reasoning that leans on it (anything needing `unfold Natural.add` /
`unfold Natural.multiply`) inside the `Natural/` floor.** Above that floor,
go through lemmas / `ring` so the asymmetry is invisible — e.g. both
`t + 0 = t` and `0 + t = t` are just `:= ring`. Opacity + `ring` are
exactly what make the prover see no difference between the two forms; a
non-foundational proof that has to `unfold` add to compute is a smell.

**Exception: patterns.** Pattern positions (`| successor(k) => ...`)
require the bare constructor — the parser accepts neither `1 + k` nor
`k + 1` there. Companion memory: [[prefer_numeric_literals]] covers the
related `0`/`1`/`2` over `zero`/`successor(zero)`/`two` rule (that one *is*
still a preference).

**Where `successor(n)` reads best.** Two cases, learned the hard way:

- **Structural reduction sites in foundational files.** `Natural.add` and
  `Natural.multiply` reduce on the `successor` constructor of the first
  argument (`successor(k) + b ≡ successor(k + b)`,
  `d * successor(q) ≡ d + d * q`). Rewrite/calc matchers see the
  `successor(...)` form structurally but not always the reduced form
  behind `1 + k`. In `library/Natural/arithmetic.math` (`add_commutative`'s
  successor case) the calc starts at the reduced `successor(predecessor + b)`
  precisely so a downstream rewrite finds `predecessor + b` as a subterm;
  `(1 + predecessor) + b` would hide it. This is fine — it lives on the
  `Natural/` floor where the constructor belongs.

- **Structural-atom slots.** When `successor(n)` is a "positive successor"
  atom (e.g. a positive denominator in Rational cross-multiplication),
  `(successor(d) : Integer)` reads as one concept — "the *d*th positive
  denominator." `((1 + d) : Integer)` adds a paren pair and makes the
  reader parse a sum first (saw this on `Rational/basics.math`).

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
- **Calc heads with an all-numeral first relation do NOT.** `calc 0 = 0 + 0 ≤ …`
  can't pin a carrier from `0 = 0 + 0`, so it defaults to `Natural`; seed it
  with one cast — `calc (0 : Real)`. A first relation with a non-numeral
  operand (`calc 0 ≤ abs(x)`) seeds fine — only the all-numeral case needs the
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
  a lemma forces the `1 + 1` form — `calc … ≤ Real.one + Real.one = 2`. (AGM's
  `means_inequality_double` does exactly this for its doubling factor.)
- An ALL-numeral product keeps at least one ascription: `(2 : Real) * (2 : Real)`,
  never bare `2 * 2` (which elaborates as the `Natural` literal `4`).

## Bind a repeated cast with `let`, don't re-ascribe it

A coercion is shown at one syntactic site by design (see the
coercion-registry principle). In a calc that lives entirely in one
carrier, that principle backfires: the same ascription
`(successor(d) : Integer)` gets re-typed at every term — eight times
in a Rational cross-multiplication is common. The fix is NOT to hide
the cast (a carrier-scoped region would move it off-screen and weaken
"coercions visible at one site"); it is to **name it once** with a
`let` and reuse the name:

```math
-- Noisy: the cast is re-ascribed on every line.
calc (successor(d_x) : Integer) * n_y + (successor(d_y) : Integer) * n_x
   = …(successor(d_x) : Integer)…(successor(d_y) : Integer)…

-- Clean: bind each positive denominator once, reuse the name.
let dx : Integer := (successor(d_x) : Integer);
let dy : Integer := (successor(d_y) : Integer);
calc dx * n_y + dy * n_x
   = …dx…dy…
```

The kernel ζ-unfolds the `let` whenever def-eq is needed (see the
`let` and ζ section), so the auto-prover and `rewrite` still see
through `dx` to `(successor(d_x) : Integer)`. The cast appears
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
`let mean := (x + y) / 2` and bare `tolerance > 0` claims over a `let` both
work as written (pinned by `Test/zeta_let_test.math`). The one remaining atom
treatment is `linear_combination`, whose cited hypothesis equations feed its
coefficient bookkeeping at their stated spellings — keep explicit forms
there. The dual caveat is reduction: a `cases`/`if` refinement won't compute
*through* a `let`, so when a goal `P(augmentedRow(k))` must ι-reduce as `k`
is refined, keep the full application `P(augmentedScaledRow(s, m, k))` in the
claim's *type* (only the `let` name in the surrounding prose).

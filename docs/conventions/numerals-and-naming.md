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

## Prefer `1 + n` over `successor(n)` in expressions

`successor(n)` is the Peano constructor; `1 + n` is the same value in
the carrier's `+`. They are definitionally equal (kernel reduces
`1 + n = successor(0) + n = successor(0 + n) = successor(n)`), so they
typecheck interchangeably wherever an EXPRESSION is expected. The `1 + n`
form reads as math; `successor(...)` reads as bureaucracy.

Same applies to deeper successors: prefer `2 + n` over
`successor(successor(n))`, and `n + 1` is fine when it parses more
naturally (commutativity is also definitional via `add_commutative` but
even better, the kernel reduces either form to the constructor chain).

A goal stated as `1 ≤ successor(k)` reads better as `1 ≤ 1 + k` or just
`1 ≤ k + 1`. The corresponding helper `Natural.successor_positive`
proves it either way.

**Exception: patterns.** Pattern positions (`| successor(k) => ...`)
require the bare constructor — the parser doesn't accept `1 + k` there.
Companion memory: [[prefer_numeric_literals]] covers the related
`0`/`1`/`2` over `zero`/`successor(zero)`/`two` rule.

**When `successor(n)` wins anyway.** Two situations where the
substitution makes the proof *harder* to read, learned the hard way:

- **Structural reduction sites.** `Natural.add` and `Natural.multiply`
  are defined by recursion on the `successor` constructor of the first
  argument, so `successor(k) + b ≡ successor(k + b)` and
  `d * successor(q) ≡ d + d * q` are definitional reductions the
  kernel will perform. Rewrite-matchers and calc-step matchers see the
  `successor(...)` form structurally, but they don't always see the
  reduced form behind `1 + k`. Concretely: in
  `library/Natural/arithmetic.math:60` (`add_commutative`'s successor
  case), the calc starts at the REDUCED form `successor(predecessor + b)`
  precisely so a downstream rewrite can find `predecessor + b` as a
  subterm. Writing `(1 + predecessor) + b` instead breaks that.
  Foundational Natural arithmetic files (`basics`, `peano`,
  `arithmetic`, plus `divide`, `divides_subtract`, `divisibility`,
  `power`) keep `successor(...)` for this reason.

- **Structural-atom slots.** When `successor(n)` appears uniformly as a
  "positive successor" atom (e.g. positive denominator in Rational
  cross-multiplication), `(succ(d) : Integer)` reads as one concept —
  "the *d*th positive denominator." `((1 + d) : Integer)` adds an
  extra paren pair (the inner one is forced by `+`'s precedence under
  type ascription) and makes the reader parse a sum before recognising
  the slot. Saw this on `Rational/basics.math:transitive_natural`
  where the substitution made the proof noticeably noisier.

Rule of thumb: prefer `1 + n` when the `+1` is doing arithmetic work
the reader cares about (`1 ≤ 1 + k`, `1 + k = succ(k)` reductions).
Keep `successor(n)` when it's a structural placeholder.

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

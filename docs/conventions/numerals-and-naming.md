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

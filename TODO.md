# TODO

Language and library improvements, in priority/dependency order. Items
move from **Active** to **Completed** with a date when they land; items
in **Opportunistic** are smaller wins to slot in when their motivating
pain becomes acute.

## Active

### 1. More math content — start here
Build the abstract algebra layer: `Group`,
`Ring`, `Field`, `CommutativeRing` as Proposition records;
`Integer` as a `CommutativeRing` instance; then `Rational :=
(Integer × Natural⁺) / ~`, then `Real` (Cauchy sequences or Dedekind
cuts), then vector spaces / linear algebra.

### 2. Parallel verification
Optimistic per-theorem parallelism with a thread pool: register
signatures eagerly, parallelize body verification, collect all errors
at end, fail if any worker fails. **Defer until the operator-
overloading change settles** — parallelizing over a fast-changing
elaborator means doing the work twice.

Subtleties: per-worker universe-meta naming; thread-safe kernel
caches; deterministic error-ordering at the end; slow theorems set
the floor (consider splitting long proofs into lemmas).

### 3. `by ring` (and `by group`, `by abelian_group`, …)
Term-normalization tactic for ring identities. Highest payoff,
highest effort. **Wait until we have enough algebra content (item
3) to design the procedure against real use cases** — premature
normalization is hard to redo.

## Opportunistic

Smaller items to land when the motivating pain becomes acute:

- **`Quotient.induct₂` / `Quotient.lift₂` library helpers.** Halve
  the boilerplate for binary lemmas on quotient types. Slot in when
  we hit Rationals.
- **Multi-pattern fix.** Relocate function-argument bindings inside
  inner cases so the helper chains in `Integer/basics.math`,
  `Integer/addition.math`, etc. collapse. See commit 9e022a6 message
  for the design sketch.
- **`rewrite h at e` tactic.** Useful for non-ring rewrites; less
  urgent given `by ring` will cover the ring case.

## Completed

- **2026-05-14: Operator overloading for Integer.** `+`, `*`, `-` now
  dispatch on operand type, routing Integer operands to `Integer.add`,
  `Integer.multiply`, `Integer.subtract`. Lookup uses the raw inferred
  type so definitions like `Integer` retain their name. Commit
  `4dd4042`.
- **2026-05-14: Ascription as coercion.** `(x : T)` now auto-inserts a
  canonical embedding chain when `x`'s type doesn't match `T` but a
  registered chain exists. Initial registry: `Natural → Integer` via
  `Natural.to_integer`. Grows as new number systems land. Commit
  `8efd117`.
- **2026-05-14: Make narrow tactic keywords contextual.** `claim`,
  `obtain`, `assume`, `set`, `suffices`, `from`, `on`, `with`,
  `case`, `apply`, `contradiction` now parse as identifiers in name
  positions. Commit `cd1f993`.
- **2026-05-14: Free 10 dead reserved keywords.** `hypothesis`,
  `motive`, `target`, `proof`, `qed`, `have`, `show`, `induction`,
  `of`, `reduction`. Commit `ce59030`.

## Index of relevant chat decisions

- **Coercions: explicit only, never implicit.** Cascaded explicit
  casts (`Real.to_complex(Rational.to_real(...))`) are unbearable,
  but visible casts at one syntactic site (`(x : T)`) localize the
  type change and force the reader/writer to know what type is
  involved. Mathlib's `push_cast`/`norm_cast` are evidence that
  implicit coercion is the single biggest source of "my proof
  should work but doesn't" pain in formal math; we won't repeat it.
- **Embedding paths are canonical, not searched.** If two paths
  ever exist from source to target, reject the cast at elaboration
  time. (Currently a single linear chain, so this is a future
  invariant.)
- **Mathematician-friendly identifiers.** No sigil-marked or
  ALL_CAPS keywords; the math vocabulary belongs to the user.
  Tactic-block keywords are contextual; hard keywords are kept
  minimal.

# TODO

Language and library improvements, in priority/dependency order. Items
move from **Active** to **Completed** with a date when they land; items
in **Opportunistic** are smaller wins to slot in when their motivating
pain becomes acute.

## Active

### 1. Cast via ascription `(x : T)` — start here
Generalize the existing type-ascription form so that when `x`'s
inferred type doesn't match `T` but a canonical embedding chain
exists, the chain is composed and inserted automatically.

**Decision (2026-05-14):** use the ascription form `(x : T)` rather
than introducing a `cast` keyword. The current `SurfaceAscription`
already means "I claim this has this type"; extending it to insert
canonical embeddings is the natural generalization. No new keyword,
no parser change — pure elaborator work.

**Initial registry:** just `Natural.to_integer : Natural → Integer`.
Grows to `Integer → Rational`, `Rational → Real`, `Real → Complex`
as those types land. Single canonical linear chain — reject
ambiguity at elaboration time if multiple paths ever exist.

### 2. Operator overloading for Integer (and beyond)
Currently `+ / * / -` desugar only to `Natural.add` / `Natural.multiply`.
Make the elaborator dispatch on operand type — initially via a
hardcoded map (`Natural → Natural.add`, `Integer → Integer.add`,
…); move to an instance/registry system later. Combined with (1),
this is the biggest readability win on existing-style code.

### 3. More math content
Once (1) and (2) are in, build the abstract algebra layer: `Group`,
`Ring`, `Field`, `CommutativeRing` as Proposition records;
`Integer` as a `CommutativeRing` instance; then `Rational :=
(Integer × Natural⁺) / ~`, then `Real` (Cauchy sequences or Dedekind
cuts), then vector spaces / linear algebra.

### 4. Parallel verification
Optimistic per-theorem parallelism with a thread pool: register
signatures eagerly, parallelize body verification, collect all errors
at end, fail if any worker fails. **Defer until elaborator changes
from (1)–(2) settle** — parallelizing over a fast-changing kernel
means doing the work twice.

Subtleties: per-worker universe-meta naming; thread-safe kernel
caches; deterministic error-ordering at the end; slow theorems set
the floor (consider splitting long proofs into lemmas).

### 5. `by ring` (and `by group`, `by abelian_group`, …)
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

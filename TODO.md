# TODO

Language and library improvements, in priority/dependency order. Items
move from **Active** to **Completed** with a date when they land; items
in **Opportunistic** are smaller wins to slot in when their motivating
pain becomes acute.

## Active

### 1. More math content — in progress
Abstract algebra layer landed (Monoid, Group, AbelianGroup, Ring,
CommutativeRing as Proposition predicates; Integer is a
CommutativeRing; Natural is a commutative monoid under both ops; a
few generic group lemmas demonstrated). Supporting infrastructure
also landed: Quotient.induct_two (binary induction helper) and
Natural multiplication cancellation. Next:

- **Integer cancellation lemma.** For the Rational equivalence
  transitivity proof we need:
  `x · Natural.to_integer(successor(k)) = y · Natural.to_integer(successor(k)) → x = y`.
  Proof: induct both x and y down to representatives `make(p1, q1)`,
  `make(p2, q2)`; the product reduces to `make(p·succ(k), q·succ(k))`;
  the equivalence factors out `succ(k)` via distributivity_right;
  apply Natural.multiply_cancel_right; reassemble via Quotient.sound.
  Probably ~80–120 lines.
- **Rational basics.** Representative `(numerator : Integer,
  denominatorMinusOne : Natural)`, equivalence `(n1, d1) ~ (n2, d2)
  iff n1 · succ(d2) = n2 · succ(d1)`, reflexivity / symmetry /
  transitivity (transitivity uses the cancellation lemma above),
  `Rational := Quotient(RationalRepresentative, RationalEquivalent)`.
  Probably ~150–200 lines.
- **Rational arithmetic.** `Rational.add`, `Rational.multiply`,
  `Rational.negate`, `Rational.subtract`, `Rational.zero`,
  `Rational.one`, plus the field axioms (commutativity, associativity,
  distributivity, multiplicative inverse for non-zero). Two-step
  Quotient.lift pattern; the binary-lift boilerplate is the same as
  Integer.add/multiply (Quotient.lift_two is sketched in
  Logic/quotient.math but currently fails the elaborator — revisit
  later). Probably ~600–800 lines.
- **Integer → Rational embedding.** `Integer.to_rational(n) := mk(make(n, 0))`.
  Extends the cast registry: ascription `(x : Rational)` on an
  Integer auto-applies this.
- **Field** predicate, with a non-zero-implies-invertible witness.
- **Real** (Cauchy sequences over Rational, or Dedekind cuts).
- More generic abelian-group / ring / field lemmas as they're needed.

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

- **`Quotient.lift_two`.** Sketched in `Logic/quotient.math` but
  currently rejected by the elaborator with a universe-argument
  mismatch through the nested polymorphic lifts. Manual two-step
  lifts (Integer.add pattern) work fine. Revisit when the universe-
  handling code in the elaborator is more robust.
- **Multi-pattern fix.** Relocate function-argument bindings inside
  inner cases so the helper chains in `Integer/basics.math`,
  `Integer/addition.math`, etc. collapse. See commit 9e022a6 message
  for the design sketch.
- **`rewrite h at e` tactic.** Useful for non-ring rewrites; less
  urgent given `by ring` will cover the ring case.

## Completed

- **2026-05-14: Natural multiplication cancellation.** `a · c = b · c`
  with `c ≥ 1` forces `a = b`. Three supporting helpers
  (`add_equals_zero_left`, `multiply_equals_zero_with_positive_right`,
  `multiply_cancel_left`). Unblocks Rational transitivity. Commit
  `8e63b9b`.
- **2026-05-14: `Quotient.induct_two`.** Binary induction helper:
  one call replaces a nested-induct + at-representatives chain. The
  twin `Quotient.lift_two` was attempted but currently fails the
  elaborator's universe-arg handling; the manual two-step lift in
  Integer.add etc. remains the path of least resistance. Commit
  `fcfb34a`.
- **2026-05-14: Abstract algebra layer.** Monoid, CommutativeMonoid,
  Group, AbelianGroup, Ring, CommutativeRing as Proposition
  predicates; Integer is a commutative ring (8 instance witnesses);
  Natural is a commutative monoid under both + and ·; three generic
  group lemmas (`right_inverse_unique`, `left_inverse_unique`,
  `inverse_involution`). Also fixed `desugarCongruenceOf` to close
  the domain/codomain types — without the fix, generic lemmas over a
  binder-bound carrier type failed with "unbound internal variable".
  Commit `a4a4421`.
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

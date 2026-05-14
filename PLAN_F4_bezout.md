# Plan: F-4 Bezout's identity (with Natural mod and Integer subtraction)

Tracking document for F-4 and the two prerequisites the user wanted to
build out for their own sake. Update the status column as items land.

## Context

Bezout's identity: for `a, b : Natural`, there exist `x, y : Integer` such that
`a · x + b · y = gcd(a, b)`. The classical proof is the extended
Euclidean algorithm; it needs two pieces we don't yet have:

1. **Natural division-with-remainder**: for any `a` and `b ≥ 1`, find
   `q, r : Natural` with `a = q · b + r` and `r < b`. Equivalent to
   `Natural.mod` + `Natural.quotient`.
2. **Integer subtraction**: `Integer.subtract(x, y) := Integer.add(x,
   Integer.negate(y))`. Needs `Integer.negate` (swap representative
   components, respect the equivalence, lift via Quotient.lift).

Currently:
- `library/Integer/{basics,addition,multiplication,embedding}.math`
  give Integer, `+`, `·`, and `Natural.to_integer`.
- No Integer arithmetic identities (commutativity, associativity,
  distributivity) are proved yet. The Bezout proof needs most of
  them.

A useful intermediate target: a `Ring` predicate / record that
`Integer` instantiates. That's deferred to phase G; for F-4 we just
prove the identities directly on `Integer`.

## Approach

Four sequential phases. Each is a single commit-sized chunk.

### F-4A — Integer ring structure

Prove the commutative-ring identities on Integer. Each lemma factors
through:
1. The same identity on `IntegerRepresentative` (componentwise on
   Naturals, via `Natural.add_*` / `Natural.multiply_*`).
2. `Quotient.induct` (since equality on `Integer` is what we're
   proving — predicate is a Proposition).

Lemmas:
- `Integer.add_commutative(x y : Integer) : x + y = y + x`
- `Integer.add_associative(x y z : Integer) : (x + y) + z = x + (y + z)`
- `Integer.add_identity_left(x : Integer) : Integer.zero + x = x`
- `Integer.add_identity_right(x : Integer) : x + Integer.zero = x`
- `Integer.multiply_commutative(x y : Integer) : x · y = y · x`
- `Integer.multiply_associative(x y z : Integer) : (x · y) · z = x · (y · z)`
- `Integer.multiply_identity_left(x : Integer) : Integer.one · x = x`
- `Integer.multiply_identity_right(x : Integer) : x · Integer.one = x`
- `Integer.distributivity_left(x y z : Integer) : x · (y + z) = x · y + x · z`
- `Integer.distributivity_right(x y z : Integer) : (x + y) · z = x · z + y · z`

Pattern for each: state for representatives first as a Natural-level
lemma; lift via `Quotient.induct` (and `Quotient.sound` where the
representative-level identity is propositional rather than
definitional).

**Friction note**: `Quotient.induct` consumes ONE Integer at a time.
For binary lemmas like commutativity we'll nest two inducts (induct
on x then on y) or factor through a helper that fixes one argument.
Expected ~500-700 lines for the full ring structure; mechanical but
tedious. Same multi-pattern friction as F-3.

### F-4B — Natural division-with-remainder

`Natural.divide_with_remainder(a : Natural) (b : Natural) (positiveDivisor : 1 ≤ b) : Σ q r. a = q · b + r ∧ r < b`

Or equivalently with an Exists wrapper:
`∃ q r. a = q · b + r ∧ r < b`.

(Prefer the Exists form for now — we don't have Σ-types and don't
need one.)

Proof by strong induction on `a`:
- If `a < b`: `q = 0`, `r = a`. Then `a = 0 · b + a` and `a < b`.
- If `a ≥ b`: `a - b` exists (via `Natural.subtraction_witness`).
  Recurse on `a - b` to get `q', r'` with `a - b = q' · b + r'` and
  `r' < b`. Then `a = (q' + 1) · b + r'` (since `a - b + b = a` and
  `(q' + 1) · b = q' · b + b`).

Companion projections:
- `Natural.quotient(a, b, positiveDivisor) : Natural` — first witness.
- `Natural.mod(a, b, positiveDivisor) : Natural` — second witness.

Or keep them as Exists.eliminate destructures at call sites; the
projections are sugar.

**Lemmas needed first** (mostly already in `library/Natural/`):
- `Natural.subtraction_witness` (have).
- `Natural.successor_less_or_equal_successor` (have).
- `Natural.totality_of_less_or_equal` (have).
- A "case split on `a < b` vs `b ≤ a`" combinator — derivable from
  `decides_less_or_equal` (have) + `Or.eliminate`.

Expected ~80-120 lines.

### F-4C — Integer subtraction

Three pieces:

1. **`Integer.negate_representatives(rep) := make(negative, positive)`**
   (swap components). One-line definition by pattern-match.

2. **`Integer.negate_respects(rep ~ rep') → negate(rep) ~ negate(rep')`** —
   from `(a, b) ~ (a', b')` (i.e. `a + b' = b + a'`) derive
   `(b, a) ~ (b', a')` (i.e. `b + a' = a + b'`). Just symmetric
   commutativity reshuffles. Short helper chain (`negate_after_first` +
   `negate`).

3. **`Integer.negate : Integer → Integer`** — lift `negate_representatives`
   via `Quotient.lift` with the respect lemma.

4. **`Integer.subtract(x y : Integer) : Integer := Integer.add(x, Integer.negate(y))`**.

5. **Identities** worth landing:
   - `Integer.add_negate_left(x) : Integer.add(Integer.negate(x), x) = Integer.zero`
   - `Integer.add_negate_right(x) : Integer.add(x, Integer.negate(x)) = Integer.zero`
   - These make Integer an additive group on top of the additive
     monoid from F-4A.

Expected ~150-200 lines.

### F-4D — Bezout via extended Euclidean

Goal: `∃ (x y : Integer). Natural.to_integer(a) · x + Natural.to_integer(b) · y = Natural.to_integer(gcd(a, b))`.

Or more usefully, since GCD existence will fall out of the proof:
`∃ (g : Natural) (x y : Integer). Natural.to_integer(a) · x + Natural.to_integer(b) · y = Natural.to_integer(g) ∧ Natural.is_gcd(g, a, b)`.

**Proof outline** (strong induction on `b`, using F-4B for the
quotient/remainder step):

- Base case `b = 0`: `gcd(a, 0) = a` (from `Natural.is_gcd_zero_right`
  in F-2). Take `x = 1`, `y = 0`: `a · 1 + 0 · 0 = a`. ✓
- Inductive case `b ≥ 1`:
  - Apply `divide_with_remainder(a, b)` to get `q, r` with
    `a = q · b + r` and `r < b`.
  - By IH on `b, r` (with `r < b`), get `g, x', y'` with
    `b · x' + r · y' = g` and `is_gcd(g, b, r)`.
  - Then `g = b · x' + r · y' = b · x' + (a - q · b) · y'
            = a · y' + b · (x' - q · y')`. So `x = y'`,
    `y = x' - q · y'` (Integer subtraction!). ✓
  - And `is_gcd(g, a, b)` follows from `is_gcd(g, b, r)` plus
    `a = q · b + r` (a separate small lemma `is_gcd_remainder_lift`).

**Lemmas needed**:
- All of F-4A (commutative-ring identities on Integer).
- F-4B (`divide_with_remainder`).
- F-4C (`Integer.subtract`).
- `Natural.is_gcd_remainder_lift(a, b, q, r) : a = q · b + r → is_gcd(g, b, r) → is_gcd(g, a, b)`.
  - Proves: any common divisor of (a, b) also divides (b, r); and
    vice-versa. Standard.

Expected ~200-300 lines (the algebra inside the existential is the
bulk).

## Files this will create

- `library/Integer/ring.math` — F-4A identities. Imports
  `Integer/{basics, addition, multiplication}`.
- `library/Integer/negation.math` — F-4C `negate` and `subtract`.
- `library/Natural/division.math` — F-4B `divide_with_remainder`,
  `mod`, `quotient`. Imports `Natural/subtraction.math`.
- `library/Natural/bezout.math` — F-4D the main theorem.
  Imports everything else.

Or fewer/larger files — the split above is one possibility.

## Friction we'll likely hit again

- **Multi-pattern with hypothesis types depending on destructure** —
  every `_respects` proof in F-4A and F-4C will need a 2-helper chain
  (same as F-3). At ~10 ring identities each with 2-3 helpers, that's
  ~30 extra helper definitions just for plumbing. If it becomes
  unbearable, the full multi-pattern fix (relocate bindings inside
  inner cases) is worth doing first — see commit
  9e022a6 message for what's left to do there.
- **`Quotient.induct` binary lemmas** — induct binds one argument at
  a time. Each binary lemma needs two nested inducts (or a curried
  inner). Same pattern as `Integer.add` from F-3.
- **Universe-level annotations** — quotients are level 0, equalities
  at level 0. Boilerplate: `Quotient.lift.{0, 0}`, `Quotient.sound.{0}`,
  `Quotient.induct.{0}`, `Equality.{0}`. No surprises.

## Suggested resume order

Land F-4A first (gets the ring identities out of the way and exercises
the Quotient.induct + helper-chain pattern at scale; if it becomes
painful, do the full multi-pattern fix BEFORE F-4C). Then F-4B (pure
Natural-side, can land before or after F-4A — independent). Then
F-4C. Then F-4D.

One commit per phase; smaller commits within a phase if useful.

## Items worth deferring past F-4

- A `Ring` / `CommutativeRing` predicate as a Proposition-record. Wait
  until we have a second instance (Rational? Real?) so the
  abstraction has payoff.
- `Integer.compare` (≤, <, sign): not needed for Bezout. Will be
  needed before Rational ordering.
- Polynomial multiplication identities: way off in the future.

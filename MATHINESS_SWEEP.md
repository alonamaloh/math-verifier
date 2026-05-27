# MATHINESS_SWEEP.md — tracking the library-wide mathiness pass

A running ledger of which files have been gone through with the
"make proofs read as math" lens, and what's still pending. Companion
to `LANGUAGE.md` (idioms) and `LANGUAGE_VISION.md` (design direction).

## Approach in each file

For each proof:
1. Does it read like the math sentence a textbook would use?
2. If not, is there a sugar that gets it there?
3. Apply the sugar; verify the file still builds.
4. Note any new limitations that surfaced.

## Status

### Natural/ — partially done

**Covered (with refactors landed):**
- `peano.math` — `Natural.two_not_three_plus` rewritten with named claims; `?` applied.
- `arithmetic.math` — `multiply_associative` calc cleanup.
- `maximum.math` — redundant `(cases … : T)` annotations removed.
- `cancellation.math` — `(cases … } : T → U)(arg)` → `cases … refining arg`.
- `divides_subtract.math` — same refining cleanup; verbose `Exists.introduce` → tuple form.
- `padic_valuation.math` — one site refactored; **most of this large file (1503 lines) not yet looked at**.
- `prime.math` — `?` on And.left and successor lemma.
- `divisibility.math` — verbose `Exists.introduce` → tuple form; refining cleanup.
- `strong_recursion.math` — tuple form for `Or.introduceRight(Exists.introduce(…))`.
- `decide_divides.math` — `And.introduction(A, B, p, q)` → `⟨p, q⟩`.
- `prime_two.math` — `And.introduction` → tuple.
- `prime_split.math` — same.
- `distance.math` — `?` applied at two sites.
- `bezout.math` — major refining cleanup in `has_bezout_step` (22 → 8 lines).
- `euclid.math` — `?` applied where the proof arg fixes the Naturals; reverted nested-`?` chains.
- `factorization.math` — `?` at four sites.

**Covered but no changes (already clean):**
- `basics.math` — definitions only, no proofs.
- `order.math` — pattern-match defs are right; one CIC convoy that doesn't have a sugar.
- `subtraction.math` — already idiomatic.
- `gcd.math` — uses tuple form, let destructure throughout; clean.

**Pending (left for later):**
- `power.math`
- `monus.math`
- `multiply_order.math`
- `divide.math` — **large (583 lines)**; structural recursion files often have idiomatic pattern-match forms, but worth a sweep.
- `division.math`
- `prime_divisor.math` / `prime_divisor_v2.math` / `prime_divisor_v3.math`
- `prime_divides_product.math`
- `padic_valuation.math` — **large (1503 lines)**; one site touched, the rest pending.

### Integer/ — partially done

**Covered (with refactors landed):**
- `basics.math` — `?` on add_cancel_right.
- `addition.math` — `add_after_first_respects` uses cases instead of
  explicit Quotient.induct motive.
- `ring.math` — major win: 34 → 21 declarations. Collapsed
  triple-helper stacks (at_representatives + after_first +
  after_first_second + main) into single cases-based proofs for:
  add_commutative, add_associative, add_identity_left,
  multiply_commutative, multiply_identity_left, distributivity_left,
  multiply_associative.
- `negation.math` — add_negate_left helper folded in.
- `algebra.math` — multiply_zero_left and multiply_negate_right helpers
  folded in.
- `multiplication.math` — cases instead of explicit motive on
  multiply_after_first_respects.

**Pending:**
- `absolute_value.math`, `absolute_value_natural.math`,
  `absolute_value_multiplicative.math`, `cancellation.math`,
  `embedding.math`, `instances.math`, `order.math`, `sign.math`.

The triple-helper collapse pattern is the biggest single win. Any
Integer-level proof that follows it (separate `_at_representatives` →
`_after_first_second` → `_after_first` → main) is a candidate.

### Rational/ — pending

### Real/ — partially covered

Refactored during the earlier patterns-in-binders sweep:
- `algebra.math`, `ring.math`, `absolute_value.math`, `order.math`, `supremum.math` (selected sites).
- `linearity.math`, `multiplication.math`, `addition.math`, `field.math`, `apartness.math`, `convergence.math` — **not yet looked at with the `?` lens**.

### PAdic/ — partially covered

Refactored during the earlier sweep:
- `ring.math` (one site).

**Pending:**
- `absolute_value.math`, `addition.math`, `negation.math`, `multiplication.math`, `algebra.math`, `instances.math`, `embedding.math`, `cauchy_bounded.math`, `basics.math`.

### Other folders not yet swept

- `Logic/` — foundational; mostly definitions and axioms, but might have proofs.
- `Equality/` — same.
- `Algebra/` — definitions; less proof bureaucracy.
- `Set/` — small.
- `Lists/` — small.

## Patterns to keep watching for

Each time these come up, the swap is mechanical and pays off:

| Bureaucracy | Sugar |
|---|---|
| `Exists.introduce(T, λq. P(q), w, p)` | `⟨w, p⟩` |
| `And.introduction(A, B, p, q)` | `⟨p, q⟩` |
| `Lemma(<recoverable from proof>, <…>, proof)` | `Lemma(?, ?, proof)` |
| `(cases x { … } : T → U)(arg)` | `cases x refining arg { … }` |
| `Quotient.induct_two(λ. goal, atRep, x, y)` | `Quotient.induct_two(atRep, x, y)` |
| `cases x { \| Quotient.mk(rep) => … }` | `cases x { \| rep => … }` or directly `cases x { \| ConstructorPattern => … }` |
| `Equality.symmetry(lemma)` (when used once) | bare `lemma` (calc diff inference handles direction) |
| Pattern-match definition + cases with explicit motive | structural pattern-match is fine if natural; otherwise `by_induction` |

## Known limitations encountered

- **Nested `?` chains** don't share unification state. Workaround: spell the outer args explicitly.
- **Multi-name `refining` + quotient cases**: fixed earlier.
- **`Quotient.exact` short form**: doesn't exist yet; verbose form is the only option (~11 call sites in the library).

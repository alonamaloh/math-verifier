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

### Integer/ — done

All structural files (`basics`, `addition`, `multiplication`, `ring`,
`negation`, `algebra`, `cancellation`, `order`, `sign`,
`absolute_value`, `absolute_value_natural`, `embedding`, `instances`)
have been swept. The triple-helper collapse pattern was the biggest
win:
- `ring.math`: 34 → 21 declarations.
- All other files: smaller wins.

Files NOT yet looked at:
- `absolute_value_multiplicative.math` (159 lines) — quick peek showed
  no obvious verbose patterns; worth a careful read someday.

### Rational/ — substantially done

Refactored:
- `basics.math` — `?` on multiply_cancel_right.
- `addition.math`, `multiplication.math` — `cases` instead of
  Quotient.induct motive on the after_first_respects helpers.
- `ring.math` — collapsed double-obtain to single.
- `algebra.math` — same.
- `order_arithmetic.math` — two Quotient.induct stacks → cases-refining.
- `positive.math` — IsNonneg.multiply → cases-refining.

NOT yet refactored: `field.math`, `triangle.math`, `triangle_more.math`,
`order_multiplication.math` (has Quotient.exact stacks),
`absolute_value.math`, `reciprocal_function.math`, `reciprocal.math`,
`order.math`, `negation.math`, `halve.math`, `linearity.math`,
`embedding.math`, `instances.math`.

### Real/ — partially done

Refactored in earlier patterns-in-binders sweep AND this sweep:
- `ring.math` — drop motives on zero_add, add_negate_right, negate_negate.
- `algebra.math` — collapse distributivity_left's nested induct + induct_two.
- `absolute_value.math`, `order.math`, `supremum.math` — earlier work.

NOT yet refactored: `linearity.math`, `multiplication.math`,
`addition.math`, `field.math`, `apartness.math`, `convergence.math`,
`negation.math`, `embedding.math`, `basics.math`, `cauchy_bounded.math`,
`reciprocal.math`, `sequence.math`, `instances.math`.

### PAdic/ — partially done

- `ring.math` — collapse add_associative, zero_add, add_negate_right.
- `algebra.math` — collapse multiply_associative, one_multiply,
  distributivity_left.

NOT yet refactored: `absolute_value.math` (~7 induct sites),
`addition.math`, `negation.math`, `multiplication.math`,
`cauchy_bounded.math`, `embedding.math`, `instances.math`, `basics.math`.

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

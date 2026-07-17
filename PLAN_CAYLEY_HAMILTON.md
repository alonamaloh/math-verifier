# PLAN_CAYLEY_HAMILTON — the eigen-arc (kickoff for a fresh session)

Owner-approved direction (2026-07-17): after det(AB) and rank–nullity,
the next headline is the characteristic polynomial and Cayley–Hamilton.
Chosen deliberately to COMPOSE the two freshly-polished towers — Matrix/
determinant (σ(i), ∘, the Leibniz form) and Polynomial (p[k], ≈, +/*/∸,
Coefficients.one) — and to let new proofs drive the next round of
language friction, per the productive polish→friction→improve→sweep
pattern.

## Warm-up (do FIRST, fresh session)

- **U3+U6 from PLAN_USABILITY.md** (checker self-verification +
  auto-settled mechanical categories). Deferred from the 2026-07-17
  session deliberately: they are precision work on the checker every
  future polish depends on, and that session ended with two
  exit-code-masking process slips (see commit 7a493d08's message — a
  broken-gate push, caught and corrected). Fresh eyes required. They
  also pay off during this arc's own polish passes.
- Optional quick wins to exercise fresh notation: Freek #52 (a size-n
  finite set has 2^n subsets — Set/finite counting + the new
  Natural.two_power lemmas) and #58 (C(n,k) = n!/(k!(n−k)!) — binomial,
  factorial, honest division all exist).

## The mathematical ladder

1. **Generalize Matrix/det from Field to CommutativeRing.** Matrix(f, m, n),
   Matrix.multiply, determinant, and the det lemma stack (row-permutation,
   alternating collapse, multiplicativity) are `{f : Field}` today, but
   NOTHING in the determinant theory needs division — audit which proofs
   actually use Field-only facts (reciprocal appears only in
   finite_permutation-adjacent reindexing? verify). Target: the whole det
   stack at `{r : CommutativeRing}`, with the Field versions as
   instances. This is the arc's main infrastructure lift and is reusable
   far beyond CH.
2. **Polynomial ring bundling.** `Polynomial.ring(r)` /
   `Polynomial.commutative_ring(r, commutativity)` exist
   (quotient_field.math uses them) — check they provide the
   CommutativeRing bundle the generalized Matrix needs, and that ring/
   field tactic support at the polynomial carrier is adequate (the
   `ring` tactic at an abstract CommutativeRing bundle — status?).
3. **Matrices over F[x], and xI − A.** Define the characteristic matrix
   for A : Matrix(F, n, n): entries are degree-≤1 polynomials. Needs the
   Field↪F[x] entry embedding (constant polynomials — Polynomial.monomial
   at exponent 0; consider a named coercion so entries read `(A(i,j) : F[x])`
   or similar; a `coercion` registration may make xI − A read naturally).
4. **charPoly(A) := det(xI − A) : F[x].** Immediate corollaries as the
   acceptance tests for the generalization: charPoly is monic of degree n
   (needs degree-of-det reasoning — the Leibniz sum's degree bound: each
   permutation term has degree ≤ n with equality only for the identity;
   this exercises Polynomial.DegreeLessThan and the ∘/σ(i) machinery
   together); det(A) = (−1)^n · charPoly(A)[0] (constant term).
5. **Evaluation homomorphism.** `Polynomial.evaluate` does NOT exist yet
   (deliberately — `p(k)` was reserved for it when `()`/`[]` were split).
   Define evaluation at a COMMUTING element of an F-algebra; the use case
   is evaluation at the matrix A (matrices commute with scalars and with
   powers of A). Design decision to make early: evaluate into a general
   algebra with a commuting-image hypothesis vs the specific
   Matrix-algebra instance first (recommend: specific first, prove value,
   generalize if a second consumer appears — the () registration playbook).
   REGISTER `operator (()) on (Polynomial) := Polynomial.evaluate…`-style
   application ONLY IF the evaluation design lands cleanly — this is the
   long-reserved `p(x)` spelling; get the owner's eyes on the signature
   before registering.
6. **Cayley–Hamilton: charPoly(A)(A) = 0.** Recommended route: the
   classical adjugate argument — adj(xI − A) · (xI − A) = charPoly(A)·I
   in Matrix(F[x], n, n), then compare coefficients (matrices of
   polynomials ≅ polynomials with matrix coefficients — this transposition
   is the proof's one subtle infrastructure piece; plan it explicitly).
   Needs: adjugate/cofactor development (new; builds on det via
   row/column expansion — itself a missing, valuable lemma: Laplace
   expansion), or the alternative telescoping-sum proof that avoids
   explicit adjugates. DECIDE at design time with the file in front of
   you; Laplace expansion is independently valuable either way.

## Friction watchlist (expected, feed the improve/sweep loop)

- Abstract-carrier constants (`Ring.zero(r)`, `Field.one(f)`) — the
  numeral work stops at concrete carriers; this arc will hit it hard.
- Under-binder congruence through Ring.Sum/productOver (U-list item;
  the det-degree bound will stress it).
- The `a − b` narrowing (PLAN_NATURAL_NARROWING) — degree arithmetic
  (n ∸ 1 vs n − 1 with bounds in scope) will surface real sites for N0.
- Order-chain closer v2 — degree comparisons will feed it.
- Matrix entry/dimension index bookkeeping — watch whether NaturalsBelow
  plumbing wants new ergonomics.

## Process

Per-brick: build → verify (make -j 16 library/tests under ulimit) →
polish the new file with the marker flow immediately (don't accumulate
debt) → manifest-add at birth → commit → push. Read
docs/conventions/proof-style.md and the readability memory's judgment
table before the first polish pass.

## Status ledger

| item | state | notes |
|------|-------|-------|
| W  warm-up: U3+U6 | DONE 2026-07-17 | see PLAN_USABILITY.md ledger for details |
| W' warm-up: Freek #52/#58 | OPTIONAL | quick wins on fresh notation |
| C1 det over CommutativeRing | DONE 2026-07-17 (42b0915b) | zero Field-only facts; aggregation → commutative_ring_aggregation.math, field_aggregation deleted |
| C2 polynomial ring bundle check | DONE 2026-07-17 | Polynomial.commutative_ring → commutative.math; CommutativeRing.polynomial_ring; ring tactic OK at polynomial bundle (Test/matrix_commutative_ring_instances_test) |
| C3 xI − A + entry embedding | DONE 2026-07-17 | entrywise definition (compositional form blocked by mixed-carrier operator resolution); Polynomial.constant/indeterminate; matrix ops+operators; motive-peel elaborator fix |
| C4 charPoly + degree/constant-term corollaries | DegreeLessThan + MONIC DONE 2026-07-17; constant term NEXT | see memory cayley_hamilton_arc for the ready bricks + friction recipes |
| C5 evaluation homomorphism | TODO | design signature with owner; `p(x)` registration decision |
| C6 Cayley–Hamilton | TODO | adjugate/Laplace vs telescoping — decide at design time |

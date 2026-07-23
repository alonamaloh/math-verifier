# Plan: the one-two-five converse

## Decision

Keep `Matrix.OneTwoFiveConverse` as an explicit deep input for now.  The
all-at-once census in `PLAN_TERNARY_CONVERSES.md` found no analogue of the
elementary one-two-four reduction to the three-squares theorem.

This is not merely a failed search for the right identity:

- the obstruction for `x²+2y²+5z²` is 5-adic,
  `25^a(25b+10)` or `25^a(25b+15)`, while Legendre's obstruction is
  2-adic;
- multiplying the target by a fixed scalar cannot uniformly turn
  one-two-five admissibility into three-squares admissibility;
- the known direct proof treats `x²+2y²+5z²` as one of three determinant-10
  ternary classes and isolates it by congruence conditions. It is not a
  coordinate transform from the sum of three squares.

The relevant direct reference is Blackwell–Durham–Thompson–Treece,
[A Generalization of Mordell to Ternary Quadratic Forms](https://arxiv.org/pdf/1508.02694),
especially §2 and §3.6.

## What is already isolated

`Algebra/rank_four_weighted_d5_foundation` exposes exactly the interface the
rank-four work needs:

```text
Matrix.OneTwoFiveConverse :=
  every natural outside the two 25-adic obstruction families
  is represented by x²+2y²+5z².
```

No client depends on a proposed proof method. The 33 nonexceptional selected
weighted-`d=5` rank-four forms are now conditionally universal from this one
interface:

- five diagonal forms in
  `Algebra/rank_four_weighted_d5_zero_residue_covers`;
- 28 bordered forms in `Algebra/rank_four_weighted_d5_covers`.

The bordered covers use only elementary arithmetic. An obstructed target is
written as `25^a(25b+q)`. The proof represents the base `25b+q`, then scales
all four coordinates by `5^a`. For each form and each `q∈{10,15}`, a fixed
fourth coordinate gives an admissible one-two-five residual after a finite
prefix. The generator emits explicit kernel-checked witnesses for that finite
prefix and the handwritten theorem proves the uniform tail.

## Direct formalization route

If the project chooses to discharge `Matrix.OneTwoFiveConverse` directly,
the shortest known route is a specialized Mordell-style development, not the
full theory of p-adic lattices.

1. **Elementary obstruction and descent**

   - Prove the forbidden residues `10,15 mod 25`.
   - Prove that a representation of `25m` forces all three coordinates to be
     divisible by five, hence descends to a representation of `m`.
   - Package the exact obstruction direction for all powers of 25.

2. **Quadratic-residue infrastructure**

   - Legendre/Jacobi symbols and quadratic reciprocity.
   - Chinese-remainder assembly of the required congruences.
   - A specialized prime-in-arithmetic-progression theorem strong enough for
     the residue classes modulo 400 and 800 used in §3.6.  This is a
     restricted Dirichlet theorem and may dominate the cost of the entire
     route; it is the principal formalization risk, not a routine supporting
     lemma.

3. **Mordell construction at determinant 10**

   - Formalize
     `m f = (Ax+By+mz)² + ax² + 2hxy + by²`
     with `ab-h²=10m`.
   - Prove the congruence conditions make the coefficients integral.
   - Construct `A,B,a,h,b` in the cases from §3.6.

4. **Finite determinant-10 classification**

   - Certify that the relevant reduced ternary classes are exactly
     `x²+2y²+5z²`, `2x²+2y²+2xz+3z²`, and `x²+y²+10z²`.
   - Use the represented value `6 mod 16` to eliminate the latter two.
   - Conclude the desired class represents the target.

5. **Assemble and remove the interface**

   - Prove `Matrix.OneTwoFiveConverse`.
   - Rebuild every weighted-`d=5` cover without changing any client theorem.
   - Add statement-shape guards for the represented-set theorem and its
     25-adic descent, since a vacuous converse would silently validate every
     conditional client.

## Alternative route and gate

The genus route is genuinely valid here: Blackwell et al. state that the
forms they treat, including `x²+2y²+5z²`, are alone in their genera.  The
three determinant-ten classes appearing in the Mordell construction do not
contradict that statement; the construction first lands in a finite list of
classes, then uses a congruence to select the desired one.

The all-at-once census has replaced the old “wait for the odd family” gate.
Several published regular ternary converses remain, so shared deep
infrastructure may have multiple consumers.  Before committing to it:

- note that the proved odd-`C=5` reduction's 12 rank-four covers are now
  complete and add no deep interface;
- pilot the index-three/index-six reductions identified in
  `PLAN_TERNARY_CONVERSES.md`; and
- keep the nonregular determinant-seven odd parent out of any blanket genus
  claim.

After those cheap routes are exhausted, compare a shared class-one/genus
layer with shared Mordell infrastructure.  Do not formalize the
one-two-five Mordell proof in isolation merely because it has a published
specialized route.

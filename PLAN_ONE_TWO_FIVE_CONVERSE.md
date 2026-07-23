# Plan: the one-two-five converse

## Decision

Keep `Matrix.OneTwoFiveConverse` as an explicit deep input for now. The bounded
pilot found no analogue of the elementary one-two-four reduction to the
three-squares theorem.

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
     the residue classes modulo 400 and 800 used in §3.6. This is the largest
     new external arithmetic input in the Mordell route.

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

The genus route is also valid: prove local representability and show the
one-two-five form is alone in its genus. But that route requires the gated
`ℤ_p`-lattice/regularity block in `PLAN_15_THEOREM.md`. It should be chosen
only if several remaining ternary converses will share that machinery.

The next decision point comes after the odd-family conditional covers. At
that point, compare the remaining converse set:

- if several forms need the same integral local-global theorem, pay for the
  genus layer once;
- if one-two-five is isolated, the specialized Mordell route above is likely
  the narrower formalization.

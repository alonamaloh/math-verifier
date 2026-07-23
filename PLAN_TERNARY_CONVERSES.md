# Plan: ternary converse census and route selection

## Decision

Classify all ternary converse obligations before investing in genus theory or
a form-specific Mordell proof.  The discriminant immediately identifies the
bad primes and suggests useful integral changes of variables, but it does not
by itself prove regularity or show that two represented sets coincide.
Accordingly, this plan distinguishes:

- reductions already proved in the library;
- reductions whose identity is known but whose integral congruence recovery
  is not yet formalized;
- published regular represented sets that still need a deep converse; and
- the odd determinant-seven parent, for which a generic regularity converse
  would be false.

This census changes the order of work.  First take every elementary reduction,
then finish the rank-four covers over those reduced parents, and only then
choose shared deep infrastructure for the irreducible converse cluster.

## Current ledger

The `clients` column counts selected rank-four normal forms.  There are 207
selected forms, of which six are already certified nonuniversal exact-truant
forms.  Thus the universality target is 201 forms.

| Ternary input | determinant | bad primes | exact admissibility input | clients | status and route |
| --- | ---: | --- | --- | ---: | --- |
| `x²+y²+z²` | 1 | 2 | not `4^a(8b+7)` | 115 | Central `Matrix.ThreeSquaresConverse`. The integral rational-to-integral descent is done; rational existence remains. It also supplies one-two-four and all 12 odd-`C=5` clients. |
| `x²+y²+3z²` | 3 | 2, 3 | not `9^a(9b+6)` | 9 | Published regular form. Keep `Matrix.TripleSquaresConverse` explicit until the shared deep route is chosen. |
| `x²+2y²+3z²` | 6 | 2, 3 | not `4^a(16b+10)` | 8 | Published regular form; `Matrix.OneTwoThreeConverse` remains deep. |
| `x²+2y²+6z²` | 12 | 2, 3 | not `4^a(8b+5)` | 7 | Published regular form; `Matrix.OneTwoSixConverse` remains deep. No elementary reduction is currently known. |
| `x²+3y²+6z²` | 18 | 2, 3 | square mod 3 and not `4^a(16b+14)` | 8 | Published regular form. It embeds as an index-three sublattice of `x²+y²+2z²`; integral recovery is not yet proved. |
| `2x²+3y²+6z²` | 36 | 2, 3 | twice a square mod 3 and not `4^a(8b+7)` | 7 | Published regular form. It embeds as an index-six sublattice of three squares; integral recovery is not yet proved. |
| `x²+2y²+4z²` | 8 | 2 | not `4^a(16b+14)` | included in the 103 | **Proved reduction.** `Matrix.one_two_four_converse_of_three_squares` derives it from three squares. |
| `x²+2y²+5z²` | 10 | 2, 5 | not `25^a(25b+10)` or `25^a(25b+15)` | 33 | Genuine deep input. The form is alone in its genus, so a genus route is valid; a specialized Mordell route is also known. See `PLAN_ONE_TWO_FIVE_CONVERSE.md`. |
| `x²+2y²+2yz+5z²` | 9 | 2, 3 | not `4^a(8b+7)` | 12 | **Proved reduction and covers.** `Algebra/odd_five_converse_reduction` proves equality of represented sets with three squares; `Algebra/rank_four_odd_c5_covers` discharges all 12 selected rank-four clients. |
| `x²+2y²+2yz+4z²` | 7 | 2, 7 | no regular represented set | 14 universal candidates, 2 exact truants | Do not introduce a false parent converse. This determinant-seven parent is not regular: local admissibility alone misses global values. Attack the 14 rank-four cosets directly, or prove a restricted coset theorem tailored to them. |

There are now 187 selected forms with conditional universality proofs:
115 from three squares (including all weighted `d=4` and odd-`C=5`
clients), 9 from triple squares, 8 from one-two-three, 7 from one-two-six,
8 from one-three-six, 7 from two-three-six, and 33 from one-two-five.  The
14 outstanding nonexceptional forms are exactly the odd-`C=4` family.

## Elementary reductions

### Completed: odd `C=5`

The forward identity is

```text
x² + 2y² + 2yz + 5z² = x² + (y+2z)² + (y-z)².
```

Conversely, among three square roots two have equal squares modulo three.
After changing one sign they are congruent modulo three, so they can be
written as `y+2z` and `y-z`.  The library now proves both directions and
derives `Matrix.OddFiveConverse` from `Matrix.ThreeSquaresConverse`.

For a rank-four border `2ryw+cw²`, the useful completed identity is

```text
9Q = (3x)² + (3(y+2z)+rw)² + (3(y-z)+2rw)² + (9c-5r²)w².
```

`Algebra/rank_four_odd_c5_cover` packages a more efficient integral base
shear.  Choose `w` with `9 | rw`, write `s=rw/9`, and use

```text
Q(x,y-5s,z+s,w) = F(x,y,z) + cw² - 45s².
```

The generator records 586 explicit base witnesses below the uniform tails,
split at 20 rows per theorem.  All 12 selected forms are now conditionally
universal from `Matrix.ThreeSquaresConverse`.

### Candidates: weighted `d=3`

These identities are valid over the integers by expansion, but the reverse
maps impose congruence conditions.  They are therefore candidates, not yet
reductions:

```text
2x² + 3y² + 6z²
  = (x+y+z)² + (x-y-z)² + (y-2z)²

x² + 3y² + 6z²
  = x² + (y+2z)² + 2(y-z)².
```

For the first identity, the image lattice has index six.  For the second, it
has index three, and `x²+y²+2z²` is already reducible to three squares after
doubling the target.  The next pilot should prove or refute integral recovery
from the exact local hypotheses already present in
`Integer.TwoThreeSixLocalConverse` and `Matrix.OneThreeSixLocalConverse`.
If recovery works, 15 more clients cease to require deep converse inputs.

No elementary reduction for `x²+2y²+6z²` is currently known, and none is
claimed by this plan.

## Deep-route decision

After the two remaining elementary pilots, recount the irreducible
interfaces.

1. If triple squares, one-two-three, one-two-six, and one-two-five remain,
   there are enough consumers to justify shared infrastructure rather than a
   one-off theorem.
2. A genus route must prove integral local representability and one-class
   genus results for each participating form.  It is mathematically valid for
   one-two-five: the determinant-ten form is alone in its genus.  The three
   determinant-ten classes used in the Mordell proof are not thereby
   genus-mates; the finite class elimination belongs to that construction.
3. A Mordell route shares quadratic-residue, reciprocity, CRT, reduction, and
   class-enumeration machinery across several forms.  However, its required
   prime-in-arithmetic-progression input is a restricted Dirichlet theorem,
   and may dominate the entire formalization cost.  It must be budgeted as
   the route's principal risk, not as a routine sublemma.
4. The determinant-seven odd parent is excluded from either blanket
   regularity route.  Its 14 rank-four clients require direct quaternary or
   restricted-coset work.

No deep route should begin until the two index-lattice pilots have executable
statements.  The odd-`C=5` clients are complete; the pilots can still change
the deep-interface count by 15.

## Execution order

1. **Done:** prove the odd-`C=5` represented-set reduction.
2. **Done:** use an integral base shear plus 586 generated,
   kernel-checked finite witnesses to discharge all 12 selected odd-`C=5`
   covers from `Matrix.ThreeSquaresConverse`.
3. Pilot the two-three-six and one-three-six index-lattice recoveries.  Keep a
   pilot only if it eliminates the existing exact local converse without
   adding an equally deep replacement.
4. Pilot one determinant-seven odd rank-four coset.  Measure whether direct
   residual selection plus finite tables scales to all 14 forms.
5. Recount the remaining interfaces and choose either a shared
   class-one/genus development or shared Mordell infrastructure.  Do not
   start with one-two-five in isolation.
6. Preserve statement-shape guards and cold-library verification throughout:
   all these interfaces feed many conditional clients, so a silently
   weakened converse would have a large blast radius.

## References

- Blackwell, Durham, Thompson, and Treece,
  [A Generalization of Mordell to Ternary Quadratic Forms](https://arxiv.org/pdf/1508.02694).
  Their forms are stated to be alone in their genera; §3.6 treats
  `x²+2y²+5z²`.
- Doyle, Muskat, Pehlivan, and Williams,
  [Regular ternary quadratic forms](https://math.colgate.edu/~integers/t45/t45.pdf).
  The tables give the exact exceptional sets used by the current interfaces,
  including the odd determinant-nine form.

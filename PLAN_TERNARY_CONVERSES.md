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
| `x²+2y²+2yz+4z²` | 7 | 2, 7 | restricted safe set modulo 12 and 49 | 14 universal candidates, 2 exact truants | **All direct covers proved.** Seven earlier clients use sublattice or neighbor arguments. The final seven use `Matrix.DetSevenSafeConverse`, explicit modulo-588 residual covers, and finite witness tables; exceptional `Q_(1,7)` also uses `Matrix.ThreeSquaresConverse`. The parent remains nonregular, so no blanket converse is claimed. |

All 201 selected universality targets now have conditional proofs:
115 from three squares (including all weighted `d=4` and odd-`C=5`
clients), 9 from triple squares, 8 from one-two-three, 7 from one-two-six,
8 from one-three-six, 7 from two-three-six, 33 from one-two-five, and seven
earlier direct determinant-seven covers, with the final seven determinant-
seven forms supplied by `Algebra.det_seven_covers`. These client groups
partition the 201 targets, although their classical converse dependencies
overlap. The other six selected rank-four forms remain the kernel-certified
exact-truant forms and are deliberately not called universal.

## Determinant-seven direct frontier

All 14 nonexceptional odd-`C=4` lattices now have kernel-checked conditional
universality proofs. The first seven are the inexpensive direct reductions:

- `(r,c)=(0,4)` and `(3,8)` contain covered weighted-`d=4` lattices at
  index two and therefore reduce to three squares;
- `(1,3)` contains a covered weighted-`d=5` lattice at index two;
- `(3,7)` contains a covered weighted-`d=3` lattice at index two;
- `(0,6)` contains one-two-six, and an orthogonal norm-14 shift carries
  every base obstruction after the two initial witnesses to an admissible
  one-two-six residual;
- `(1,4)` has two index-two neighbor cosets.  The even coset is
  one-two-six, while the odd coset is recovered from `16b+6` represented by
  one-two-three.  A rational isometry of `x²+2y²+3z²` with denominator two
  makes the two outer coordinates odd and supplies integral coordinates;
- `(1,5)` is the auxiliary odd-`C=5` `(r,c)=(1,4)` form after swapping the
  last two coordinates.  It reuses the generic odd-`C=5` tail and a
  generated, 20-rows-per-theorem finite prefix.

The final seven, `(0,7)`, `(1,6)`, `(1,7)`, `(2,8)`, `(2,9)`, `(3,10)`,
and `(3,11)`, use the precise restricted parent interface
`Matrix.DetSevenSafeConverse`. Deterministic modulo-588 certificates choose
an orthogonal shift whose positive residual lies in that safe set, while
explicit kernel-checked tables cover the bounded branch. Six forms use the
determinant-seven section directly. For `Q_(1,7)`, odd targets use the same
norm-315 construction; even targets use the alternative section
`2(x²+2y²+2yz+5z²)` and its norm-90 complement, reducing through the proved
odd-five/three-squares equivalence. `Matrix.detSeven_seven_universal`
collects the seven theorems while retaining both classical inputs.

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

The dependency audit and determinant-three pilot are now recorded in
`PROOF_TERNARY_CONVERSE_DEPENDENCIES.md`. They settle the route-selection
question conservatively: even if both remaining elementary pilots succeed,
four non-three-squares regular forms remain, feeding 57 selected rank-four
clients. Shared infrastructure is therefore justified without waiting for
those pilots.

1. Build a bounded rank-three genus development rather than a general
   arbitrary-rank theory. Its first end-to-end target is
   `Matrix.TripleSquaresConverse`.
2. A genus route must separately prove integral local representability,
   representation by some class in the genus, and the relevant one-class
   genus results for each participating form.  It is mathematically valid for
   one-two-five: the determinant-ten form is alone in its genus.  The three
   determinant-ten classes used in the Mordell proof are not thereby
   genus-mates; the finite class elimination belongs to that construction.
3. The verified determinant-three pilot proves that a reduced binary
   determinant-three complement is one of only
   `[[1,0],[0,3]]` and `[[2,1],[1,2]]`. This makes the finite table cheap and
   identifies short-vector geometry, dyadic integral equivalence, and
   local-to-genus representation as the actual risks. The complete
   human-readable proof in `PROOF_TRIPLE_SQUARES_CONVERSE.md` goes further:
   a Hermite/projection bound forces the required norm-one splitting, so no
   general ternary reducer is needed for this first target.
4. A Mordell route shares quadratic-residue, reciprocity, CRT, reduction, and
   class-enumeration machinery across several forms.  However, its required
   prime-in-arithmetic-progression input is a restricted Dirichlet theorem,
   and may dominate the entire formalization cost.  It must be budgeted as
   the route's principal risk, not as a routine sublemma.
5. The determinant-seven odd parent is excluded from either blanket
   regularity route.  Its 14 rank-four clients require direct quaternary or
   restricted-coset work.

The two index-lattice pilots remain worthwhile because they can remove 15
clients, but they no longer gate the shared route. The first implementation
slice follows `PROOF_TRIPLE_SQUARES_CONVERSE.md`: local eligibility,
Hasse--Minkowski and lattice patching, the low-dimensional Hermite bound,
the norm-one split, and the 2-adic separation. Hasse--Minkowski is itself a
large shared input—standard proofs use Dirichlet or equivalent reciprocity
machinery—so it receives its own gate. Mordell remains a form-specific
fallback.

## Execution order

1. **Done:** prove the odd-`C=5` represented-set reduction.
2. **Done:** use an integral base shear plus 586 generated,
   kernel-checked finite witnesses to discharge all 12 selected odd-`C=5`
   covers from `Matrix.ThreeSquaresConverse`.
3. Pilot the two-three-six and one-three-six index-lattice recoveries. Keep a
   pilot only if it eliminates the existing exact local converse without
   adding an equally deep replacement.
4. **Done:** all 14 nonexceptional determinant-seven clients have direct
   conditional covers. The final seven use the reviewed restricted-safe-set
   proof and generated finite certificates, not a false regularity converse.
5. **Done:** the exact dependency audit and determinant-three finite
   classification pilot select a bounded shared class-one/genus development.
   See `PROOF_TERNARY_CONVERSE_DEPENDENCIES.md` and
   `Algebra.ternary_genus_determinant_three_pilot`.
6. **Done:** write the complete determinant-three proof specification in
   `PROOF_TRIPLE_SQUARES_CONVERSE.md`, including every elementary local,
   patching, geometry-of-numbers, binary-classification, and 2-adic step.
   Hasse--Minkowski is the single precisely stated substantial classical
   input.
7. Implement that proof end to end. Start with exact rank-three
   lattice/equivalence objects and the local lemmas; use the Hermite
   projection argument rather than building a general ternary reducer.
8. Preserve statement-shape guards and independent cold-library verification
   throughout: all these interfaces feed many conditional clients, so a
   silently weakened converse would have a large blast radius.

## References

- Blackwell, Durham, Thompson, and Treece,
  [A Generalization of Mordell to Ternary Quadratic Forms](https://arxiv.org/pdf/1508.02694).
  Their forms are stated to be alone in their genera; §3.6 treats
  `x²+2y²+5z²`.
- Doyle, Muskat, Pehlivan, and Williams,
  [Regular ternary quadratic forms](https://math.colgate.edu/~integers/t45/t45.pdf).
  The tables give the exact exceptional sets used by the current interfaces,
  including the odd determinant-nine form.

# Ternary converse dependency audit

## 1. Decision

The remaining classical converse debt justifies one shared, deliberately
rank-three genus development. It does **not** justify a general theory of
quadratic spaces and lattices in arbitrary rank, and it does not justify
starting with the Mordell construction for one isolated form.

The minimum useful shared development has this boundary:

1. integral positive ternary lattices, their Gram matrices, determinant,
   integral equivalence, and representation;
2. reduced ternary representatives and kernel-checked enumeration at the
   finitely many determinants actually used here;
3. local integral representation at the bad primes
   \(\{2,3,5,7\}\), with good-prime lemmas that avoid enumerating all other
   primes one at a time;
4. the theorem that an integer represented locally by a genus is represented
   by some integral class in that genus; and
5. per-form certificates identifying the relevant genus classes and their
   exact local eligibility conditions.

This route should be attempted before any Mordell-style route. The latter
adds quadratic reciprocity and primes in prescribed arithmetic progressions;
the published one-two-five construction, for example, chooses primes in
classes modulo \(1000\). Those are large dependencies that the other
converses do not otherwise need.

The three-squares converse is a separate branch. Its integral
rational-to-integral descent is already formalized, so it needs only the
existence of an admissible rational point. Forcing it through integral genus
theory would throw away completed work.

The first end-to-end genus proof is now detailed in
`PROOF_TRIPLE_SQUARES_CONVERSE.md`. It improves the G1 boundary below:
determinant three does not need a general ternary reduction algorithm.
A low-dimensional Hermite bound forces a norm-one vector, orthogonal
splitting reduces the problem to the verified binary pilot, and an explicit
primitive mod-4 invariant separates the two candidates at \(p=2\).

The determinant-seven safe converse is also not a class-number-one client.
It needs the same local/genus foundations, but its proof uses two explicitly
classified small genera and a safe-residue argument to choose the desired
class. No blanket regularity statement for its odd determinant-seven parent
is valid.

## 2. Exact interface ledger

The client counts below count selected rank-four normal forms, not textual
references to the interface.

| Interface | form or input | clients | route after this audit |
| --- | --- | ---: | --- |
| `Matrix.ThreeSquaresConverse` | \(x^2+y^2+z^2\), excluding \(4^a(8b+7)\) | 115 | Finish rational existence; reuse the completed integral descent. |
| `Matrix.TripleSquaresConverse` | \(x^2+y^2+3z^2\), excluding \(9^a(9b+6)\) | 9 | First class-one/genus client and the bounded pilot. |
| `Matrix.OneTwoThreeConverse` | \(x^2+2y^2+3z^2\), excluding \(4^a(16b+10)\) | 8 | Shared genus route unless a later direct reduction is genuinely cheaper. |
| `Matrix.OneTwoSixConverse` | \(x^2+2y^2+6z^2\), excluding \(4^a(8b+5)\) | 7 | Shared genus route; no elementary reduction is currently known. |
| `Matrix.OneThreeSixLocalConverse` | \(x^2+3y^2+6z^2\), with its mod-3 square condition and \(4^a(16b+14)\) exclusion | 8 | The index-three recovery succeeds: derive it from `ThreeSquaresConverse` by the explicit sign/permutation argument in `PROOF_REMAINING_TERNARY_CONVERSES.md`, Section 6. |
| `Integer.TwoThreeSixLocalConverse` | \(2x^2+3y^2+6z^2\), with its mod-3 condition and three-square exclusion | 7 | Keep the index-six recovery pilot, but budget the shared genus route. |
| `Matrix.OneTwoFiveConverse` | \(x^2+2y^2+5z^2\), excluding the two \(25^a\) families | 33 | Shared genus route. The form is alone in its genus; Mordell is the fallback, not the default. |
| `Matrix.DetSevenSafeConverse` | \(x^2+2y^2+2yz+4z^2\) on `Natural.IsDetSevenSafe` | 7 final direct covers | Reuse local/genus foundations, then formalize the two small genus classifications and the safe-class selection from the detailed proof document. |

The one-three-six recovery is now complete, while the two-three-six recovery
remains only a pilot.  Four non-three-squares one-class forms still remain,
feeding 57 selected rank-four clients. Shared infrastructure is therefore
justified without assuming the remaining pilot succeeds.

The exact obstruction predicates and the interface statements are already
kernel-visible in their respective library modules. They should remain the
public boundary while the implementation beneath them changes.

## 3. Dependency graph

The shared route is not one theorem called “genus.” It has three logically
independent inputs:

```text
integral ternary lattices
        |
        +--> reduction theorem --> finite reduced-form enumeration
        |                              |
        |                              +--> genus/class certificates
        |
        +--> Z_p lattices --> per-prime local eligibility
                               |
                               +--> represented by the genus
                                              |
genus/class certificate + represented by the genus
                                              |
                                   exact converse for one form
```

For a class-number-one form, the last step is short: local eligibility gives
representation by some class in the genus, and the class certificate
identifies that class with the desired form. For determinant seven, the genus
certificate has multiple classes and the residue argument must select the
desired one.

This distinction matters for planning:

- A finite list of reduced forms does not prove local-to-global
  representation.
- A local-to-genus theorem does not prove that a particular form represents
  the integer.
- A published list of exceptional congruence families must still be proved
  equivalent to local representability for the exact integral lattice.
- Agreement over \(\mathbb Q_p\) is too weak; these are
  \(\mathbb Z_p\)-lattice statements.

Jones and Pall make the same separation: congruential eligibility first
gives representation by some form in the genus, while the one-class
calculation identifies that form. Their proofs of one-class results use
tables of reduced forms plus integral transformations, not determinant alone.

## 4. The determinant-three pilot

`Algebra.ternary_genus_determinant_three_pilot` formalizes the complete finite
arithmetic core of the smallest class computation.

For a reduced positive binary Gram matrix

\[
  \begin{pmatrix}a&b\\b&c\end{pmatrix}
\]

with \(b\ge 0\), reduction gives \(2b\le a\le c\), and determinant three gives
\(ac=b^2+3\). The kernel-checked proof first derives \(a\le2\):

\[
  4b^2\le a^2,\qquad a^2\le b^2+3
  \quad\Longrightarrow\quad 3a^2\le12.
\]

It then proves that the only possibilities are

\[
  (a,b,c)=(1,0,3)
  \quad\text{or}\quad
  (a,b,c)=(2,1,2).
\]

Thus the downstream determinant-three table is tiny. The second lattice is
even and the first is odd, so a 2-adic parity invariant distinguishes them.

`PROOF_TRIPLE_SQUARES_CONVERSE.md` now supplies the missing human proof:

1. a two-dimensional Hermite bound and projection argument give
   \(m^3\le64D/27\), forcing a norm-one vector when \(D=3\);
2. the norm-one vector splits integrally and leaves a binary complement of
   determinant three;
3. the two binary candidates give ternary lattices separated by a primitive
   norm-divisible-by-four invariant over \(\mathbb Z_2\); and
4. Hasse--Minkowski, explicit equal-norm reflections, and finite lattice
   patching prove representation by a class in the genus.

Thus the finite table and the ternary reduction problem are both removed
from the determinant-three critical path. The foundational costs are
\(p\)-adic arithmetic, rational Hasse--Minkowski, local-lattice patching,
and the elementary Euclidean-lattice geometry used by the short-vector
bound. Hasse--Minkowski remains a major item: standard explicit proofs over
\(\mathbb Q\) use Dirichlet's theorem or package comparable work into global
reciprocity. It is nevertheless shared infrastructure, including with the
open rational-existence step for three squares.

## 5. Formalization slices and gates

### G0. Exact objects and statement guards

- Define only rank-three integral Gram matrices/lattices at first.
- Define integral equivalence by a unimodular change of basis.
- Define local equivalence and local representation over
  \(\mathbb Z_p\).
- Restate each existing public converse from these notions and guard the
  elaborated statement against accidental weakening.

**Gate:** the new statements imply the current interfaces without changing
their source-level or elaborated propositions.

### G1. Reduction and certified enumeration

- For determinant three, formalize covolume, orthogonal projection, the
  two-dimensional Hermite bound, and the resulting
  \(m^3\le64D/27\) ternary bound.
- Split the resulting norm-one vector and connect its binary complement to
  the proved classification pilot.
- Formalize the primitive mod-4 invariant separating the two candidates
  over \(\mathbb Z_2\).
- Defer a general rank-three reducer/enumerator until a later determinant
  actually needs it.

**Gate:** independently reproduce the Jones–Pall one-class result for
\(x^2+y^2+3z^2\).

### G2. Local integral arithmetic

- Build only the \(p\)-adic integer and lattice facts demanded by the bad
  primes in this ledger.
- Treat \(p=2\) as its own work package; do not hide dyadic Jordan arguments
  behind odd-prime APIs.
- Prove good-prime stability once.
- For determinant three, prove that the exact exclusion
  \(9^a(9b+6)\) is equivalent to local eligibility.

**Gate:** derive the local eligibility predicate for triple squares rather
than assuming Dickson's represented-set theorem.

### G3. Integral local-to-genus theorem

- Prove Hasse--Minkowski for the rational form
  \(x^2+y^2+3z^2-nw^2\), or discharge a guarded general theorem.
- Budget the required Hilbert reciprocity and prime-existence input
  explicitly; do not count Hasse--Minkowski as a small wrapper.
- Formalize the explicit reflection carrying equal nonzero-norm vectors to
  each other.
- Patch finitely many altered \(\mathbb Z_p\)-lattices through a finite
  quotient and the Chinese remainder theorem.
- Conclude that an integer represented over every \(\mathbb Z_p\) and over
  \(\mathbb R\) is represented by some integral class in the genus.
- Keep this separate from every class-number computation.

**Gate:** combine G1–G3 to prove `Matrix.TripleSquaresConverse` with no new
classical interface.

### G4. Reuse across the remaining forms

- First test whether the determinant-three norm-one splitting generalizes at
  determinants \(6,10,12,18,36\); introduce a reducer/enumerator only where
  the small-vector bound leaves more than a binary complement.
- Prove the exact local predicates already exposed by the library.
- Discharge the class-one cases.
- Implement the completed one-three-six recovery, and continue the
  two-three-six index-lattice experiment; if the latter succeeds with only
  elementary transformations, delete its deep client.

**Gate:** discharge the remaining regular-form interfaces, or record a precise
counterexample to the class-one route and use the published specialized
regularity proof for that form.

### G5. Determinant seven

- Reuse G0–G3.
- Certify the determinant-seven and determinant-fourteen genus tables used
  in `PROOF_15_THEOREM_REMAINING.md`.
- Formalize the safe-residue class-selection argument.

**Gate:** prove `Matrix.DetSevenSafeConverse`; do not assert regularity of the
parent form.

## 6. Stop conditions

Pause and reconsider the route if any of these occurs:

- G1's covolume/projection proof requires a much more general analytic or
  Euclidean-lattice library than its elementary paper proof suggests.
- G2 shows that the exact dyadic predicates require substantially more
  theory than the current forms share.
- Hasse--Minkowski and its reciprocity/prime-existence dependencies are not
  reusable enough across three squares and the regular ternary forms to
  justify their cost.
- G3 expands beyond Hasse--Minkowski and finite lattice patching into a
  spinor-genus development not used by the determinant-three proof.
- Enumeration finds that a target form is not alone in its genus and the
  published regularity proof requires a form-specific argument of comparable
  cost to Mordell.

Absent one of these findings, the next mathematical target is G0 followed by
the determinant-three G1 slice—not a one-two-five Mordell proof.

## References

- B. W. Jones and G. Pall,
  [*Regular and semi-regular positive ternary quadratic forms*](https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/5599-11511_2006_Article_BF02547347.pdf).
  In particular, pp. 166–173 separate representation by a genus from the
  one-class calculation and explicitly list \((1,1,3)\) among the base
  one-class genera.
- P. Doyle, J. Muskat, A. Pehlivan, and K. S. Williams,
  [*Regular ternary quadratic forms*](https://math.colgate.edu/~integers/t45/t45.pdf).
  Its tables record the exact exceptional sets used by the current
  interfaces; it cites Dickson's classical represented-set results.
- S. Blackwell, G. Durham, K. Thompson, and T. Treece,
  [*A Generalization of Mordell to Ternary Quadratic Forms*](https://arxiv.org/pdf/1508.02694).
  Section 4.1 exhibits the one-two-five Mordell route and its auxiliary
  prime conditions modulo \(1000\).

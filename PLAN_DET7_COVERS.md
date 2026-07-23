# Plan: the final determinant-seven rank-four covers

## Purpose and scope

`PROOF_15_THEOREM_REMAINING.md` gives the detailed mathematical proof for the
last seven selected rank-four forms. This file is the implementation plan for
that proof. It does not reproduce the mathematics; section numbers below refer
to the proof document.

The deliverable is conditional universality for

```text
Matrix.squarePlusDoubleSquareOddRankFourRepresentative(4, r, c)
```

at

```text
(r,c) = (0,7), (1,6), (1,7), (2,8), (2,9), (3,10), (3,11).
```

Together with the 194 existing conditional covers, this reaches all 201
rank-four universality targets in the selected escalator classification. It
does **not** make the full Fifteen Theorem unconditional: the new
determinant-seven converse and the already isolated ternary converses remain
explicit classical inputs.

## Decision: expose the smallest honest classical interface

The rank-four proofs should not wait for a general theory of genera. Carry
Proposition 2.5 of the proof document as a named interface, parallel to
`Matrix.ThreeSquaresConverse` and `Matrix.OneTwoFiveConverse`.

Call the interface `Matrix.DetSevenSafeConverse`, not
`DetSevenGenusRepresentation`. Its statement says nothing about genera, and a
future proof could use Jones's theorem, the Pall--Kaplansky route reconstructed
in Section 2, or another argument.

The source-level definitions are to have exactly this mathematical content:

```text
Natural.IsDetSevenSafe(n) :=
  Natural.modulo(n, 12) ≠ 7
  ∧ Natural.modulo(n, 12) ≠ 10
  ∧ Natural.modulo(n, 49) ≠ 0
  ∧ Natural.modulo(n, 49) ≠ 21
  ∧ Natural.modulo(n, 49) ≠ 35
  ∧ Natural.modulo(n, 49) ≠ 42

Matrix.DetSevenSafeConverse :=
  ∀ (n : ℕ). n ≥ 1 → Natural.IsDetSevenSafe(n) →
    Matrix.Represents(
      Matrix.squarePlusDoubleSquareOddForm(4),
      (n : ℤ))
```

The explicit positivity premise is intentional. It matches Proposition 2.5,
documents the theorem's domain, and avoids making clients depend on the
incidental fact that zero fails the conservative modulo-49 test.

This interface is one-way. No client may use its converse or claim that
`Natural.IsDetSevenSafe` is the exact represented set. In particular, the
predicate conservatively rejects all multiples of 49.

The full derivation in Section 2 remains mathematical documentation for the
classical debt. If genus theory is formalized later, it should prove this
interface without changing any of the seven clients.

## Lock the interface before adding clients

A false or weakened converse could silently validate every final cover.
Ordinary successful verification is not a sufficient guard.

Add a small test module and an elaborated-output check that lock all of the
following:

1. `Natural.IsDetSevenSafe` contains all six exclusions, with `12` and `49`
   in the divisor positions of `Natural.modulo`.
2. `Matrix.DetSevenSafeConverse` quantifies over every natural `n`, requires
   `n ≥ 1` and `Natural.IsDetSevenSafe(n)`, and concludes representation by
   `Matrix.squarePlusDoubleSquareOddForm(4)` of `(n : ℤ)`.
3. The conclusion has not collapsed to an identity or to representation by a
   form supplied as an unconstrained argument.
4. Each final universality theorem visibly retains the interface arguments on
   which it depends.

Follow the existing `kernel dump cache` pattern in
`scripts/check_carrier_normal_form.sh` and
`scripts/check_matrix_ergonomics_statements.sh`. Add a dedicated
`scripts/check_det7_statement_shapes.sh` and a Makefile target rather than
folding these high-blast-radius checks into an unrelated script.

The test module must also make the predicate visibly non-vacuous:

- positive controls: `1`, `2`, and `13` are safe;
- modulo-12 negative controls: `7` and `10` are not safe;
- valuation-one modulo-49 controls: `21`, `35`, and `42` are not safe;
- the deliberately conservative multiple-of-49 control: `49` is not safe.

Use direct arithmetic proofs for these controls. Do not register them as
`automatic`; tests and generated modules should cite named facts explicitly.

## Gap analysis against the current library

| Proof component | Existing support | New formal work |
| --- | --- | --- |
| Least positive exception (Section 1) | `Matrix.IsTruant`, `Matrix.truant_exists`, and the `positive`, `missed`, and `represents_below` projections in `Algebra/truant` | A minimal squarefree predicate and the lemma that a truant of an integral quadratic form is squarefree |
| Scaling in the squarefree argument | `Matrix.quadraticForm_scale` and existing scaling arguments in the rank-four covers | Package the contradiction from `n=d²q`, representation of `q<n`, and coordinate scaling; avoid new factorization theory |
| Orthogonal residual principle (Lemma 1.2) | `Matrix.diagonalExtension_represents_parent_plus_square` is the model, and `Matrix.represents_by_witness` is the final constructor | A lemma for a represented ternary section plus an explicit orthogonal vector inside the same rank-four lattice |
| Determinant-seven ternary theorem (Section 2) | The form is already `Matrix.squarePlusDoubleSquareOddForm(4)` | `Natural.IsDetSevenSafe`, `Matrix.DetSevenSafeConverse`, controls, and statement-shape guard; no genus implementation in this plan |
| The modulo-588 covers (Section 3) | `Natural.modulo`, quotient/remainder lemmas, and `finite_check` | Kernel proofs of the six generic rows and the odd exceptional row, generated or reflected from all 588 residues |
| Odd-\(C=4\) coordinate algebra (Section 4) | `Matrix.squarePlusDoubleSquareOddRankFourRepresentative_coordinateTuple_computes` and many existing odd-\(C\) clients | One general orthogonal-vector/value lemma, then seven small specializations recording the norms |
| Six generic universality proofs (Section 5) | Existing conditional rank-four universality modules provide the proof style | Assemble truant, squarefree, unsafe, CRT residual, positivity, converse, and orthogonal lift |
| Alternative section \(K=2H\) (Section 6.1) | Tuple witnesses and `ring` handle the coordinate identities | Prove the three-vector embedding, its Gram matrix, the norm-90 orthogonal vector, and transfer of representations into \(Q_{1,7}\) |
| \(H\) and three squares (Section 6.2) | Reuse `Integer.odd_five_representation_of_three_squares`, `Matrix.squarePlusDoubleSquareOddForm_five_represents_of_three_squares`, and `Matrix.odd_five_converse_of_three_squares` from `Algebra/odd_five_converse_reduction` | Only the scaling-by-two wrapper needed for \(K=2H\); do not re-prove the odd-five reduction |
| Exceptional parity argument (Sections 6.3--6.4) | `Matrix.ThreeSquaresConverse`, natural divisibility/modulo arithmetic | The small 2-adic/parity lemmas giving the even bound 90 and the odd norm-315 residual argument |
| Finite prefixes (Section 7) | Generated witness modules, `Matrix.represents_by_witness`, chunks of at most 20 rows, aggregate `finite_check` theorems, and generator `--check` modes | A determinant-seven generator, emitted modules, aggregate theorems, and a Makefile drift check |

The general theorem `Matrix.squarePlusDoubleSquareOddRankFourRepresentative_universal`
from `Algebra/rank_four_completed_cover_universality` is useful only if the
determinant-seven argument is naturally packaged as an `OddCompletedCover`.
Do not force the proof through that interface: the truant/residual argument
may be clearer as a direct `Matrix.IsUniversal` proof.

## Formal statement of the elementary infrastructure

### Squarefree truants

There is no current squarefree API to reuse. Introduce only what this proof
needs, for example

```text
Natural.IsSquarefree(n) :=
  ∀ (d : ℕ). d ≥ 2 → ¬(d * d ∣ n).
```

Then prove:

```text
Matrix.IsTruant(A, n) → Natural.IsSquarefree(n).
```

The proof is elementary. If `n=d²q` with `d≥2`, then positivity gives
`1≤q<n`; the truant property represents `q`, and scaling its vector by `d`
represents `n`. Keep this lemma independent of the seven forms so later
escalator arguments can reuse it.

### Residual lifting

Prove a reusable scalar-coordinate lemma with the following content:

```text
g(x,y,z) = a
Q(v) = m
v is orthogonal to the embedded ternary section
──────────────────────────────────────────────
Q((x,y,z,0) + t*v) = a + m*t².
```

For the present family it is acceptable, and probably clearer, to state the
lemma directly for
`Matrix.squarePlusDoubleSquareOddRankFourRepresentative(4,r,c)` and the
explicit vector

```text
v = ⟨0, -4*r, r, 7⟩
```

when `r≠0`, with `v=⟨0,0,0,1⟩` for `r=0`. The proof should be a short
`ring` calculation followed by `Matrix.represents_by_witness`.

Record the seven norms in named, kernel-checked specializations:

```text
(0,7)  ↦ 7
(1,6)  ↦ 266
(1,7)  ↦ 315
(2,8)  ↦ 280
(2,9)  ↦ 329
(3,10) ↦ 238
(3,11) ↦ 287
```

This makes any transcription error in the mathematical table local and
auditable.

### Modulo-588 certificates

Formalize Lemmas 3.1 and 3.2 with exactly the choice sets and count vectors
in the proof document. The executable checker
`scripts/check_det7_human_proof.js` remains the discovery and audit artifact;
it is not a formal certificate.

The formal route should be:

- enumerate residues `0 ≤ a < 588`;
- discharge non-source residues from the squarefree residue restrictions or
  from `Natural.IsDetSevenSafe(a)`;
- for each remaining residue, cite one of the listed `t` values and produce a
  residue `b<588` congruent over the integers to `a-m*t²`, with
  `Natural.IsDetSevenSafe(b)`;
- lift the congruence result from `a` to arbitrary `n`; and
- only after a separate inequality proves `m*t²<n`, identify the natural
  residual `n ∸ m*t²` and transport safety to it.

Do not encode `a-m*t²` with natural monus inside the 588-case certificate:
for small residue representatives that would clamp a negative integer to
zero and compute the wrong residue. Use integer congruence, or an equivalent
nonnegative offset modulo 588, for the finite calculation.

The output must preserve the source counts from the reviewed proof:

```text
m=7:   100,10,5,1,1
m=266: 94,9,10,1,2,1
m=280: 93,9,7,4,2,2
m=329: 94,9,9,2,1,2
m=238: 94,9,10,1,2,1
m=287: 93,9,8,3,2,2
m=315, odd sources: 48,5,6,1,2,1
```

The modular lemma must not assert positivity of `n-m*t²`; that is a separate
inequality in the universality proof.

## Finite-certificate scale gate

Do not immediately generate a witness theorem for every target in the
conservative intervals of Section 7. Those intervals contain 102,312
positive targets in total.

The universality proofs only reach the finite branch for a least exception.
Filtering to squarefree targets that fail `Natural.IsDetSevenSafe` reduces
the six generic intervals to:

| form | bound | possible least-exception targets |
| --- | ---: | ---: |
| \(Q_{0,7}\) | 252 | 48 |
| \(Q_{1,6}\) | 9576 | 1738 |
| \(Q_{2,8}\) | 22680 | 4104 |
| \(Q_{2,9}\) | 26649 | 4819 |
| \(Q_{3,10}\) | 8568 | 1556 |
| \(Q_{3,11}\) | 23247 | 4205 |

For \(Q_{1,7}\), use the proof's parity split: even candidates are needed
only through 90, while odd candidates are needed through 11,340. After the
same squarefree/unsafe filtering, this leaves 1,105 candidates. The
conservative total is therefore still 17,575 explicit witness rows.

That is too large to accept without measurement. Before committing generated
library modules, implement a generator prototype and compare these routes:

1. **Filtered explicit witnesses.** Emit facts only for the 17,575 states
   compatible with the truant hypotheses. Noncandidate states close by
   contradiction from squarefreeness, safety, or parity.
2. **A compact bounded certificate.** Test whether `finite_check` or a small
   proof-producing reflection layer can carry the witness table without one
   source theorem per target.
3. **Sharper reviewed bounds.** Reconstruct Bhargava's smaller cutoffs only
   if the human proof is first amended with the exact argument and reviewed.
   Do not silently substitute published table bounds for the conservative
   bounds proved in `PROOF_15_THEOREM_REMAINING.md`.

Choose a route only after recording:

- emitted source lines, theorem count, and module count;
- verification time for each generated chunk and its aggregate;
- peak size of a theorem's local lemma context;
- regeneration and `--check` time.

The current generated-cover discipline remains mandatory:

- at most about 20 witness rows per leaf theorem unless measurement supports
  another small limit;
- aggregate modules cite leaf theorems by name;
- generated theorems are not `automatic`;
- the search program emits explicit integer witnesses that the kernel checks;
- deterministic output and a `--check` drift mode;
- no four-hour monolithic kernel job.

If all three routes are still impractical, stop at this gate and revise the
mathematical finite argument. Do not bury the cost under thousands of
unchecked or automatically visible facts.

## Execution stages and commit boundaries

### D0 — Interface and guards

- Add `Natural.IsDetSevenSafe`.
- Add `Matrix.DetSevenSafeConverse`.
- Add the positive and negative controls.
- Add the elaborated statement-shape script and Makefile target.

Acceptance:

- all controls verify;
- the dump guard sees the exact predicate and converse shapes;
- no rank-four client has yet been added.

Commit this stage independently because every later theorem trusts it.

### D1 — Elementary truant and residual infrastructure

- Add the minimal squarefree predicate.
- Prove that a truant is squarefree.
- Prove the odd-\(C=4\) orthogonal residual lemma.
- Prove the seven norm specializations.

Acceptance:

- each norm is verified by the kernel from the actual matrix formula;
- the generic lift concludes the original target, not a definitionally
  weakened identity;
- reusable lemmas do not mention the final finite bounds.

### D2 — Modulo-588 cover

- Generate or hand-package the seven residue lemmas.
- Verify the source counts and choice sets against
  `scripts/check_det7_human_proof.js`.
- Add regeneration drift checking.

Acceptance:

- all 588 residues are accounted for;
- the six generic lemmas require squarefreeness only through the consequences
  `n mod 4 ≠ 0` and `n mod 49 ≠ 0`;
- the exceptional lemma has the explicit odd premise;
- no lemma smuggles in positivity of a subtracted residual.

### D3 — Finite-certificate pilot and decision

- Prototype all three finite routes on \(Q_{0,7}\).
- Prototype the winning route on the largest interval, \(Q_{2,9}\), before
  generating the remaining forms.
- Record the measurements and chosen representation in this plan.

Acceptance:

- the pilot's formal theorem has the hypotheses actually available for a
  least exception;
- a deliberately omitted candidate makes the aggregate fail;
- regeneration is deterministic;
- verification cost is compatible with ordinary laptop development.

This is a mandatory decision point, not merely a performance polish.

### D4 — Six generic covers

- Generate the accepted finite certificates for the six intervals.
- Prove the six conditional universality theorems from
  `Matrix.DetSevenSafeConverse`.
- Add an aggregate theorem for the six generic forms.

Each proof follows Theorem 5.1 exactly:

```text
nonuniversal
→ choose truant n
→ n squarefree
→ g does not represent n
→ n is not safe
→ choose residual t modulo 588
→ either n is in the finite certificate
   or the positive safe residual is represented by g
→ lift through the orthogonal vector
→ contradiction.
```

### D5 — Exceptional cover

- Formalize the alternative section \(K=2H\) and its norm-90 complement.
- Reuse the existing odd-five/three-squares reduction.
- Prove the even least-exception bound.
- Generate the accepted even/odd finite certificates.
- Prove `Q_(1,7)` universal from both
  `Matrix.DetSevenSafeConverse` and `Matrix.ThreeSquaresConverse`.

The theorem signature must retain both arguments. A statement guard must fail
if either disappears.

### D6 — Rank-four assembly and documentation

- Add one final theorem collecting all seven covers.
- Wire it into the selected rank-four coverage theorem so the count becomes
  201/201 conditional universality targets plus six exact-truant forms.
- Update `PLAN_TERNARY_CONVERSES.md`, `PLAN_15_THEOREM.md`, and
  `library/Algebra/fifteen-theorem.md` with the precise new boundary.
- Keep `PROOF_15_THEOREM_REMAINING.md` as the reviewed mathematical source;
  amend it only if D3 chooses a sharper mathematical argument.

The final assembly theorem should take the union of all still-live classical
interfaces explicitly. It must not be named or documented as an
unconditional Fifteen Theorem.

## Verification policy

At every commit:

- verify every changed handwritten module and every generated leaf/aggregate
  affected by the commit;
- run `scripts/check_det7_human_proof.js`;
- run the determinant-seven statement-shape guard;
- run all relevant generator `--check` modes;
- inspect generated diffs for theorem-name drift and accidental `automatic`
  declarations.

The current project policy delegates full cold `make library` checks to the
independent verification process. Do not launch a redundant cold build on
the development laptop unless that policy changes. A failure reported by the
independent process blocks the next stage and is fixed before further
mathematical commits.

Before declaring D6 complete, compare elaborated theorem statements against
the pre-det7 baseline. Verification success alone does not detect silent
theorem weakening.

## Completion criteria

This plan is complete only when:

1. all seven selected forms have kernel-checked conditional universality
   theorems;
2. the six generic theorems depend only on
   `Matrix.DetSevenSafeConverse`;
3. the exceptional theorem depends on
   `Matrix.DetSevenSafeConverse` and `Matrix.ThreeSquaresConverse`;
4. all finite claims are backed by explicit kernel-checked certificates and
   deterministic drift checks;
5. the interface and client statement guards pass;
6. the selected rank-four ledger reports 201/201 conditional universality
   targets without erasing the six exact-truant forms; and
7. documentation still identifies `Matrix.DetSevenSafeConverse` as an
   undischarged classical theorem, rather than presenting the full Fifteen
   Theorem as unconditional.

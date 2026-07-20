# Plan: matrix proof ergonomics for the Fifteen Theorem

This is a bounded infrastructure plan prompted by the first rank-three
isometry calculation. It is not a general linear-algebra roadmap and it is not
an open-ended tactic project. Its purpose is to make the repeated matrix
computations in the Fifteen Theorem proportional to their mathematics before
the rank-four classification multiplies them.

The target experience is:

> For a symbolic change of basis, the author states the structural facts and
> lets a noncommutative ring normalizer perform the distributive bookkeeping.
> For a small concrete change of basis, the author supplies the matrix and its
> inverse and lets verified computation check the products.

Every generated proof remains an ordinary kernel-checked term.

## Why this work is on the critical path

The first top-shear orbit exposed three different costs.

| Proof obligation | Current evidence | Recurrence risk |
|---|---|---|
| Identify one structured matrix with another | `Matrix.topUnit_eq_outerProduct_topBasis` occupies roughly 120 source lines | Every new block constructor otherwise needs an entrywise inclusion/top split |
| Expand a symbolic pullback | `Matrix.topShear_pullback_diagonalExtension` occupies 139 source lines; its central calculation manually applies transpose, distributivity, identity, and reassociation laws | Every symbolic shear or elementary basis operation repeats the same noncommutative algebra |
| Check a small explicit isometry | The current library has only `Matrix.equal_of_entries`; fixed-size candidates descend to `NaturalsBelow` cases and scalar calculations | Rank three has dozens of raw candidates and rank four is expected to have hundreds of isometry classes |

The recent two-unit-border mathematics commit added 772 lines across its proof
and build-manifest changes. Some of those lines are reusable mathematics, but
the final theorem is much shorter than the matrix scaffolding required to
reach it. That ratio is acceptable once; it is not acceptable as the normal
cost of rank-four deduplication.

The problem is not scalar arithmetic. Once a goal reaches an Integer entry,
`ring` works well. The missing layers are:

1. extensionality at the same block level in which the matrix was constructed;
2. normalization for a ring whose multiplication is not commutative; and
3. bounded verified evaluation of closed, small matrix expressions.

## Execution boundary

The remaining four one-unit borders over `x²+y²` should first be finished with
the existing shear theorem. They are expected to collapse to
`x²+y²+2z²`; this is useful mathematics and a final control sample for the
current experience.

Start this ergonomics plan immediately after that orbit and before a sustained
attack on the 23 candidates over `x²+2y²`. It must be complete, deliberately
stopped, or explicitly deferred before rank-four enumeration begins.

## Scope

### In scope

- A block-level extensionality API for `(1+n) × (1+n)` matrices.
- Focused formulas for the existing `borderedAssembly`,
  `diagonalExtension`, outer-product, and top-shear constructions.
- An explicit noncommutative ring-normalization tactic, if the probe confirms
  that it substantially shortens the symbolic pullback.
- A bounded tactic for equality and inverse checks on small concrete matrices,
  if finite-index enumeration can be made reliable without a new dependent
  programming project.
- Applying the result to representative Fifteen-Theorem isometry proofs and
  measuring the reduction.

### Out of scope

- New kernel reduction rules or trusted reflection.
- A matrix literal syntax.
- Searching for an isometry or inverse. The author or generator still supplies
  the witness.
- Gaussian elimination, determinant automation, Smith or Hermite normal form,
  lattice reduction, or a general linear solver.
- Symbolic equality at arbitrary matrix dimensions by unfolding finite sums.
- Rewriting old verified matrix proofs merely for style.
- Changing `ring` to assume commutative matrix multiplication.
- Global `automatic` registrations for routine matrix rewrite lemmas.
- The carrier-inference gaps in polymorphic function arguments and citation
  elaboration. Those are separate elaborator work.

## Design constraints

1. **Preserve noncommutativity.** A normalizer may use additive
   commutativity, associativity of multiplication, distributivity, identities,
   inverses for addition, and supplied relations. It must never reorder the
   factors in a matrix word. `A*B = B*A` is a required negative control.
2. **Build certificates.** Tactics construct applications of existing
   `IsRing`, matrix extensionality, finite-enumeration, and scalar arithmetic
   theorems. The kernel sees no oracle result.
3. **Keep automation explicit and local.** New tactics fire only when named.
   Library lemmas are ordinary theorems unless a separately measured
   registration is indispensable.
4. **Separate symbolic from concrete computation.** Symbolic pullbacks need
   free noncommutative-ring normalization. Closed `3×3` and `4×4` products need
   finite evaluation. Neither mechanism should pretend to solve the other.
5. **Decline outside the supported fragment.** Symbolic dimensions, unknown
   carriers, unsupported constructors, or matrices above the configured bound
   receive a short diagnostic rather than generic proof search.
6. **Guard statement meaning.** Any refactor of an existing theorem is checked
   against its pre-change elaborated declaration, not merely re-verified.
7. **Measure before generalizing.** Each stage must shorten a live consumer or
   it does not earn a broader abstraction.

## Work plan

Status markers: `[ ]` TODO · `[~]` in progress · `[B]` blocked · `[x]` done ·
`[-]` deliberately skipped.

### M0. Freeze representative probes and the baseline `[ ]`

Create a focused `library/Test/matrix_ergonomics_test.math` before adding
machinery. It should contain:

1. a symbolic noncommutative expansion analogous to
   `(I+T) * D * (I+N)`;
2. equality of two `(1+n) × (1+n)` symmetric matrices from equal leading
   block, border column, and corner;
3. one explicit `3×3` integral matrix product and one inverse verification;
4. one pullback `Uᵀ*A*U = B` using concrete matrices.

Add negative controls for:

- attempting to prove `A*B = B*A` for arbitrary square matrices;
- invoking concrete evaluation at a symbolic dimension;
- invoking it on a dimension above its supported bound.

Record:

- source lines devoted to the current control proofs;
- direct verification time and any expensive-proof warnings;
- the elaborated statements of the control declarations;
- which expressions fail because of missing library lemmas and which fail
  because the proof language cannot perform the calculation.

Do not design a tactic from memory before this probe is recorded.

Acceptance: the baseline test and negative controls are stable, the existing
library remains green, and the measurements are written into this section.

### M1. Add block-level extensionality and congruence `[ ]`

Stay in the mathematics library for this stage.

Add the smallest API that lets proofs remain at the bordered-matrix level:

- a `Matrix.borderRow` projection, unless using the transpose gives an equally
  readable and inference-stable API;
- general extensionality for `(1+n) × (1+n)` matrices from leading block,
  border row, border column, and corner;
- a symmetric specialization that needs only leading block, border column,
  and corner;
- congruence for `Matrix.borderedAssembly`;
- characterization lemmas for the leading block, both borders, and corner of
  the existing structured constructors;
- only the addition, negation, transpose, and product block formulas demanded
  by the M0 probes.

Do not introduce a second block-matrix datatype. These are observations about
the existing `Matrix` functions and constructors.

Live acceptance:

- reprove `Matrix.topUnit_eq_outerProduct_topBasis` without an entrywise
  inclusion/top case tree in the theorem body;
- prove the M0 structured equality using the symmetric extensionality lemma;
- no new residual cleanliness leaks or global search warnings.

The target is at least a 50% reduction in the two control proof bodies. If the
API merely moves the same case split into a differently named one-use lemma,
stop and redesign it.

### M2. Prototype an explicit noncommutative ring normalizer `[ ]`

The preferred surface name is `noncomm_ring`; the final name is chosen only
after checking the parser and existing tactic vocabulary.

Normalize a ring expression to a finite sum of words:

- an atom becomes a one-letter word;
- multiplication concatenates words without sorting their letters;
- addition and negation combine integer multiplicities of identical words;
- the multiplicative identity is the empty word;
- zero terms disappear;
- the outer sum may be ordered deterministically because ring addition is
  commutative.

The certificate builder uses the supplied `IsRing` operations and laws. The
existing `Matrix.ring(c,n)` instance should make square matrices the primary
consumer, but the tactic itself should work for any `Ring.carrier`.

Required positive probe:

```text
((I + T) * D) * (I + N)
  = D + T*D + D*N + (T*D)*N
```

up to the library's precise association and addition spelling.

Required negative probe:

```text
A * B = B * A
```

must be declined, not proved.

This stage does not normalize transpose, outer products, matrix-vector
application, or finite sums. Those are rewritten to ring atoms by named
structural facts before invoking the tactic.

Acceptance:

- the symbolic M0 expansion closes with one explicit tactic call;
- generated proof terms pass ordinary kernel checking;
- the negative control remains negative;
- off-ring and unsupported goals decline immediately;
- the full test suite shows no new proof-search or elaboration regression.

Stop condition: if proof construction requires duplicating most of the
commutative `ring` implementation without a reusable certificate layer, first
extract that layer or mark M2 `[B]`. Do not land a second large, divergent
normalizer.

### M3. Build the structured pullback layer `[ ]`

Use M1 and, if successful, M2 to package the recurring change-of-basis
calculation.

Candidate lemmas, to be adjusted to the cleanest statements found by the
probes:

- expansion of `(I+T) * D * (I+N)` in an arbitrary ring;
- a pullback specialization with `T = Nᵀ`;
- the square-zero inverse of `I+N` stated in the matrix vocabulary;
- pullback formulas for an outer-product shear;
- bordered/diagonal-extension identification through block extensionality.

Then refactor `Matrix.topShear_pullback_diagonalExtension` as the live
acceptance theorem. Preserve its elaborated statement byte-for-byte at the
declaration level.

Acceptance:

- its 139-line body falls below 70 lines, with the distributive expansion
  occupying at most one tactic line or one named generic lemma;
- the theorem mentions the mathematical data (`A`, `v`, `A·v`, and
  `Q_A(v)`) rather than entry indices;
- `Matrix.topShear_invertible` uses the generic square-zero inverse without
  restating both multiplication expansions;
- focused build, full tests, error tests, clean check, and elaborated-output
  comparison all pass.

M3 is the minimum successful endpoint of this plan. Even if concrete
evaluation is deferred, the symbolic matrix layer must no longer require
manual distributive choreography.

### M4. Time-box concrete small-matrix evaluation `[ ]`

This is a probe-gated optional stage, not permission to build a general
decision procedure.

Target an explicit tactic such as `matrix_compute` with this contract:

1. the goal is equality of matrices over a supported scalar carrier;
2. both dimensions reduce to numerals no greater than a small fixed cap
   (initially 5);
3. the tactic applies matrix extensionality, exhausts the finite row and
   column indices, unfolds supported matrix constructors and finite sums, and
   sends each scalar equality to the existing scalar normalizer;
4. for invertibility, the user supplies the proposed inverse and a helper
   reduces the obligation to the two products.

The first supported expression vocabulary is deliberately small:

- matrix functions whose entries reduce at concrete indices;
- `zero`, `identity`, addition, negation, scalar multiplication,
  multiplication, and transpose;
- `outerProduct`, `borderedAssembly`, and `diagonalExtension` only if their
  existing definitions reduce without broad new machinery.

The tactic does not search for an inverse, choose a basis change, or enumerate
candidate matrices.

Acceptance:

- a concrete `3×3` inverse check is the witness plus one computation line;
- a concrete `3×3` pullback is one computation line after naming `U`, `A`,
  and `B`;
- one representative `4×4` example verifies within the agreed proof budget;
- diagnostics identify the first unsupported constructor or non-concrete
  dimension;
- full tests and clean checks remain green.

Stop condition: if exhausting `NaturalsBelow(n)` requires a new general
dependent eliminator or more infrastructure than the evaluator itself, record
the finding and mark M4 `[-]`. In that case, prefer generated entry lemmas
using the M1 API during the Fifteen-Theorem enumeration.

### M5. Validate on the Fifteen-Theorem frontier and stop `[ ]`

Apply the landed machinery to a deliberately small consumer set:

1. the top-shear proof;
2. one concrete rank-three isometry not definitionally covered by the generic
   shear theorem;
3. one representative candidate over `x²+2y²`;
4. one synthetic `4×4` isometry shaped like the future rank-four workload.

For each, record before/after:

- proof-body lines;
- number of entrywise index case splits;
- explicit calls to associativity/distributivity/identity lemmas;
- direct verification time and expensive-proof warnings.

Success criteria:

- symbolic pullbacks contain no manual distributive chain;
- concrete isometry verification contains no hand-written entry cases;
- representative proof bodies shrink by at least 50%;
- no elaborated theorem statement changes;
- no cleanliness-budget increase;
- no material full-suite performance regression.

At that point stop. Resume the Fifteen-Theorem mathematics and let real
consumers justify any further matrix automation.

## Commit and verification discipline

Use small commits:

1. M0 probes and measurements.
2. M1 library API.
3. M2 tactic and its positive/negative controls, if it passes the stop gate.
4. M3 symbolic pullback refactor.
5. M4 concrete evaluator, if it passes the probe gate.
6. M5 consumer proofs.
7. Plan/status documentation separately from mathematics or elaborator code.

For every semantic stage run:

- the focused matrix ergonomics test;
- the affected library targets;
- `make tests`;
- `make error-tests`;
- `make clean-check`;
- the carrier-normal-form and elaborated-output guards;
- `git diff --check`.

Before and after any refactor of a named theorem, compare its elaborated
statement against the pre-stage build. Successful type checking is not enough:
the earlier carrier work demonstrated that a theorem can silently collapse to
reflexivity while every ordinary gate stays green.

## Definition of done

This plan is done when symbolic matrix-ring bookkeeping is one explicit proof
step, block-structured equality stays at block level, and either:

- small concrete isometries verify by bounded checked computation; or
- the concrete evaluator has been deliberately rejected with a documented
  reason and a tolerable generated-proof fallback.

It is not necessary to automate all matrix mathematics. The stopping test is
whether rank-three and representative rank-four isometry verification now
scales with the number of mathematical candidates rather than with the number
of matrix entries and distributive rewrites.

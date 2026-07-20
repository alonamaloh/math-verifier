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

Two existing prover components are relevant and should be reused rather than
rediscovered:

- `src/elaborator/group.cpp` already builds kernel certificates for ordered
  noncommutative words, including reassociation, identity removal, and
  adjacent inverse cancellation when the whole carrier is a group;
- the `field` path in `src/elaborator/ring.cpp` already contracts commutative
  monomials using reciprocal relations constructed from caller-supplied
  nonzero evidence.

Neither component solves this problem directly. The current polynomial
normalizer sorts the factors inside each monomial, while a matrix monomial must
retain their order. But they establish both certificate-building patterns the
new mode will need.

## Execution boundary

**Reached 2026-07-20.** The four one-unit borders over `x²+y²` have been
finished with the existing shear theorem. One parameterized isometry collapses
all four to `x²+y²+2z²`, whose exact truant is 14. The proof added 776 lines
across the arithmetic lemmas, binary-form consequences, ternary
representative, orbit theorem, and cleanliness ledger. It is the final control
sample for the current matrix-proof experience.

This ergonomics plan now runs before a sustained attack on the 23 candidates
over `x²+2y²`. It must be complete, deliberately stopped, or explicitly
deferred before rank-four enumeration begins.

## Scope

### In scope

- A block-level extensionality API for `(1+n) × (1+n)` matrices.
- Focused formulas for the existing `borderedAssembly`,
  `diagonalExtension`, outer-product, and top-shear constructions.
- A noncommutative ordered-word mode of the existing `ring` tactic, if the
  probe confirms that it substantially shortens the symbolic pullback.
- A tightly restricted layer of caller-supplied, strictly reducing monomial
  relations, gated after the unconditional ordered-word mode works.
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
- Hardcoding a total `inverse(A)` operation or inverse-cancellation rule for
  matrices. `Matrix.IsInvertible(A)` currently supplies an existential inverse
  matrix and its two product equations; there is no canonical matrix inverse
  expression for the tactic to recognize.
- General equational rewriting, noncommutative Gröbner bases, or completion of
  arbitrary rewrite systems.
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
3. **Keep automation explicit and local.** The new noncommutative `ring` mode
   initially runs only for an explicit `by ring`, not from the generic
   equality battery. Library lemmas are ordinary theorems unless a separately
   measured registration is indispensable.
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
8. **Relations are evidence, not axioms.** A caller-supplied monomial rule is
   accepted only with a proof of its equality. The tactic applies that proof
   by congruence inside words and sums; it never infers nilpotency,
   invertibility, or commutation.

## Work plan

Status markers: `[ ]` TODO · `[~]` in progress · `[B]` blocked · `[x]` done ·
`[-]` deliberately skipped.

### M0. Freeze representative probes and the baseline `[x]`

Create a focused `library/Test/matrix_ergonomics_test.math` before adding
machinery. It should contain:

1. a symbolic noncommutative expansion analogous to
   `(I+T) * D * (I+N)`;
2. the square-zero specialization
   `(I+N) * (I-N) = I` from a supplied proof `N*N = 0`, first written as
   an unconditional expansion followed by substitution;
3. equality of two `(1+n) × (1+n)` symmetric matrices from equal leading
   block, border column, and corner;
4. one explicit `3×3` integral matrix product and one inverse verification;
5. one pullback `Uᵀ*A*U = B` using concrete matrices.

Add negative controls for:

- attempting to prove `A*B = B*A` for arbitrary square matrices;
- attempting to use `N*N = 0` without supplying its proof;
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

#### M0 results — 2026-07-20

The controls live in `library/Test/matrix_ergonomics_test.math`; their
elaborated declarations are guarded by
`scripts/check_matrix_ergonomics_statements.sh`. Five `ErrorTest` fixtures
cover the pending ordered expansion, false factor commutation, missing
square-zero evidence, symbolic dimensions, and the provisional dimension-six
concrete-evaluation boundary.

The warm direct verification time is **0.14 s**, with no expensive-proof
warnings. Source measurements (whole declaration, including statement) are:

| Control | Current lines | Finding |
|---|---:|---|
| symbolic `(I+T)D(I+N)` expansion | 21 | valid, but needs five explicit matrix-law calc steps |
| symmetric block equality | 124 | descends to the four entry regions; this is the M1 target |
| named concrete 3×3 product | 8 | short only because the offset's generic square-zero theorem already matches |
| named concrete 3×3 inverse | 17 | witness plus the two generic square-zero product lemmas |
| named concrete 3×3 pullback | 14 | short only because it is exactly the existing generic top-shear theorem |

The existing live consumers remain the larger measurements:
`Matrix.topUnit_eq_outerProduct_topBasis` is roughly 120 lines and
`Matrix.topShear_pullback_diagonalExtension` has a 139-line body.

The most important probe result changes the implementation diagnosis. The
repository **already has** an ordered sum-of-products certificate engine in
`proveAbstractRingAC`, including distributivity, identities, negation, and
like-word collection for `Ring.carrier(s)`. The matrix expansion nevertheless
fails with the commutative fingerprint diagnostic. Dispatch sees
`Matrix(r,n,n)`, follows its `CommutativeRing` parameter, and sends
matrix-spelled `+` and `*` to the scalar commutative normalizer, which then
atomizes the matrix-operation applications. Thus M2a is primarily a
structure-selection and maintainability task: expose the actual
`Matrix.ring(r,n)` structure to the existing ordered engine, make the engine's
role and naming accurate, and avoid creating another normalizer.

The other failures divide cleanly:

- block equality is a **missing library API**;
- arbitrary closed matrix evaluation is a **missing proof-language
  calculation mechanism** (`matrix_compute` does not exist);
- square-zero inversion itself is **not missing**:
  `Ring.one_add_square_zero_multiply_inverse` and its left-handed companion
  already package the proof once an `IsRing` witness and `N*N=0` are in
  scope. Relation-aware `ring` therefore has to beat this existing one-line
  mathematical API to justify M2b;
- the concrete pullback control is easy only because it has the exact shape
  of the generic top-shear theorem. A genuinely different explicit isometry
  still has no bounded evaluator.

### M1. Add block-level extensionality and congruence `[x]`

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

#### M1 results — 2026-07-20

The bordered vocabulary now includes `Matrix.borderRow`, general
`Matrix.bordered_extensionality`, and
`Matrix.symmetric_bordered_extensionality`. The only full inclusion/top split
is inside the general theorem. The symmetric specialization derives the row
from symmetry and the border column; consumers provide exactly the block,
column, and corner data they know mathematically.

The supporting observation API contains:

- all four faces of an outer product and of the top-basis outer product;
- leading block, both borders, and corner of `Matrix.topUnit`;
- both borders of `Matrix.diagonalExtension` (joining its existing block and
  corner faces);
- both borders of `Matrix.borderedAssembly`, plus
  `Matrix.borderedAssembly_congruence`.

No second block datatype and no global automatic registrations were added.
Addition, negation, transpose, and product projection formulas were not added:
the M0 controls did not demand them, so M1 stopped at the measured surface.

The symmetric block control falls from a 124-line baseline declaration to 16
lines (its proof body is one block-level citation). The live
`Matrix.topUnit_eq_outerProduct_topBasis` declaration falls from 103 lines to
39, a **62%** reduction, and its body has no inclusion/top case tree. Its
supporting face lemmas are independently useful observations rather than a
one-use renamed copy of the old proof. Warm control verification remains
**0.14 s**. Full tests, 71/71 error tests, statement-shape guards, and the
clean check all pass; the cleanliness budget remains 397 and no search warning
was added.

### M2a. Extend `ring` with unconditional ordered-word mode `[x]`

M0 found that most of the ordered engine already exists under the historical
name `proveAbstractRingAC`. Do not reimplement it. This stage must first audit
that engine's certificate boundaries and tests, then give it an accurate
ordered-ring name and a structure-based entry point. The new semantic work is
to recognize square matrices as the carrier of `Matrix.ring(c,n)` and route
their surface `Matrix.add`/`Matrix.multiply` expressions through that engine.

Keep the surface spelling `ring`. Choose the normalizer from the algebraic
structure that is actually available:

- when multiplicative commutativity is available, preserve the current
  commutative polynomial normalizer unchanged;
- when only `IsRing` is available, use an ordered-word polynomial normalizer;
- when no ring structure is available, decline as today.

The noncommutative normal form is a finite map from ordered words to signed
integer multiplicities:

- an atom becomes a one-letter word;
- multiplication concatenates words without sorting their letters;
- addition and negation combine integer multiplicities of identical words;
- the multiplicative identity is the empty word;
- zero terms disappear;
- the outer collection of words may be ordered deterministically because ring
  addition is commutative.

For a generic ring, only integer multiples of `1` are universally central
coefficients. A base-ring scalar acting on a matrix is not promoted to a
coefficient in this stage; it remains an atom or structured factor unless a
later algebra-aware extension is justified.

The certificate builder uses the supplied `IsRing` operations and laws. The
existing `Matrix.ring(c,n)` instance makes square matrices the primary
consumer. The existing behavior for an abstract `Ring.carrier(s)` must remain
intact and share the same entry point; matrix support is not a fork.

Reuse rather than fork:

- the ordered-word, reassociation, identity, congruence, and proof-chain
  machinery in `group.cpp` is the closest multiplicative precedent;
- the existing ordered implementation in `ring.cpp` is the starting point;
  audit its overlap with `group.cpp` and the commutative outer-polynomial
  machinery, extracting a shared certificate layer only where that reduces
  real duplication without destabilizing the mature commutative path;
- do not copy the current multi-thousand-line commutative normalizer and edit
  every factor sort into concatenation.

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
application, finite sums, or supplied hypotheses. Those expressions are
rewritten to ring atoms by named structural facts before invoking the tactic.

Acceptance:

- the symbolic M0 expansion closes with one explicit `ring` call;
- generated proof terms pass ordinary kernel checking;
- the negative control remains negative;
- off-ring and unsupported goals decline immediately;
- the existing commutative `ring` corpus elaborates to the same statements
  and shows no material performance change;
- the noncommutative mode is not yet called from the automatic equality
  battery, so unrelated matrix equalities gain no speculative search cost.

Stop condition: if proof construction requires duplicating most of the
commutative `ring` implementation without a reusable certificate layer, first
extract that layer or mark M2a `[B]`. Do not land a second large, divergent
normalizer.

#### M2a results — 2026-07-20

The historical `proveAbstractRingAC` engine is now
`proveOrderedRingEquality`. It remains the single certificate-producing
implementation for `Ring.carrier(s)` and square matrices; no commutative
normalizer was copied. A carrier is first resolved to an `OrderedRingView`,
then its surface operations are definitionally re-expressed through one
uniform `Ring` bundle. The first registered surface view is
`Matrix.ring(c,n)`.

The entry boundary is explicit in two independent types:

- `RingInvocation` records whether `elaborateRing` came from an explicit
  tactic or internal proof search;
- `OrderedRingViewPolicy` grants either only an existing abstract projection
  or registered surface views.

Every caller must choose a policy; there is no permissive default. Thus
`by ring` can normalize square-matrix words, while the generic equality
battery retains its old carrier set and search behavior. An ErrorTest locks
this boundary.

The engine expands by distributivity, preserves factor order, handles zero,
one, subtraction, and negation, and emits ordinary equality certificates from
the `Ring` laws. Its existing proof-directed canonical representation is a
sorted additive collection of signed ordered products: repeated equal words
represent integer multiplicity and inverse pairs cancel. This is
mathematically the finite word-to-integer map specified above, but it is not a
new data-level map. Retaining that representation avoided a second
normalizer; a compact coefficient IR should be extracted only if a measured
large-word consumer justifies changing the mature certificate path.

The required expansion is now a six-line declaration whose proof is the
single token `ring`, down from the 21-line baseline. Additional probes cover
`(I+N)(I-N)=I-N²` and ensure a rectangular product nested in a square-matrix
sum remains an opaque ordered-ring atom. `A*B=B*A`, missing square-zero
evidence, and automatic use without an explicit tactic all remain negative.

Warm verification of the focused control file is **0.14 s**, unchanged from
M0. Full tests, 71/71 error tests, and the clean check pass; the cleanliness
budget remains 397. A pre/post comparison of all 626 existing interface files
found exactly one difference, the focused Test interface that gained the new
positive declarations. All 625 unaffected interfaces were byte-identical.

### M2b. Add strictly reducing caller-supplied monomial rules `[-]`

Do this only after M2a is correct and measured. The first consumer is the
square-zero fact in the shear inverse:

```text
squareZero : N*N = 0
(I+N) * (I-N) = I by ring(squareZero)  -- spelling is provisional
```

The surface syntax is chosen during M0/M2a after inspecting how `field` accepts
side evidence. The semantic contract is more important than the spelling.

Accept only proved, oriented monomial rules of one of these forms:

```text
word = 0
word = k * shorterWord
```

where `k` is an integer coefficient and the right-hand word is strictly
shorter. Normalize the unconditional polynomial first, then reduce each word
with a deterministic strategy, carrying the supplied equality through its
left and right word context and through the outer sum by congruence.

Strict length reduction guarantees termination. Overlapping rules may make
the chosen result incomplete but cannot make it unsound: every reduction has
a kernel-checked equality certificate. Initially either reject overlapping
rules, or document the deterministic order and accept that a true goal may
decline. Do not implement critical-pair completion in this plan.

`N*N = 0` is the only required relation for this stage. A future explicit
inverse witness could supply

```text
U*V = I
V*U = I
```

as two ordinary shortening rules. Do not hardcode `inverse(U)` syntax:
`Matrix.IsInvertible(U)` is presently `∃ V. U*V=I ∧ V*U=I`, and the Fifteen
Theorem proofs use the produced matrix `V`, not an abstract inverse operation.

Acceptance:

- the square-zero M0 probe closes with one relation-aware `ring` call;
- omitting the relation keeps the negative control negative;
- rules are used only in the proved direction supplied by the caller;
- `A*B = B*A` remains negative even in the presence of unrelated rules;
- malformed, non-monomial, non-decreasing, or carrier-mismatched rules receive
  a focused diagnostic;
- the unconditional M2a mode remains unchanged and independently testable.

M2b is optional for the minimum plan endpoint. If its proof plumbing begins to
grow into arbitrary equational rewriting, retain the two-line
`by ring; by substituting squareZero` proof style and mark M2b `[-]`.

#### M2b decision — deliberately skipped 2026-07-20

The required consumer does not justify the mechanism. The library already has
both noncommutative square-zero inverse directions as
`Ring.one_add_square_zero_multiply_inverse` and
`Ring.one_add_square_zero_inverse_multiply`. M3 can expose these once in the
matrix vocabulary, after which a matrix consumer supplies `N²=0` and cites one
ordinary theorem.

By contrast, relation-aware `ring` would not be a small extension of M2a. It
would require:

- changing `SurfaceRing` and every surface-expression copier/visitor to carry
  and elaborate relation arguments;
- introducing a stable data-level ordered-word IR (the present engine emits
  certificates while transforming expressions);
- validating carrier, orientation, monomial shape, strict length decrease,
  and overlaps; and
- building certified subword replacement through multiplication contexts and
  the outer additive collection.

That is a useful design if several consumers need distinct word relations, but
for the sole `N²=0` case it is a general rewrite subsystem whose result is no
shorter than the existing named mathematical API. The unconditional M2a
identity `(I+N)(I-N)=I-N²` remains available for a readable two-step
calculation. Reconsider M2b only when a real consumer presents a relation not
already captured by a reusable ring theorem.

### M3. Build the structured pullback layer `[x]`

Use M1 and M2a, plus M2b if it passes its gate, to package the recurring
change-of-basis calculation.

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
  restating both multiplication expansions; if M2b landed, refactor the
  generic `Ring.one_add_square_zero_*` lemmas themselves to use the supplied
  monomial relation rather than bypassing the generic library theorem;
- focused build, full tests, error tests, clean check, and elaborated-output
  comparison all pass.

M3 is the minimum successful endpoint of this plan. Even if concrete
evaluation is deferred, the symbolic matrix layer must no longer require
manual distributive choreography.

#### M3 results — 2026-07-20

The structured layer now separates three reusable facts.

- `Matrix.one_add_square_zero_multiply_inverse` and its left-handed companion
  expose the existing generic `Ring` results in matrix vocabulary.
- `Matrix.one_add_square_zero_invertible` packages the opposite unipotent as
  the two-sided inverse once `N²=0` is supplied.
- `Matrix.outerProductShear_pullback` takes exactly the structural data
  `Dᵀ=D`, `D·y=w`, and `⟨w,y⟩=q`; its single ordered `ring` step performs the
  unconditional expansion, while the existing outer-product laws identify
  the three cross terms.

`Matrix.collect_scaled_corner` is the small companion that reorders the
additive matrix terms and applies `Matrix.scale_add_scalar` to combine the two
corner coefficients. It replaces the former entrywise matrix extensionality
proof.

The live `Matrix.topShear_pullback_diagonalExtension` declaration is now 63
lines, with a **55-line proof body**, down from the 139-line body baseline.
It contains no entry indices and no explicit associativity, distributivity,
or identity citations. Its matrix expansion is one citation of
`Matrix.outerProductShear_pullback`. `Matrix.topShear_invertible` is now a
16-line declaration and cites the generic square-zero invertibility theorem
instead of restating both products.

During integration, an exact-shape matrix expansion theorem was briefly added
to the global library. The generic proof search then solved M2a's
explicit-tactic negative control by citing that theorem, even though it never
entered ordered `ring`. The theorem was removed and the reusable shear lemma
keeps its `ring` invocation internally. This preserves the intended automation
boundary as well as the ErrorTest that locks it.

Warm focused verification is **0.12 s**. Full tests, 71/71 error tests, and the
clean check pass, with the cleanliness budget unchanged at 397. The complete
`Algebra.escalator_tree` interface is byte-identical to the frozen pre-M3
interface; interface diffs for `matrix_ring`, `matrix_inverse`, and
`escalation` consist only of the five new supporting declarations.

### M4. Time-box concrete small-matrix evaluation `[-]`

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

#### M4 result — 2026-07-20

The probe reached the stop condition, so no `matrix_compute` syntax or
elaborator code was added.

`NaturalsBelow.enumerate(n)` supplies a complete list, but the library has no
dependent list predicate/eliminator that turns proofs at the listed elements
into `∀ (i : NaturalsBelow(n)). P(i)`. The reusable successor decomposition
`NaturalsBelow.inclusion_or_top` instead exposes an existential predecessor.
For a fixed `3×3` or `4×4` equality, a tactic would therefore need either:

- a new general dependent `List.All`-style certificate family, its lookup
  theorem, and a matrix extensionality theorem built on it; or
- tactic-side generation of nested existential case trees, transports, and
  scalar subgoals.

The first option is a general dependent-programming addition whose design and
library placement are larger than the bounded evaluator. The second makes the
elaborator own a fragile proof-language case compiler. Both violate this
stage's probe gate and the request to keep the tactic architecture durable.
The existing one- and two-index special lemmas do not extend cleanly to the
initial bound of five.

The two `ErrorTest` fixtures remain as executable documentation of the desired
diagnostics. They should continue to fail as unknown syntax until a future
consumer justifies the missing finite-elimination infrastructure. M5 uses the
promised fallback: structured, generated proofs assembled from the M1 block
API, the M3 shear API, and ordinary isometry composition, with no handwritten
matrix-entry case trees.

### M5. Validate on the Fifteen-Theorem frontier and stop `[~]`

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
3. M2a ordered-word `ring` mode and its positive/negative controls.
4. M2b caller-supplied monomial relations, only if it passes its stop gate.
5. M3 symbolic pullback refactor.
6. M4 concrete evaluator, if it passes the probe gate.
7. M5 consumer proofs.
8. Plan/status documentation separately from mathematics or elaborator code.

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

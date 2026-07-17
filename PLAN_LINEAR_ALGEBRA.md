# PLAN_LINEAR_ALGEBRA.md — finite-dimensional linear algebra (rank–nullity and det multiplicativity)

The two headline targets are **rank–nullity** (`dim ker T + dim im T = dim V`)
and **det(AB) = det(A)·det(B)**. They are chosen as *expressiveness probes*,
not for the mathematics: everything in the library so far lives over a fixed
carrier (ℤ, ℚ, ℝ, ℂ, a fixed group/ring/field, polynomials over a fixed base).
Linear algebra is the first branch that forces **families indexed by a count
that is itself proof data** (`NaturalsBelow(n) → V`) and **transport across a
proven `n = m`**. That is the one characteristic CIC pressure point we have
never tested. The primary deliverable of this branch is therefore *information*:
does the dependent-index / transport story stay ergonomic, or do proofs drown in
casts? Treat friction around `NaturalsBelow(n) ≃ NaturalsBelow(m)` as a finding
to record (in `STRESS_PROBES.md`), not just an obstacle to route around.

**On "finite-dimensional".** The vector-space *axioms are the standard,
unrestricted ones* and the `VectorSpace` structure is fully general — nothing in
the definitions is capped at finite dimension. "Finite-dimensional" governs only
(a) which *structure* carries a natural-number `dimension` and (b) which
*theorems* (the counting ones) are stated unconditionally. `IsBasis` is
index-generic and admits infinite bases (e.g. `{xⁿ}` for `F[x]`); see Stage D.

**On the axiom of choice.** This branch is built to make *turning AC on later
non-disruptive*, without adopting it now. Choice is **threaded as an explicit
`Proposition` hypothesis**, never added as a global axiom (see "Axiom-of-choice
architecture"). The finite-dimensional and countable-dimensional layers are
provably choice-free; only the general infinite-dimensional invariance/existence
results take a `(choice : AxiomOfChoice)` parameter. No step here may add an
axiom to the trusted base.

## Status ledger

Update this section before ending any session that works on the plan.

- **Stage 0 (decisions)** — 0.1/0.2 SETTLED by the Stage A landing
  (2026-07-11): `Field` = `CommutativeRing` + `Nontrivial` +
  `NonzeroInvertible` (predicates over the bundle, so `Field.make` reads
  as its content); universe check confirmed (`Field : Type(1)` carrying
  a `Type(1)` bundle is fine); reciprocal via `Logic.the` over
  `Field.inverse_unique`. 0.3 (two layers) and 0.4 (index bridge) are
  settled on paper, exercised by Stages B/D.
- **Stage A — DONE (2026-07-11).** `Algebra/field_bundle.math`: the
  `Field` record, projections, operation wrappers + operators
  (`+ - * ⁻¹`), `instance Field.is_ring`, the flattened law layer (the
  names `ring` demands), `Field.is_field`, `Field.inverse_unique`,
  `Field.reciprocal`, `Field.reciprocal_multiplies`. Instances:
  `Real.field` (`Real/field_bundle.math`), `Rational.field`
  (`Rational/field_bundle.math`, over the new
  `Rational/ring_bundle.math` — ℚ had no `Ring`/`CommutativeRing`
  bundle). A `FiniteField`/ℤp instance is deferred until a consumer
  wants it (IntegerMod lacks a `CommutativeRing` bundle; measure
  first). Elaborator support landed with it: `computeRingScheme`
  treats `Field.carrier(f)` like `CommutativeRing.carrier(c)` (sound —
  commutativity is a bundle field), `carrierProjectionField` recurses
  through the bundle layers (Field.make → CommutativeRing value → Ring
  value → carrier; also fixes the latent CommutativeRing-instance
  case), and the postfix-operator path saturates implicit-carrying
  dispatch functions with holes (`x⁻¹` over an abstract field).
  Acceptance: `Test/field_bundle_test.math` (ring-normalisation over
  abstract `Field.carrier`, bare instance axioms, by-less reciprocal
  cancellation, concrete-instance reduction). All five files in the
  clean manifest.
- **Stage B — DONE (2026-07-12).** `Algebra/vector_space.math`:
  `IsVectorSpace` (abelian group + the four scalar-action laws), the
  bundled `VectorSpace(f)` record INDEXED by its field (Type(1),
  parameterized inductive — the first in the library), projections,
  operations + operators (`+ - •`), `instance
  VectorSpace.is_abelian_group`, an `automatic` flattened law layer
  (no `ring` normaliser exists over a vector carrier, so the scan is
  what discharges bare vector arithmetic — six group laws + the four
  scale laws), and the `F`-over-itself instance
  (`Field.vector_space`). `Algebra/coordinate_space.math`: `Fⁿ` as
  `NaturalsBelow(n) → Field.carrier(f)` under pointwise operations —
  the first genuinely dependent-indexed carrier — with
  `CoordinateSpace.equal_of_pointwise` as the one extensionality
  bridge and every law a pointwise field fact closed by `ring`.
  FOUNDATIONAL PREREQUISITE LANDED WITH IT: **function extensionality
  is now a THEOREM** (`Function.extensionality`, Logic/functions.math)
  — derived from the quotient axioms + η (evaluate through the
  pointwise-equality quotient; the round trip computes back by lift-ι
  + η), no new axiom, honoring the no-axiom guardrail. Elaborator
  support: the `•` token (lexer/parser, multiplicative precedence);
  two-phase operator implicit recovery (a heterogeneous operator's
  left operand may not pin every implicit — `•` pins {f} from the
  scalar, the RIGHT operand's type against the second explicit domain
  pins {V}); `carrierProjectionField` peels implicit-carrying
  projections and reads through `VectorSpace.make` (parameter first,
  carrier second). Acceptance: `Test/vector_space_test.math`.
  PROBE FINDINGS (the branch's purpose): (1) the `by <lemma>` citation
  path does NOT ∀-intro a Pi goal before matching, so the ∀-shaped
  law legs need explicit binder lambdas around the pointwise bridge —
  a candidate follow-up for the citation machinery; (2) the leak
  taxonomy counts `equal_of_pointwise(<pointwise lambda>)` term calls
  as direct proof-lemma calls. RESOLVED 2026-07-12 (owner ruling: keep
  judging by the two criteria, prefer bottom-up): the lambda idiom was
  never necessary — the legs are now take-blocks stating the pointwise
  fact (`∀ (k …). … by Field.<law>;`) closed by an argument-free
  `done by CoordinateSpace.equal_of_pointwise`, and the bridge itself
  is `done by Function.extensionality`; `coordinate_space.math` is IN
  the manifest at unchanged budget. The idiom (and its top-down
  `suffices … by <bridge>` variant for multi-step pointwise chains —
  the construct already existed in reference.md, undocumented in
  proof-style.md) is now recorded in proof-style.md's raw-CIC tells.
  CLEAN_LEAK_BUDGET resynced 230→232 (field_bundle's two `Logic.the`
  proof-data tokens, the Real.reciprocal idiom — my Stage A gate ran
  before the manifest edit, so the +2 surfaced here).
- **Stage C — DONE (2026-07-12).** `Algebra/vector_space_lemmas.math`:
  the derived scale facts as `automatic` lemmas (no `ring` over vector
  carriers, so the scan is the normaliser): `zero_scale` (0·v = 0),
  `scale_zero` (a·0 = 0), `negate_one_scale` ((−1)·v = −v),
  `subtract_self`, `subtract_add_cancel`.
  `Algebra/subspace.math`: `IsSubspace` (zero + add/scale closure;
  negate-closure DERIVED via (−1)·v), accessor projections as
  proof-data `definition`s (the bundle-file pattern — keeps
  constructions leak-free), and the induced space on the subtype
  mirroring `subgroup_group`: ops inherit from V with closure
  membership proofs, every law reduces through
  `Subtype.equal_of_value_equal`, `Subspace.is_vector_space` assembles
  by argument-free `by Subspace.<law>` citations (the `Field.is_field`
  idiom), `Subspace.vector_space : VectorSpace(f)` bundles it. DESIGN
  CALL: `Subspace.carrier(V, subset, subspace)` is parameterized by
  the closure PROOF so the `+`/`•` operators recover it from the
  operand type (the PAdic `(p, primality)` recovery precedent) —
  subspace arithmetic reads `(x + y) + z`, no five-argument spellings.
  `Algebra/linear_map.math`: `IsLinearMap` (∧ of additivity +
  homogeneity), `LinearMap.additive`/`homogeneous` accessor
  definitions, preserves zero/negate/subtract, identity map + compose,
  `kernel`/`image` + both `*_is_subspace` (take/suppose/choose/witness
  shapes, no tuples), injective ⟺ trivial kernel via
  `Function.IsInjective` (reused from Logic/functions), and
  `Subspace.inclusion_is_linear`/`_is_injective`. Acceptance:
  `Test/linear_map_test.math`. TWO ELABORATOR GAPS fixed at the root
  (both in the Stage C commit): (1) the operator desugarer elaborated
  the RIGHT operand with the left's type as a hard expected type — a
  heterogeneous operator's right operand (`a • Subtype.value(x)`) got
  its implicits poisoned; the propagation is now a HINT with a
  bottom-up retry (elaboration + type inference share the retry).
  (2) The plain-call path inferred a declared implicit prefix only for
  EXACTLY-fully-applied calls, so a genuine partial application after
  the prefix (`Subspace.inclusion(V, subset, subspace)` leaving its
  function argument open) jammed V into the `{f}` slot; the guard is
  now `<=` (positional-with-implicits spellings are outside the
  window). PROBE FINDINGS: the conjunction-leg projection (`P by h`)
  does not δ-unfold a defined proposition (`by tLinear` fails with a
  `<unknown>`-head message — inbox entry filed); the robust idiom is
  accessor citations `by LinearMap.additive(tLinear)` at stated-leg
  expected types, then hypothesis application in chains. Accessor
  citations under a congruence wrapper used to fail to reach the
  differing subterm (ROOT-FIXED — see the Stage-E friction ledger, item
  (2): the diff descent's structural gate broke above a defeq-but-not-
  structural shared operand; now cite argument-free straight through the
  congruence). Gates: library+tests,
  error-tests 54/0, export-check 2677, clean-check GREEN at budget 232
  (all three files manifest-added leak-free, re-run after the manifest
  edit), serial warning-site diff IDENTICAL (6 standing advisory
  sites both sides).
- **Stage D — DONE (2026-07-12).** Stage 0.4 index bridge DECIDED and
  recorded in docs/PLAN_GENERIC_AGGREGATION.md: combination data are
  FUNCTIONS WITH A BOUND (`selection : Natural → I`, `coefficients :
  Natural → Field.carrier(f)`, `count`), aggregated by the existing
  `Algebra.Fold` below the count; `I`-indexed families enter through
  composition; injectivity is stated below the bound;
  `NaturalsBelow(n)` appears only as an instance of `I` — never as an
  aggregation index (rejected: extending families with a default,
  which needs proof-carrying conditionals and a second fold).
  `Algebra/linear_combination.math`: `VectorSpace.add_is_monoid`,
  `fold_operation (+) on VectorSpace.carrier`, and
  `VectorSpace.linearCombination` DEFINED VIA THE SUM BINDER —
  `sum i from 0 to count - 1 of coefficients(i) • family(selection(i))`
  — plus the `_zero`/`_one`/`_add_one` characterizing lemmas.
  ELABORATOR EXTENSION (root, not workaround): the `fold_operation`
  registry now accepts Pi-quantified IsMonoid witnesses (registration
  peels binders, name-keyed as before) and the fold binder
  instantiates the witness per use by first-order-matching its carrier
  template against the body's actual carrier (then closes the cores
  over the local binders; the expected-type check opens the expected
  side, as the coercion path does). Σ-notation now works over ANY
  bundled carrier — Stage H's matrix sums get it for free.
  `Algebra/span.math`: index-generic `VectorSpace.Spans` /
  `LinearlyIndependent` (selection injective below the count) /
  `IsBasis` (∧, with proof-data accessors) / `FinitelyGenerated`
  (`NaturalsBelow(count)` generators — the finite case as an `I`
  instance). First instance: `Field.one_family_is_basis` — {1} is a
  basis of F over itself (spanning = v·1 via `linearCombination_one`;
  independence via `NaturalsBelow.one_subsingleton` + injectivity
  capping the count at 1) — and `Field.vector_space_finitely_generated`.
  Acceptance: `Test/span_test.math`. Gates: library+tests, error-tests
  54/0, export-check 2693, clean-check GREEN 172 files at budget 232
  (both files manifest-added leak-free; the one flagged token — an
  applied `recalling VectorSpace.zero_add(V)` — was restructured to an
  argument-free citation), serial warning-site diff IDENTICAL.
  Kept-despite-warning hints: the `by selectionInjective` /
  `below_one_is_zero` / assembling citations in span.math (operative
  reasons, deliberate).
- **Stage E — DONE (2026-07-14).** `FiniteDimensional` + `F[x]` (2026-07-12), the
  **Steinitz exchange lemma core** (`independent_le_spanning`) + the **official
  index-generic `exchange`** (packaging bridge, commit 8e57928b), AND **pruning**
  (`FinitelyGenerated ⟹ FiniteDimensional`, `Algebra/basis_pruning.math` — see the
  Phase 1 "Prune" worklist entry). All choice-free. Enabled along the way by a
  definitional fix (`Spans` now contains 0, so `{0}` is 0-dimensional).
  - **`FiniteDimensional` — DONE.** `Algebra/finite_dimensional.math`:
    `VectorSpace.FiniteDimensional(V) := ∃ n. ∃ (b : NaturalsBelow(n) →
    carrier). IsBasis(b)` (the propositional finite-basis predicate; the
    `dimension` value + bundled record wait for Stage F invariance, which
    needs the exchange lemma). Instance: `Field.vector_space_finite_dimensional`
    (F is finite-dimensional over itself, dimension 1, via the {1} basis).
    IN the clean manifest.
  - **`F[x]` with the {xⁿ} basis — DONE (the worked infinite instance).**
    `Algebra/polynomial_vector_space.math`. Checked the Polynomial rep
    first (per the plan): it is a quotient of coefficient lists with
    `Polynomial.coefficientOf`, a `Polynomial.monomial(r,c,j)` = c·xʲ with
    `coefficientOf_monomial_at`/`_off`/`_multiply`, and
    `Polynomial.exists_degree_bound` — but NO reconstruction lemma and NO
    lifted scale, so those were built. Scalar action `a•p :=
    monomial(a,0)*p` (coeff = a·coeff, from `_monomial_multiply` at
    exponent 0); the four module laws reduce index-by-index to base-ring
    identities via `equal_of_coefficientOf_equal`. The base ring is
    `Field.coefficient_ring(f) = CommutativeRing.ring(Field.commutative_ring(f))`,
    whose carrier/constants are the field's BY DEFINITION (so Polynomial
    ops and field scalars share a carrier, no coercion — the key that made
    it tractable). Basis: bridge lemma
    (`coefficientOf` is additive ⟹ commutes with the combination fold,
    landing on a field-side `Algebra.Fold`), single-term extraction over
    that fold (`fold_vanishes` + a BOUNDED `fold_single_point` — bounded
    because a general injective selection's off-diagonal is controlled only
    in range), spanning (degree-bound + identity selection + diagonal
    single-point) and independence (evaluate the vanishing combination at
    `selection(i)`; injectivity kills the other monomials). `F[x]` is a
    basis-carrying space that is NOT `FiniteDimensional` (Natural-indexed
    basis). Choice-free (export-check axiom inventory unchanged).
    **IN THE CLEAN MANIFEST as of 2026-07-12 (commit a85db753).** It had
    held 15 positional proof-lemma citations + 2 `Equality.symmetry` (17
    leaks); the earlier "argument-free pass FAILED / multi-premise
    citations can't discharge" note turned out stale — every positional
    theorem call is now an argument-free `by Lemma` (the auto-prover
    discharges the premises from context; the multi-premise fold citations
    included), the two `Equality.symmetry(h)` reductios became bare
    `x = y by h; done`, and the resulting unused-name cascade settled by
    dropping the now-dead `as <name>` labels. 17 → 0 leaks; clean-check 174
    files / 232 residual leaks unchanged.
  - **Exchange lemma (Steinitz) — CORE DONE (2026-07-14).** The
    independent-≤-spanning, one-swap-at-a-time argument (where
    `Field.reciprocal` FINALLY enters). This is the abstract crux and the
    transport probe feeding Stage F dimension. `Algebra/exchange_lemma.math`
    proves `VectorSpace.independent_le_spanning` (canonical-coordinate form):
    `StandardIndependentBelow(uu, m)` + (`w` vanishes past `n`) + `Spans(w)`
    ⟹ `m ≤ n`. The packaging bridge to the index-generic
    `LinearlyIndependent`/`Spans` (`VectorSpace.exchange`) LANDED 2026-07-14
    (commit 8e57928b — see the Phase 1 "Bridge" worklist entry). Landed earlier
    this session:
    - **Reciprocal-solve** — `scale_reciprocal_cancel` (`a⁻¹·(a·v)=v`),
      `InSpanOf.scale_cancel` (a nonzero multiple of `v` in a span puts `v`
      in the span). First genuine use of field-over-ring structure.
    - **Canonical coordinates** — `standardCombination(g,c,n) = Σ_{i<n}c(i)•g(i)`
      (identity selection, so "the coefficient at slot j" is well-defined) with
      `_add_one`/`_congruence`/`_bump` (bump-one-coordinate), a generic
      `Function.updateAt` (type-variable codomain to dodge the `Field.carrier`
      motive quirk), and `linearCombination_standardize` (any combination of a
      family that VANISHES PAST `n` normalises to canonical coordinates —
      induction on length, bumping the selected slot, dropping out-of-range
      terms). Normalisation is what made the exchange step read a slot's
      coefficient without a summation-regrouping/histogram lemma.
    - **Pivot extraction** (sub-piece 1) — `StandardIndependentBelow` +
      `exchange_find_pivot`: independence of `uu(0..k)` forces some REMAINING
      slot (index in `[k,n)`) to carry a nonzero coefficient (else a `-1` at
      slot k is a nontrivial vanishing combination; `Field.negate_one_nonzero`).
    - **The swap step** — `swapIn(g,k,j,v)` (transpose-and-overwrite, two
      `updateAt`s; the `i=j`-first case order handles `j=k` uniformly) and
      `exchange_step`: `uu(k)` swapped in at slot `k`, old `g(k)` parked at slot
      `j`, swapped-out `g(j)` recovered by `scale_cancel` after isolating it via
      a zeroed-coefficient combination through the modified family;
      `InSpanOf.of_combination` + `.transitive` discharge "still spans".
    - **Induction + inequality** — `exchange_build` (for each `k ≤ n`, a
      spanning family whose first `k` entries are `uu(0..k-1)`) then
      `independent_le_spanning` (if `m>n`, the `k=n` family exhibits `uu(n)` as
      a combination of `uu(0..n-1)` → contradiction).
    - **PROBE VERDICT (see STRESS_PROBES.md):** (i) [PROVER] there is NO
      additive/`ring`-additive normaliser over `VectorSpace.carrier`, so group
      identities like `(a+b)-a=b` (`add_subtract_cancel_left`) and the medial
      law are hand-proven — filed a two-tier tactic (additive-group normaliser;
      free-module `linear_combination` collecting like terms via field-coeff
      `ring`). Owner concurs this is the right tool. (ii) [SURFACE] the
      `NaturalsBelow(n)` reindexing pain the plan feared did NOT hit the guts —
      working over `Natural`-indexed families with bounded predicates turned
      delete/insert/swap into `Function.updateAt`/`swapIn` point-updates. The
      transport cost is confined to the not-yet-built bridge.
    - **NOT YET IN CLEAN MANIFEST** — like `coordinate_space`/`polynomial_
      vector_space` initially: builds green under default gates (library+tests
      PASS), but has ~60 `--check-redundant-by` hints that need the careful
      per-site read-through (half are load-bearing keeps), deferred.
    - **Packaging bridge — DONE (2026-07-14, commit 8e57928b).** See the Phase 1
      "Bridge" worklist entry for the full recipe. NEXT for Stage E is **Prune**.
    ---
    Foundation landed 2026-07-12 (below), all consumed by the core above:
    - **Combination module-algebra** (`Algebra/linear_combination.math`):
      `linearCombination_scale` (`a·Σcᵢbᵢ = Σ(a·cᵢ)bᵢ`) and
      `linearCombination_add_coefficients` (`Σcᵢbᵢ + Σdᵢbᵢ = Σ(cᵢ+dᵢ)bᵢ`),
      plus the medial-law helper `VectorSpace.add_pair_interchange`. By
      induction, peeling `linearCombination_add_one`.
    - **Span-membership API** (`Algebra/span.math`):
      `VectorSpace.InSpanOf(family, v)` (v is a finite combination of
      members) with `of_spans`/`Spans.of_in_span` (definitional bridge),
      `InSpanOf.member`, and `InSpanOf.scale`. NOTE: `InSpanOf(family, 0)`
      is NOT provable for an arbitrary (possibly empty) index type `I` — the
      empty combination still needs a `selection : Natural → I` — so there is
      no bare `InSpanOf.zero`; membership lemmas carry an `I` inhabitant.
    - **Combination concatenation → `InSpanOf.add` — DONE (commit 615adf9d).**
      `VectorSpace.combineFunctions left right count` concatenates two
      `Natural`-indexed families at a cut (`if i < count then left(i) else
      right(i − count)`); ONE generic `{A : Type(0)}` definition serves both
      selection and coefficients (`Field.carrier(f)` as the RETURN type
      trips the "cases motive not a Sort" quirk, but a plain type variable
      `A` does not — generalize). `combineFunctions_below`/`_shifted` reduce
      the branches via `Logic.if_positive`/`if_negative`.
      `linearCombination_pointwise_below` (bridges `linearCombination` to
      `indexedAggregate` to reuse `indexedAggregate_pointwise_below`) then
      `linearCombination_concatenate` by induction on the RIGHT count (peel +
      IH + associativity — NOT the Fold_split/rebase route first sketched;
      induction is cleaner and `Fold_rebase_start` proved unnecessary and was
      dropped). `InSpanOf.add` witnesses the merged data — the `InSpanOf`
      subspace trio (member/scale/add) is complete. `if` rests on
      `Logic.classical_decidable` (theorem over the documented `Logic.the`) →
      NO new axiom (export-check inventory unchanged). NOTE: the raw
      `cases … { | Ctor(x) => … }` pattern-match is a discouraged CIC form —
      use `if P then a else b` for value-level branching, not `cases` on
      `compare_strict`.
    - **Span-transitivity — DONE (commit fa73f6db).** `InSpanOf.transitive`:
      each generator of `inner` lies in span(`outer`) ⟹ span(inner) ⊆
      span(outer). Via `InSpanOf.of_combination` (a combination of inner
      members is in span(outer), by induction on the length: peel the last
      term = scaled generator, add to the shorter combination via the IH,
      closing from member/scale/add). Base case needs a `J` inhabitant to
      write `0 = 0·outer(inhabitant)` — the same caveat the other InSpanOf
      lemmas carry.
    - **Steinitz exchange induction — DONE 2026-07-14** (see the CORE DONE
      block above). Span-transitivity is the substitution its replacement step
      performs; `Field.reciprocal` enters via `InSpanOf.scale_cancel`.
  - **FinitelyGenerated ⟹ finite basis (pruning) — FOUNDATION + KEY FIX DONE,
    redundancy/induction remaining.** See the Phase 1 "Prune" worklist entry for
    the full remaining design. FOUNDATION (commit ad2491e1) + the reindexing
    helper landed. **DEFINITIONAL FIX (commit c7bad820, `Spans` now contains 0):**
    the probe surfaced that `Spans`/`InSpanOf` demanded a selection `Natural → I`,
    which is uninhabited for `I = NaturalsBelow(0)`, so the EMPTY family could not
    span — making the trivial space `{0}` finitely generated but NOT
    finite-dimensional (no expressible basis), i.e. `FinitelyGenerated ⟹
    FiniteDimensional` was FALSE for `{0}`. Owner ruling: `{0}` IS 0-dimensional;
    learn from Mathlib (span = closure that always contains 0). FIX:
    `Spans(family) := ∀v. v = 0 ∨ (∃ combination)` — the empty sum reaches 0 with
    no selection witness. `InSpanOf` unchanged (so exchange's combination
    extraction is untouched); `InSpanOf.of_spans` gained an index inhabitant (for
    the `v=0` leg), `InSpanOf.zero` moved to span.math, and the `Spans` producers
    ({1}-basis, F[x] monomials, exchange's swap/bridge) establish `InSpanOf` then
    close by auto ∨-intro. All gates green after the change.
  - **DESIGN NOTE — representation of a linear combination — DECIDED 2026-07-14:
    KEEP the current `selection : Natural → I` + `count` encoding; the
    subset-indexed `Σ (i ∈ S)` migration is DROPPED.** The reasoning was: the
    exchange/pruning proofs are about the index SET changing by one element, and
    a finite-subset `S ⊆ I` encoding would make `S ∖ {j}`/`S ∪ {j}` first-class
    — but at the cost of a REPRESENTATION migration rippling through span, the
    `{1}` basis, `F[x]`, and the coefficient module-algebra. The plan was to run
    Steinitz ONCE on the current encoding as the honest reindexing test first.
    **Verdict: the reindexing pain never materialised** — working over
    `Natural`-indexed families with bounded predicates turned delete/insert/swap
    into `Function.updateAt`/`swapIn` POINT-UPDATES (see
    `Algebra/exchange_lemma.math`), so the subset migration is not worth its
    cost and is dropped. The cheap, orthogonal win survives as a live to-do: a
    `Σ (i < count) …` display binder that parses to / prints as
    `linearCombination(…)` — pure notation over the existing function, no
    proof-engine change (worklist item **Σ-sugar** below).
  - **Friction found this session, re-triaged (the branch's deliverable):**
    (1) `by substituting eq1, eq2` (comma) is not supported — `substituting`
    rewrites with ONE equation (the search picks a single candidate, it does
    not chain rewrites); split into one `substituting` per step. FIXED AT
    THE SOURCE: the parser now rejects the comma with a clear message
    (`ErrorTest/substituting_comma_list`) instead of a confusing downstream
    "expected expression". (2) GENUINE recurring BUG — the Stage-C
    "accessor-under-congruence mis-pins implicits", which recurred for a
    backward scale-rewrite nested under `+`. ROOT-FIXED (`diff_bridges.cpp`,
    `tryApplyBareLemmaToDiff`): the diagnosis was NOT backward-vs-forward
    unification but the descent's structural-equality gate — the two calc
    endpoints elaborate independently, so a shared operand (an operator's
    ring instance) can come out `Field.commutative_ring f` on one side and
    `CommutativeRing.ring (Field.commutative_ring f)` on the other, defeq
    but not structural. Requiring structural equality to pick the shared
    sibling broke the descent one level ABOVE the differing subterm, so the
    cited accessor never reached it. Fix: keep structural equality primary
    (a definitional test alone would wrongly mark a defeq-lemma's CHANGED
    operand "unchanged" too — the `embed(-b)`/`negate(embed b)` case), and
    fall back to defeq ONLY to break the tie when NEITHER component is
    structurally equal. The scale-law workarounds in
    `Algebra/polynomial_vector_space.math` are deleted — all four laws now
    cite `Field.coefficientOf_polynomial_scale` argument-free straight
    through the congruence. Regression: `Test/accessor_congruence_repro.math`.
    Gates: library+tests green, error-tests 55/0. (3) NON-BUG (my usage
    error): the decidable `by cases { case P as h: … otherwise as h2: … }`
    form DOES work as a calc-step justification (needs `import axioms` for
    `otherwise`) — I had wrongly used the raw `cases E { | Or.introduceLeft
    … }` pattern-match, which is not the calc-step hint grammar AND is the
    discouraged raw-CIC form. Prefer the decidable form. (4) NON-BUG:
    `Natural.lt_or_le` is in `Natural.division` BY DESIGN (its proof needs
    the trichotomy helpers that live there — see the file header); a
    discoverability note, not a misplacement.
  - Note: bundled induced spaces of kernel/image (`Subspace.vector_space`
    applied to `kernel_is_subspace`) were left to consumers — construct
    them where Stage G needs dimensions.
- **Stage F — CORE DONE (2026-07-14).** `Algebra/dimension.math`: the choice-free
  finite half — a well-defined `dimension : Natural` and its invariance, all gates
  green (library + tests, export-check 2858 decls, axioms unchanged).
  - `VectorSpace.HasDimension(V, n)` (some `NaturalsBelow(n)`-indexed basis exists;
    `FiniteDimensional(V)` is definitionally `∃ n. HasDimension(V, n)`).
  - `basis_size_unique` — two finite bases of a fixed space have equal size:
    `VectorSpace.exchange` applied in BOTH directions + `Natural.le_antisymmetric`.
    `dimension_unique` (choose bases, apply it) and `bases_equinumerous` (the
    invariance re-expressed as `Equinumerous(NaturalsBelow(m), NaturalsBelow(n))`,
    a single `substituting` over `Equinumerous.reflexive`).
  - `dimension` via `Logic.the` over `dimension_unique` (structurally identical to
    `Field.reciprocal`); `dimension_has_basis` (`Logic.the_satisfies`),
    `dimension_equals` (read a dimension off any exhibited finite basis).
    `Field.vector_space_dimension`: a field is 1-dimensional over itself.
  - `SameDimension` — the general, index-agnostic relation via `Equinumerous`
    (`∃ (I : Type(0)). …`, using the universe-polymorphic `Exists.{1}`; no
    `Cardinal` type) + `same_dimension_of_equal_dimension` for the finite case.
  - **PROBE VERDICT (STRESS_PROBES.md):** the `n = m` transport crux the branch
    was built to measure did NOT bite — it was pre-paid at the exchange bridge.
    Because Steinitz runs over `Natural`-indexed families with `NaturalsBelow.make`
    confined to `VectorSpace.exchange`, the invariance proof sees only a clean
    `m ≤ n` / `IsBasis` interface: no `cast`, no dependent motive, no elaborator
    help. `Logic.the` for the `Natural`-valued invariant was frictionless.
  - NOT yet in clean manifest (shares the deferred redundant-by read-through).
    REMAINING for Stage F (Stage 0.3 bundle): the stronger
    `FiniteDimensionalVectorSpace` record layered over `VectorSpace` carrying
    `dimension`/`basis`/`IsBasis` — build when Stage G needs it (currently the
    unbundled `dimension(V, fd)` view suffices).
- **Stage G — DONE (2026-07-14).** `LinearMap.rank_nullity` (dim V = dim ker T +
  dim im T), `Algebra/rank_nullity.math`, choice-free. See the memory tracker
  [[linear_algebra_build]] for the brick 1–5 detail.
- **Stage H — DONE (det(AB) = det(A)·det(B), headline #2).** `Matrix.determinant_multiply`
  (`Algebra/determinant_multiplicative.math`), all gates green (library + tests +
  export-check 3122, axioms UNCHANGED — choice-free). Bricks 1–6 complete. 6c landed
  2026-07-15 (`Lists/remove.math`, `Field.sumOver_remove`, `Field.sumOver_involution_pairing`
  in `Algebra/involution_pairing.math` — genuine orbit-pairing, char-free, NOT `Σ=−Σ`;
  `Matrix.alternating_collapse` at ι = σ↦σ∘swap(a,b) via `Field.productOver_permutation`).
  6d landed 2026-07-16: `Permutation.of_injective` (injective self-map ⟹ permutation via
  pigeonhole surjectivity + `Logic.the` inverse), `Field.sumOver_restrict_support` +
  `Field.sumOver_permutation`, `Matrix.determinant_row_permutation` (Σ_σ sign σ·∏B(pi,σi)
  = sign p·det B, via σ↦σ∘p reindex + `Field.from_integer_multiply_units`),
  `Function.allFunctions_distinct`, and the assembly (Leibniz expand → 6a distribute →
  productOver_multiply → Fubini → 6c kills non-injective φ → restrict_support to the
  permutation image → sumOver_map → 6d row-permutation → det A·det B). Remaining LA work
  is all non-critical: the polish sweep, Σ-sugar/Norm-b automation, AC infra.
- **LA POLISH DEBT — CLOSED 2026-07-17.** Waves 1–2 (dimension + the
  determinant cluster) landed 2026-07-16 (see the polish-session entry);
  wave 3 landed 2026-07-17 in the overnight loop: exchange_lemma
  (5579b02d, 135 findings, manifest-added at +1 leak), basis_pruning
  (a62bc6b9, 154 findings, 4 documented checker false-positive reverts,
  +2 leaks), rank_nullity (6de1b274, 290 findings, zero reverts, +23
  leaks — all structural hypothesis-application data args). Budget
  272 → 297 with dated Makefile notes. Every Stage A–H file is now at
  the clean-manifest bar; nothing remains open in this plan.

## Remaining worklist (authoritative running order)

Sequenced 2026-07-14 after the Steinitz core landed. Rationale: finish Stage E
(index-bookkeeping, which the normaliser tactic would not help) with current
tools; then build the automation interlude (it pays off across the arithmetic-
heavy F/G/H, not the bookkeeping of the bridge/pruning); then the headlines.
The one judgment call is where the normaliser sits — after Stage E here; move it
before **Bridge**/**Prune** only if you want the automation to land first on
principle. Sizes: S/M/L. Each elaborator item (Σ-sugar, Norm-a, Norm-b) touches
the parser/elaborator, so it needs a clean `make tests` cycle, not just a warm
library build.

**Phase 0 — housekeeping**
- [ ] **Manifest** (S, polish) — redundancy read-through of
  `Algebra/exchange_lemma.math` (~60 `--check-redundant-by` hints, ~half are
  load-bearing keeps per `redundant_by_is_half_keeps`); then add to
  `scripts/clean_manifest.txt`. Like `coordinate_space`/`polynomial_vector_space`
  were added after their initial landing.

**Phase 1 — finish Stage E**
- [x] **Bridge — DONE (2026-07-14, commit 8e57928b).** The official
  `VectorSpace.exchange : LinearlyIndependent(u : NaturalsBelow(m)) ∧ Spans(w : NaturalsBelow(n)) → m ≤ n`
  (`Algebra/exchange_lemma.math`), derived from `independent_le_spanning`.
  Delivered exactly as planned: `Function.extendBelow` (+`_below`/`_past`)
  extends a `NaturalsBelow(m)→A` family to a total `Natural→A` map via
  `Function.extendBelowWithDecision` — the value-level dependent conditional
  over `Logic.classical_decidable(i<m)`, the `Rational.minimumWithDecision`
  pattern-match whose `yes(below)` arm forms `NaturalsBelow.make(i, below)`;
  GENERIC in the codomain `A` (bare type variable, dodges the Sort quirk). The
  characterizing equations are `by`-less `if i<m then … else …` proofs (the
  `if_split_test` idiom), NOT `if_positive_dependent` citations. Both families
  extend with fallback `zero`; the clamped selection `Natural→NaturalsBelow(m)`
  is `NaturalsBelow.clamp(fallback) := extendBelow(identity, fallback)` — the
  reusable "reindex into the finite type" helper (its cousin serves Prune).
  Independence and spanning transport across the reindexing via the new
  `VectorSpace.linearCombination_congruence` (`linear_combination.math`,
  arbitrary-family/selection sibling of `standardCombination_congruence`, same
  `indexedAggregate_pointwise_below` reduction). `m=0` is immediate (`0≤n` by
  `Natural.zero_least`); the `m>0` branch (`case m = 1 + predecessor`) supplies
  `NaturalsBelow.make(0, mPositive)` as the clamped-selection fallback. The
  risky citations all held first try: `done by independent` (the hypothesis'
  full ∀-chain instantiated + injectivity/vanishing premises discharged from
  named context facts), the two congruence transports, and
  `done by independent_le_spanning`. UNBLOCKS Stage F. NOT yet in clean
  manifest (shares the deferred redundant-by read-through with the core).
- [x] **Prune — DONE (2026-07-14, `Algebra/basis_pruning.math`).**
  `VectorSpace.FinitelyGenerated.finite_dimensional` (headline) is proven,
  choice-free, all gates green. `spanning_finite_dimensional` inducts on the
  family size: the empty family is a basis (base), each dependent step drops a
  redundant vector (`independent_or_droppable` finds one via the redundancy
  contrapositive; `dropIndex_redundant` isolates it by position-bump +
  `scale_cancel`; `spans_dropIndex` keeps spanning via `skip` surjectivity +
  transitivity) and recurses; `size_one_finite_dimensional` splits size 1 on
  triviality (zero vector ⟹ empty basis of `{0}`; nonzero ⟹ itself a basis).
  Enabled by the Spans-contains-0 fix (so `{0}` is 0-dimensional). NOT yet in the
  clean manifest (redundant-by read-through deferred, ~20 unused-name hints).
  **Foundation DONE (2026-07-14, commit ad2491e1):**
  `linearCombination_bump_position` (arbitrary-selection position bump),
  `InSpanOf.of_combination_selected` (used-indices refinement of of_combination),
  and the `NaturalsBelow.skip(jv)` reindexing helper (`skipValue`/`skipInverseValue`
  + `skip_avoids` + `skipInverse_skipValue` round trip). **UNBLOCKED by the
  Spans-contains-0 fix (commit c7bad820):** the trivial space `{0}` is now
  finite-dimensional (empty basis spans via `∀v. v=0`), so the theorem is TRUE.
  **REMAINING (redundancy + induction, design fully worked out):**
  1. `NaturalsBelow.skip_surjective` — `value(index)≠jv → ∃i. skip(jv,i)=index`
     (via `skipInverse`; needs the NaturalsBelow-valued inverse with its bound).
  2. Redundancy: `g:NaturalsBelow(1+count)→V`, `¬LinearlyIndependent(g)` ⟹
     `∃j. InSpanOrZero(g∘skip(value j), g(j))` where `InSpanOrZero(fam,v):= v=0 ∨
     InSpanOf(fam,v)`. Route (avoids the messy `¬∀` extraction): prove the
     CONTRAPOSITIVE inside "→independent" — take `N,σ,c,inj,comb=0`, suppose
     `c(i0)≠0`; `j:=σ(i0)`; by `linearCombination_bump_position` at `i0` with
     `e=-c(i0)`: `(-c(i0))•g(j) = linearCombination(g, updateAt(c,i0,0), σ, N)`,
     and the RHS reindexes (congruence, `skipInverse`) to a combination of
     `g∘skip(value j)` (position `i0` has coeff 0 so its selection is free) ⟹
     `InSpanOf(g∘skip, (-c(i0))•g(j))` ⟹ `InSpanOf(g∘skip, g(j))` by
     `InSpanOf.scale_cancel`. **count=0 (size 1) is a SEPARATE case**: injectivity
     into the `NaturalsBelow(1)` singleton forces `N=1`, so `comb=c(0)•g(point)=0`
     with `c(0)≠0` ⟹ `g(point)=0` (the `v=0` leg of `InSpanOrZero`; `g∘skip`
     is the empty family).
  3. Spanning-preservation: `Spans(g)` + `InSpanOrZero(g∘skip(value j), g(j))` ⟹
     `Spans(g∘skip(value j))`. Every `g(index)` is in `span-or-zero(g∘skip)`:
     `index≠j` ⟹ member (skip surjectivity); `index=j` ⟹ the hypothesis. Then a
     zero-aware transitivity (reuse `InSpanOf.transitive`, handle the `=0` leg).
  4. Induction on `size`: base `size=0` ⟹ `IsBasis(g)` (empty family: independence
     vacuous, `Spans(g)` given) ⟹ `FiniteDimensional` at `n=0`; step, excluded
     middle on `∃j. Spans(g∘skip(value j))` — right ⟹ IH at `count`; ¬ ⟹ prove
     `LinearlyIndependent(g)` (via the redundancy contrapositive) ⟹ `IsBasis(g)`.
  5. `FinitelyGenerated.finite_dimensional` = choose generators, apply the helper.
  Keeps the bundled `FiniteDimensional` record and the unbundled existence view in
  sync (Stage F builds the record).

**Phase 2 — automation interlude (leverage before F/G/H)**
- [ ] **Σ-sugar** (S, elaborator/display) — a `Σ (i < count) …` binder that
  parses to / prints as `VectorSpace.linearCombination(…)`. Pure notation, no
  proof-engine change. Makes everything already built and F/G/H read like maths.
- [x] **Norm-a — DONE (2026-07-14).** The `group` tactic gained an abelian mode
  over `VectorSpace.carrier`: sorts the reduced word (via `add_commutative`) and
  re-cancels, unfolds `VectorSpace.subtract`. Closes `(a+b)-a=b`, the medial law,
  and additive rearrangements — by `group` and as bare calc steps
  (`src/elaborator/group.cpp`, `Test/vector_group_test.math`). Retired
  `add_subtract_cancel_left` + `add_pair_interchange` (deleted) and collapsed the
  assoc/comm chains in `exchange_lemma`/`basis_pruning`/`linear_combination`.
  `a•v` stays opaque (that is tier b = **Norm-b** below). Gates green,
  export-check 2858, axioms unchanged.
- [ ] **Norm-b** (L, elaborator/tactic) — free-module `linear_combination`
  normaliser: treat each distinct vector as an atom, normalise both sides to a
  canonical `Σ cᵢ • vᵢ` by collecting like terms (adding coefficients in the
  field, discharged by `ring`/`field`), compare atom-by-atom. Subsumes Norm-a;
  collapses the `linearCombination_*` algebra and the coordinate manipulation in
  `exchange_lemma.math` to one-liners. Highest-impact automation this branch has
  surfaced (owner-requested). Full design in `STRESS_PROBES.md` (Steinitz
  verdict + side-quest).

**Phase 3 — dimension + headlines** (Stage F/G/H detail lives in the build-order
section below)
- [x] **Stage F — CORE DONE (2026-07-14, `Algebra/dimension.math`).** `dimension`
  (choice-free finite invariance from the exchange lemma) + `SameDimension`. The
  transport crux the branch was built to measure turned out FRICTIONLESS —
  pre-paid at the exchange bridge (see the Stage F ledger entry + STRESS_PROBES).
  Remaining (deferred, optional): the bundled `FiniteDimensionalVectorSpace`
  record (Stage 0.3) — build when Stage G wants it.
- [x] **Stage G** (L, math) — **rank–nullity** (headline #1): `dim ker T + dim im T
  = dim V` for `T : V → W` linear, `V` finite-dimensional, choice-free. **DONE
  2026-07-14 — `LinearMap.rank_nullity` proved in `Algebra/rank_nullity.math`,
  library+tests+export-check 2888 green, axiom inventory UNCHANGED (choice-free).**
  All five bricks landed: brick 4 `VectorSpace.extend_to_basis` (sift a basis of V
  through `sift_extend_aux`, growing the family with `appendVector` only on
  out-of-span vectors, exact-prefix tracking by value-match — the size stays a
  running `sz` with a carried `sz = k + r` equation, so no `NaturalsBelow(k+r)`
  index transport); brick 5 = `LinearMap.appended_images_span`
  (`spans_of_value_covered` + the new disjunctive `InSpanOf.of_combination_covered`,
  which routes empty combinations to the "=0" leg and so NEVER needs an
  index-inhabitant — this killed the zero-vector-inhabitant obstruction) and
  `LinearMap.appended_images_independent` (standardize the kernel expansion into an
  identity selection over `[0,k)` via `linearCombination_standardize`, reindex the
  appended combination into `ext` over `[k,sz)`, CONCATENATE over the disjoint
  ranges — injective because the ranges never collide — and apply `ext`
  independence). The n=m/subtype transport thesis HELD end-to-end: the whole
  subtype cost stayed confined to brick 1's `Subspace.linearCombination_value`; the
  real Stage-G cost was the finite-family concatenation algebra (selection
  injectivity across disjoint index blocks), exactly as the earlier verdict
  predicted. GOTCHAS banked in memory ([[linear_algebra_build]]): the `Spans`
  by-citation fold-desync (Spans unfolds to `Or`) forced proving `Spans` via an
  explicit `take x` block, not a `done by <lemma>` citation; `NaturalsBelow.clamp`
  under a `let` needs explicit `clamp_below` args (or a once-cited value-lemma);
  `decompose_at_least`'s context auto-discharge misfires in reversed calc steps
  (pass the `atLeast` proof explicitly). The "finite-family
  construction" infra the earlier verdict flagged as missing was BUILT first: the
  `module` tactic (tier-b, separate deliverable), `appendVector` + its
  characterising lemmas, `linearCombination_drop_zero_position` (the position-skip),
  the append lemma `independent_append_outside_span` (a vector outside span(e)
  extends independent e — the hard one, via `dropIndex_redundant`+`InSpanOf.transitive`
  and the drop lemma for injectivity), brick 3 `subspace_finite_dimensional` (subspace
  of f.d. is f.d., maximal-independent via `Natural.least_witness`), and
  `NaturalsBelow.widen`/`InSpanOf.append_monotone`. REMAINING: brick 4 = sift `e ++
  basisV` appending out-of-span vectors (exact-prefix tracking through
  `NaturalsBelow(k+r')`) to a basis of V extending the ker-basis; brick 5 = the
  appended images are a basis of `im T`, giving `dim V = dim ker T + dim im T`.
  (Earlier note, now superseded: bricks 3–5 were flagged blocked on this infra —
  it exists now.) Brick 1
  (`Subspace.linearCombination_value` + independence/spanning value-transport
  corollaries) compiled first try — the `Subtype`/`Subspace` boundary the branch
  was built to measure is FRICTIONLESS (confirms the Stage F thesis: one reusable
  transport lemma confines the whole subtype cost). Brick 2
  (`LinearMap.image_finite_dimensional`, on `LinearMap.apply_linearCombination`):
  `im T` finite-dimensional. **Finding: the real Stage-G cost is NOT the subtype
  boundary but building a size-`k+r` `NaturalsBelow`-indexed basis (append the
  ker-basis / concatenate) and re-proving `LinearlyIndependent` — its injective-
  selection requirement collides under any `NaturalsBelow(1+m)→NaturalsBelow(m)`
  reindex, needing a *position-skip* fold lemma that doesn't exist yet
  (scope ≈ one of exchange/pruning). Filed as a side-quest.** Route = basis
  extension (avoids `Quotient`).
  Available foundation: `LinearMap` + `kernel`/`image` as subspaces
  (`kernel_is_subspace`/`image_is_subspace`, `linear_map.math`),
  `Subspace.vector_space` (induced space, carrier = `Subtype(V.carrier, member)`),
  `dimension` + `dimension_equals` (Stage F), `exchange`/`independent_le_spanning`
  (Steinitz), `FinitelyGenerated.finite_dimensional` (pruning), the full
  `InSpanOf`/`Spans`/`LinearlyIndependent` API, and the abelian `group` normaliser.
  Concrete sub-lemma decomposition (each its own brick, land green + commit):
  1. **Subspace subtype-transport bridge (THE crux, do first).** Relate a
     `linearCombination` in `Subspace.vector_space(V, S, sub)` to one in `V`
     through `Subtype.value`: `Subtype.value(linearCombination_subspace(fam, c,
     sel, k)) = linearCombination_V((i)↦Subtype.value(fam(i)), c, sel, k)` (induct
     on `k`, peel `linearCombination_add_one`, reduce `Subspace.add`/`scale` to
     `V`'s ops via `Subtype.equal_of_value_equal` — the Stage-C reduction). This
     is the transport the branch was built to MEASURE; record its cost in
     STRESS_PROBES. Corollaries: independence/spanning transport between a
     subspace family and its value-image in `V`.
  2. **`im T` is finite-dimensional.** `T ∘ (basis of V)` lifted into the image
     subtype (`i ↦ Subtype.make(T(b(i)), ⟨witness b(i)⟩)`) SPANS
     `Subspace.vector_space(W, image, image_is_subspace)` — every image element is
     `T(v)`, `v = Σcᵢbᵢ`, so `T(v) = Σcᵢ T(bᵢ)` by additivity+homogeneity (bridge
     (1) + `LinearMap.additive`/`homogeneous`). ⟹ `FinitelyGenerated` ⟹ f.d. by
     pruning. Let `r := dim im T`.
  3. **`ker T` is finite-dimensional.** A subspace of a f.d. space is f.d.: any
     independent family in `ker T` is independent in `V` (bridge (1)) so ≤ `dim V`
     by `independent_le_spanning`; maximal-independent = basis. Cleanest concrete
     form: adapt the pruning argument to grow a basis of `ker T` (or prove the
     general "subspace of f.d. is f.d." lemma once and reuse for both). Let
     `k := dim ker T`.
  4. **Basis extension (Steinitz corollary).** A basis `e_0..e_{k-1}` of `ker T`
     (as independent vectors in `V`) extends to a basis `e_0..e_{k-1}, a_0..
     a_{r-1}` of `V` by appending spanning vectors not yet in the span (the
     `independent_or_droppable`/`InSpanOf` machinery from pruning, run in the
     growing direction). So `dim V = k + r'` where `r'` = number appended.
  5. **The appended images are a basis of `im T`.** `T(a_0)..T(a_{r'-1})` are
     independent (a vanishing combination pulls back into `ker T ∩ span(a)= {0}`)
     and span `im T` (from step 2's spanning). ⟹ `r' = r = dim im T`
     (Stage F invariance). Conclude `dim V = dim ker T + dim im T`.
  FRICTION TO WATCH (record in STRESS_PROBES): the `Subtype`/`Subspace` value
  boundary — every basis of `ker T`/`im T` lives in a subtype, and steps 4–5 move
  vectors between the subtype and the ambient `V`/`W`. Bridge (1) is meant to
  confine that cost to one reusable lemma; whether it stays confined is the
  finding. Keep bases `Natural`-indexed with bounded predicates where the exchange
  architecture already paid off, `NaturalsBelow` only at the `dimension` boundary.
  New file: `Algebra/rank_nullity.math` (+ maybe `Algebra/subspace_dimension.math`
  for the subtype-transport bridge + "subspace of f.d. is f.d.", if it wants to be
  reusable for Stage H).
- [x] **Stage H0** (M, math) — permutation **sign/parity** — DONE (built as
  brick 3, `Algebra/permutation_sign.math`: sign + multiplicativity).
- [x] **Stage H** (M–L, math) — **det(AB) = det(A)·det(B)** (headline #2) — DONE
  2026-07-16 (`Matrix.determinant_multiply`, export-check 3122, choice-free).

**Cross-cutting (deferrable throughout)**
- [ ] **AC infra** (M, infra) — `Logic/choice.math` (`AxiomOfChoice` Prop +
  Zorn/well-ordering) + AC-gated *general* (infinite-dimensional) invariance.
  CONFIRMED ABSENT. Needed ONLY for non-well-orderable-space basis invariance;
  the finite core (F/G/H), `F[x]`, rank–nullity, determinants never wait on it.

## What is already in place (so this isn't re-litigated)

- **The finite-index type already exists.** `NaturalsBelow(n)`
  (`Set/finite.math`) is `Subtype(Natural, k ↦ k < n)` — our `Fin n` — with
  `.make` / `.value` / `.below` and value-extensionality
  (`NaturalsBelow.equal_of_value`). **Do not invent a new `Fin`.** Build finite
  bases and matrices as families over `NaturalsBelow`.
- **Counting / cardinality is a *relation*, not a `Cardinal` value.**
  `Equinumerous(A, B)` (`Set/equinumerous.math`) is a `Proposition` (an
  equivalence relation); `HasSize(X, n)` (`Set/finite.math`) is finite,
  `Natural`-valued. There is **no `Cardinal` type**, no cardinal *order* (`≼`),
  and (apparently) no Schröder–Bernstein yet. Design dimension around
  equinumerosity + `HasSize`, not around a cardinal object (Stage F).
- **Pigeonhole / size congruences.** `Set/finite_pigeonhole.math` and the
  `HasSize`/equinumerosity congruences in `Set/finite_sum.math` are what
  finite-dimensional invariance should reduce to.
- **The bundling pattern.** `Group` / `Ring` / `CommutativeRing`
  (`Algebra/*_bundle.math`) are single-constructor dependent records in
  `Type(1)` carrying carrier + ops + the `Is…` proof, with `cases g { … }`
  projections, flattened law projections (each `claim Is…(…) since X.is_X;
  done`), and `operator` declarations. Mirror this for `Field`, `VectorSpace`,
  and `FiniteDimensionalVectorSpace`.
- **The scalar-field predicate.** `IsField(carrier, add, zero, negate, multiply,
  one)` (`Algebra/field.math`) = `IsCommutativeRing ∧ zero ≠ one ∧ ∀ x ≠ 0. ∃ y.
  x·y = 1`. The inverse is **existential**, not a function (Stage 0.2). There is
  **no bundled `Field` record yet** — Stage A creates it.
- **Generic finite aggregation is in flight.** `docs/PLAN_GENERIC_AGGREGATION.md`
  introduces `Algebra.indexedAggregate(A, op, e, s, n)` with `bigSum`/`bigProduct`,
  backed by the `List.product` fold (`Lists/list.math`) and its
  permutation-invariance (`Lists/permutation.math`). **Linear combinations are
  `bigSum` over the vector abelian group**, so Stage D is downstream of that
  layer's Stage 1. Coordinate; do not roll a second fold.
- **Unique choice is already here.** `Logic.the` (definite description) is the
  *unique*-existence sibling of the choice axiom we are preparing for; the global
  AC axiom, if ever added, is literally `Logic.the` with the uniqueness
  requirement dropped. `Quotient.*` is available if a `Cardinal` type or the
  quotient route to rank–nullity is ever wanted.

## Axiom-of-choice architecture (prepare for AC without adopting it)

Goal: every choice-needing theorem is proven *today* as an honest conditional,
so "turning AC on" is later a one-axiom, purely additive change that invalidates
nothing.

- **`Logic/choice.math` — the gate.** Define choice as a `Proposition`
  (choice-function form):
  `AxiomOfChoice := ∀ (I : Type(0)) (A : I → Type(0)) (R : ∀ i. A(i) → Proposition).
  (∀ i. ∃ x. R(i, x)) → ∃ (f : ∀ i. A(i)). ∀ i. R(i, f(i))`.
  Prove, once and conditionally, the standard equivalences
  `AxiomOfChoice → Zorn` and `→ WellOrdering` (real but standard work). Keep it
  `Type(0)`-level for now; note that a universe-polymorphic restatement may be
  wanted when the algebra cluster (maximal ideals, algebraic closures) arrives.
  This file is **general infrastructure**, not linear-algebra-specific; LA is
  just its first customer.
- **Thread, never adopt.** A theorem that genuinely needs choice takes an
  explicit `(choice : AxiomOfChoice)` parameter and discharges its existentials
  through it (or through the derived `Zorn`). Theorems without the parameter are
  verifiably choice-free. Do **not** write `axiom Logic.choice`.
- **Confine choice to `Proposition` positions.** Use a threaded `choice` only to
  inhabit `Proposition`s, never to construct `Type`-level data you then compute
  on. The design already respects this: basis *existence* is a `∃` (a Prop), and
  the finite-dimensional bundle carries an *explicitly constructed* basis, never
  one pulled from choice. This keeps the eventual non-reducing axiom
  computationally irrelevant.
- **"Turn it on" later (do not write yet).** A future one-line
  `axiom Logic.choice : AxiomOfChoice` plus a thin file of unconditional
  restatements (feeding the axiom to discharge each `(choice : …)` hypothesis).
  Monotone and additive. We may also choose to leave everything conditional
  forever.

## Stage 0 — decisions to settle before writing structure

1. **Bundle a `Field`.** `Algebra/field_bundle.math`: a `Field` record =
   `CommutativeRing` + `zero ≠ one` + the inverse witness, mirroring
   `CommutativeRing.make`. `VectorSpace` is indexed by a `Field` so scalar
   multiplication recovers the scalar field from the operand type (the implicit
   recovery `RingModulo` uses for its modulus). Universe note: `Field : Type(1)`,
   and a `VectorSpace` carrying a `Field` *value* + a `Type(0)` carrier should
   still land in `Type(1)` — confirm before building on it.
2. **Reciprocal as a function.** The exchange step divides by a nonzero scalar,
   but `IsField` only gives `∃ y. x·y = 1`. The field inverse is **unique**, so
   derive a reciprocal *function* via `Logic.the` over that unique existence —
   stays inside LEM + unique choice, adds no axiom. Add `Field.reciprocal`
   (nonzero arg) and its characterizing lemma. Reach for nothing stronger than
   description here.
3. **Two structure layers, named distinctly.** The general `VectorSpace`
   (Stage B) is unrestricted. `FiniteDimensionalVectorSpace` (Stage 0.3 bundle)
   is a *separate, stronger* record layered over it — like `CommutativeRing` over
   `Ring` — additionally carrying `dimension : Natural`, a
   `basis : NaturalsBelow(dimension) → carrier`, and its `IsBasis` proof. Only
   this layer has a `dimension`; a bare `VectorSpace` has none (and shouldn't).
   Also prove the unbundled existence theorem "finitely generated ⟹ has a finite
   basis" (Stage E) — choice-free, keeps the bundled and unbundled views in sync.
4. **Linear-combination index shape.** `indexedAggregate` folds `s : Natural → A`
   over the first `n`. Pick one bridge to `NaturalsBelow`/`I`-indexed families and
   use it everywhere; record it in the aggregation plan so it is shared.

## Build order (each stage ends green under `make -j 16 library`)

- **Stage A — `Field` bundle + reciprocal.** Per Stage 0.1–0.2. Instances: ℝ, ℚ,
  a `FiniteField`. Flattened law projections + `Field.reciprocal` and
  `x ≠ 0 → x · reciprocal(x) = 1`.
- **Stage B — `VectorSpace` over a `Field` (general, unrestricted).**
  `Algebra/vector_space.math`: `IsVectorSpace(field, carrier, add, zero, negate,
  scale)` (abelian group on vectors + the four scalar-action laws), then the
  bundled `VectorSpace` record. Instances: the **standard space `Fⁿ`** as
  `NaturalsBelow(n) → F` (also the first real `NaturalsBelow`-indexed object),
  and `F` over itself. A `scale` operator with a symbol distinct from `·`.
- **Stage C — subspaces and linear maps.** `Subspace` (carrier predicate closed
  under `add`/`scale`, plus the induced `VectorSpace`), `LinearMap` (preserves
  `add` and `scale`; reuse the `Algebra/group_homomorphism.math` idiom), and
  `kernel`/`image` as subspaces.
- **Stage D — span, independence, finite generation; index-generic `IsBasis`.**
  Linear combinations via `bigSum` over the vector group (gated on
  `PLAN_GENERIC_AGGREGATION` Stage 1). Define over an **arbitrary index type
  `I`** (so infinite bases are first-class), with finiteness living in the
  combinations, not the basis:
  - `Spans(f : I → V) := ∀ v. ∃ k, ∃ (σ : NaturalsBelow(k) → I), ∃ c.
    v = bigSum(i ↦ scale(c(i), f(σ(i))))`.
  - `LinearlyIndependent(f : I → V) :=` for every **injective**
    `σ : NaturalsBelow(k) → I` and coefficients `c`,
    `bigSum(i ↦ scale(c(i), f(σ(i)))) = zero → ∀ i. c(i) = zero`.
  - `IsBasis(f) := LinearlyIndependent(f) ∧ Spans(f)`.
  Injective `NaturalsBelow(k) → I` selections keep this agnostic to decidable
  equality on `I` and reuse the `bigSum`/`NaturalsBelow` toolkit. `I = Natural`
  gives infinite bases; `I = NaturalsBelow(n)` is the finite case (identity
  selection).
- **Stage E — basis existence (finite) + Steinitz + `F[x]`.** `FinitelyGenerated`;
  the **exchange lemma** (independent ≤ spanning, swapping one vector at a time —
  where `Field.reciprocal` is used); **finitely generated ⟹ has a finite basis**
  by pruning a finite spanning set (choice-free). Define
  `FiniteDimensional(V) := ∃ n, ∃ (b : NaturalsBelow(n) → carrier), IsBasis(b)`.
  Worked **infinite-dimensional instance**: `F[x]` with `{xⁿ}` as a `Natural`-indexed
  basis — independence (a nonzero polynomial has a nonzero coefficient) and
  spanning (every polynomial is a finite combination of monomials) are both
  direct and choice-free. *Check the existing `Polynomial` representation first*:
  if polynomials are finite coefficient lists / finite support, spanning is
  near-definitional.
- **Stage F — dimension.** Define the **general relation**
  `SameDimension(V, W) := (a basis of V) Equinumerous (a basis of W)` — no
  `Cardinal` type needed. Then split invariance on choice:
  - *Finite-dimensional invariance (choice-free).* From the exchange lemma, any
    two `NaturalsBelow`-indexed bases of a fixed space are equinumerous, hence
    equal `HasSize` via the `Set/finite` congruences. Gives
    `dimension : FiniteDimensionalVectorSpace → Natural` and well-definedness.
    **This is the transport crux** — the size-equality is a propositional `n = m`
    you transport bundled data along; record how heavy it is.
  - *General invariance (AC-gated).* "All bases of an arbitrary `V` are
    equinumerous" is **not** a ZF theorem (Läuchli-style models give a space with
    bases of different cardinalities); the standard proof leaks choice in the
    cardinal arithmetic `κ·ℵ₀ = κ` and the uniform enumeration of finite
    supports. State it in `Algebra/dimension_general.math` threading
    `(choice : AxiomOfChoice)`. Note the free win: **countable-dimensional spaces
    (e.g. `F[x]`) get invariance choice-free** because the whole space is
    well-orderable — so `F[x]`'s basis is provably `Equinumerous(_, Natural)`
    (choice-free), and any basis is provably infinite (choice-free); only
    invariance for *non-well-orderable* spaces (Hamel basis of ℝ over ℚ) needs
    `choice`.
- **Stage G — rank–nullity (headline #1).** Finite-dimensional, choice-free.
  Route: extend a basis of `ker T` to a basis of `V` (Stage E exchange/extension);
  the `T`-images of the extension vectors form a basis of `im T`; count. Avoids
  `Quotient`. (Alternative: `V/ker T ≅ im T` via `Quotient` — also a fine probe;
  pick one, note why.)
- **Stage H — determinants (headline #2).** Matrices as `NaturalsBelow(m) →
  NaturalsBelow(n) → F`; matrix multiply via `bigSum`. Determinant as the signed
  sum over permutations of `NaturalsBelow(n)`. **Prerequisite to confirm first
  (Stage H0):** `Lists/permutation.math` has permutations and product-invariance,
  but the **sign / parity** of a permutation may be missing — if so, build it
  (inversions, or parity-of-transposition-count well-definedness). Then
  `det(AB) = det(A)·det(B)`. This is the Sₙ-flavored dependent-index probe,
  complementary to F/G's transport-heavy one.

### Stage H sub-plan (started 2026-07-14)

**H0 scouting findings (confirmed):**
- `Lists/permutation.math` is the Coq-style **list-rearrangement** relation
  (`List.Permutation` over `List(A)`), NOT the bijection group. It gives
  `List.Permutation.product_invariant` (a commutative-associative fold is
  order-blind) — reusable for reindexing an `indexedAggregate`, but it is not
  the permutation OBJECT determinants sum over. **Sign/parity: absent. Build it.**
- No `Algebra/matrix*.math`, no `determinant` anywhere. Clean slate.
- Aggregation = `Algebra.indexedAggregate(A, op, e, s, n)` over
  `NaturalsBelow`-style `s : Natural → A`, `n : Natural` count. Rich toolkit:
  `_pointwise` `_split` `_shift` `_add` `_scale` `_constant`
  `commutative_monoid_interchange` `_is_fold` `_eq_list_product`. (There is no
  separate `bigSum`/`bigProduct` symbol — use `indexedAggregate` directly.)
- Bijection engine = `Set/equinumerous.math`: `Function.IsInverse` (two-sided),
  `identity_is_inverse`, `compose_inverse`, `inverse_swap`,
  `IsInjective`/`IsSurjective`/`IsBijective` bridges.
- Finite pigeonhole = `Set/finite_pigeonhole.math`:
  `NaturalsBelow.injective_domain_le_codomain`, `no_injection_when_smaller`,
  `pigeonhole_redirect*` — the tools for "a self-injection of `NaturalsBelow(n)`
  is bijective".

**Representation decision:** a permutation of `NaturalsBelow(n)` is carried as an
explicit **inverse pair** — a single-constructor record `Permutation(n)` holding
`forward`, `backward : NaturalsBelow(n) → NaturalsBelow(n)` and a
`Function.IsInverse(forward, backward)` proof. Carrying the inverse explicitly
(not an existential `IsBijective`) is what made `Equinumerous` an equivalence
constructively, and it lets `compose`/`inverse`/`identity` reuse the equinumerous
engine directly. Group laws are then immediate.

**Brick order (each its own file/section, committed green before the next):**
1. **`Algebra/finite_permutation.math` — the group `Sₙ`** — DONE (ad1a36b3):
   `Permutation(n)`, `apply`, `identity`, `compose`, `inverse`; group laws;
   extensional equality (`equal_of_apply_equal` via `make_equal` + funext).
2a. **Transpositions** — DONE (12f32473): `swap(a,b)` via a classical `if`,
   involution, self-inverse, `apply_swap_*`.
2b. **Extend across the boundary** — DONE (f54290ae): `extend(σ) : Permutation(1+m)`
   fixing the top, via `Function.extendBelow` (no dependent-`if`).
2c-i. **Restrict** — DONE (6fcb23ec): `restrict(τ, fixesTop) : Permutation(m)`;
   `extend`⇄`restrict` mutually inverse (`extend_restrict`/`restrict_extend`).
2c-ii. **Enumeration LIST** — DONE (`Algebra/permutation_enumeration.math`):
   `Permutation.allPermutations(n) : List(Permutation(n))` with
   `allPermutations_complete` (every τ) + `allPermutations_distinct` (each once).
   All gates green (library+tests+export-check 2974, axiom inventory UNCHANGED —
   choice-free). Structure:
   - **`NaturalsBelow.enumerate(n) : List(NaturalsBelow(n))`** (the index list) +
     `enumerate_complete`/`enumerate_distinct`, then `Permutation.insertRow(σ) =
     map(rowElement(σ), enumerate(1+m))` where
     `rowElement(σ,j) = swap(top,j) ∘ extend σ`; `concatRows(m)` recurses on the
     LIST (m fixed) as `empty↦empty`, `prepend(σ,rest)↦append(insertRow σ,
     concatRows rest)`; `allPermutations(1+m) = concatRows(m, allPermutations(m))`.
   - **DEPENDENT-INDEX RECURSION over the sealed Natural — THE key technique.**
     `enumerate` and `allPermutations` both have result type indexed by the
     recursion variable (`List(NaturalsBelow(n))` / `List(Permutation(n))`), and
     the `1+m` step spelling is NOT defeq the `successor` the recursor eliminates
     on. A manual `Equality_recursor` transport type-checks but REFUSES to
     ι-reduce (the recursor needs a *syntactic* `refl`, and `one_add(m)` is not),
     stranding every downstream proof. FIX that works: write the arm as
     `| 1 + m => unfold Natural.add in <body-at-1+m>` — the unfold makes
     `1+m ≡ successor m` while checking the arm, so the arm stores an honest
     `1+m`-typed body with NO transport, and the reduct is clean. The `_one_plus`
     bridge is then `unfold Natural.add in reflexivity(<body>)`. (A count-recursion
     with `n` held fixed also dodges it but drags a `count ≤ n` proof whose
     `successor`/`1+c` spelling re-bites; the unfold-in-arm route is cleaner and
     reusable for any n-indexed data recursion.)
   - **completeness** routes each τ through the top-index decomposition
     `Permutation.decompose_top` (`τ = swap(top,τ(top)) ∘ extend(lower τ)`,
     built here with `lower`, `restrict_congruence`, `swap_compose_self`);
     membership via `member_append_left/right` + `map_member` + `concatRows_member`.
   - **distinctness**: per-row via `rowElement` injectivity (`compose_right_cancel`)
     + `enumerate_distinct`; cross-row disjointness because `lower` RECOVERS σ from
     any row member (`lower_of_row` / `insertRow_member_lower`), so distinct σ give
     disjoint rows; assembled by the new `List.distinct_append` +
     `member_append_invert` over the distinct level-m list. New Lists lemmas:
     `member_append_invert`, `distinct_append`, `range_up_complete/_member_lt/
     _distinct` (the range_up API completion; range_up ended up unused once the
     index list moved to `enumerate`, kept as legitimate API).
   The det sum is `indexedAggregate`/`List.product` over `allPermutations`.
3. **Sign** — DONE (`Algebra/permutation_sign.math`): `sign(σ) : Integer`
   `sign_is_unit` (∈ {−1,+1}), `sign_identity` (=1), and **multiplicativity**
   `sign_compose : sign(σ∘τ) = sign σ · sign τ`. All gates green (library + tests +
   export-check 3016, axiom inventory UNCHANGED — choice-free). **ROUTE: the product
   formula** `sign(σ) = ∏ orient(σi,σj)` over `orderedPairs(n)` (the value-ordered
   filter of the index enumeration's Cartesian square), `orient(x,y) = if
   value(x)<value(y) then 1 else −1`. Multiplicativity was ONE pair reindexing:
   `pairFactor` gives `pairOrient(σ∘τ,p) = pairOrient(τ,p) · pairOrient(σ,pairImage(τ,p))`
   pointwise (via orient antisymmetry), `product_pointwise_multiply` splits the map
   product, the τ-factor reassembles `sign τ` directly, and the σ-factor — reindexed
   by `pairImage(τ,·) = sort(τ·,τ·)`, which permutes `orderedPairs` (`pairImage_permutes`
   via `permutation_of_distinct_inclusion`, injectivity from the two-sided
   `pairImage_cancel`) — reassembles `sign σ` by `product_invariant`. New reusable
   Lists infra: `cartesianProduct` (+member/distinct), `map_map`, `Permutation.map`,
   `map_congruence_on`, `product_of_ones`/`product_of_units`, `product_pointwise_multiply`.
   The route beat inversion-parity/transposition-generation exactly as predicted (no
   transposition-flip counting). Whether `sign(swap(a,b)) = −1` is needed for brick 6
   — derive it then (multiplicativity + a direct 2-index computation).
4. **`Algebra/matrix.math`** — DONE (58339472): `Matrix(f, rows, columns) :=
   NaturalsBelow(rows) → NaturalsBelow(columns) → Field.carrier(f)`;
   `Matrix.multiply` (entry = inner product over the shared middle index) +
   `Matrix.multiply_entry`. All gates green (library + tests + export-check
   3020, axioms UNCHANGED — choice-free). **Design deviation from "via
   indexedAggregate":** the inner sum runs over the index enumeration list
   `NaturalsBelow.enumerate(middle)` (through the new reusable `Field.sumOver(term,
   items) = List.product ∘ List.map` field list-sum), NOT `indexedAggregate` over
   `Natural`. Reason: `indexedAggregate` reads a `Natural → carrier` summand, so a
   matrix entry `A(i, k)` would need a total `Natural → NaturalsBelow(middle)`
   clamp with a fallback — impossible to produce at `middle = 0`. Summing over
   `enumerate(middle)` lets the summand read `NaturalsBelow(middle)` directly
   (no clamp) and `middle = 0` is the empty list. This is ALSO the shape brick 5
   (Leibniz sum over the permutation list) and brick 6 (sum over the enumerated
   function space) need — the outer sums have no `indexedAggregate` "count", they
   are inherently List enumerations, so `Field.sumOver`-over-a-list is the uniform
   Stage-H aggregation primitive. `m`/`n`/`p` kept as literal `Natural` variables.
5. **`determinant(M)`** — DONE (37ba69eb): `Matrix.determinant(matrix) =
   Field.sumOver((σ) ↦ Field.from_integer(f, sign σ) · Field.productOver((i) ↦
   matrix(i, apply(σ,i)), enumerate(n)), allPermutations(n))` in
   `Algebra/determinant.math`, + `Matrix.determinant_expansion` (definitional
   restatement). All gates green (library + tests + export-check 3030, axioms
   UNCHANGED — choice-free). **The sign embedding** (the plan glossed "sign(σ)·…"
   over the field, but sign : Integer): built `Algebra/ring_from_integer.math` —
   `Ring.from_integer : Integer → Ring.carrier(r)` the initial-ring map (`a−b ↦
   from_natural(a)−from_natural(b)`, lifted across Integer's difference quotient),
   with `from_integer_at_difference`/`_one`/`_negate_one`; `Field.from_integer(f,z)
   = Ring.from_integer` on the field's underlying ring (carrier defeq
   `Field.carrier`). `Field.productOver` added as the multiplicative companion of
   brick-4's `Field.sumOver`. GOTCHAS: (a) `linear_combination` does NOT work over
   an abstract `Ring.carrier` (only `CommutativeRing`/`Field`); the from_integer
   respect subtract-equality is proved via `substituting` + additive-only `ring`
   rearrangements (abstract Ring `ring` closes +-assoc/comm only). (b) `IntegerEquivalent(rep1,
   rep2)` after `let ⟨a,b⟩`/`let ⟨c,d⟩` is defeq `a+d=b+c` but not syntactic —
   extract it as `a + d = b + c by equivalent as crossNat` before `substituting`.
   (c) `negate(one)` is not defeq `from_difference(0,1)` in a calc-start — bridge
   with `negate(one) = from_difference(0,1) by unfolding Integer`.
6. **`det(AB) = det(A)·det(B)`** — IN PROGRESS. Leibniz expansion, non-injective
   terms collapse (alternating), reindex the surviving sum over `Sₙ`.
   **DONE so far — the reusable field/list aggregation backbone**
   (`Algebra/field_aggregation.math`, commits d8977c70 + abdd3c1e; owns
   `Field.sumOver`/`Field.productOver`, moved here from matrix/determinant): the
   permutation-free algebra every Leibniz step needs —
   `sumOver`/`productOver` `_empty`/`_prepend`/`_append`/`_map`/`_congruence`;
   `sumOver_scale_left`/`_right`; `sumOver_multiply_sumOver` (bilinear
   `(Σa)(Σb)=ΣₓΣ_y aₓb_y`); `sumOver_add`; `sumOver_zero_function`;
   **`sumOver_interchange`** (Fubini — swap the σ/φ double sum); **`productOver_multiply`**
   (`∏xᵢyᵢ=(∏xᵢ)(∏yᵢ)` — split `A(i,φi)·B(φi,σi)`). All clean list inductions,
   `ring` for field rearrangements. Gates green through export-check 3046.
   **REMAINING (the hard combinatorial core — multi-session):**
   - **(6a) function-space enumeration + generalized distributivity** — DONE
     (`Algebra/function_enumeration.math`). DESIGN DECISION RESOLVED: **Option A
     (function objects)** — φ : NaturalsBelow(n) → NaturalsBelow(n), enumerated by
     `Function.functionsBelow(C, choices, k)` via a codomain-fixed,
     domain-widening recursion (extend-by-value on the top index), riding the
     same `unfold Natural.add in <arm>` dependent-index bridge as allPermutations.
     Timeboxed allFunctions+completeness attempt came in CLEAN (no fight), so
     committed to A. Landed: `Function.extendByValue` + apply lemmas
     (`_below`/`_inclusion`/`_top`) + `extendByValue_decompose` (via
     Function.extensionality); `functionsBelow`/`allFunctions` +
     `functionsBelow_complete`/`allFunctions_complete`; and the headline
     `Field.productOfSums_distributes` `∏_{i<rows} Σ_{c∈choices} h(i,c) =
     Σ_{φ∈functionsBelow} ∏_{i<rows} h(i,φi)` (induction on rows; step peels the
     top row, applies IH to the restricted h'(x,c)=h(inclusion(m,x),c), matches
     the bilinear double sum against concatenated rows via Fubini) with corollary
     `Field.productOfSums_over_allFunctions` (C=NB(n), choices=enumerate(n)).
     Helpers `sumOver_concatFunctionRows` + `productOver_extendByValue_split`.
     The row-type tension dissolved by keeping h on NB(rows) and restricting in
     the IH — no NaturalsBelow embedding. `allFunctions_distinct` NOT yet built
     (needed only for the 6d reindex). Gates: export-check 3067, choice-free.
   - **(6b) `sign(swap(a,b)) = −1`** — DONE (`Algebra/permutation_transposition_sign.math`).
     `Permutation.sign_swap`: transposition of distinct indices is odd. Route as
     planned: reduce to value(a)<value(b) (`swap_symmetric`), induct on the
     value-distance (`sign_swap_gap`, statement `value(b) = (1+d)+value(a)`); the
     step conjugates by an adjacent transposition swap(a,c), value(c)=value(a)+1,
     via `swap_conjugate_by_swap` (swap(a,c)∘swap(a,b)∘swap(a,c)=swap(c,b)) +
     `sign_compose` + `sign_swap_square` (unit) to drop the gap by one. Base
     `sign_swap_adjacent`: the adjacent swap inverts exactly the single ordered
     pair {a,b} — `pairOrient_swap_adjacent_other` (a 5-leaf value casing on i,j
     vs a,b, over `value_apply_swap_at_left/right/other`) gives +1 on every other
     pair, and reusable `List.product_isolate_single` collapses the sign-product
     to the one −1 factor. Gates: export-check 3080, choice-free. FRICTION FLAGGED
     (see [[stage_h_brick6a_decision]] / session notes): `NaturalsBelow.below(x)`
     mis-infers its implicit `n` under a `value(inclusion …) < k` ascription;
     `ring` can't see through an opaque `value(b)` that a hypothesis equates to a
     sum (name+flip the hypothesis instead).
   - **(6c) alternating collapse — DONE (2026-07-15, export-check 3094, choice-free).**
     `Matrix.alternating_collapse` (`Algebra/alternating_collapse.math`): for
     non-injective φ (φa=φb, a≠b), `Σ_σ sign(σ)·∏_i B(φi,σi) = 0`. Landed exactly as
     scoped — genuine orbit-pairing, no `Σ=−Σ`. Four units, committed separately:
     (1) `Lists/remove.math` — `List.remove` (drop first occurrence, classical
     head/x decision) + `remove_member_subset/_complete/_ne`, `remove_distinct`,
     `length_remove_member`. (2) `Field.sumOver_remove` (in field_aggregation).
     (3) `Algebra/involution_pairing.math` — `Field.sumOver_involution_pairing`: sum
     over a distinct list closed under a fixed-point-free sign-reversing involution
     = 0, by STRONG INDUCTION on length, removing the head's 2-element orbit each
     step (each orbit's two terms sum to zero). Char-FREE. (4)
     `Matrix.alternating_collapse` — instantiates the pairing lemma at ι = σ↦σ∘swap(a,b)
     on `allPermutations(n)`: closure from `allPermutations_complete`, fixed-point-free
     from `apply_injective`, involutive from `swap_compose_self`, reversing from the
     paired products being equal (`Field.productOver_permutation` reindexes the index
     product by the transposition; φ∘swap = φ since φa=φb) and the sign flipping
     (`sign_swap`=−1 + `sign_compose`, cased on `sign_is_unit` to dodge a general
     `from_integer_multiply`). Helpers `Field.from_integer_one`/`_negate_one`.
     GOTCHAS banked: `by cases` on a bare `head=x` eagerly substitutes head→x (use an
     explicit `head=x ∨ ¬(head=x)` disjunction); a `↦`-lambda body inside
     `induction … using strong_induction` drops the expected type (use statement-form
     `take`/`suppose`); a relation chain is the CLAIM not a `by`-justification;
     `substituting` takes ONE equation (split calc steps); the unused-`memTail` warning
     flags the NAME not the FACT (drop `as`, keep the line). Original scoping kept below.
     **SCOPING (2026-07-15, before a fresh Stage-H session):**
     - **CRUX subtlety — must use GENUINE ORBIT-PAIRING, not `Σ = −Σ`.** The
       tempting shortcut (reindex the sum by the involution ⟹ `Σ g = Σ g∘ι =
       Σ(−g) = −Σ g` ⟹ `2·Σ = 0` ⟹ `Σ = 0`) is UNSOUND over a general field:
       `2·S = 0 ⟹ S = 0` needs char ≠ 2. det multiplicativity must hold over any
       field (incl. char 2), so the lemma has to genuinely pair the list into
       2-element orbits `{x, ιx}` (each `g(x)+g(ιx)=0`) and sum those. Confirmed
       the intended route; do NOT take the `Σ=−Σ` bait.
     - **Missing infra (build FIRST).** No `List.remove`/`List.delete` and no
       `sumOver`/`productOver` "remove one element" lemma exist yet (checked:
       Lists/ has membership/distinct/append but no element-removal; the only
       "isolate" tool is `List.product_isolate_single` in
       permutation_transposition_sign.math). The lemma wants: `List.remove(x, L)`
       (drop first occurrence) + `Field.sumOver_remove` (`x∈L ⟹ sumOver(g,L) =
       g(x) + sumOver(g, remove(x,L))`), then STRONG INDUCTION on length removing
       the orbit `{head, ι(head)}` — `remove` twice drops length by 2, preserves
       distinctness + ι-closure. Plan: build `List.remove` + its member/length/
       distinct lemmas and `sumOver_remove` as a reusable Lists/field-aggregation
       unit, THEN the involution-pairing sum-zero lemma, THEN instantiate at
       τ=swap(a,b) on allPermutations for the collapse. Est. the pairing lemma +
       infra ≈ one exchange-sized file (~200–400 lines).
   - **(6d) injective reindex + assembly** — injective φ ⟹ bijection (pigeonhole)
     ⟹ a Permutation φ̂; C(φ)=sign(φ̂)·det(B) by reindexing σ=ρ∘φ̂ (sign_compose +
     productOver_map through φ̂); sum over injective φ ↔ `allPermutations` bridge;
     then `det(AB)=Σ_φ̂ (∏A(i,φ̂i))·sign(φ̂)·det(B)=det(A)·det(B)`.

Realistic size: multi-session. Bricks 2, 3, 6 are the cost; 1, 4, 5 are
scaffolding. ALL DONE (2026-07-16): 6-backbone, 6a, 6b, 6c, 6d — Stage H complete.

## Choice-profile guardrails

- **No global axioms.** Everything is provable from the current base
  (LEM + unique choice/description + propext + quotients), with choice-needing
  results threading `(choice : AxiomOfChoice)` (above). If any step seems to want
  more than that hypothesis provides, stop and flag it — a finding, not a license.
- **Adopting AC stays safe.** Because you are already classical, AC adds
  choice-strength only (Diaconescu's LEM is already yours), and an axiom is
  logically monotone — it can only add theorems. The two real risks,
  computational opacity and silent erosion of the choice-free core, are both
  handled by threading + the "choice only in `Proposition` positions" rule: a
  proof can use choice only if it visibly takes the hypothesis, so the auto-prover
  cannot silently declassify a choice-free result.
- **Finite-dimensional / countable layers stay unconditional.** No `(choice : …)`
  parameter on anything finite-dimensional, on `F[x]`, or on rank–nullity and
  determinants.

## Diagnostic checkpoints (the actual point of the branch)

At the end of Stages F, G, and H, record in `STRESS_PROBES.md`: how much of each
proof was transport/cast bookkeeping around `NaturalsBelow(n)` vs. mathematical
content; whether any `cases`-on-expression / dependent-motive limitation
(cf. the `*_bundle` projection notes) bit; and whether dimension transport needed
elaborator help. If transport is painful, the fix is an elaborator/automation
improvement (a transport/`cast`-normalization helper, `PLAN_CAST_NORMALIZATION.md`),
**not** a proof hack — per CLAUDE.md "fix bugs, never work around them."

## Pointers

- Conventions: `docs/conventions/structures-and-inference.md` (bundles, implicit
  inference, instances, operators), `docs/conventions/proof-style.md` (math-like
  phrasing; raw-CIC tells to avoid — read before writing proofs),
  `docs/conventions/algebra-tactics.md` (`ring`/`field`).
- Models to imitate: `Algebra/group_bundle.math`,
  `Algebra/commutative_ring_bundle.math` (structure),
  `Algebra/first_isomorphism.math` (a counting/structure proof of comparable
  shape), `Set/finite.math` + `Set/equinumerous.math` +
  `Set/finite_pigeonhole.math` (the counting toolkit).
- Hard dependency: `docs/PLAN_GENERIC_AGGREGATION.md` (land its Stage 1 before
  Stage D). New general-infrastructure file: `Logic/choice.math`.
- Tracking: tick rows in `docs/freek_100.md`; map new modules in `docs/library.md`.

## Suggested order

`Logic/choice.math` (define the `AxiomOfChoice` Prop + Zorn/well-ordering
equivalences — independent of the rest; the finite core does not wait on it) →
A → B → C → D (after generic aggregation Stage 1) → E (incl. `F[x]`) → F
(finite-dimensional `dimension` choice-free; general invariance AC-gated) →
**G (rank–nullity)** → H0 (permutation sign, if needed) →
**H (det multiplicativity)**. Stages A–F are the real cost; G and H are
comparatively short once basis/dimension and matrix/permutation scaffolding stands.

## Appendix — matrix layer and the matrix ↔ linear-map bridge (off the critical path)

This records the type design for matrices and their relationship to linear maps.
**Neither headline theorem depends on the bridge** (see "Scope" below), so this is
its own module and must not gate Stage G or H.

**Three distinct objects.** Conflating them is what makes the topic feel murky:

```
LinearMap(V, W)   -- abstract structure: apply : V.carrier → W.carrier + preservation proofs
Matrix(K, m, n)   -- pure data:          NaturalsBelow(m) → NaturalsBelow(n) → K.carrier
multiplyMatrixVector(M, v)
                  -- concrete induced map on STANDARD spaces:
                  --   (NaturalsBelow(n) → K.carrier) → (NaturalsBelow(m) → K.carrier)
                  --   := i ↦ bigSum(j ↦ M(i)(j) · v(j))
```

A `Matrix` is scalars in a grid — no maps, no spaces, no proofs. A `LinearMap`
between arbitrary spaces is a third thing. A matrix is the *coordinate
representation* of a map, and "coordinate" means "relative to chosen bases".

**The unifying idea: an ordered finite basis of `V` *is* an isomorphism
`V ≅ Kⁿ`.** For `b : NaturalsBelow(n) → V.carrier`:

```
combine(b)     : (NaturalsBelow(n) → K.carrier) → V.carrier
               := c ↦ bigSum(i ↦ scale(c(i), b(i)))          -- coordinates ⟼ vector
coordinates(b) : V.carrier → (NaturalsBelow(n) → K.carrier)  -- its inverse (vector ⟼ coordinates)
```

`IsBasis(b)` says *exactly* that `combine(b)` is a bijection: `Spans` is
surjectivity, `LinearlyIndependent` is injectivity. So `(b, IsBasis b)` is a
linear isomorphism `StandardSpace(K, n) ≅ V`. **This is why the basis must be an
ordered family `NaturalsBelow(n) → V`, not a set/predicate** — a set could not
index matrix rows/columns; the ordered family is what makes matrices definable.
(Confirms the Stage D representation choice pays off here.)

**The bridge**, with `n = dim V`, `m = dim W`:

```
matrixOf(bV, bW, T) : Matrix(K, m, n)
   := i j ↦ coordinates(bW)( T.apply(bV(j)) )(i)      -- column j = coords of T(bV(j))
mapOf(bV, bW, M)    : LinearMap(V, W)
   := combine(bW) ∘ multiplyMatrixVector(M) ∘ coordinates(bV)
```

These are mutually inverse. The theorem that earns its keep — **composition
becomes multiplication** — is the entire content of "matrices model linear maps",
and is what *forces* the definition of matrix multiplication:

```
matrixOf(bV, bU, compose(S, T)) = multiplyMatrix(matrixOf(bW, bU, S), matrixOf(bV, bW, T))
```

**Transport friction (expected, and worth measuring).**
`multiplyMatrix : Matrix(K,m,n) → Matrix(K,n,p) → Matrix(K,m,p)` needs the inner
`n`s equal *definitionally*. Same variable ⟹ fine; one `dim V` and one `dim W`
for proven-equidimensional spaces ⟹ you transport across
`NaturalsBelow(dim V) ≃ NaturalsBelow(dim W)`, the branch's core stress point.
**Keep matrices indexed by literal `Natural` variables as long as possible and
specialize to `dim V` only at the boundary**, so casts stay at the edges rather
than smeared through proofs. Record the cost in `STRESS_PROBES.md`.

**Scope — off the critical path for both probes.**
- `det(AB) = det(A)·det(B)` lives entirely in `Matrix(K, n, n)` — pure scalar
  grids, no abstract spaces, no `matrixOf`.
- The Stage G rank–nullity route (extend a basis of `ker T`, push forward) is
  basis-level and abstract — it never forms a matrix.

So build the matrix layer as its own modules whenever convenient —
`Algebra/matrix.math` (concrete grid, `multiplyMatrixVector`, `multiplyMatrix`,
`determinant`) and `Algebra/matrix_representation.math` (the `matrixOf`/`mapOf`
bridge and the composition-becomes-multiplication theorem) — and **do not let it
gate G or H**.

**Deep version (later, optional).** `LinearMap(V, W)` carries a pointwise vector
space structure, and then `matrixOf`/`mapOf` upgrades from a bijection to a
*vector-space* isomorphism `Hom(V, W) ≅ Matrix(K, m, n) ≅ K^(m·n)`. That is the
satisfying statement to aim the representation module at, but it is strictly more
than the two probes require.


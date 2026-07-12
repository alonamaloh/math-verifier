# Plan: carrier-generic finite sum/product, on the Lists fold

## Status

- **Stage 0** — decided. Carrier for binomial: `IsCommutativeRing` for now
  (no `IsCommutativeSemiring` yet; subtraction merely unused), tighten later.
  Range orientation: a new **ascending** `List.range_up(n) = [0,…,n−1]`,
  grown at the tail so `List.product`'s head-recursion and
  `indexedAggregate`'s tail-recursion line up by reassociation alone (the
  bridge needs no commutativity).
- **Stage 1** — done. `Algebra/monoid_power.math` (`Monoid.power` +
  `power_add_one`); `Lists/range.math` gains `range_up` + `range_up_add_one`;
  `Algebra/aggregation.math` has `indexedAggregate`, the `List.product`
  bridge (`indexedAggregate_eq_list_product`), and the commutative-monoid
  toolkit (`_add_one`, `_pointwise`, `_pointwise_below`, `_split`, `_add`
  via `commutative_monoid_interchange`, `_scale`, `_constant` = monoid
  power). Library green; elaborator untouched. Order lemmas + telescoping
  (need an ordered field / inverses) deferred to Stage 2 in `Real/`.
- **Stage 2** — done. `Real.partialSum` / `Real.partialProduct` are now
  defined as the additive / multiplicative `indexedAggregate` instances
  (defeq to the old recursions, so all ~12 consumers stay green untouched).
  The algebraic lemmas (`_pointwise`, `_pointwise_below`,
  `_pointwise_bounded`, `_split`, `_add`, `_scale`; product `_pointwise`,
  `_split`) are thin wrappers citing the generic toolkit — passing Real's
  monoid laws (`add_associative`, `add_zero`, …) by name and the `_scale`
  distributivity/`c·0` obligations via `ring`. Stayed Real (order / group /
  Rational-specific, no generic analogue yet): `_nonneg`,
  `_monotone_of_nonneg`, `_le_pointwise`, `_zero_term`, `_window_bound`,
  `abs_partialSum_le`, `telescoping`, `_negate`, `_subtract`,
  `_scale_right`, `_constant_cast`, `partialProduct_nonneg`,
  `partialProduct_scale`. Library green.

- **Stage 3** — in progress. **Key correction:** `ring` *already* drives
  goals over an abstract `CommutativeRing.carrier(c)` (commutativity sourced
  from the bundle — see `Test/ring_commutative_ring_test.math`), and
  `Polynomial.Sum(r, f, n)` already supplies a generic-ring summation with a
  toolkit (`shift`, `add`, `scale_left/right`, `extensional` registered as
  the rewrite-under-Σ congruence, `convolution_shift`). So generic binomial
  needs **no elaborator work** and the plan's bespoke `indexedAggregate`/
  `bigSum` mechanism is superseded by `Polynomial.Sum` for the ring case
  (Stage 1's `indexedAggregate` still backs `Real.partialSum` at the monoid
  level + the Lists bridge).
  - Done: `Algebra/ring_power.math` (`Ring.power` + `power_add_one`),
    `Algebra/ring_from_natural.math` (`Ring.from_natural` + `_one`, `_add`).
  - Done: `Polynomial/binomial.math` — `CommutativeRing.binomial_theorem`
    `(a+b)ⁿ = Σ_{k≤n} from_natural(C(n,k))·(aᵏ·bⁿ⁻ᵏ)` over `CommutativeRing`,
    via `Polynomial.Sum` + `Ring.power` + `Ring.from_natural` + `ring` (commit
    bfb1fec; `let R` cleanup 65d2813). Supporting: `Ring.power`/`from_natural`,
    `monus_one_plus_shift`, `Sum.add_one`/`Sum.shift_one_plus`. **No
    elaborator change** — `ring` already drives `CommutativeRing.carrier`, and
    `let R` does not hide commutativity (earlier claim was wrong; failures were
    content bugs + the `1+n`↔`successor` citation-matcher asymmetry, handled by
    `1 +`-form wrapper lemmas — see [[one_plus_vs_plus_one_asymmetry]]).
  - Done (dedup): the ring finite-sum + binomial moved BELOW Real into
    `Algebra/` (Real is a sibling of Polynomial, so the generic must be in
    Algebra to serve both): `Polynomial.Sum`→`Ring.Sum` in
    `Algebra/ring_summation.math`, binomial in `Algebra/binomial.math`.
    `Real.binomial_theorem` (892→124) and `ComplexNumber.binomial_theorem`
    (1195→151) are now instances via three bridges each (powers, the
    finite sum over 1+n terms, the Natural-coefficient cast), with
    `Real.commutative_ring` / `ComplexNumber.commutative_ring` bundles.
    ~1800 lines of duplicated induction removed; statements unchanged so all
    consumers are untouched. `Real.ring` moved to `Real/ring_bundle.math`.
- **Stage 4** — done (no code changes). AGM rides on the generic toolkit
  transitively: it uses `Real.partialSum`/`partialProduct` (re-backed onto
  `indexedAggregate` in Stage 2) and their lemmas — the algebraic ones it
  cites (`_split`, `_pointwise`, `_scale`) are the generic wrappers, and the
  order/power ones (`_nonneg`, `_zero_term`, `partialProduct_scale`) stay
  Real, exactly as planned. Verified: it never reinvented its own Sum/Product.

**All stages complete.** Library + tests green.

## Index bridge for finite families (PLAN_LINEAR_ALGEBRA Stage 0.4, decided 2026-07-12)

Linear-algebra combination data are **functions with a bound**, matching this
layer's native interface — never `NaturalsBelow`-indexed:

- a combination over a family `b : I → V` is `(selection : Natural → I,
  coefficients : Natural → Field.carrier(f), count : Natural)`, aggregated by
  `Algebra.Fold`/`indexedAggregate` below `count`; terms at or above `count`
  are junk the fold never reads (`_pointwise_below` is the containment lemma);
- an `I`-indexed family enters through **composition** (`i ↦ c(i) • b(σ(i))`),
  so no conversion of families is ever needed;
- side conditions (injectivity of a selection) are stated **below the bound**:
  `∀ i j. i < count → j < count → σ(i) = σ(j) → i = j`;
- `NaturalsBelow(n)` appears only as an *instance of `I`* (finite generating
  families, the Stage-E/F bundled bases), never as an aggregation index.

Rejected alternative: extending a `NaturalsBelow(k) → A` family to
`Natural → A` with a default — needs a proof-carrying conditional per use and
either a second fold or a bridge lemma family; the function+bound form needs
zero new machinery and is how the analysis layer (`Real.partialSum`) already
speaks.

## Why

`Real.partialSum` / `Real.partialProduct` (series.math, finite_products.math)
are a Real-specific finite-aggregation layer indexed by `(s : Natural → Real, n)`.
`Lists/list.math` already has a **generic monoid fold** `List.product(A, op, e,
list)` (and `List.sum` = that fold with `add`/`zero`), with `List.product_append`
as its split lemma. The two don't share code. Consequences:

- `Real.binomial_theorem` is stuck in `Real/` although it is a **commutative
  semiring identity** (no ring subtraction — the `n−k` exponent is
  `Natural.monus`, coefficients are `Natural.binomial` cast in). It belongs in
  `Algebra/` over a commutative (semi)ring.
- `arithmetic_geometric_mean` reinvents finite products/sums instead of the
  generic fold.

**Goal (owner: "do both"):** one generic aggregation that (a) keeps the
analysis-friendly *function + bound* interface and (b) is *backed by* the
`Lists` fold, generic over a commutative monoid. Then binomial → `Algebra/`
over a commutative semiring; AGM + the analysis library sit on the shared
toolkit.

## Design

`Algebra.indexedAggregate(A, op, e, s, n)` — defined by recursion on `n`
(`| 0 => e | n+1 => op(indexedAggregate(…, n), s(n))`), matching the current
`partialSum` shape so the existing proofs port. Then prove the **Lists bridge**

    indexedAggregate(A, op, e, s, n)
      = List.product(A, op, e, List.map(Natural, A, s, List.range_down(n)))   -- or range(n)

so the `Lists` lemmas (`product_append`, pairing) transfer and we genuinely use
the Lists machinery ("both": recursion interface + Lists backend).

- `Algebra.bigSum    (R, s, n) := indexedAggregate(R, R.add,      R.zero, s, n)`
- `Algebra.bigProduct(R, s, n) := indexedAggregate(R, R.multiply, R.one,  s, n)`
  over the additive / multiplicative commutative monoid of a (semi)ring `R`.

**What generalizes vs. what stays Real.** The *algebraic* toolkit moves to the
generic layer (needs only `IsCommutativeMonoid`, plus distributivity for
`scale`): empty/`_zero`, `_add_one` (recursion unfold), `_split` (from
`product_append`), `_pointwise`, `_add`, `_scale`, `_constant`, telescoping. The
*order* lemmas need an ordered field and **stay in `Real/`**: `_nonneg`,
`_monotone_of_nonneg`, `_le_pointwise`, `_window_bound`,
`partialProduct_nonneg`.

## Dependencies to confirm before Stage 1

- **Generic `power` over a monoid** (`Monoid.power(R, x, k : Natural)`), needed
  by binomial. `Real.power` is Real-specific today — add `Monoid.power` and make
  `Real.power` its instance (or bridge).
- **Natural coefficient action** `(Natural.binomial(n,k) : R)` generically — via
  the Natural→semiring map (repeated add). Confirm/add `Natural.to_semiring`
  (or reuse the ring `from_natural`).
- **`IsCommutativeSemiring`?** `IsCommutativeMonoid` and `IsCommutativeRing`
  exist; there is no semiring. Binomial can be stated over `IsCommutativeRing`
  now (subtraction merely unused) and tightened to a new
  `IsCommutativeSemiring` later — decide in Stage 0. Tightest-correct is the
  semiring; pragmatically `IsCommutativeRing` unblocks everything.

## Stages (each ends green under `make -j16 library`; elaborator untouched → no `make tests`)

- **Stage 0 — decide the carrier.** Pick `IsCommutativeRing` vs a new
  `IsCommutativeSemiring` for binomial's home; decide range orientation
  (`range_down` vs `range`) for the Lists bridge. Small, no code.
- **Stage 1 — generic aggregation + Lists bridge + algebraic toolkit.** New
  `Algebra/aggregation.math`: `indexedAggregate`, the `List.product` bridge, and
  the algebraic lemmas ported from series/finite_products (carrier-generic).
- **Stage 2 — Real instance.** Re-express `Real.partialSum`/`partialProduct` as
  `bigSum`/`bigProduct` at Real (alias or `= …` bridge), re-home the order-only
  lemmas, keep every current consumer (convergence, harmonic, triangular,
  cauchy_schwarz, series) green.
- **Stage 3 — binomial generic.** `Algebra/binomial.math`: the theorem over a
  commutative (semi)ring using `bigSum` + `Monoid.power` + the Natural action;
  port the Pascal-rule induction (purely algebraic). `Real.binomial_theorem`
  becomes the instance.
- **Stage 4 — AGM.** Move its sums/products onto the generic toolkit; the
  order-bearing steps stay Real. Optional, lower priority.

## Risks

- **Blast radius of Stage 2.** `series.math` feeds convergence/harmonic/
  triangular/cauchy_schwarz. The bridge must preserve their lemma names/shapes —
  prefer aliasing `Real.partialSum := bigSum(Real, …)` over renaming.
- **`ring`/normaliser interaction** with a generic `op` — the algebraic lemmas
  must cite monoid laws explicitly (no `ring` on an abstract carrier).
- **Power/coefficient generality** is the gating prerequisite (above); if
  `Monoid.power` is awkward, Stage 3 stalls — do it first within Stage 1.

# Real numbers and analysis

Reals are equivalence classes of rational Cauchy sequences. Most consumers
should import the sealed [interface.math](interface.math), which exposes the
carrier, operations, order, completeness, and proved theorems without loading
construction internals.

## Main definitions

- Construction: `CauchyRationalSequence`, `CauchyEquivalent`, and `Real` / `ℝ`
  in [basics.math](basics.math)
- Embedding `Rational.to_real`; arithmetic, order, absolute value, reciprocal,
  power, and field/ring bundles
- Convergence: `Real.SequenceConverges`, `Real.SequenceConvergent`,
  `Real.SequenceIsCauchy`, and `Real.limit`
- Series: `Real.partialSum` and `Real.SeriesConverges`
- Completeness order notions: `Real.IsUpperBound`, `Real.IsBoundedAbove`, and
  `Real.IsSupremum`
- Functions: `Real.square_root`, `Real.exponential`, and `Real.e`
- Calculus: `Real.ContinuousAt`, `Real.ContinuousOn`, and
  `Real.HasDerivativeAt`

## Main theorems

- Ordered field: `Real.is_field`, order linearity, and the embedding
  preservation/reflection theorems
- Limits: uniqueness and algebra in `convergence` and `limits`, including
  `Real.monotone_bounded_converges`
- Completeness: `Real.supremum_exists` and
  `Real.cauchy_sequence_converges`
- Series: `Real.geometric_series` and dominated convergence/Cauchy results
- Roots and continuity: `Real.square_root_squares`,
  `Real.intermediate_value`, and the continuity algebra
- Derivatives: constant, identity, sum, product, scale, uniqueness, and
  `Real.HasDerivativeAt.continuous`
- Exponential: `Real.exponential_converges`, `Real.exponential_zero`, and
  `Real.e_above_two`
- Cardinality: `Real.not_enumerable`

## Where to look

- Construction boundary: `sequence`, `cauchy`, `basics`, `interface`
- Ordered-field core: `addition` through `order_field`
- Limits and completeness: `convergence`, `limits`, `supremum`,
  `cauchy_complete`
- Series and special functions: `series`, `power`, `square_root`,
  `exponential`, `exponential_addition`
- Calculus: `continuity`, `derivative`, `intermediate_value`
- Major inequalities/results: `cauchy_schwarz`, `arithmetic_geometric_mean`,
  `harmonic_series`, `binomial_theorem`, `triangular_series`

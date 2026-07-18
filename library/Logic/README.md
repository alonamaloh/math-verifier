# Logic

This directory supplies the logical and type-level vocabulary used everywhere
else. Start with `basics`, then import only the connective or construction
needed by the proof. Foundational axioms themselves live in
[`../axioms.math`](../axioms.math).

## Main definitions

- Propositions: `True`, `False`, `And`, `Or`, and `Not` in
  [basics.math](basics.math)
- Existential quantification: `Exists` in [exists.math](exists.math)
- Function properties: `Function.IsInjective`, `Function.IsSurjective`, and
  `Function.IsBijective` in [functions.math](functions.math)
- Type-level pairs and alternatives: `Product` / `Pair`, `Sigma`, and `Sum` /
  `DisjointUnion` in `product`, `sigma`, and `sum`
- Quotient relations: `IsEquivalenceRelation` and quotient induction helpers in
  [quotient.math](quotient.math); `Quotient` itself is axiomatic
- Well-founded recursion: `Accessible`, `WellFounded`, and
  `WellFounded.recursion` in [well_founded.math](well_founded.math)

## Main theorems

- Elimination and projections: `False.eliminate`, `And.left`, `And.right`,
  `Or.eliminate`, and `Exists.eliminate`
- Classical reasoning: `Logic.double_negation_eliminate`,
  `Logic.by_contradiction`, and `Logic.not_forall_implies_exists_not`
- Extensionality: `Function.extensionality`,
  `Function.dependent_extensionality`, and
  `Equality.propositional_extensionality`
- Quotients: `Quotient.compute`, `Quotient.equal_implies_equivalent`,
  `Quotient.induct_two`, and `Quotient.induct_three`
- Recursion equation: `WellFounded.recursion_unfold`

Use `Product`/`Sigma`/`Sum` when a construction must eliminate into `Type`;
their proposition-valued analogues cannot generally produce data.

# Sets and finite cardinality

Sets are predicates, not a separate container. This directory adds subtypes,
enumerability, equinumerosity, and the finite counting layer.

## Main definitions

- `Set(T) := T → Proposition`, membership `Set.member` (`∈`), subset
  `Set.subset` (`⊆`), and `Set.IsNonempty` in [basics.math](basics.math)
- Predicate subtype `Subtype(A, P)` in [subtype.math](subtype.math)
- Countability `IsEnumerable(X)` in [enumerable.math](enumerable.math)
- Explicit-inverse cardinal equivalence `Equinumerous(A, B)` in
  [equinumerous.math](equinumerous.math)
- Finite yardstick `NaturalsBelow(n)` and cardinality predicate `HasSize(X, n)`
  in [finite.math](finite.math)

## Main theorems

- `Set.subset.reflexive` and `Set.subset.transitive`
- `Subtype.equal_of_value_equal`
- `Equinumerous.reflexive`, `.symmetric`, and `.transitive`
- `HasSize.transport`, `HasSize.unique`, and `NaturalsBelow.has_size`
- Counting rules: `HasSize.sum`, `HasSize.product`, and `HasSize.one_plus`
- Pigeonhole: `NaturalsBelow.injective_domain_le_codomain`
- Countability: `IsEnumerable.along_surjection` and `IsEnumerable.quotient`
- Cantor: `Cantor.no_surjection_onto_powerset` and
  `Set.powerset_of_naturals_not_enumerable`

The explicit inverse in `Equinumerous` is deliberate: a proposition-level
surjectivity witness cannot be extracted into a data-producing inverse.

# Sets and finite cardinality

Sets are predicates, not a separate container. This directory adds subtypes,
enumerability, equinumerosity, and the finite counting layer.

## Main definitions

- `Set(T) := T → Proposition`, membership `Set.member` (`∈`), subset
  `Set.subset` (`⊆`), and `Set.IsNonempty` in [basics.math](basics.math)
- The Boolean operations `∪`, `∩`, `∖`, `Set.universe`, `Set.empty`,
  `Set.complement`, extensionality `Set.equal_of_same_members`, and the image
  `Set.image(f, subset)` in [algebra.math](algebra.math)
- Predicate subtype `Subtype(A, P)` in [subtype.math](subtype.math)
- Countability `IsEnumerable(X)` in [enumerable.math](enumerable.math)
- Explicit-inverse cardinal equivalence `Equinumerous(A, B)` in
  [equinumerous.math](equinumerous.math)
- Finite yardstick `NaturalsBelow(n)` and cardinality predicate `HasSize(X, n)`
  in [finite.math](finite.math)
- The cons/uncons interface for `NaturalsBelow(1 + n)` — `NaturalsBelow.first`,
  `.shiftUp`, `.dropFirst`, and `.first_or_shift` — in
  [finite_successor.math](finite_successor.math). What
  `NaturalsBelow.one_plus_equinumerous` says as a bijection, said as elements,
  which is the form an indexing argument can use
- Choice over a finite index, `NaturalsBelow.choice`, in
  [finite_choice.math](finite_choice.math)
- Cardinality of a **subset** — `Set.IsEnumeration(A, enumeration)`,
  `Set.IsFinite(A)`, and `Set.size(enumeration, subset)` — in
  [enumeration.math](enumeration.math). `HasSize` counts a *type*; this counts
  a subset of one, as a natural number that can be compared and incremented

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
- Subset counting: `Set.size_le_of_subset`, `Set.size_lt_of_member_missing`,
  `Set.equal_of_size_eq` — equal counts force equal sets — and
  `Set.size_lt_of_proper_subset`

The explicit inverse in `Equinumerous` is deliberate: a proposition-level
surjectivity witness cannot be extracted into a data-producing inverse.

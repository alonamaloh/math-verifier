# Lists

This directory provides the library's single polymorphic list type and the
finite combinatorics built on it. Start with `list`; add operation modules as
needed.

## Main definitions

- `List(A)`, `List.empty`, `List.prepend`, membership `List.member` / `∈`, and
  fold `List.product` in [list.math](list.math)
- `List.append`, `List.map`, `List.length`, `List.filter`, and `List.remove`
- `List.sumOver(values, list)` — the sum of a ℕ-valued function over a
  list's members, in [sum.math](sum.math)
- `List.unionOver(pieces, list)` — the union of a family of sets over a
  list's members, in [set_union.math](set_union.math). The finite union with
  its finiteness carried by a list; written as a recursion so that each
  induction step is a two-set statement, with `List.unionOver_member` /
  `.member_invert` recovering the comprehension reading
- `List.range_down` for `1,…,n`, `List.range_up` for `0,…,n-1`, and
  `List.range_down_offset`
- Inclusion `List.Includes`, spelled `⊆` — every member of the smaller list
  is a member of the larger, saying nothing about order or multiplicity. The
  same operator `Set` uses, since `∈` is already overloaded that way.
  Transparent, so a `⊆` fact in context discharges an individual membership
  with no citation
- Pairwise distinctness `List.Distinct`
- `List.deduplicate(list)` — the list with its repetitions removed, in
  [deduplicate.math](deduplicate.math): same members
  (`List.deduplicate_subset` and `List.subset_deduplicate`) and
  `List.deduplicate_distinct` afterwards. What a construction owes a
  consumer that requires distinctness — a graph's vertex and edge lists —
  when what it gathered may repeat itself
- Reordering relation `List.Permutation`
- Cartesian list product `List.cartesianProduct`

## Main theorems

- Membership: `List.member_prepend_invert`, `List.member_append_invert`,
  `List.map_member`, and `List.filter_member_complete`
- Folds: `List.Permutation.product_invariant` and `List.product_append`
- Structure: `List.Permutation.symmetric`, `List.Permutation.extract`,
  `List.Permutation.length_invariant`, and
  `List.Permutation.distinct_invariant`
- Ranges: `List.range_down_complete`, `List.range_up_complete`,
  `List.range_down_distinct`, and `List.range_up_distinct`
- Pair cancellation: `List.product_one_of_paired_inverses`
- Counting: `List.length_le_of_distinct_inclusion` — a list without
  repetitions is no longer than any list holding all of its elements
- Sums: `List.sumOver_append`, `List.sumOver_add`,
  `List.sumOver_congruence` and `List.sumOver_constant`
- Finite unions: `List.unionOver_append` splits a union where the list
  concatenates, `List.unionOver_same_members` says only the members matter
  (so deduplicating or reordering leaves a union alone),
  `List.unionOver_pointwise` replaces the family by a pointwise-equal one, and
  `List.unionOver_map` turns a union over a mapped list into one of the
  composite over the original
- Counting members: `List.sumOver_indicator` — summing one per member
  that satisfies a condition counts them — and `List.filter_length_two`

`filter` and `remove` use classical decisions and publish characterizing
equations; reason through those theorems rather than unfolding their bodies.

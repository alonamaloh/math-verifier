# Lists

This directory provides the library's single polymorphic list type and the
finite combinatorics built on it. Start with `list`; add operation modules as
needed.

## Main definitions

- `List(A)`, `List.empty`, `List.prepend`, membership `List.member` / `∈`, and
  fold `List.product` in [list.math](list.math)
- `List.append`, `List.map`, `List.length`, `List.filter`, and `List.remove`
- `List.range_down` for `1,…,n`, `List.range_up` for `0,…,n-1`, and
  `List.range_down_offset`
- Pairwise distinctness `List.Distinct`
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

`filter` and `remove` use classical decisions and publish characterizing
equations; reason through those theorems rather than unfolding their bodies.

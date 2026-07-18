# Natural core

## Representation and recursion

`Natural` is a sealed, opaque alias over the inductive `Natural.Raw`. Outside
`Natural/`, use `ℕ`, numerals, and arithmetic; do not mention `Natural.Raw`,
`zero`, or `successor`. In particular, spell a successor as `n + 1` or
`1 + n`. This is the abstraction rule even where a construction-level name
happens to be accepted by the elaborator.

The primitive recursor `Natural.recursion` and the constructor spellings are
for implementing the boundary. Ordinary proofs use `by induction`; ordinary
definitions use the arithmetic patterns supported by the surface language.
The induction step is presented as `1 + n`. The boundary theorems
`Natural.induction_on_one_plus`, `Natural.cases_on_one_plus`,
`Natural.induction_on_successor`, and `Natural.cases_on_successor` connect
surface proofs to the sealed representation; the successor-named forms belong
to boundary implementation, not downstream proof vocabulary. Use
`Natural.strong_induction` when the hypothesis is available for every smaller
natural. Data definitions with a decreasing natural measure use
`Natural.lt_wellFounded`.

## Arithmetic

[arithmetic.math](arithmetic.math) contains the semiring laws and additive
cancellation. The names most often useful to proofs are:

- `Natural.zero_add`, `Natural.add_zero`, `Natural.one_add`, `Natural.add_one`
- `Natural.add_associative`, `Natural.add_commutative`,
  `Natural.add_cancel_left`, `Natural.add_cancel_right`
- `Natural.zero_not_one_plus`, `Natural.add_eq_zero_left_zero`,
  `Natural.add_eq_zero_right_zero`
- `Natural.zero_multiply`, `Natural.multiply_zero`, `Natural.one_multiply`,
  `Natural.multiply_one`
- `Natural.multiply_associative`, `Natural.multiply_commutative`,
  `Natural.distributivity_left`, `Natural.distributivity_right`

Multiplicative cancellation needs a positive common factor:
`Natural.multiply_cancel_right` and `Natural.multiply_cancel_left` in
[cancellation.math](cancellation.math).

## Order

`a < b` means that `b` exceeds `a` by a positive amount. Introduce or unpack
that witness with `Natural.lt_intro` and `Natural.lt_elim`. `a ≤ b` is
`a < b ∨ a = b`, but proofs should normally use the named interface:

- `Natural.zero_least`, `Natural.LessOrEqual.reflexive`,
  `Natural.LessOrEqual.transitive`, `Natural.le_antisymmetric`
- `Natural.lt_transitive`, `Natural.LessThan.weaken`,
  `Natural.lt_trichotomy`, `Natural.lt_or_le`
- `Natural.add_left_monotone`, `Natural.add_left_strict_monotone`,
  `Natural.add_left_le_cancel`
- `Natural.add_one_le_of_lt`, `Natural.lt_of_add_one_le`,
  `Natural.le_of_lt_one_plus`

`Natural.subtraction_witness(b, a, h)` turns `h : b ≤ a` into a natural `c`
with `a = b + c`. Use `a ∸ b` only when truncated subtraction is intended.
Its main laws are `Natural.monus_zero`, `Natural.monus_self`,
`Natural.monus_add_left`, and `Natural.le_implies_monus_zero`.

For positivity and nonzero goals, `Natural.order` owns
`Natural.one_le_add_one`, `Natural.one_le_one_plus`,
`Natural.nonzero_of_positive`, and `Natural.one_le_of_nonzero`.
`Natural.add_order` owns additive monotonicity lemmas such as
`Natural.add_left_strict_monotone`. Prefer the direct arithmetic or order
fact over induction.

## Decisions and comparisons

`Natural.decides_equality`, `Natural.decides_less_or_equal`, and
`Natural.decides_divides` return proposition-level positive/negative evidence.
When a function must branch and produce data, use
`Natural.compare_strict(k, m) : Natural.StrictComparison(k, m)`; its cases carry
`k < m` or `m ≤ k`.

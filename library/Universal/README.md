# Universal algebra

Signatures, algebras, terms, and the machinery of absorption — the foundation
for Zhuk's theorem on the left centre of a subdirect relation.

## Main definitions

- `Universal.Signature` — a family of operation-symbol types indexed by arity,
  in [signature.math](signature.math). Indexing *by* arity makes the arity
  definitional, so an operation's argument tuple is
  `NaturalsBelow(arity) → carrier` with no dependency on the symbol.
- `Universal.Algebra` — a carrier bundled with its interpretation, with
  `Universal.Algebra.carrier` and `Universal.Algebra.interpret` as projections.
- `Universal.Algebra.IsIdempotent` and `Universal.IsSubuniverse`, also in
  [signature.math](signature.math).
- `Universal.Term` — terms over a signature with variables from an arbitrary
  type, in [term.math](term.math), together with `Universal.Term.evaluate` and
  `Universal.Term.substitute`.
- `Universal.generated` — the least subuniverse containing a set, and
  `Universal.Signature.HasNoConstants`, in [generated.math](generated.math).
- `Universal.termValues` — the values of terms whose variables range over a set,
  in [generation.math](generation.math).
- `Universal.Algebra.power` and `Universal.Algebra.product` — powers over an
  arbitrary index type and binary products, in [product.math](product.math).
- `Universal.box`, `Universal.restrict`, `Universal.project` and
  `Universal.cylinder` — the relational constructions, in
  [relation.math](relation.math).
- `Universal.Algebra.dependentProduct` — the product of a family of algebras,
  with `Universal.dependentBox`, in
  [dependent_product.math](dependent_product.math). The power is its constant
  case, recorded by `Universal.Algebra.power_eq_dependentProduct`.
- `Universal.IsEssential`, `Universal.firstCoordinateIn` and
  `Universal.deleteFirst`, in [essential.math](essential.math).
- `Universal.Witnesses`, `Universal.Absorbs`, `Universal.BinaryAbsorbs`,
  `Universal.IsTaylorIdentity` and `Universal.IsTaylorOn`, in
  [absorption.math](absorption.math).
- `Universal.StarIndex`, `Universal.starPrepend`, `Universal.starBase` and
  `Universal.starStep` — the star powers' index type and one level of their
  recursion, in [star_power.math](star_power.math).

## Main theorems

- `Universal.IsSubuniverse.universe` and `Universal.IsSubuniverse.singleton`
- `Universal.Term.evaluate_mem` — preservation: a term's value lies in any
  subuniverse holding its variables' values.
- `Universal.Term.evaluate_substitute` — evaluating a substituted term is
  evaluating the original under the valuation that first evaluates each
  assigned term.
- `Universal.generated.contains_base`, `.least`, `.is_subuniverse`, `.monotone`,
  and `.empty` — the characterising facts. Because a set is a predicate,
  "least subuniverse containing `base`" is directly definable as quantification
  over the subuniverses that contain it, so no closure construction is needed.
- `Universal.Term.evaluate_power`, `.first_evaluate_product` and
  `.second_evaluate_product` — terms are evaluated coordinatewise. This is the
  whole content of the product constructions; every later fact about relations
  reduces to it.
- `Universal.generated_eq_termValues` — the generated subuniverse is exactly the
  term values. The variable type is the generating set itself, so no enumeration
  of the generators appears anywhere.
- `Universal.restrict_interpret` — reindexing a tuple along a map of index types
  is a homomorphism of powers. The five relational constructions of blueprint
  Lemma 1.19 are its consequences: `IsSubuniverse.intersection`, `.box`,
  `.project` (its image), `.cylinder` (its preimage), and reindexing along a
  bijection as the case where the map is one.
- `Universal.Term.evaluate_rename` — the blueprint's `t[ρ]`, evaluated.
- `Universal.Witnesses.rename` and `Universal.Absorbs.of_renaming` — a witness
  built over whatever index type a construction hands you is given a numeric
  arity afterwards, by renaming along a bijection.
- `Universal.BinaryAbsorbs.of_one_sided` — one-sided closure plus a Taylor
  identity gives two-sided binary absorption. The only place a Taylor identity
  is used.
- `Universal.starStep_evaluate` — one level of a star power evaluates the base
  term at the values its blocks take.
- `Universal.Term.evaluate_dependentProduct` — terms are evaluated
  coordinatewise in a product of a family, as in a power.
- `Universal.no_essential_of_witnesses` — a term witnessing absorption forbids
  an essential relation on the same index. The move Part II turns on: evaluate
  the witnessing term *in the power*, at the tuple of witnesses.
- `Universal.IsEssential.deleteFirst` — essentiality survives deleting a
  coordinate, which is how an essential relation of large arity produces ones of
  every smaller arity.

## Two representation choices

**Arguments are a function, not a list.** `Universal.Term.apply` takes
`arguments : NaturalsBelow(arity) → Universal.Term(…)`. Structural recursion and
induction go through the tuple directly, so no proof carries a length side
condition. This relies on the elaborator recognising a recursive call on an
application of a higher-order recursive field; see
`Test/higher_order_recursion_test.math`.

**Variables come from an arbitrary type.** Substitution is then
`(source → Term(target)) → Term(source) → Term(target)` — one operation covering
renaming, identification of variables, and the introduction of unused ones.

**A star power is not a recursive definition.** Its result type mentions the
depth, so recursion on the depth would be dependent, and its `1 + rest` arm
would have to produce a `StarIndex(arity, successor(rest))` where it has a
`StarIndex(arity, 1 + rest)`. `Natural.add` is opaque, so those are not
definitionally equal. `star_power.math` therefore publishes `starBase` and one
level, `starStep`; the iteration happens inside a proof, where an
equation-shaped `by induction on depth` *rewrites* the goal to the `1 + rest`
form instead of needing it to reduce.

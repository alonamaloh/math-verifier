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

## Main theorems

- `Universal.IsSubuniverse.universe` and `Universal.IsSubuniverse.singleton`
- `Universal.Term.evaluate_substitute` — evaluating a substituted term is
  evaluating the original under the valuation that first evaluates each
  assigned term.

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

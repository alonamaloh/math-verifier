# Equality

This directory defines universe-polymorphic propositional equality. Nearly every
library module imports [basics.math](basics.math).

## Main definitions

- **Equality** — `Equality(A, x, y)`, written `x = y`
- **Reflexivity constructor** — `Equality.reflexivity`

The generated recursor provides substitution and transport. Surface proofs
should normally use equality chains and `substituting`; direct recursor use is
reserved for foundational code.

## Main theorems

- `Equality.not_equal_symmetric`: symmetry of disequality
- `Equality.transport_proposition`: transport a proposition-valued family
- `Equality.propositional_extensionality`: logical equivalence implies equality
  of propositions; declared in [`../axioms.math`](../axioms.math)

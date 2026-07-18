# Library

This is the formal mathematics library. Before using an area, read its
directory `README.md`; then open a focused note, if present, and finally the
specific `.math` modules that own the declarations you need. Imports are
fine-grained and flow from foundational layers toward constructed mathematics.

## Foundations

- [Logic](Logic/README.md): propositions, quantifiers, functions, products,
  sums, quotients, and well-founded recursion
- [Equality](Equality/README.md): propositional equality and transport
- [Natural](Natural/README.md): `ℕ`, arithmetic, order, division, and number
  theory
- [Lists](Lists/README.md): lists, membership, folds, maps, ranges, filters,
  permutations, and distinctness
- [Set](Set/README.md): predicate sets, subtypes, cardinality, and finite
  counting

The root module [axioms.math](axioms.math) contains the library's only admitted
foundational axioms: propositional extensionality, excluded middle, quotient
infrastructure, definite description, and the explicitly unsafe `sorry`
placeholder.

## Algebra and number systems

- [Algebra](Algebra/README.md): groups, rings, fields, factorization, linear
  algebra, matrices, determinants, and Cayley–Hamilton
- [Integer](Integer/README.md), [Rational](Rational/README.md), and
  [Real](Real/README.md): the number tower `ℤ → ℚ → ℝ`
- [Polynomial](Polynomial/README.md): polynomial rings, degree, division,
  Bézout, and quotient fields
- [RingModulo](RingModulo/README.md): quotients of commutative rings by a
  principal ideal
- [IntegerMod](IntegerMod/README.md): `ℤ/nℤ`, finite prime fields, Wilson,
  Fermat, and Euler
- [ComplexNumber](ComplexNumber/README.md): `ℂ`, coordinates, modulus,
  completeness, exponential, and trigonometry
- [GaussianInteger](GaussianInteger/README.md): `ℤ[i]`, norm, Euclidean
  division, and sums of two squares
- [FiniteField](FiniteField/README.md): polynomial quotient construction of
  finite fields

## Verification suites

- [Test](Test/README.md): successful surface-language and elaborator examples
- [ErrorTest](ErrorTest/README.md): intentionally failing error-message tests

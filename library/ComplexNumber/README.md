# Complex numbers

Complex numbers are constructed as `ℝ[x]/(x²+1)`. The quotient view supplies
the ring and field; the coordinate map supplies the familiar `a + bi` view.

## Main definitions

- `ComplexNumber` / `ℂ` and `Complex.definingPolynomial` in
  [basics.math](basics.math)
- Imaginary unit `ComplexNumber.i` and real embedding
  `ComplexNumber.from_real`
- Coordinates `ComplexNumber.coordinates`, `.realPart`, `.imaginaryPart`, and
  constructor `ComplexNumber.ofCoordinates`
- Modulus `ComplexNumber.modulus`
- Convergence predicates, `ComplexNumber.limit`, power, and
  `ComplexNumber.exponential`
- Real functions `Real.cosine` and `Real.sine`, defined through the complex
  exponential

## Main theorems

- Field structure: `ComplexNumber.is_field`
- Coordinate reconstruction: `ComplexNumber.reconstruct`,
  `ComplexNumber.eq_of_coordinates`, and
  `ComplexNumber.coordinates_ofCoordinates`
- `ComplexNumber.i_squared` and preservation laws for `from_real`
- Modulus: `ComplexNumber.modulus_squares`,
  `ComplexNumber.modulus_multiplicative`, and
  `ComplexNumber.modulus_triangle`
- Completeness: `ComplexNumber.cauchy_sequence_converges`
- Exponential: `ComplexNumber.exponential_converges`,
  `ComplexNumber.exponential_add`, and `ComplexNumber.exponential_zero`
- Trigonometry: `ComplexNumber.euler_formula` and identities/bounds in the
  `trigonometric_*` modules

The coordinate modules form a chain: `coordinates` builds the polynomial lift,
`coordinate_map` descends through the quotient, and `reconstruction` proves
that the two coordinates determine the complex number.

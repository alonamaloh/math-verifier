# Gaussian integers

Gaussian integers are `ℤ[i] = ℤ[x]/(x²+1)`. Coordinates turn quotient classes
into pairs of integers; the norm makes the ring Euclidean.

## Main definitions

- `GaussianInteger`, its defining polynomial, and integer embedding in
  [basics.math](basics.math)
- `GaussianInteger.i`
- `GaussianInteger.coordinates`, `.realPart`, `.imaginaryPart`, and
  `.ofCoordinates`
- Integer norm `GaussianInteger.normInteger` and its natural-valued companion
- Bundles `GaussianInteger.integral_domain`,
  `GaussianInteger.euclidean_domain`, and
  `GaussianInteger.principal_ideal_domain`

## Main theorems

- Reconstruction: `GaussianInteger.reconstruct` and
  `GaussianInteger.coordinates_ofCoordinates`
- `GaussianInteger.i_squared`
- Norm: `GaussianInteger.normInteger_multiply`,
  `GaussianInteger.eq_zero_of_norm_zero`, and no-zero-divisors
- Euclidean division: `GaussianInteger.has_euclidean_division`
- Unit classification in [units.math](units.math)
- Descent result `GaussianInteger.sum_of_two_squares_of_divides_square_plus_one`
- Fermat's theorem `Natural.prime_one_mod_four_sum_of_two_squares`

The coordinate and reconstruction modules parallel the complex-number
construction, but all coordinates and norms remain integral.

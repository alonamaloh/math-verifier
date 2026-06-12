# Plan: `ring` at RingModulo carriers (ℂ, ℤ[i], F_{p^k})

## Why now

The complex-exponential push (2026-06-12) had to route EVERY ℂ algebraic
identity through `ComplexNumber.eq_of_coordinates` + two Real-`ring`
computations (~25 lines each), because `ring` is non-functional at
RingModulo carriers. Probes (this session):

- `z * (w + z) = z * w + z * z := ring` at `ComplexNumber` FAILS with
  "the identity is FALSE as a polynomial identity" — the tactic engages
  but misreads the operator applications (`RingModulo.add`/`multiply`
  carry two implicit bundle arguments, so the term trees don't match the
  shape the tactic's operation-recognizer expects).
- `z - w = z + -w := ring` fails EARLIER: unary `-` does not elaborate at
  `ComplexNumber` ("no `<T>.negate` in scope") — `RingModulo/operations.math`
  registers binary `+`, `-`, `*` but no unary minus.
- `w - z = -(z - w)` (with `RingModulo.negate` spelled): ring engages,
  treats `subtract`/`negate` applications as opaque atoms, declares the
  identity false.

The next math (trig: ℂ functional equation = ℂ-Mertens, conjugation)
needs dozens of ℂ regroupings; at ℝ, half of Mertens was `by ring`
one-liners. Fix the tactic first.

## Root cause (confirmed by reading ring.cpp:78-86)

The tactic's operation recognizer works by NAMING CONVENTION: for a
carrier named `T` it looks for the constants `T.add`, `T.subtract`,
`T.multiply`, `T.negate`, `T.zero`, `T.one`. Real/Integer/Rational/
Natural satisfy it; ℂ does not — its carrier is `ComplexNumber` (an
alias of `RingModulo(c, m)`) but its operations are the GENERIC
`RingModulo.add{c}{m}` etc.; there is no `ComplexNumber.add` constant,
so every operation application is mis-segmented. Nothing mathematical is
missing — the manipulation lemmas are generic (Algebra/ring_lemmas) —
the tactic just cannot SPELL the operations.

## Work items

1. **Resolve operations through the instance registry instead of the
   naming convention.** We already register canonical commutative-ring
   instances (`instance Real.ring`, ComplexNumber.is_commutative_ring,
   RingModulo/instances). An instance VALUE syntactically contains the
   operation terms; the tactic should look up the registered instance
   for the goal's carrier type and read the add/multiply/negate/zero/one
   TERMS out of it, then match goal subterms against those (structural,
   falling back to defeq). Keep the naming convention as a fallback.
   Then ANY ring with a registered instance gets the tactic for free
   (ℂ, ℤ[i], F_{p^k}, Z/(m)) — zero per-ring code, which is the point.
   Proof-emission side: the abstract-ring path already exists
   (Test/abstract_ring_ac_test, bundled-ring algebra), so certificates
   can cite the generic lemmas instantiated with the bundle.
2. **Register unary minus for RingModulo**: the operator layer resolves
   unary `-` via `<T>.negate`; either register
   `operator (-) on (RingModulo) := RingModulo.negate` (mirroring however
   Real/Integer register theirs) or add the alias the resolver expects.
3. **Operator dispatch inside pattern-definition bodies.** In
   `definition Foo : … | successor(n) => X + Y`, `+`/`*` fail with
   "operator '+' is not supported for operand type 'Quotient'" even
   though the SAME expressions dispatch fine in theorem bodies
   (ComplexNumber.partialSum/power had to spell RingModulo.add/multiply).
   Likely the definition-body path lacks the alias-aware expected-type
   resolution the theorem path got in the 2026-06 operator work.
4. **Regression tests**: extend Test/ring_modulo_test.math (currently
   construction-only) with tactic goals at ComplexNumber and at
   RingModulo(integerCommutativeRing, m): distributivity, subtract
   unfold, negate pull-out, and a definition-body operator use.
   `make tests` clean.

## After

Sweep ComplexNumber/exponential.math: collapse the eq_of_coordinates
plumbing for pure ring identities (add_cancel_left, the unique-proof
difference split, …) to `by ring` where it now closes — keep
eq_of_coordinates itself (it is the right tool for NON-ring facts).
Then resume trig per the `real_analysis_arc` memory NEXT section.

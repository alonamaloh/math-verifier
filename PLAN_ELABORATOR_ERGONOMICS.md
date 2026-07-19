# Plan: elaborator ergonomics exposed by the Fifteen Theorem

This is the implementation plan for proof-system friction encountered while
formalizing the Fifteen Theorem. It complements `PLAN_ERGONOMICS.md`: that file
is the project-wide catalogue, while this file is a bounded elaborator project
with concrete regressions and acceptance tests.

The target experience is simple:

> Once an expression determines the carrier, numerals and Natural variables in
> the same operator or relation should lift to that carrier without annotations.

The elaborator must implement that rule by constructing ordinary coercion
terms. The kernel remains unchanged and checks every generated term.

## Evidence from the rank-three escalation proof

The following probes were run in
`library/Algebra/rank_three_escalation_bounds.math` on 2026-07-19.

| Surface expression | Result today | Finding |
|---|---|---|
| `b * b < 3`, for `b : ℤ` | accepts | A syntactic Integer operand seeds the relation correctly. |
| `b = 1`, for `b : ℤ` | accepts | A positive numeral inherits the Integer carrier. |
| `b = -1` | rejects without `-(1 : ℤ)` | Unary `-` dispatches on the Natural literal before the equality's expected type reaches it. |
| `b = -m`, for `m : ℕ` | rejects without `-(m : ℤ)` | The same early unary dispatch prevents the registered Natural-to-Integer lift. |
| `M(i,i) < 3`, for an integer matrix | rejects without `(3 : ℤ)` | The entry's type is presented as `CommutativeRing.carrier(Integer.bundle)`; relation selection does not normalize it to Integer. |
| `M(i,i) = 0 ∨ M(i,i) = 1` | does not match the Integer classifier with bare numerals | Expected carrier information does not cross independent disjunct/equality nodes reliably when the left side is an abstract carrier. |
| `M(i,i) * truant(A)` | rejects without casting `truant(A)` | Operator dispatch does not use the concrete carrier hidden behind the ring bundle to lift the Natural operand. |
| `((5 : ℕ) : ℤ)` | unnecessary | `(5 : ℤ)` is the direct spelling; in an Integer-expected position, bare `5` is enough. |

This is not one request for more permissive guessing. It is one bidirectional
elaboration defect appearing at several syntax nodes: known carrier information
is lost before overloaded operators, relations, and unary operands are
elaborated.

## Design constraints

1. **No kernel arithmetic or new definitional equalities.** The elaborator
   inserts registered coercions; the kernel checks the result.
2. **Only canonical upward coercions.** Reuse the coercion registry and its
   unique joins. Never guess between unrelated carriers or coerce downward.
3. **Bidirectional, not numeral-specific.** The same mechanism should cover a
   literal `3` and a Natural term such as `truant(A)`.
4. **Respect abstraction.** A carrier projection whose closed structure
   argument reduces to Integer should provide the same dispatch evidence as
   the literal type `Integer`.
5. **Fail deterministically.** Ambiguous expressions remain errors, and the
   diagnostic explains which carrier could not be selected.
6. **Cost-gate hot paths.** Normalize carrier heads only after ordinary
   elaboration fails, or when the opposite operand supplies a unique target.

## Work plan

### E0. Freeze the failures as small tests

Status: `[ ]`

Add one focused feature test and corresponding negative controls before
changing the elaborator. The feature test should cover:

- positive Integer numerals and Natural variables on the right of `=`, `<`,
  `≤`, `+`, and `*`;
- unary `-` under an Integer-typed equality and inequality;
- integer matrix entries, so the abstract-carrier path is exercised;
- a citation whose conclusion contains bare numeral leaves;
- one two-edge lift, such as Natural to Rational, to ensure the solution uses
  the coercion registry rather than an Integer special case.

Negative controls must keep unrelated carriers, downward coercions, and an
unseeded all-Natural expression rejected.

Likely files:

- `library/Test/expected_carrier_propagation_test.math`
- `library/ErrorTest/ambiguous_expected_carrier.math`

### E1. Make relation elaboration genuinely bidirectional

Status: `[ ]`

For `=`, `<`, and `≤`, collect carrier evidence from both operands before
committing to a relation implementation:

1. elaborate the informative operand;
2. normalize its type to a dispatchable carrier head;
3. elaborate the other operand with that carrier as its expected type;
4. use the coercion registry if its inferred type is lower;
5. select the relation only after both operands have been reconciled.

Do not let a bare numeral select `Natural.LessThan` while the opposite operand
already determines Integer. Preserve the existing carrier-join behavior for
two independently informative operands.

Acceptance probes:

```text
b * b < 3
M(i,i) < 3
M(i,i) = 0
```

All three elaborate to Integer relations without annotations.

### E2. Propagate expected carriers through unary operators

Status: `[ ]`

Unary dispatch currently sees the operand before the surrounding relation has
resolved its carrier. Thread the expected carrier into unary elaboration and
try that registered operator before reporting that Natural has no negation.

Acceptance probes:

```text
b = -1
b = -m          -- b : ℤ, m : ℕ
q < -n          -- q : ℚ, n : ℕ
```

Each must elaborate through canonical upward coercions. A standalone `-m`
with no expected carrier must remain rejected.

### E3. Normalize closed structure carriers for dispatch

Status: `[ ]`

Teach carrier discovery to see through closed registered structures such as
`CommutativeRing.carrier(Integer.commutative_ring_bundle)` without globally
unfolding opaque mathematical definitions.

Preferred implementation:

- first consult the structure/instance information already used by operator
  registration and canonical instances;
- use bounded weak-head normalization only as a fallback;
- cache the normalized head for the duration of one elaboration.

This normalized carrier evidence must be shared by relation dispatch, binary
operator dispatch, expected-type coercion, and citation matching. Avoid four
slightly different notions of "this is Integer".

Acceptance probes:

```text
M(i,i) * truant(A)
M(i,i) < 3
M(i,i) = 0
```

No operand annotations are required.

### E4. Reconcile citation conclusions and premises after carrier inference

Status: `[ ]`

Once a goal fixes the carrier, citation matching should compare conclusions
after applying the same canonical coercion reconciliation used for ordinary
arguments. It should then infer explicit binders from the reconciled goal and
discharge the reconciled premises from context.

Regression from this proof:

```text
done by Integer.square_below_three(Matrix.borderColumn(B)(i))
```

This should close a goal written with bare `0` and `1`; it must not fail because
the goal's numeral leaves were elaborated as Naturals before matching.

Keep this scoped to registered coercions and conclusion-directed inference.
Do not add search over arbitrary equality theorems.

### E5. Improve the failure mode and prover budget behavior

Status: `[ ]`

When expected-carrier propagation fails, report:

- the informative operand's inferred type;
- the carrier head considered for the overloaded operator/relation;
- whether no registered upward coercion exists or the carrier stayed opaque;
- the smallest useful annotation, if one is genuinely required.

Also keep a direct citation failure from falling through into a long generic
auto-prover search. The rank-three proof currently turns a local carrier
mismatch into an effort-budget exhaustion; after E1–E4 it should either
succeed or fail immediately with a carrier-specific explanation.

### E6. Sweep real proofs and measure the result

Status: `[ ]`

Use the rank-three escalation file as the first acceptance file, then sample
matrix, polynomial, and quadratic-form modules.

Primary target:

- no positive numeral annotations in matrix-facing equalities, inequalities,
  or arithmetic once another operand fixes Integer;
- no annotations inside unary negation once the surrounding expression fixes
  the target carrier;
- no nested numeral casts such as `((5 : ℕ) : ℤ)`;
- retain casts that express a real boundary, such as explicitly comparing a
  Natural-computed square as an Integer when no surrounding expression supplies
  the carrier.

Record before/after counts, compile time, and any annotation that survives with
an explanation. Do not run a blind repository-wide rewrite.

## Implementation order and commits

1. E0 tests and measurements.
2. E1 relation propagation.
3. E2 unary propagation.
4. E3 abstract-carrier normalization.
5. E4 citation reconciliation.
6. E5 diagnostics.
7. E6 proof cleanup and documentation.

Each semantic step gets its own commit with its regressions. Elaborator commits
and mathematical cleanup commits remain separate.

## Validation gates

For every elaborator step:

```text
make -j 16 tests
make -j 16 error-tests
make -j 16 library
make clean-check
```

Also run the focused feature/error tests directly while iterating. Compare
clean-manifest leak counts and wall-clock elaboration time before and after E3,
because carrier normalization touches hot dispatch paths.

## Definition of done

The project is complete when:

- every E0 positive probe elaborates without annotations;
- every negative control still fails with a stable, carrier-specific message;
- the rank-three escalation proof contains only mathematically meaningful
  casts;
- full tests, error tests, library verification, and clean check pass;
- no kernel change or axiom is introduced;
- the conventions document states the resulting rule in one paragraph a
  mathematician can predict without knowing elaborator internals.

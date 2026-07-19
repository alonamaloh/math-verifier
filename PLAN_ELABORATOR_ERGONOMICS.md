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

## Evidence

Probes re-run 2026-07-19 against `library/Algebra/rank_three_escalation_bounds.math`
and the `Integer`/`Matrix` cones.

| Surface expression | Result today | Root cause |
|---|---|---|
| `b * b < 3`, for `b : ℤ` | accepts | A syntactic Integer operand seeds the relation correctly. |
| `b = 1`, for `b : ℤ` | accepts | The `=` path passes the left type to the right operand. |
| `b = -1` | rejects without `-(1 : ℤ)` | The expected carrier *does* reach unary `-`, but dies at the numeral leaf. See E2. |
| `b = -m`, for `m : ℕ` | rejects without `-(m : ℤ)` | Same node; the operand is elaborated but never coerced to the expected carrier. |
| `M(i,i) < 3`, for an integer matrix | rejects without `(3 : ℤ)` | Carrier normalization exists but is gated behind primary dispatch, which the bare numeral already won. |
| `M(i,i) = 0 ∨ M(i,i) = 1` | rejects with bare numerals | Different root cause: the `=` path never calls carrier normalization at all. |
| `M(i,i) * truant(A)` | rejects without casting `truant(A)` | As `M(i,i) < 3`. |
| `((5 : ℕ) : ℤ)` | unnecessary | `(5 : ℤ)` is the direct spelling; in an Integer-expected position, bare `5` is enough. |

Measured baseline: `rank_three_escalation_bounds.math` carries **297** explicit
`(n : ℤ)` / `-(n : ℤ)` annotations, nearly all of them numerals at a position
where another operand already fixes Integer.

This is not one request for more permissive guessing. It is one bidirectional
elaboration defect appearing at several syntax nodes: known carrier information
is lost before overloaded operators, relations, and unary operands are
elaborated.

## Current machinery (survey 2026-07-19)

Read this before writing code — most of what the target rule needs already
exists, and the work is largely unification rather than new construction.

- **Coercion registry**: `Environment::coercionRegistry`, `src/kernel/kernel.hpp:161`.
  Keys are raw source-level head names; values are chains. Registration
  (`src/elaborator/statements.cpp:572`) transitively closes the registry and
  **rejects diamonds**, so a present chain is provably the unique path and
  reachability is a single lookup.
- **The join primitive**: `Elaborator::combineOperands`,
  `src/elaborator/statements.cpp:787` (~63 lines, pure, isolated). Computes the
  canonical upper bound of two head names plus both coercion chains, and errors
  on an ambiguous join. **E1 and E3 want exactly this primitive.** It needs no
  redesign — only better inputs. (E4 does *not*; see that section.)
- **Candidate lists and pair search already exist**: `collectHeads` and
  `tryHeadPairs`, `src/elaborator/desugar_equality.cpp:303` and `:363`. Each
  operand already yields an ordered head list (raw head first, then successive
  single-step unfoldings), and `tryHeadPairs` searches the pairs left-major,
  taking the first registration that resolves. E1 should extend these, not
  invent a parallel mechanism.
- **Reverse-alias enrichment**: `reverseAliasHeads`,
  `src/elaborator/desugar_equality.cpp:327`, used at `:376`/`:379`. This handles
  an operand arriving *already* normalized (a recursive self-reference whose
  declared return type got reduced, so `ComplexNumber` shows up as
  `Quotient(…)`), which the forward unfold can never find. It runs as a second
  phase only after the first `tryHeadPairs` fails.
- **Carrier normalization already exists**: `Elaborator::carrierProjectionField`,
  `src/elaborator/desugar_eliminators.cpp:473`. Peels `<S>.carrier(bundle)` to
  the carrier as written, and correctly stays stuck on an *abstract* bundle so
  dispatch is unchanged. It has only **four** external call sites
  (`statements.cpp:216`; `desugar_equality.cpp:406`, `:408`, and `:677` — the
  last inside `applyOperatorImplicitFillers`, not the dispatch tiers).
- **Two separate relation paths**, which is why the probes fail two different ways:
  - `=` is an inline block at `src/elaborator/dispatch.cpp:1917`. It does *not*
    call `carrierProjectionField`, so the join is simply dead for bundled carriers.
  - `<`, `≤`, `+`, `*`, … go through `desugarArithmeticOperator`,
    `src/elaborator/desugar_equality.cpp:11-583` (573 lines, twelve ordered
    fallback tiers). It *does* call `carrierProjectionField`, but at tier 11,
    gated behind everything else failing. (The four helpers that follow it —
    `applyOperatorImplicitFillers` at `:584`, `tryProvePositive` at `:795`,
    `tryProveNonzero` at `:885`, `dischargeTrailingSideConditions` at `:935` —
    are separate functions; do not count them as one ~980-line body.)
- **Head names today**: free function `headConstantName`,
  `src/elaborator/term_utilities.cpp:7`, with ~87 call sites (91 textual
  occurrences including its declaration and definition). Any new notion of
  "this is Integer" must coexist with it, not race it.

## Design constraints

1. **No kernel arithmetic or new definitional equalities.** The elaborator
   inserts registered coercions; the kernel checks the result.
2. **Only canonical upward coercions.** Reuse the coercion registry and its
   unique joins. Never guess between unrelated carriers or coerce downward.
3. **Bidirectional, not numeral-specific.** The same mechanism should cover a
   literal `3` and a Natural term such as `truant(A)`.
4. **Respect abstraction.** A carrier projection whose closed structure
   argument reduces to Integer should provide the same dispatch evidence as
   the literal type `Integer`. An abstract bundle must stay stuck.
5. **Fail deterministically.** Ambiguous expressions remain errors, and the
   diagnostic explains which carrier could not be selected.
6. **Cost-gate hot paths.** Normalize carrier heads only after ordinary
   elaboration fails, or when the opposite operand supplies a unique target.

## The ordering constraint

E1 and E3 consume the same primitive: *given two operands, produce a common
carrier plus coercion chains.* That is `combineOperands`, and it is already
clean. What it lacks is normalized head names for its inputs.

E4 is not in that group — it compares whole proposition trees, not an operand
pair — which is a second reason to sequence it last and treat it as conditional.

**Therefore carrier normalization comes first.** Doing it first makes
bidirectional relation elaboration and citation reconciliation substantially
smaller changes, because both then inherit one shared notion of the carrier
instead of each growing its own.

Sections below are ordered for execution. Relative to the first draft of this
plan the only **label** change is that the old E1 and E3 swapped places — E1 is
now carrier normalization, E3 is bidirectional relation elaboration. E0 and
E2–E6 keep their numbers.

Every section's **content** has since been revised, so read them rather than
diffing against memory of the first draft. In particular E2's diagnosis is
corrected, E4 is now conditional on E1–E3 not already closing it, and E5 records
its tension with E4.

## Work plan

### E0. Freeze the failures as small tests

Status: `[ ]`

Add one focused feature test and corresponding negative controls before
changing the elaborator. The feature test should cover:

- positive Integer numerals and Natural variables on the right of `=`, `<`,
  `≤`, `+`, and `*`;
- unary `-` under an Integer-typed equality and inequality;
- integer matrix entries, so the **concrete bundled-carrier** path is exercised
  — `Matrix(Integer.commutative_ring_bundle, …)` presents entries as
  `CommutativeRing.carrier(Integer.commutative_ring_bundle)`, a projection over
  a *closed* bundle that must reduce to `Integer`. This is the opposite of the
  abstract case below, and the two must not be conflated: concrete reduces,
  abstract stays stuck;
- a citation whose conclusion contains bare numeral leaves;
- one two-edge lift, such as Natural to Rational, to ensure the solution uses
  the coercion registry rather than an Integer special case.

Negative controls must keep unrelated carriers and downward coercions rejected,
and must hold an **abstract** bundle (`Ring.carrier(s)` for a variable `s`)
stuck, so it still fails to dispatch.

The unseeded controls must be named precisely: an ordinary Natural expression
like `1 + 2` obviously stays legal. What must stay rejected is an expression
whose *only* reading needs a non-Natural carrier that nothing supplies — a
standalone `-1`, or an untyped division with no expected type in sight.

Likely files:

- `library/Test/expected_carrier_propagation_test.math`
- `library/ErrorTest/ambiguous_expected_carrier.math`

### E1. Share one notion of the carrier head

Status: `[ ]`

Promote the existing `carrierProjectionField` into one shared entry point, and
route the consumers through it — relation dispatch, binary operator dispatch,
expected-type coercion, and citation matching — so there are not four slightly
different notions of "this is Integer".

**Return candidates, not a single name.** A single `-> std::string` is too
lossy: a raw head can exist and still be unhelpful (`CommutativeRing.carrier`),
and returning it would *mask* the projected concrete carrier — which is exactly
today's `M(i,i) < 3` failure. The shape should be

```text
carrierHeadCandidates(type) -> std::vector<std::string>   // ordered, deduplicated
```

producing, in order: the raw head, alias unfoldings, the concrete carrier
projection, then bounded weak-head normalization. Cache per elaboration. Names
rather than `ExpressionPointer`s keep this composable with `headConstantName`'s
~87 existing call sites.

This is a generalization of the existing `collectHeads`
(`desugar_equality.cpp:303`), which already returns raw-head-then-unfoldings;
E1 adds the carrier-projection and WHNF tiers to it.

**Pair-search semantics — inherit them, do not invent them.** Where both
operands yield candidate lists, reuse `tryHeadPairs` (`:363`) unchanged:
left-major iteration, first resolving registration wins, earlier candidates
strictly preferred. Determinism then follows from list order, which is why the
order above is normative rather than advisory — the concrete carrier projection
must come *after* the raw head and alias unfoldings, so adding it cannot change
any dispatch that resolves today.

**Preserve the reverse-alias phase.** The two-phase structure at `:374-382` —
run `tryHeadPairs`, and only on failure enrich both lists with
`reverseAliasHeads` and retry — must survive. Forward unfolding of the operand
type cannot reach a registration whose *definition body* reduces to that type,
so this is not subsumed by adding tiers to `collectHeads`. Keep it as the
outermost phase: E1's new tiers join the first pass, and the reverse-alias
retry stays last.

One duplicate to fold up while here: the `.carrier` string-suffix test in unary
dispatch at `dispatch.cpp:2107` is a hand-rolled second implementation of the
same idea.

**Out of scope for this step:** the hardcoded projector whitelist at
`desugar_eliminators.cpp:485`. Deriving it from the registered bundles does not
work as stated — `canonicalBundleRegistry` (`kernel.hpp:196`) maps a structure
and carrier to a bundle, but does not encode *which constructor argument is the
carrier field*, and that layout differs per structure (`Ring.make` takes it
first; `CommutativeRing.make`/`Field.make` recurse through the nested layer;
`VectorSpace.make` is a parameterized inductive where the field parameter comes
first). Generalizing it needs a real carrier-projection descriptor. File that
separately rather than smuggling it into E1.

Acceptance probes:

```text
M(i,i) * truant(A)
M(i,i) < 3
M(i,i) = 0
```

Equality is expected to improve **here**, not at E3: the `=` path already
performs a `combineOperands` join (`dispatch.cpp:1963`) and fails only because
`headConstantName` hands it `CommutativeRing.carrier`. Feeding it candidates
should be sufficient. If `M(i,i) = 0` still fails after E1, that is a finding to
record — it means the `=` path needs the operand reordering of E3 as well.

### E2. Let expected carriers reach the operand leaf

Status: `[ ]`

**Corrected diagnosis.** The plumbing already exists: `dispatch.cpp:2076`
propagates the expected type into the unary `-` operand whenever that type has
a `Constant` head. The failure is one level lower —
`Elaborator::elaborateNumericLiteral` (`src/elaborator/inference.cpp:3047`)
takes only `(numeric, line, column)` and unconditionally emits a
`NaturalLiteral`. The expected type never reaches the leaf, so the operand types
as `Natural`, `Natural.negate` does not exist, and dispatch reports that Natural
has no negation.

Preferred fix, in order of preference:

1. call `coerceToExpectedTypeViaRegistry` (`src/elaborator/coercion.cpp:26`) on
   the operand after `dispatch.cpp:2088` — a small change reusing existing
   machinery, and the same call that argument positions already make;
2. only if that proves insufficient, make numeric literals expected-type-aware.

Also relax the "bare `Constant` only" gate at `dispatch.cpp:2078` to accept an
E1-normalized carrier, and mirror the propagation into the postfix path
(`dispatch.cpp:2240`), which today passes no expected type at all.

Acceptance probes:

```text
b = -1
b = -m          -- b : ℤ, m : ℕ
q < -n          -- q : ℚ, n : ℕ
```

A standalone `-m` with no expected carrier must remain rejected.

### E3. Make relation elaboration genuinely bidirectional

Status: `[ ]`

For `=`, `<`, and `≤`, collect carrier evidence from both operands before
committing to a relation implementation:

1. elaborate the informative operand;
2. normalize its type via E1;
3. elaborate the other operand with that carrier as its expected type;
4. use the coercion registry if its inferred type is lower;
5. select the relation only after both operands have been reconciled.

Do not let a bare numeral select `Natural.LessThan` while the opposite operand
already determines Integer. Preserve the existing carrier-join behavior for
two independently informative operands.

**This step is not additive, and that is the project's main risk.** Every
existing fallback tier in `desugar_equality.cpp` is documented as safe
*precisely because* it is reached only where elaboration previously errored
(see the comment at `:453`). Reordering dispatch changes behavior for
expressions that **compile today**, and a mis-dispatch to a different carrier
can still typecheck rather than erroring. Full library re-verification from a
cold cache is the only thing that catches this; treat it as a required gate for
this step, not an optional one.

Three specific hazards:

- `desugar_equality.cpp:135` carries an explicit design comment stating that a
  data operator's operand types are synthesized bottom-up and *"NEVER from an
  enclosing context."* That invariant is deliberate and correct for data
  operators. Scope this step to **relations only** — both paths already
  special-case relation symbols — and revise that comment to record the split
  rather than silently violating it.
- The `≥`/`>` flip at `desugar_equality.cpp:46` swaps operands, so it inverts
  which side is "informative".
- The `--check-redundant-casts` probe at `desugar_equality.cpp:66` re-runs this
  function up to three times and depends on structural-equality invariants.

The `=` path (`dispatch.cpp:1956`) also lacks the bottom-up retry that the
arithmetic path has (`desugar_equality.cpp:174`). Add the symmetric try/catch
so a failed expected-type attempt degrades to today's behavior instead of
erroring.

Acceptance probes:

```text
b * b < 3
M(i,i) < 3
M(i,i) = 0
```

All three elaborate to Integer relations without annotations. The latter two may
already pass after E1; re-measure before starting, and narrow this step to
whatever remains.

### E4. Reconcile citation conclusions and premises after carrier inference

Status: `[ ]` — **conditional; re-measure after E3 before starting.**

E1–E3 may make citation goals match already, since the goal's numeral leaves
will elaborate at the right carrier in the first place. Run the regression below
after E3 and skip this step entirely if it passes.

If it does not pass, note that this is **not** a matter of calling
`combineOperands`. That primitive reconciles two operands; citation matching
compares entire proposition trees, so reconciliation has to walk the goal and
the conclusion in parallel and coerce at corresponding leaves. Scope that work
before committing to it.

Once a goal fixes the carrier, citation matching should compare conclusions
after applying the same canonical coercion reconciliation used for ordinary
arguments. It should then infer explicit binders from the reconciled goal and
discharge the reconciled premises from context.

This is the one genuinely new construction in the project. Citation matching has
no coercion hook to extend — the only coercion awareness is `asNumeralLiteral`
(`src/elaborator/diff_bridges.cpp:1060`), which recognizes `0`/`1` through cast
towers. That is far narrower than reconciling via `combineOperands`.

Natural insertion point: on match failure, between the peel loop and
`completeCitationFromBindings` (`src/elaborator/induction.cpp:1766`).

Regression from this proof:

```text
done by Integer.square_below_three
```

This should close a goal written with bare `0` and `1`; it must not fail because
the goal's numeral leaves were elaborated as Naturals before matching. Note the
argument-free citation: the goal-driven form is the house style, and the earlier
positional spelling `Integer.square_below_three(Matrix.borderColumn(B)(i))` is
not what this project should be making work.

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

**E4 and E5 are in tension and must be budgeted together.** E4 adds a retry
inside `autoFillHintForClaimCore`, a function already re-entered by the
ζ-unfold retry (`induction.cpp:1650`) and by the speculative context scan, and
whose own comments name that re-entry as the dominant cost. Measure the failing
path before and after E4; if the added reconciliation attempt widens it, gate
the retry on the goal and conclusion actually having distinct carrier heads, so
it costs nothing when carriers already agree.

### E6. Sweep real proofs and measure the result

Status: `[ ]`

Use `library/Algebra/rank_three_escalation_bounds.math` as the first acceptance
file — its 297 explicit integer casts are the measured baseline — then sample
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
2. E1 shared carrier-head normalization.
3. E2 expected carrier at the operand leaf.
4. E3 bidirectional relation elaboration.
5. E4 citation reconciliation.
6. E5 diagnostics and budget.
7. E6 proof cleanup and documentation.

Each semantic step gets its own commit with its regressions. Elaborator commits
and mathematical cleanup commits remain separate.

Expect E2 to be small once E1 lands, and expect some E3 acceptance probes to
start passing during E1 — verify rather than assume, and drop any step whose
probes already pass.

## Validation gates

For every elaborator step:

```text
make -j 16 tests
make -j 16 error-tests
make -j 16 library
make clean-check
```

Also run the focused feature/error tests directly while iterating. Compare
clean-manifest leak counts and wall-clock elaboration time before and after E1,
because carrier normalization touches hot dispatch paths.

For E3 specifically, additionally verify the library **from a cold cache** — a
warm rebuild will not re-elaborate files whose sources did not change, and this
step can silently re-dispatch expressions that still typecheck.

## Definition of done

The project is complete when:

- every E0 positive probe elaborates without annotations;
- every negative control still fails with a stable, carrier-specific message;
- `rank_three_escalation_bounds.math` contains only mathematically meaningful
  casts, measured against its 297-cast baseline;
- full tests, error tests, library verification, and clean check pass;
- no kernel change or axiom is introduced;
- the conventions document states the resulting rule in one paragraph a
  mathematician can predict without knowing elaborator internals.

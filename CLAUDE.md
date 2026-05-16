# CLAUDE.md — project conventions and idioms

This file is auto-loaded into Claude's context. It documents the
**idiomatic** way to write proofs in this library, so future sessions
don't fall back to verbose patterns.

## Build

`make -j 16 library` from the project root. The dep graph is parallel;
warm rebuilds are sub-second. Always use `-j 16` (don't use bare `make`).

## Quotient idioms — use the short forms

The elaborator has type-and-relation inference for every Quotient
operation. Use the SHORT forms by default. The verbose forms exist
only as fallbacks when the elaborator can't infer; expect that to
be rare.

### Quotient.mk(rep)

```math
-- Short (preferred): T inferred from rep's type, R from expected type.
definition Rational.zero : Rational :=
  Quotient.mk(RationalRepresentative.make(Integer.zero, zero))

-- Verbose (avoid unless necessary):
definition Rational.zero : Rational :=
  Quotient.mk(RationalRepresentative, RationalEquivalent,
              RationalRepresentative.make(Integer.zero, zero))
```

The short form needs an expected type of shape `Quotient(T, R)` from
context (the surrounding theorem's return type, or an enclosing
function argument). If no expected type is available — e.g., as the
operand of unary `-`, or as the immediate body of `function (rep)`
inside `Quotient.lift` — the short form errors with `"cannot infer
the equivalence relation R"`. In those cases, fall back to verbose.

### Quotient.sound(x, y, proof)

```math
-- Short (preferred): T from x's type, R from proof.
Quotient.sound(rep1, rep2, equivProof)

-- Verbose:
Quotient.sound(RationalRepresentative, RationalEquivalent,
                rep1, rep2, equivProof)
```

### Quotient.lift(f, h, q)

```math
-- Short (preferred): T, R, U all inferred.
Quotient.lift(
    function (rep) => ...,
    function (rep1 rep2 hyp) => ...,
    q)

-- Verbose:
Quotient.lift(RationalRepresentative, RationalEquivalent, Rational,
               function ...,
               function ...,
               q)
```

### Quotient.induct(motive, atRep, q)

```math
-- Short (preferred): T, R inferred from q.
Quotient.induct(
    function (xArg : Rational) => P(xArg),
    function (rep : RationalRepresentative) => proofAtRep(rep),
    x)
```

### Quotient.induct_two(motive, atRep, q1, q2)

Same pattern, 4 args. For binary laws.

### Quotient.induct_three(motive, atRep, q1, q2, q3)

5 args, for ternary laws (associativity, distributivity). This was
added to avoid the awkward `function (yArg) (zArg) =>
Quotient.induct_two(yArg, zArg)` lambda-wrap that the older library
files use. New 3-arg laws should prefer `induct_three`.

## Implicit arguments

`{x : T}` binder syntax is supported on `definition`, `theorem`, and
`axiom`. Use this when a parameter is determined by another's type:

```math
theorem refl_implicit {T : Type(0)} (x : T) : x = x :=
  reflexivity(T, x)

-- Call site doesn't pass T:
refl_implicit(n)  -- T inferred as Natural
```

PAdic operations currently thread `(p : Natural) (primality :
Natural.is_prime(p))` explicitly. If you're writing NEW PAdic code,
consider making them implicit: `{p : Natural} {primality :
Natural.is_prime(p)}`. Existing PAdic code uses explicit form for
historical reasons; migration is a planned cleanup.

## Naming

- **No abbreviations in identifiers.** `representative`, not `rep` (in
  declaration names). Local-variable `rep` is fine.
- Long fully-qualified names (`Rational.padic_absolute_value`) are
  searchable. Don't shorten.
- `IsX` (predicate) and `X_is_Y` (witness) conventions match the
  algebraic-instance pattern in `library/Rational/instances.math`.

## Multi-pattern bindings

The elaborator does NOT fully support multi-pattern pattern-match
definitions where binders depend on the destructure (see TODO.md
"Multi-pattern fix"). When you need this, use a helper-chain pattern:
one outer pattern-match that pulls in the dependent binders, then an
inner case-analysis that uses them. Examples: `Integer/basics.math`,
`Integer/addition.math` use `_after_first` helpers.

## `cases` with hypothesis

To case-split on an expression and retain an equation between the
expression and the matched form, use the function-then-apply pattern:

```math
(function (absX : Natural) (eqAbsX : Integer.absolute_value_natural(x) = absX) =>
   (cases absX {
      | zero => function (eqZero : ... = zero) => ...
      | successor(k) => function (eqSucc : ... = successor(k)) => ...
    } : Integer.absolute_value_natural(x) = absX → <Goal>)(eqAbsX))
(Integer.absolute_value_natural(x),
 reflexivity(Natural, Integer.absolute_value_natural(x)))
```

This is verbose but currently the only way to retain the equation
through the case split. (A future tactic could automate this — see
TODO.md.)

## `ring` tactic limitations (v1)

`by ring` handles pure-sum or pure-product rearrangement but NOT
distributivity (it can't bridge `a*(b+c)` and `a*b+a*c`). For ring
identities that need distributivity, write a `calc` block with
explicit `Rational.distributivity_left/right`, `add_commutative`,
`add_associative`, `multiply_commutative`, etc. steps.

A `by ring` v2 with polynomial normalization is on TODO.md but
deferred until enough algebra content drives the design.

## `rewrite(lemma)`

Inside a `calc` step, `by rewrite(L)` for `L : a = b` finds the
unique structural occurrence of `a` on the calc step's LHS and
replaces with `b`. Only works in calc context (needs the step's
target as expected type). If `a` occurs multiple times or zero
times, fall back to explicit `congruenceOf(function (z) => …, L)`.

## File organization

```
library/
  axioms.math          -- foundational axioms (propext, function ext, etc.)
  Logic/               -- Equality, Quotient machinery, exists, etc.
  Natural/             -- Naturals, all the way to bezout, padic_valuation
  Integer/             -- Integers as Natural × Natural quotient
  Rational/            -- Rationals as (Integer, Natural) quotient
  Real/                -- Reals as Cauchy quotient of Rationals
  PAdic/               -- p-adics as p-adic-Cauchy quotient of Rationals
  Algebra/             -- IsMonoid, IsGroup, IsRing, IsCommutativeRing
  Test/                -- small test files for features (not math content)
```

Each module's files are layered (basics → operations → laws →
instances). Imports flow up; you can't import a layer above you.

## Kernel quirks to know

See `~/.claude/projects/-Users-alvaro-claude-math/memory/kernel_quirks.md`
for the full list. Highlights:

- **No large elimination from Prop.** Non-empty Prop inductives have
  motive fixed at Prop. Empty Prop inductives (False) admit large
  elimination.
- **Function-wrapping for cases-on-expression** (see "cases with
  hypothesis" above).
- **Identical-printed-types universe issues** can arise when nested
  polymorphic functions get inferred universe parameters that don't
  unify the way the user expects. Workaround: add explicit `.{u, v}`
  annotations.

## Memory

The user has persistent memory at
`~/.claude/projects/-Users-alvaro-claude-math/memory/`. See `MEMORY.md`
there for the index. Notable entries:

- `padic_construction_status.md` — p-adic construction is complete
  (operations + ring laws + IsCommutativeRing instance).
- `software_engineering_for_math.md` — math library design follows
  SE best practices (descriptive names, refactoring), not math
  writing traditions.
- `keep_git_current.md` — commit coherent pieces as they land.

## Operator overloading

`operator (sym) on (T1, T2) := F;` registers `sym` to dispatch on
the heads of T1 and T2. T1 and T2 must be the heads of types, not
parameterized type applications. So:

- `operator (+) on (Integer, Integer)` works.
- `operator (+) on (PAdic, PAdic)` would conceptually work but
  `PAdic.add` takes `(p, primality, x, y)`, not `(x, y)`. Once `(p,
  primality)` become implicit on `PAdic.add`, the operator overload
  will work.

# TODO

Language and library improvements, in priority/dependency order. Items
move from **Active** to **Completed** with a date when they land; items
in **Opportunistic** are smaller wins to slot in when their motivating
pain becomes acute.

## Active

### 1. More math content — in progress

**Plan revision history**: The original Integer-cancellation route
was blocked because the kernel lacked the converse of
`Quotient.sound`. After a long discussion of foundations, the user
chose to add **propositional extensionality** as a kernel axiom and
derive `Quotient.exact` from it. With those in hand, Integer
cancellation is a straightforward 100-line proof, and Rational can
be built the natural way (Integer numerator, positive Natural
denominator). The concrete-triple workaround has been replaced.

Status:
- **DONE: Foundation upgrade.** Propositional extensionality
  (`Logic/extensionality.math`), `Quotient.exact` (derived in
  `Logic/quotient.math`), and `Integer.multiply_cancel_right_by_natural_successor`
  (in `Integer/cancellation.math`).
- **DONE: Abstract algebra layer.** Monoid, Group, Ring, CommutativeRing
  predicates; Integer and Natural instances; a few generic group lemmas.
- **DONE: Quotient.induct_two** for binary lemmas on quotient types.
- **DONE: Natural multiplication cancellation** + helpers.
- **DONE: Rational basics, the natural way.**
  `RationalRepresentative.make(numerator : Integer,
  denominatorMinusOne : Natural)`; cross-multiplication equivalence
  at Integer level; reflexivity / symmetry / transitivity verified;
  `Rational := Quotient(...)`; constants. Transitivity uses
  `Integer.multiply_cancel_right_by_natural_successor` directly.
- **DONE: Rational.add_representatives** (the new formula on
  Integer/Natural pairs).
- **DONE: Rational.add, Rational.multiply, Rational.negate,
  Rational.subtract.** All four operations lifted via Quotient.lift
  with their respect proofs.
- **DONE: Rational ring laws.** Both commutativities, both
  identities, additive inverse, both associativities, both
  distributivities (`Rational/ring.math` + `Rational/algebra.math`).
- **DONE: Rational is a CommutativeRing.** Eight instance witnesses
  in `Rational/instances.math`.
- **DONE: Kernel perf.** Structural-equality fast path in
  `isDefinitionallyEqual` — cold-rebuilding the whole library is
  now ~0.3s with `make -j 16` (was ~40 minutes before).

Next:

- **Integer → Rational embedding.** `Integer.to_rational(n) :=
  mk(make(n, 0))`. Extends the cast registry: ascription
  `(x : Rational)` on an Integer auto-applies this.
- **Field** predicate, with a non-zero-implies-invertible witness.
  Rational is then a Field instance.
- **Real** (Cauchy sequences over Rational, or Dedekind cuts).
- More generic abelian-group / ring / field lemmas as needed.

Pain points encountered while writing the Rational laws — these are
the strongest motivators for the ergonomics work in items 2/3 below:

- ~~**No "rewrite at position".**~~ **DONE: `rewrite(lemma)` tactic.**
  Finds the unique structural occurrence of the lemma's LHS in the
  goal's LHS and builds the `congruenceOf` wrapper automatically. Works
  when the LHS is unique; otherwise the user must still write explicit
  `congruenceOf(function (x) => …, lemma)`. Bulk conversion of existing
  calls is opportunistic.
- **No ring/abelian-group automation.** Associativity / distributivity
  proofs require manual rearrangement step-by-step. The Rational
  3-arg laws have 6-11 step kernels each that would be `by ring` in
  most systems. **Status:** Deferred — a proper `by ring` is a 1-2
  day project (polynomial normalization + proof emission, or
  reflection infrastructure). The narrower `rewrite` tactic captures
  most of the per-step boilerplate today, so the marginal payoff of
  `by ring` is lower than it was before `rewrite` landed.
- ~~**Triple-destructure boilerplate.**~~ **DONE:
  `obtain Quotient.mk(rep) from x;` WLOG sugar.** Single line per
  representative pulled. Removed ~426 lines (~20%) of pure plumbing
  across `Rational/{ring,algebra}.math`.

### 2. Parallel verification
Optimistic per-theorem parallelism with a thread pool: register
signatures eagerly, parallelize body verification, collect all errors
at end, fail if any worker fails. **Defer until the operator-
overloading change settles** — parallelizing over a fast-changing
elaborator means doing the work twice.

Subtleties: per-worker universe-meta naming; thread-safe kernel
caches; deterministic error-ordering at the end; slow theorems set
the floor (consider splitting long proofs into lemmas).

### 3. `by ring` (and `by group`, `by abelian_group`, …)
Term-normalization tactic for ring identities. Highest payoff,
highest effort. **Wait until we have enough algebra content (item
3) to design the procedure against real use cases** — premature
normalization is hard to redo.

## Opportunistic

Smaller items to land when the motivating pain becomes acute:

- **`Quotient.lift_two`.** Sketched in `Logic/quotient.math` but
  currently rejected by the elaborator with a universe-argument
  mismatch through the nested polymorphic lifts. Manual two-step
  lifts (Integer.add pattern) work fine. Revisit when the universe-
  handling code in the elaborator is more robust.
- **Multi-pattern fix.** Relocate function-argument bindings inside
  inner cases so the helper chains in `Integer/basics.math`,
  `Integer/addition.math`, etc. collapse. See commit 9e022a6 message
  for the design sketch.
- **`rewrite h at e` tactic.** Useful for non-ring rewrites; less
  urgent given `by ring` will cover the ring case.

## Ergonomics audit (2026-05-16) — math-friendliness backlog

From an end-to-end audit of the p-adic construction (~6600 LOC in
`library/PAdic/`). Goal: make proofs feel familiar to mathematicians
and LLMs.

### Already implemented but not adopted (mechanical refactor required)

- **Quotient.mk / sound / lift / induct / induct_two have short forms
  with inference.** Elaborator desugarings exist at
  `elaborator.cpp:2237–2275`:
  - `Quotient.mk(rep)` — infers T from rep, R from expected type.
  - `Quotient.sound(x, y, proof)` — infers T from x, R from proof.
  - `Quotient.lift(f, h, q)` — infers T, R, U.
  - `Quotient.induct(motive, atRep, q)` — infers T, R.
  - `Quotient.induct_two(motive, atRep, q1, q2)` — infers T₁/R₁/T₂/R₂.
  Our `library/PAdic/*.math` (and `library/Real/*.math`,
  `library/Rational/*.math`) routinely use the verbose 5/6-arg forms.
  Refactoring would cut ~150 boilerplate sites in PAdic alone.

### Top friction points (with category and remedy)

1. **Verbose `Quotient.mk(T, R, rep)` usage in our own code.** Elaborator
   already supports short form. *Remedy: bulk refactor — task below.*

2. **Threading `(p, primality)` through every PAdic operation.** Cat:
   elaborator. Adds visual noise + LLMs frequently miss them. Two
   possible remedies: (a) **implicit arguments `{p : Natural}
   {primality : Natural.is_prime(p)}`** — the syntax + counting
   machinery already exists (`elaborator.cpp:534–544`,
   `implicitArgumentCounts`) but currently only fires on axioms; needs
   extension to `definition` / `theorem`. (b) **section binders** — bigger
   project. (a) is the smaller fix and would help PAdic immediately.

3. **3-arg ring law nesting quirk (Quotient.induct + nested induct_two).**
   Cat: kernel/elaborator. Naive triple-induct fails; we need
   `function (yArg) (zArg) => Quotient.induct_two(...)` wrapping
   (see `library/PAdic/ring.math:171–293`). *Remedy:* add a
   `Quotient.induct_three` desugaring (5-arg: motive, atReps, q1, q2,
   q3) and a corresponding `induct_two_three` etc. as needed. Sugar
   only.

4. **No operator overload on parameterized types.** Cat: elaborator.
   `operator (+) on (PAdic, PAdic)` would need `PAdic.add` to have type
   `PAdic → PAdic → PAdic`, but ours is
   `(p, primality, x, y) → ...`. *Remedy:* once #2 lands and `(p,
   primality)` become implicit, the operator signature becomes
   `PAdic(p, primality) → PAdic(p, primality) → PAdic(p, primality)`
   and dispatch works.

5. **`by ring` v1 doesn't handle distributivity.** Cat: tactics. Every
   multiplicative-over-additive associativity/distributivity proof
   needs 5–15 manual `congruenceOf` steps. *Remedy:* `by ring` v2 with
   polynomial normalization. Deferred — 1–2 day project (see item 3
   above).

6. **`Quotient.sound` needs three relation properties when expected
   type isn't inferable.** Cat: kernel API. *Remedy:* document; rarely
   bites once short-form is adopted.

7. **Fully-qualified long names crowd lines.** Cat: elaborator/syntax.
   `Rational.padic_absolute_value`, `PAdicCauchySequence.sequenceFunction`.
   *Remedy:* a per-block `open NAMESPACE` directive that introduces
   short aliases. Lower priority — long names are searchable and
   unambiguous.

8. **Hypothesis-introduction via `function (x)(eq) => cases x { ... }`.**
   Cat: tactics. The `cases h : expr with ... in` form would be more
   discoverable. *Remedy:* a `cases` tactic that takes a `with`-pattern
   and binds the equation automatically. Bigger project, defer.

### Quick wins (1–3 hours each)

- **Refactor `library/PAdic/*.math` to use short Quotient.* forms.**
  Mechanical, big payoff. Estimate ~150 sites, ~2 hours.
- **Refactor `library/Rational/*.math`, `library/Real/*.math` similarly.**
  Lower urgency but same payoff per call site.
- **Extend implicit-arg recognition (`{x : T}` binders) to `definition`
  and `theorem`, not just `axiom`.** Likely ~1 hour given the
  machinery already exists. Unlocks `(p : Natural)` implicit threading
  in PAdic.
- **Add `Quotient.induct_three` and `Quotient.induct_four` desugarings.**
  Patterns for n-ary ring laws. ~1 hour.
- **Better error messages for nested Quotient.induct case-shape errors.**
  When the case body has wrong arity, suggest "wrap with `function
  (next_args) => ...`". ~30 min.
- **Document the existing short-form inference in `claim_language.md`
  or a new `quotient_idioms.md`.** ~30 min.

## Completed

- **2026-05-14: Rational as CommutativeRing.** Operations
  (add/multiply/negate/subtract) + respect proofs + ring laws
  (commutativity, identity, inverse, associativity, distributivity)
  + IsCommutativeRing instance witness. Five new files
  (`Rational/{addition,multiplication,negation,ring,algebra,instances}.math`,
  plus updates to `Rational/basics.math`). Includes kernel perf
  optimization — `isDefinitionallyEqual` now short-circuits on
  structural equality before WHNF, turning the slowest file from a
  38-minute build into a 80ms build. Commits `19d061b`, `8eea667`,
  `0fe54a8`, `2ede0fa`, `9c008dd`, `790519c`.
- **2026-05-14: Per-file .mathv caching + Makefile.** The kernel
  binary now writes a serialized .mathv file per source and reads
  back cached deps; `make -j N library` parallelizes verification
  across the dependency DAG. Hash-based source validation; format-
  versioned binary serialization. Files: `hash.{hpp,cpp}`,
  `serialize.{hpp,cpp}`, `main.cpp` (new --source/--deps/--output
  CLI form + `kernel deps` subcommand), `Makefile`. Warm rebuild
  ~30ms; full cold rebuild ~300ms.
- **2026-05-14: Rational rebuilt with Integer numerator.** Replace
  the concrete-triple workaround with `(Integer, Natural)` — exactly
  the construction a mathematician writes. Transitivity uses Integer
  cancellation directly. `Rational.add_representatives` updated to
  the new formula. The previous Rational/basics.math + Rational/
  addition.math were rewritten end-to-end. Commit `52dd311`.
- **2026-05-14: Foundation upgrade.** Added propositional
  extensionality, derived Quotient.exact, proved Integer
  cancellation. Together these enable the natural Rational
  construction (and unblock similar constructions for Complex,
  polynomial rings, etc.). Commit `a1b4423`.
- **(superseded) Rational basics + add_representatives, concrete-
  triple version.** Replaced by the natural Integer-numerator
  representation above.
- **2026-05-14: Natural multiplication cancellation.** `a · c = b · c`
  with `c ≥ 1` forces `a = b`. Three supporting helpers
  (`add_equals_zero_left`, `multiply_equals_zero_with_positive_right`,
  `multiply_cancel_left`). Unblocks Rational transitivity. Commit
  `8e63b9b`.
- **2026-05-14: `Quotient.induct_two`.** Binary induction helper:
  one call replaces a nested-induct + at-representatives chain. The
  twin `Quotient.lift_two` was attempted but currently fails the
  elaborator's universe-arg handling; the manual two-step lift in
  Integer.add etc. remains the path of least resistance. Commit
  `fcfb34a`.
- **2026-05-14: Abstract algebra layer.** Monoid, CommutativeMonoid,
  Group, AbelianGroup, Ring, CommutativeRing as Proposition
  predicates; Integer is a commutative ring (8 instance witnesses);
  Natural is a commutative monoid under both + and ·; three generic
  group lemmas (`right_inverse_unique`, `left_inverse_unique`,
  `inverse_involution`). Also fixed `desugarCongruenceOf` to close
  the domain/codomain types — without the fix, generic lemmas over a
  binder-bound carrier type failed with "unbound internal variable".
  Commit `a4a4421`.
- **2026-05-14: Operator overloading for Integer.** `+`, `*`, `-` now
  dispatch on operand type, routing Integer operands to `Integer.add`,
  `Integer.multiply`, `Integer.subtract`. Lookup uses the raw inferred
  type so definitions like `Integer` retain their name. Commit
  `4dd4042`.
- **2026-05-14: Ascription as coercion.** `(x : T)` now auto-inserts a
  canonical embedding chain when `x`'s type doesn't match `T` but a
  registered chain exists. Initial registry: `Natural → Integer` via
  `Natural.to_integer`. Grows as new number systems land. Commit
  `8efd117`.
- **2026-05-14: Make narrow tactic keywords contextual.** `claim`,
  `obtain`, `assume`, `set`, `suffices`, `from`, `on`, `with`,
  `case`, `apply`, `contradiction` now parse as identifiers in name
  positions. Commit `cd1f993`.
- **2026-05-14: Free 10 dead reserved keywords.** `hypothesis`,
  `motive`, `target`, `proof`, `qed`, `have`, `show`, `induction`,
  `of`, `reduction`. Commit `ce59030`.

## Index of relevant chat decisions

- **Coercions: explicit only, never implicit.** Cascaded explicit
  casts (`Real.to_complex(Rational.to_real(...))`) are unbearable,
  but visible casts at one syntactic site (`(x : T)`) localize the
  type change and force the reader/writer to know what type is
  involved. Mathlib's `push_cast`/`norm_cast` are evidence that
  implicit coercion is the single biggest source of "my proof
  should work but doesn't" pain in formal math; we won't repeat it.
- **Embedding paths are canonical, not searched.** If two paths
  ever exist from source to target, reject the cast at elaboration
  time. (Currently a single linear chain, so this is a future
  invariant.)
- **Mathematician-friendly identifiers.** No sigil-marked or
  ALL_CAPS keywords; the math vocabulary belongs to the user.
  Tactic-block keywords are contextual; hard keywords are kept
  minimal.

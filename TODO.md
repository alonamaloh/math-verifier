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

- ✅ **Refactor `library/Integer/*.math` short Quotient.* forms.** Done
  2026-05-16: 17 lines saved across 6 files (8 sites).
- ✅ **Refactor `library/Rational/*.math` short Quotient.* forms.** Done
  2026-05-16: 48 lines saved across 13 files. Discovered useful trick
  — `(Quotient.mk(rep) : Rational)` ascription unlocks short form in
  expected-type-unfriendly positions. Documented in CLAUDE.md.
- ⏳ **Refactor `library/PAdic/*.math` and `library/Real/*.math` short
  Quotient.* forms.** In flight in worktree.
- ✅ **Extend implicit-arg recognition (`{x : T}` binders) to `definition`
  and `theorem`.** Already works. Verified by test at
  `library/Test/implicit_args_test.math`.
- ✅ **Add `Quotient.induct_three` desugaring.** Done. (Quotient.induct_four
  is deferred — no 4-arg laws currently need it.)
- ✅ **Better error messages for `Quotient.mk(rep)` inference failure.**
  Done — names the common failure spots and suggests the explicit
  fallback.
- ✅ **Document short-form inference and idioms in `CLAUDE.md`.** Done.

### Deferred — short forms of Or/And/Exists.eliminate

`Or.eliminate(hL, hR, disj)`, `And.eliminate(h, conj)`,
`Exists.eliminate(h, ex)` short desugarings were prototyped. The
mechanical part (extracting types from the third/second argument,
constructing the full call) works fine; the trip-up is that when the
*outer expected type* contains free variables from local binders
(common — any theorem with parameters), threading it as
`makePi("_", A, expectedType)` into the handler's elaboration causes
the kernel to lose track of those free variables ("unbound internal
variable: m" or similar).

The no-expectedType fallback works for the OUTERMOST call (the
elaborator gets Goal from handleLeft's codomain), but inside a
nested Or/Exists/And.eliminate, the inner call has no expected type
unless we propagate, so constructors like `Or.introduceLeft(p)` (with
implicit A, B from context) fail to infer their parameters.

This is structurally the same blocker as the auto-congruence in calc
prototype (item above): synthesizing terms that mix
opened-form FreeVariables with kernel-level BoundVariables. Fix
needs a careful close/open dance during desugar synthesis.

Reverted. The verbose `Or.eliminate(A, B, Goal, hL, hR, disj)` form
still works.

### Deferred — auto-congruence in calc steps

Goal: let the user write `by eq` for any calc step whose two sides
differ only by a function applied to both endpoints of `eq` — saving
the explicit `congruenceOf(function (z) => …, eq)` wrap at every site.

I prototyped this (`tryAutoCongruenceInCalc` in elaborator.cpp) and
got the structure working: extract the proof's `a = b` and the goal's
`LHS = RHS`, find the unique structural occurrence of `a` in `LHS`,
build `Equality.congruence(λz. LHS[a→z], a, b, eq)`.

What blocked it: mixing free-variable forms across pieces of the
synthesized term. The `proofComps.leftEndpoint` extracted from the
WHNF-opened proof type has FreeVariables (Internal origin), but the
`proofKernel` itself has BoundVariables (since `elaborateIdentifier`
returns BoundVariable for local binders). Synthesizing a term that
mixes both — and then having the caller's `inferTypeInLocalContext`
open it — results in "unbound internal variable" errors because the
opening pass converts BoundVariables but leaves the existing
FreeVariables alone, and the resulting form is inconsistent.

Fix path: either (a) close everything before synthesis and open the
whole result at the end, with careful index management; (b) open
`proofKernel` first via `openOverLocalBinders` and work entirely in
opened forms (matching what the other Quotient.* desugarings do).
Both are doable; (b) is the cleaner approach.

Reverted to keep `main` clean. Resume when there's time to debug the
index plumbing.

### Open follow-ups for the calc auto-prover (smaller, defer to taste)

These are the natural extensions to the current
`autoProveCalcStep` + `tryClassifyDiff` that we considered but didn't
take. Each is meaningful but smaller than the hashing project below.

- **Multi-position diff.** When `tryClassifyDiff` is stuck because
  both function and argument differ at the current App level,
  recursively prove `fn_l = fn_r` and `arg_l = arg_r` separately and
  stitch with two congruences + transitivity. Handles
  `(a+b)+(c+d) = (b+a)+(d+c)` and the remaining
  `Equality.transitivity(rewrite(A), rewrite(B))` chains in the
  library. Phase 2 of the hashing work subsumes most of this — once
  AC-equality fires at the top of `(a+b)+(c+d)` directly, the walker
  doesn't even need to descend.

- **β-aware descent (attempted, reverted).** Tried WHNF on cursors
  during descent; the problem is that `weakHeadNormalForm` unfolds
  `Natural.add` (a Definition) into a raw `Natural_recursor`
  application, which the classifier doesn't recognize as a binary
  op. Two paths forward: (a) teach the classifier about recursor-
  call shapes (much code, brittle), or (b) add a shallow "one ι-step
  only" reducer to the kernel that fires the constructor case but
  keeps the surface name. Defer until clearly motivated.

- **Local-hyp match through polymorphic binders.** The Algebra agent
  hit `combineHypothesis : op(a, b) = identity` as a function
  parameter in a generic ring lemma. Our local-hyp scan opens it for
  the def-eq check, but the polymorphic `carrier`/`operation`
  parameters leak as `Internal` FreeVariables in the synthesized
  proof and the kernel rejects it. Same root cause as the "auto-
  congruence in calc" deferred item — careful open/close index
  plumbing.

### Active — subtree hashing for the auto-prover (2026-05-17, in flight)

User-proposed and adopted in the phased form below. The idea: cache a
hash on each `ExpressionPointer`, computed bottom-up. Equality of
subtrees becomes O(1) hash compare instead of recursive
`structurallyEqual`. Then design hashes so that commutativity and
associativity fall out of equality, and use the hash to index
arbitrary library theorems by their conclusion shape.

What this unlocks beyond the speed win:

1. The classifier becomes uniform — commutativity / associativity no
   longer need bespoke `decomposeBinaryOpApplication` matchers; the
   hashes line up automatically.
2. Indexing arbitrary library theorems. Hash each theorem's
   conclusion-LHS shape; at classify time, hash the diff's left side
   and look up candidate lemmas. Distributivity, identity, and any
   user-defined rewrite lemma become first-class without bespoke
   detection.
3. Normal-form hashing for laws like distributivity: maintain a
   canonical form (e.g. push multiplication over addition); hash the
   canonical form. Then `hash(a*(b+c)) == hash(a*b + a*c)` and the
   classifier can pick either with a synthesized rewrite. (Future.)

Caveats:

- Hashes are probabilistic. We still need a verification step where
  the kernel typechecks the candidate proof — cheap, since the kernel
  is fast.
- Under binders we hash α-equivalence-modulo de-Bruijn (canonical).
- Universe arguments and FreeVariable origins need careful inclusion.

#### Phase 1 — structural subtree hash

Add a `uint64_t hash_` field to `Expression` and `Level`, populated at
construction in each `make*` function. Hash composition:

- Atoms (`Sort`, `Constant`, `BoundVariable`, `FreeVariable`): mix
  identifying fields (name / index / origin / universe args) with a
  variant tag byte.
- Compound (`Pi`, `Lambda`, `Application`, `Let`): mix the variant tag
  with the children's hashes via a non-commutative combiner
  (FNV-1a step or similar).
- Universe levels: same pattern.

First win: use the hash as a fast-reject in `structurallyEqual` —
hashes differ → return false immediately; otherwise fall back to the
recursive compare. α-equivalence comes for free because
`BoundVariable` hashes by de Bruijn index.

Cost: ~50 lines in kernel, +8 bytes per Expression node. No semantic
changes; purely a perf foundation. **Task #31.**

#### Phase 2 — AC-canonical equality for registered ops

Kernel stays structural. Elaborator gains `acEqual(env, l, r)`:

- At a node whose head is registered-commutative: compare ignoring
  child order (multiset of arg-hashes).
- At a registered-associative node: flatten the chain first.
- At a node that's both: multiset of leaves over the flattened chain.
- Otherwise: structural recursion.

Lazy AC-canonical hash cached per `(Expression*, op_set_version)`.
The auto-prover's classifier and walker switch from
`structurallyEqual` to `acEqual`. The bespoke
commutativity/associativity decomposers retire — equality alone
handles them. Cases like `(a+b) + (c+d) = (b+a) + (d+c)` (both
children commuted) trivially succeed because the walker no longer has
a "both differ" failure mode for AC ops. **Task #32.**

#### Phase 3 — theorem-shape indexing

Build a registry: `acHash(conclusion-LHS) → list-of-lemmas`.
Populated at theorem-declaration time using the AC-canonical hash
from Phase 2 so commut/assoc-equivalent LHSs collide deliberately.

At classify time, given a diff `(sub_l, sub_r)`:

1. Compute `acHash(sub_l)`.
2. Look up candidate lemmas.
3. For each candidate, run a small one-way matcher to instantiate the
   lemma's binders against `sub_l`.
4. Check `acEqual(instantiated RHS, sub_r)`.
5. If yes, emit the lemma application as the proof.

Handles arbitrary user-written rewrite lemmas — not just commut /
assoc / identity. The bespoke identity classifier added in Phase 0
can be retired. Distributivity in its non-canonical form would still
miss; a future "normal-form hashing" extension covers it. **Task
#33.**

#### Risks and order

- Phase 1 is risk-free. Hash collisions still let `structurallyEqual`
  fall through to the recursive compare; correctness preserved.
- Phase 2's main risk: AC-flattening under binders. De Bruijn indices
  keep α-equivalent terms hashing the same; we just need to flatten
  with care.
- Phase 3's risk: the matcher must refuse over-eager unification
  (e.g. don't match `f(x)` against `g(y)` just because both are
  Applications). Standard first-order matching solves this.

Implementation order: land Phase 1, measure speedup, then Phase 2.
Phase 3 builds cleanly on Phase 2's `acEqual`.

#### Deferred — pack loose-bvar / free-var flags into the hash word

See `HASH_USE_VS_LEAN.md` §2 and §5. Lean caches `hasFVar`,
`hasLooseBVar`, and `looseBVarRange` per Expr next to the hash, and
uses those to make `instantiate` / `abstract` / `substitute` O(1) on
closed subtrees. We could do the same — same construction sites as
the hash, and the bits fit in the high 8 bits of our `uint64_t hash`
field (56-bit hash is comfortably above our 10^5–10^6 expression
scale; collisions in all our use cases are correctness-preserving).

Decided to defer for two reasons:

1. **Different concern.** Phase 1 was equality fast-reject; the
   packed flags are about substitution-skip. They're orthogonal.
   Phases 2 and 3 don't need the flags.
2. **No measurement yet.** Phase 1 already gave us a 4× cold-rebuild
   speedup; we don't yet know whether `substitute` / `openBinder` are
   the next bottleneck. The decision should be data-driven.

**Trigger:** after Phases 2 and 3 land, profile a cold-rebuild of
the whole library. If `substitute` / `openBinder` show up in the top
5, pack the 8 bits. Otherwise defer further or drop. The packing
isn't load-bearing; it's a perf optimization gated on a profile.

### Next sweep — Equality combinator carrier implicit

`Equality.transport_proposition`, `Equality.transitivity`,
`Equality.symmetry`, `Equality.congruence` all take an explicit
`(A : Type)` carrier as their first argument, then `(x : A)` etc.
The carrier is derivable from `x`'s type at every call site. Library-
wide there are ~720 uses (192 + 527), and the carrier often takes its
own line. Making the carrier `{A : Type}` implicit would save ~500
lines library-wide.

Plan:
1. Change signatures in `library/Equality/basics.math` to use `{A}`.
2. Bulk-refactor call sites to drop the carrier argument.
3. Estimate: ~2 hours given the refactor agent template we used for
   Quotient.* forms.

Higher-friction items still deferred: `by ring` v2 with distributivity;
PAdic operations migrating to implicit `(p : Natural) (primality :
…)`; `operator (+) on (PAdic, PAdic)` overload; `cases h : expr with`
tactic; per-block `open NAMESPACE`.

## Ergonomics audit (2026-05-17) — full-library cross-cut

Findings from a parallel six-agent review of every directory under
`library/`. Convergence: the same five pain points dominate from
`Logic/` through `PAdic/`. Items already on the backlog above are
noted as **(see N)**; new items are flagged with the directories
that motivate them.

### New friction points

1. **Case-on-expression with retained equation — biggest line-eater
   across the library.** The function-wrap pattern from CLAUDE.md
   ("`cases` with hypothesis") appears 20+ times in
   `Natural/padic_valuation.math`, 8 times in `Natural/divide.math`
   alone, plus heavy use in `Natural/division.math`,
   `Natural/cancellation.math`, `Natural/decide_divides.math`,
   `Logic/constructor_totality.math`, `Integer/absolute_value*.math`.
   Each instance is a 6-line wrapper around what a textbook writes
   in one line. *Remedy:* `match E with eqHyp returning G { | c₁ =>
   … | c₂ => … }` where `eqHyp : E = c_i` is bound automatically in
   each arm. Sharper formulation of item 8 in the 2026-05-16 audit.

2. **`rewrite` only fires inside `calc` steps.** Outside `calc`,
   users fall back to the 6-arg
   `Equality.transport_proposition(T, motive, x, y, eq, term)` form,
   which appears 40+ times in `Natural/divide.math` alone and is
   the dominant boilerplate in `Logic/quotient.math`,
   `Natural/factorization.math`, `Natural/prime_split.math`,
   `Natural/padic_valuation.math`. *Remedy:* `by rewrite(L)`,
   `by rewrite(← L)`, and `by rewrite(L) in h` at any proof-script
   position, with motive inferred from the goal/hypothesis.
   Generalizes the existing in-calc tactic.

3. **Short `Quotient.mk` blocked under `+`, `*`, `=`, `≤`.**
   Documented in CLAUDE.md as a known limitation; in practice it
   bloats `Integer/ring.math` by ~30% and shows up at
   `Rational/triangle.math:282-294`, `Rational/positive.math:142-157`,
   `Rational/order_arithmetic.math:191-206`. *Remedy:* when an
   operand of a registered operator has head `Integer` / `Rational`
   / `Real` / `PAdic`, propagate that head as the expected type for
   an unresolved `Quotient.mk` on the other side. Roughly: have the
   operator registry seed expected types for short-form inference.

4. **`Or.eliminate` / `Exists.eliminate` / `And.eliminate` re-type
   the motive that the elaborator already knows from context.** The
   third argument is almost always the surrounding goal, retyped
   verbatim. Pyramids of these forms dominate
   `Natural/prime_split.math` (200-line `Or → Exists → And`
   staircase), `Integer/absolute_value_multiplicative.math:151-237`
   (87 lines of four-way sign dispatch), and the Cauchy-equivalence
   transitivity in `Real/basics.math:160-298` (139 lines, mostly
   ∃-unpacking). *Remedy:* `dispatch on X { case Or.introduceLeft(p):
   … }` / `case ⟨w, hw⟩: …` syntax that scrutinizes the eliminator
   targets without taking an explicit motive. This is the deferred
   sibling of the 2026-05-16 "Deferred — short forms of
   Or/And/Exists.eliminate" work; resuming it is high-leverage.

5. **`obtain ⟨a, b, c⟩ from …` cannot flat-destructure nested
   existentials and conjunctions in one step.**
   `Natural/division.math:119-179` is 60 lines whose math is
   `let ⟨q, r, eq, bound⟩ := w; ⟨succ(q), r, …, …⟩`. The current
   pattern needs three nested `Exists.eliminate` and an
   `And.eliminate`. *Remedy:* allow `let ⟨a, b, c, d⟩ := h` for
   `h : ∃ a. ∃ b. P ∧ Q`. Likely a small extension of the existing
   single-level destructure.

6. **`by_induction … using` (v3 of prime_divisor) needs the return-
   type ascription stripped.** `Natural/prime_divisor_v3.math:50-52`
   ends with `: 2 ≤ n → ∃ …)(atLeastTwo)` — the only remaining piece
   of CIC plumbing in an otherwise textbook proof. v2 is the current
   sweet spot; v3 wins once it infers its return type from the
   enclosing `theorem`.

7. **`by bridge` for pattern-match definitions on quotient reps.**
   Every binary-op respect proof in Real/PAdic spends ~30 lines
   converting `sequenceFunction(add(rep1, rep2), m)` into
   `sequenceFunction(rep1, m) + sequenceFunction(rep2, m)` via
   manual `cases` + `reflexivity`. See
   `Real/addition.math:189-198, 267-299`,
   `Real/negation.math:105-129`, and PAdic parallels. *Remedy:* a
   tactic that exposes a pattern-match definition's β-reduction as
   a one-step calc rewrite when the matched argument is structurally
   a constructor.

8. **Strict `<` doesn't transport cleanly.** `LessThan` is
   `And(LessOrEqual, Not(_ = _))`, so every transport along `<`
   manually destructures and rebuilds. See
   `Rational/order_arithmetic.math:336-356, 421-434`. *Remedy:*
   either make `<` a single-constructor record with first-class
   destructure, or add a `by strict_mono(weak_lemma, neq_lemma)`
   tactic that auto-assembles `And.introduction`.

### New big idea — `Algebra/CauchyCompletion`

`Real/*.math` (~2600 lines) and `PAdic/*.math` (~5300 lines) are
~80% parallel: same Cauchy/bounded definitions, same equivalence
relation, same Step-1/Step-2 anchor split in `cauchy_bounded.math`,
same ε/2-and-triangle pattern in `sum_is_cauchy`, identical lifts
of ring laws through `equivalent_when_sequenceFunction_equal`. A
generic completion functor parameterized by a Rational-valued
seminorm (with triangle and `norm(0) = 0`) could absorb 1500-2000
lines and force the abstraction the textbooks take for granted.
Blocked on item 2 of the 2026-05-16 audit (`(p, primality)`
implicit), so the seminorm parameter can carry its own implicits.

### prime_divisor v1 vs v2 vs v3 — adopt v2 as default for now

v2 (`obtain ⟨…⟩ from …` + anonymous `⟨…⟩` + `cases` on Or) is the
current readability sweet spot (~65 lines, reads like math). v3's
`by_induction using` is a net win but blocked by the type-ascription
leak (item 6 above). Until 6 lands, new strong-induction proofs
should follow v2's style. Once 6 lands, v3 becomes the textbook
form and v2 should migrate.

### Quick reference — directories ranked by math:plumbing ratio

Per-agent rough estimates (lower = more plumbing):

- `Algebra/` ~85% math — already textbook-shaped.
- `Rational/algebra.math`, `Rational/instances.math`,
  `Rational/embedding.math` ~75% math.
- `Natural/bezout.math`, `Natural/euclid.math` ~65% math
  (`claim … by` wins).
- `Natural/` (avg.) ~40% math.
- `Integer/` (avg.) ~35% math — quotient boundary leaks.
- `Rational/` (avg.) ~35% math — short-Quotient.mk gap dominates.
- `Real/` (avg.) ~25% math — ε-N is `Exists.eliminate` nesting.
- `PAdic/` (avg.) ~20% math — same ε-N + `(p, primality)` everywhere.
- `Logic/` ~35% math — appropriate for the foundational layer.

### Proposed first sprint (3 items, all small-to-medium elaborator changes)

1. `match E with eqHyp returning G { | … }` (item 1 above).
2. `by rewrite(L)` / `← L` / `in h` at any goal position (item 2).
3. Flat-nested `let ⟨…⟩ := …` for `∃ ∧ ∃ ∧ …` (item 5).

These are orthogonal and together retire roughly half the plumbing
the audit flagged. Items 3, 4, and the resumed Or/And/Exists
eliminator short-forms (item 4 above + the 2026-05-16 deferred
sibling) are the natural next batch — they unlock the higher-layer
wins (`by ring` v2, the CauchyCompletion functor, PAdic operator
overloads).

## Completed

- **2026-05-17: Auto-prover for calc steps + `by` optional.** `by`
  is now optional on calc steps. When absent, the elaborator runs an
  auto-prover that tries:
  (1) definitional equality → `reflexivity`;
  (2) single-position diff classified as commutativity / associativity
      (forward or reverse) / local-hypothesis match, then wrapped with
      `Equality.congruence` for each App level the diff walker
      descended through (supports both Arg and Fn descent, so a diff
      in the *first* argument of a binary op also closes).
  Commutativity and associativity lemmas are auto-registered at
  declaration time and seeded from `.mathv` deps at module start —
  no convention block needed. Sample reduction: in `Natural.multiply_
  successor_no_by`, six of seven steps drop their `by` clauses; only
  the combined β + assoc-reverse step still needs one. New tests in
  `library/Test/induction_style_test.math`. Files: `parser.cpp`
  (optional `by`), `elaborator.cpp` (shape detection +
  `autoProveCalcStep` + `tryClassifyDiff` +
  `seedAlgebraicRegistryFromEnvironment`).

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

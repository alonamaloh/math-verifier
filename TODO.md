# TODO

Planned work, in rough priority / dependency order. Once an item
lands, delete it from this file — the commit history and the project
state (`README.md`, `CLAUDE.md`) are the record of what was done.

## Library content (in flight)

The math content roadmap. Each item is independently useful; they
chain in roughly the order listed.

- **Real is a field — landed, modulo one analytic sorry.** Bundle
  in `Real/field.math` (`Real.is_field`); 0 ≠ 1 and the inverse-
  existence theorem both proved.
  - Path: classical, via `Logic.excluded_middle` (axiom).
    `Logic/excluded_middle.math` derives double-negation-eliminate,
    ¬∀ → ∃¬, ¬(A → B) → A ∧ ¬B. `Rational/linearity.math` derives
    total order linearity + `not_LessThan_implies_LessOrEqual`.
  - `Real/apartness.math`: `cauchy_apartness_from_zero` extracts
    (K > 0, M) with K ≤ |sequenceFunction(s, m)| for m ≥ M from
    ¬CauchyEquivalent(s, constant_zero). ε/2 + triangle + cancel-
    left.
  - `Rational/reciprocal_function.math`: a total
    `Rational.reciprocal_function : Rational → Rational`. Built by
    Natural-pair recursion at the rep level, lifted via two
    Quotient.lifts (over Integer numerator, then Rational). Respect
    at the Rational level via the standard uniqueness-of-inverse
    trick: from multiplication-multiplies on both reps + the reps
    being mk-equal, derive the reciprocals equal via the calc
    `recip₁ = 1·recip₁ = (mk₂·recip₂)·recip₁ = (mk₁·recip₂)·recip₁
    = recip₂·(mk₁·recip₁) = recip₂·1 = recip₂`. Multiplication law
    `x · reciprocal_function(x) = 1` for non-zero x, via
    Quotient.induct + sign_split + StrictPositiveRational (positive)
    or negate-cancellation calc (negative).
  - `Real/reciprocal.math`: pointwise reciprocal sequence built on
    `Rational.reciprocal_function`. **One `sorry`:**
    `Real.reciprocal_sequence_is_cauchy`. The argument is
    `|1/a − 1/b| = |b − a|/(|a|·|b|) ≤ |b − a|/K²`; combined with
    the underlying sequence being Cauchy at ε·K², the reciprocal
    sequence is Cauchy at ε. ~150 lines of analytic plumbing once
    someone writes the algebraic identity + the bound chain.
  - `Real/field.math`: `Real.zero_not_equal_one` (Quotient.exact at
    ε = 1), `Real.reciprocal_cauchy_sequence_multiplies` (the product
    is identically Rational.one beyond apartnessIndex),
    `Real.reciprocal_exists_for_nonzero`, `Real.is_field`.
- **Real order.** `Real.LessOrEqual` / `Real.LessThan` (via "eventually
  ≥ a positive Rational for some Cauchy representative" or
  "non-negative on every representative beyond N"). Independent of
  the field issue; useful on its own and a prerequisite for any
  monotonicity lemma. Same apartness wrinkle if you want strict <.
- **More generic abelian-group / ring / field lemmas** as the
  Real and PAdic proofs surface them. Foundation in
  `Algebra/{group_lemmas,ring_lemmas}.math` covers
  `inverse_identity`, `inverse_operation`, `cancel_left/right`,
  `zero_multiply`, `multiply_zero`, `multiply_negate_left/right`,
  `negate_multiply_negate`. Add more here as concrete-carrier
  proofs find themselves wanting them.

## Calc auto-prover — smaller open follow-ups

With Phases 1–3 landed (structural hash, `ring` AC-fallback,
lemma-index lookup by spineHash), the residual items are:

- **Polymorphic-lemma indexing.** `registerGenericRewriteLemma`
  currently skips theorems with universe parameters (most of the
  library's Natural/Integer/Rational lemmas are concrete-carrier
  and zero-universe-param, so this covers the common case). To
  index e.g. a generic monoid lemma, the matcher needs to infer
  universe-arg instantiation from the subject's carrier level.
  Straightforward extension once a polymorphic rewrite lemma is
  actually exercised.

- **Subtraction / division normalisation.** When the diff involves
  `subtract(a, b)`, normalise to `add(a, negate(b))` before matching
  so rewrites stated additively also fire on subtraction. Same idea
  for division → multiplication-by-reciprocal, gated on the non-zero
  side condition. Three lines per registered op.

- **Multi-position diff.** When the walker is stuck because both
  function and argument differ at the current App level, recursively
  prove `fn_l = fn_r` and `arg_l = arg_r` separately and stitch with
  two congruences + transitivity. The Phase-2 `ring` fallback
  subsumes most of this for purely additive / multiplicative cases;
  this item is the residual for non-AC heads.

- **β-aware descent (attempted, reverted).** WHNF on cursors during
  descent unfolds `Natural.add` into a raw `Natural_recursor` term,
  which the classifier doesn't recognise as a binary op. Two paths
  forward: (a) teach the classifier about recursor-call shapes;
  (b) add a shallow "one ι-step only" reducer to the kernel that
  fires the constructor case but keeps the surface name. Defer
  until clearly motivated.

- **Local-hyp match through polymorphic binders.** Generic ring
  lemmas hit `combineHypothesis : op(a, b) = identity` as a function
  parameter. The local-hyp scan opens it for the def-eq check, but
  the polymorphic `carrier`/`operation` parameters leak as
  `Internal` FreeVariables in the synthesized proof and the kernel
  rejects it. Same root cause as the deferred "auto-congruence in
  calc steps" item below.

- **Pack loose-bvar / free-var flags into the hash word.** See
  `HASH_USE_VS_LEAN.md` §5. Same construction sites as the structural
  hash; high 8 bits of the 64-bit field; would make `substitute` /
  `openBinder` / `closeBinder` O(1) on closed subtrees. **Trigger:**
  profile a cold-rebuild — pack the bits only if `substitute` /
  `openBinder` show up in the top 5.

## Equality combinator carrier implicit

`Equality.transport_proposition`, `Equality.transitivity`,
`Equality.symmetry`, `Equality.congruence` all take an explicit
`(A : Type)` carrier as their first argument, then `(x : A)` etc.
The carrier is derivable from `x`'s type at every call site.
Library-wide there are ~720 uses (192 + 527); the carrier often
takes its own line. Making it `{A : Type}` implicit would save
~500 lines.

Plan: change signatures in `library/Equality/basics.math`,
bulk-refactor call sites (agent template from the Quotient.* sweep
applies). Estimated ~2 hours.

## Ergonomics — top friction points

From a full-library audit (2026-05-17). Each item is annotated with
the directories that motivate it.

1. **Case-on-expression with retained equation.** ~~The function-wrap
   pattern from `CLAUDE.md` ("`cases` with hypothesis") appears 20+
   times in `Natural/padic_valuation.math`, 8 times in
   `Natural/divide.math` alone, plus heavy use elsewhere.~~ **Fixed:**
   `cases X with <equalityHypothesisName> { | c₁ => … | c₂ => … }`
   binds `<equalityHypothesisName> : X = c_i` in each arm via the
   convoy desugaring. Remaining work: sweep the library to apply
   it to the 50+ function-then-apply sites. (Like the prior
   `rewrite(eq, term)` sweep, mechanical and per-file.)

2. **`rewrite` only fires inside `calc` steps.** ~~Outside `calc`,
   users fall back to the 6-arg
   `Equality.transport_proposition(T, motive, x, y, eq, term)`
   form.~~ **Partial fix landed:** the 2-arg `rewrite(eq, term)`
   term-level form desugars to `Equality.transport_proposition(...)`
   automatically, recovering the motive from `term`'s inferred type.
   Covers the witness-transport sites (40+ in `Natural/divide.math`
   etc.). Still missing: a reverse-direction form (`← L`) and a
   "rewrite a hypothesis in place" form for `let` / `claim` bindings.

3. **Short `Quotient.mk` blocked under `+`, `*`, `=`, `≤`.**
   Documented in CLAUDE.md; in practice bloats `Integer/ring.math` by
   ~30% and shows up at `Rational/triangle.math:282-294`,
   `Rational/positive.math:142-157`,
   `Rational/order_arithmetic.math:191-206`. Remedy: when an operand
   of a registered operator has head `Integer` / `Rational` / `Real`
   / `PAdic`, propagate that head as the expected type for an
   unresolved `Quotient.mk` on the other side.

4. **`Or.eliminate` / `Exists.eliminate` / `And.eliminate` re-type
   the motive that the elaborator already knows from context.**
   Pyramids of these forms dominate `Natural/prime_split.math` (200-
   line `Or → Exists → And` staircase),
   `Integer/absolute_value_multiplicative.math:151-237` (87 lines of
   four-way sign dispatch), and the Cauchy-equivalence transitivity
   in `Real/basics.math:160-298` (139 lines, mostly ∃-unpacking).
   Partial fix landed: `Or.eliminate(hL, hR, disj)`,
   `And.eliminate(h, conj)`, `Exists.eliminate(h, ex)` short forms
   recover A, B, P, and the goal-Proposition from the scrutinee's
   type and the call-site expected type. Remaining ergonomic win:
   `dispatch on X { case Or.introduceLeft(p): … }` /
   `case ⟨w, hw⟩: …` syntax that scrutinizes the eliminator targets
   inline, eliding the outer `… .eliminate` head.

5. **`obtain ⟨a, b, c⟩ from …` cannot flat-destructure nested
   existentials and conjunctions.** `Natural/division.math:119-179`
   is 60 lines whose math is `let ⟨q, r, eq, bound⟩ := w;
   ⟨succ(q), r, …, …⟩`. The current pattern needs three nested
   `Exists.eliminate` and an `And.eliminate`. Remedy: allow
   `let ⟨a, b, c, d⟩ := h` for `h : ∃ a. ∃ b. P ∧ Q`. Likely a small
   extension of the existing single-level destructure.

6. **`by_induction … using` (prime_divisor v3 style) needs the
   return-type ascription stripped.** Its last 2 lines remain CIC
   plumbing in an otherwise textbook proof. Until that's fixed, new
   strong-induction proofs should follow v2's style.

7. **`by bridge` for pattern-match definitions on quotient reps.**
   Every binary-op respect proof in `Real/` and `PAdic/` spends ~30
   lines converting `sequenceFunction(add(rep1, rep2), m)` into
   `sequenceFunction(rep1, m) + sequenceFunction(rep2, m)` via manual
   `cases` + `reflexivity`. Remedy: a tactic that exposes a
   pattern-match definition's β-reduction as a one-step calc rewrite
   when the matched argument is structurally a constructor.

8. **Strict `<` doesn't transport cleanly.** `LessThan` is `And(≤,
   Not(_=_))`, so every transport along `<` manually destructures
   and rebuilds. See `Rational/order_arithmetic.math:336-356,
   421-434`. Remedy: either make `<` a single-constructor record
   with first-class destructure, or add a
   `by strict_mono(weak_lemma, neq_lemma)` tactic that auto-
   assembles `And.introduction`.

Proposed first sprint of three orthogonal items: **1, 2, 5**. They
retire roughly half the plumbing the audit flagged.

## `Algebra/CauchyCompletion`

`Real/*.math` (~2600 lines) and `PAdic/*.math` (~5300 lines) are
~80% parallel: same Cauchy / bounded definitions, same equivalence
relation, same Step-1 / Step-2 anchor split in `cauchy_bounded.math`,
same ε/2-and-triangle pattern in `sum_is_cauchy`, identical lifts
of ring laws through `equivalent_when_sequenceFunction_equal`. A
generic completion functor parameterized by a Rational-valued
seminorm (with triangle inequality and `norm(0) = 0`) could absorb
1500–2000 lines and force the abstraction textbooks take for
granted.

Blocked on PAdic's `(p, primality)` becoming implicit so the
seminorm parameter can carry its own implicits.

## `by ring` v2 — distributivity

The current `ring` tactic handles pure-sum or pure-product
rearrangement only. Distributivity (`a*(b+c) = a*b + a*c`) requires
polynomial normalization. This is a 1–2 day project once Phase 3 of
the auto-prover lands, since the same canonical-form infrastructure
applies. Best deferred until enough algebra content (Real field,
Rational triangle inequality, the CauchyCompletion above) drives the
design against real use cases.

## Parallel verification

Optimistic per-theorem parallelism with a thread pool: register
signatures eagerly, parallelize body verification, collect all
errors at the end. Defer until the operator-overloading and
implicit-args changes settle — parallelizing over a fast-changing
elaborator means doing the work twice. Subtleties: per-worker
universe-meta naming; thread-safe kernel caches; deterministic
error-ordering; slow theorems set the floor (consider splitting
long proofs into lemmas).

## Deferred — auto-congruence in calc steps

Goal: let the user write `by eq` for any calc step whose two sides
differ only by a function applied to both endpoints of `eq` — saving
the explicit `congruenceOf(function (z) => …, eq)` wrap at every
site.

Prototyped (`tryAutoCongruenceInCalc` in elaborator.cpp). The
structure works — extract the proof's `a = b` and the goal's
`LHS = RHS`, find the unique structural occurrence of `a` in `LHS`,
build `Equality.congruence(λz. LHS[a→z], a, b, eq)` — but
synthesizing terms that mix opened-form FreeVariables with closed-
form BoundVariables yields a malformed kernel term (see the diagnosis
in the Exists/And/Or.eliminate short forms, which had the same root
cause: `expectedType` from the call site is in CLOSED form while
sub-types pulled out of `inferTypeInLocalContext` are in OPENED
form; closing or lifting one to match the other resolves it).

Fix path: open `proofKernel` first via `openOverLocalBinders` and
work entirely in opened forms (matching the other Quotient.*
desugarings). Reverted to keep `main` clean; resume when there's
time to debug the index plumbing.


## Mixed-relation `calc` chains

Mathematicians write things like `calc p ≤ p = m` to chain an
inequality with an equality. Our current `calc` is monomorphic on
`=`. Generalising is a real but bounded design problem; deferring
until a motivating example puts pressure on it (the structured-proof
work absorbs the small `claim p ≤ p` / `claim p ≤ m` chains for now
via Step 5's transport bridge).

Composition rules to implement when the time comes:

| Proving | Allowed in the chain                  |
|---------|---------------------------------------|
| `=`     | `=` only                              |
| `≤`     | `≤` and `=`                           |
| `<`     | `<`, `≤`, and `=`                     |
| `≥`     | `≥` and `=`                           |
| `>`     | `>`, `≥`, and `=`                     |

(Strict inequality wins over non-strict, like in math.) Each step's
auto-prover stays the same; the top-level fold picks the right
composition lemma per relation pair. Likely needs new infrastructure
for "the strongest relation that bounds this chain so far" tracking.

## Opportunistic — smaller items

- **`Quotient.lift_two`.** Sketched in `Logic/quotient.math` but
  currently rejected by the elaborator with a universe-argument
  mismatch through the nested polymorphic lifts. Manual two-step
  lifts (Integer.add pattern) work fine. Revisit when the universe-
  handling code in the elaborator is more robust.
- **Multi-pattern fix — DONE.** Inner constructor patterns now emit
  a recursor chain whose motives abstract the destructured position +
  every later position binder, so dependent equality hypotheses refine
  under the destructure. The `_after_first…` helper chains in Integer/
  Rational/PAdic addition/multiplication/negation/basics/cancellation
  collapsed into single theorems. v1 limitation: inner inductives must
  be single-constructor, non-indexed, non-recursive (parameterised
  OK). Multi-constructor inner positions would need cross-row coverage
  analysis.
- **PAdic `(p, primality)` → implicit args.** Mechanical migration;
  blocks `operator (+) on (PAdic, PAdic)` and the
  CauchyCompletion abstraction. The implicit-args machinery already
  exists.
- **`operator (+) on (PAdic, PAdic)`** etc. — unblocked by the
  above.
- **Per-block `open NAMESPACE`** for terser long names like
  `Rational.padic_absolute_value`. Lower priority; the long names
  are searchable.

## Index of relevant design decisions

These are load-bearing choices that show up everywhere; they're
documented here so future work doesn't accidentally relitigate them.
The fuller explanation lives in `README.md` "Design principles."

- **Coercions: explicit only, never implicit.** Cascaded explicit
  casts are unbearable, but visible casts at one syntactic site
  (`(x : T)`) localize the type change. Mathlib's
  `push_cast` / `norm_cast` are evidence that implicit coercion is
  the single biggest source of "my proof should work but doesn't"
  pain in formal math.
- **Embedding paths are canonical, not searched.** If two paths
  ever exist from source to target, reject the cast at elaboration
  time.
- **Mathematician-friendly identifiers.** No sigil-marked or
  ALL_CAPS keywords; the math vocabulary belongs to the user.
  Tactic-block keywords are contextual where possible.
- **The trusted base is the kernel.** All elaborator features
  (auto-prover, tactics, sugar) emit explicit kernel terms that the
  kernel rechecks.

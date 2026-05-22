# TODO

Planned work, in rough priority / dependency order. Once an item
lands, delete it from this file — the commit history and the project
state (`README.md`, `CLAUDE.md`) are the record of what was done.

## Library content (in flight)

The math content roadmap. Each item is independently useful; they
chain in roughly the order listed.

- **Real is a field — fully proved.** `Real.is_field` in
  `Real/field.math`. No sorry anywhere in the dependency chain.
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
    Quotient.lifts. Respect via uniqueness-of-inverse calc.
    Multiplication law `x · reciprocal_function(x) = 1` for nonzero
    x via Quotient.induct + sign_split.
  - `Real/reciprocal.math`: the pointwise reciprocal sequence built
    on `Rational.reciprocal_function`, plus the analytic IsCauchy
    proof. Helpers proved locally:
    `Rational.reciprocal_function_subtract_identity` (the algebraic
    identity `1/a - 1/b = (b - a) · (1/a · 1/b)`),
    `Rational.LessThan.multiply_cancel_right` (strict cancellation,
    via excluded_middle on `x = y` + LessOrEqual.linear on the other
    branch). The IsCauchy proof: identity → multiply by s(m)·s(n)
    → absolute value gives `|ra - rb| · |s(m)| · |s(n)| = |s(n)
    - s(m)|`; chain `K·K ≤ |s(m)|·|s(n)|` (two
    multiply_by_nonneg_right steps) with the Cauchy bound at
    ε·K·K, then strict-cancel K·K.
  - `Real/field.math`: `Real.zero_not_equal_one` (Quotient.exact at
    ε = 1), `Real.reciprocal_cauchy_sequence_multiplies` (the product
    is identically Rational.one beyond apartnessIndex),
    `Real.reciprocal_exists_for_nonzero`, `Real.is_field`.
- **Real order.** `Real.LessOrEqual` / `Real.LessThan` (via "eventually
  ≥ a positive Rational for some Cauchy representative" or
  "non-negative on every representative beyond N"). Independent of
  the field issue; useful on its own and a prerequisite for any
  monotonicity lemma. Same apartness wrinkle if you want strict <.

- **Real completeness (sup property).** `Real.supremum_exists` in
  `Real/supremum.math` — every nonempty subset of Real that's
  bounded above has a least upper bound. Stub committed (586c028)
  with vocabulary in place; body is `sorry`.
  - Set vocabulary (`Set.basics`): `Set(T)`, `Set.member`,
    `Set.subset`, `Set.IsNonempty`, plus `∈` / `⊆` operators with
    wildcard dispatch.
  - Real bounds: `Real.IsUpperBound`, `Real.IsBoundedAbove`,
    `Real.IsSupremum`.
  - Plan: bisection on rational midpoints, classical (excluded
    middle) at each step. Cauchy sequence of `aₙ : Rational`
    converges to the sup. Sub-lemmas needed: a Rational below any
    given Real (extract from any Cauchy rep), Real-Cauchy-of-
    monotone-bounded → Real limit, limit-of-aₙ-is-upper-bound,
    limit-is-least-upper-bound. ~300-400 lines.
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

## Rational `/` operator via implicit-prop-arg discharge

Goal: an honest `/` operator on `(Integer, Natural) → Rational` with
the *actual* denominator (not the denominator-minus-one of the rep
encoding), so call sites read as math:

    Rational.halve := (1 : Integer) / 2
    Rational.zero  := (0 : Integer) / 1
    -- with d : Natural, h : d ≠ 0 in scope:
    n / d

Underlying function and operator registration:

    definition Rational.divide
            : (n : Integer) → (d : Natural) → d ≠ 0 → Rational
      | n, zero,         h => False.eliminate(Rational,
                                  h(reflexivity(Natural, zero)))
      | n, successor(k), _ => Quotient.mk(
                                  RationalRepresentative.make(n, k))

    definition Rational./ (n : Integer) (d : Natural) {h : d ≠ 0}
            : Rational := Rational.divide(n, d, h)
    operator (/) on (Integer, Natural) := Rational./

Missing language piece. The existing implicit-args machinery fills
implicits that are *uniquely determined by another argument's type*
(e.g. `{T : Type}` from `(x : T)`, or `{primality}` from `x :
PAdic(p, primality)` once the PAdic migration lands). The `{h : d ≠
0}` here isn't in any other argument's type — it has to be *proved*.
New infrastructure: when the elaborator hits an unfilled implicit
propositional argument of type P, run a discharge protocol —

  1. If P is `n ≠ 0` (or `Not(n = 0)`) and `n` head-WHNFs to
     `successor(_)`, fill with `Natural.successor_not_zero(_)`.
     Handles every literal denominator.
  2. Otherwise scan local hypotheses for a term of type P. Handles
     `d ≠ 0` already in scope.
  3. Otherwise route to the existing `by` auto-prover
     (`CHECK_REDUNDANT_BY=1` lemma-index path) for a library-lemma
     sweep.
  4. Otherwise fail with a clear "pass `Rational.divide(n, d, proof)`
     explicitly" message.

Steps 2 and 3 reuse machinery the `by` desugaring already has. Step 1
is a few lines of recognition plus a one-liner proof construction. The
larger change is the routing — detecting an unfilled implicit prop
arg in the elaborator and threading it into the discharger.

Risks:
  - Nondeterminism if multiple local hypotheses match. First-match-
    wins; explicit pass overrides.
  - Cost on every implicit-prop hole. Need a fast negative path when
    nothing matches.

Shared payoff: any future operator/function with a side-condition
implicit that isn't embedded in another arg's type gets covered by
the same machinery — generalizes beyond `/`.

Migration scope after landing: the literal-rational construction
sites (`Rational.zero`, `Rational.one`, `Rational.halve`, and ~20
others surfaced by `grep "Quotient.mk(RationalRepresentative" library/
Rational/`) collapse to one-line definitions reading as math.
Abstract-rep sites inside `Quotient.induct` motives in
`reciprocal_function.math` etc. do *not* migrate — there the rep's
`+1` offset is structurally what the proof manipulates, and `/` would
be misleading. Operator and raw constructor will coexist.

Order of operations:
  1. Discharge protocol in the elaborator (the substantive piece).
  2. `Rational.divide` + operator registration (~30 lines of library
     code).
  3. Sweep the literal-rational construction sites.

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

3. **Short `Quotient.mk` blocked under `+`, `*`, `=`, `≤`.** ~~Bloats
   `Integer/ring.math` by ~30% and shows up across `Rational/`
   files.~~ **Fixed:** binary `+`/`*`/`-`/`=`/`≤`/`<` and unary `-`
   propagate the outer expected type (when it's a Constant head) to
   the LEFT operand, and propagate left's inferred type to the RIGHT
   operand. Removes the 70+ verbose `Quotient.mk(RationalRepresentative,
   RationalEquivalent, X)` sites — sweep landed in 3846040.

4. **`Or.eliminate` / `Exists.eliminate` / `And.eliminate` re-type
   the motive.** ~~Pyramids dominate `Natural/prime_split.math`,
   `Integer/absolute_value_multiplicative.math`, Cauchy-equivalence
   transitivity in `Real/basics.math`.~~ **Fixed:** the existing
   `cases X { | Or.introduceLeft(p) => … | Or.introduceRight(q) =>
   … }` handles `Or` (and other inductives) directly — no new
   syntax needed. Library sweep landed in aa1607a + 85352d4
   retiring all 17 non-`cases` `Or.eliminate` sites. Remaining
   targets if more 4-way / ∃-unpack chains appear: extend the same
   pattern. The `Integer/absolute_value_multiplicative.math` and
   `Real/basics.math` chains noted in the audit are next.

5. **`obtain ⟨a, b, c⟩ from …` cannot flat-destructure nested
   existentials and conjunctions.** ~~`Natural/division.math:119-179`
   is 60 lines whose math is `let ⟨q, r, eq, bound⟩ := w;
   ⟨succ(q), r, …, …⟩`. The current pattern needs three nested
   `Exists.eliminate` and an `And.eliminate`.~~ **Already fixed** —
   `elaborateCasesExpression` right-associates `⟨a, b, c, d⟩` over
   any chain of 2-arg single-constructor inductives (`Exists`,
   `And`, `Sigma`). See division.math:117 (4-element destructure
   across `∃∃∧`). TODO entry was stale.

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

   **Investigated, not landed.** Two routes failed: (a) library-side
   at_make refactor — the kernel does ι-reduce, but `rewrite`'s
   `abstractStructuralOccurrence` matcher does only structural compare
   without reduction so the rewrite target can't be found inside the
   reduced term. (b) Adding WHNF to the matcher — WHNF stops at the
   outer `Rational.subtract` head and doesn't reach inner
   `sequenceFunction(make(...))` calls. Real fix needs either
   deep-β/ι matching (expensive) or `isDefinitionallyEqual`-based
   matching with unique-occurrence detection (open design question).

8. **Strict `<` doesn't transport cleanly.** ~~`LessThan` is `And(≤,
   Not(_=_))`, so every transport along `<` manually destructures
   and rebuilds.~~ **Mostly fixed:** the verbose `And.introduction(
   A, B, x, y)` form was already redundant — the elaborator's
   leading-argument inference fills A, B from the expected type, so
   the 2-arg `And.introduction(x, y)` form works at every site where
   the expected type is an `And`. Library sweep (5cc9900) drops all
   13 verbose sites. New helper `Rational.LessThan.lift` collapses
   the strict-mono pattern (weak monotonicity + injection → strict
   monotonicity) to a 4-arg call.

   Remaining tail: a few sites in `positive.math` etc. that scope-
   precede `LessThan.weaken`/`distinct` still need `And.left`/
   `And.right` explicitly. Reordering `Rational/order_arithmetic.math`
   to define `weaken`/`distinct` earlier would unblock those.

Diff-inference walker + non-calc hook (8dbde1c) was the elaborator
change that unlocked items 1 (sweep) and 2 (the `claim X : T by P`
form). Items 3, 4 are now FIXED. Items 1 and 2 sweeps are mechanical
follow-up.

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

## `ring` / `field` tactics — open follow-ups

Ring v2 (distributivity, AC, 0/1 identity, negation, ±1
cancellation) and the field tactic (`field(h1, h2, …)` with user-
provided nonzero hypotheses, per-monomial reciprocal contraction)
have landed. Remaining items, none urgent:

- **Mod-(2⁶⁴ − 59) value-fingerprint prefilter.** Failure-mode
  variant landed (a parenthetical appended to ring/field error
  messages telling the user whether the identity is plausibly true
  or provably false). The remaining piece is the *prefilter* —
  evaluate the fingerprint *before* the symbolic decision so a
  matching fingerprint lets the proof emitter skip straight to
  proof construction, and a mismatched fingerprint short-circuits
  to a clear error without running the symbolic path. Worth ~µs per
  call; payoff is mainly in interactive mode. Park until an
  interactive front-end lands.

- **Ring v3 — coefficients as ring elements (DEFERRED until binary
  literals).** Ring v2 only handles canonical coefficients in
  `{-1, +1}`. The clean design for v3 is:
    * The polynomial is `map<signature, coefficient-expression>` —
      coefficients become kernel terms (`<C>.add`, `<C>.multiply`,
      literal-coercion chains) rather than `int`. Naked atoms get
      implicit coefficient `<C>.one`.
    * Normalisation distributes first, then splits each product into
      `(closed-prefix coefficient × free-variable atom suffix)`.
      Closed pieces (literal chains, `one`/`zero`, sums of
      coefficients) land in the coefficient slot; pieces containing
      a free variable from the goal context become atoms.
    * Combining same-signature monomials: one calc step using
      `distributivity_right` backwards — `c · m + d · m = (c + d) · m`.
      *O(1) regardless of literal size, vs. v2's O(n) for the
      `(1 + 1 + … + 1)` plan.*
    * Coefficient equality decided by kernel def-eq. The kernel
      already reduces `successor^4999(zero) + successor(zero) =
      successor^5000(zero)` via the `Natural.add` recursor.

  **Why this is deferred:** the kernel's def-eq on successor-chain
  literals is *O(N²)* (measured: `4999 + 1 = 5000` by reflexivity
  takes ~5.5s; `2000 + 1 = 2001` takes ~400ms). So v3 as designed
  would inherit unusable cost for any non-tiny literal. The
  prerequisite is a binary literal representation:
    * Add a `BinaryNat` inductive (or kernel-primitive) with
      log-depth arithmetic.
    * Make numeric literals desugar to `BinaryNat` (or a coercion to
      the user's carrier via `BinaryNat`).
    * Prove correspondence with the existing `Natural`.
  Once binary literals land, v3 becomes ~600-1000 lines and the
  cost is polynomial in literal length.

  In the meantime: v2's coefficient guard fires with a clear error,
  and the fingerprint diagnostic correctly tells the user "true
  identity, tactic limitation" so they're not misled.

- **Cross-pair cancellation in field.** Field currently does only
  per-monomial reciprocal cancellation. If a like-term collision
  arises after distribution (two monomials with the same
  signature, opposite sign, where one factor differs by a
  reciprocal pair), they don't get combined. Extend by running
  ring v2's like-term cancellation pass after the reciprocal
  contraction.

- **`negate_zero` for the empty-polynomial branch of
  `proveNegateMerge`.** Needs a `<carrier>.negate_zero` axiom no
  carrier currently provides; trivial library addition unlocks it.

- **Subtract via δ.** Works today because `Rational.subtract`
  unfolds to `add(_, negate(_))` under δ. If a future carrier
  defines `subtract` as a primitive (not via the unfolding shape),
  the bridge in `proveEqualsCanonical_impl` for `subtract` breaks.
  Worth a regression test once any such carrier appears.

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


## Mixed-relation `calc` chains — DONE

Done in two commits: `elaborator: calc supports mixed =/≤ chains`
(Phase 1) and `elaborator: calc supports <, ≥, > with strictness
and direction` (Phase 2). Calc now accepts all five relations as
step separators with the composition rules from the original table:

| Proving | Allowed in the chain                  |
|---------|---------------------------------------|
| `=`     | `=` only                              |
| `≤`     | `≤` and `=`                           |
| `<`     | `<`, `≤`, and `=`                     |
| `≥`     | `≥` and `=`                           |
| `>`     | `>`, `≥`, and `=`                     |

Strict inequalities escalate the whole chain. Direction is detected
from the steps; mixing forward (`<`/`≤`) with backward (`>`/`≥`)
is rejected with a clear error (`=` is allowed in either direction).
Backward chains are normalised by reversing the endpoint + step
arrays and flipping `=` step proofs via `Equality.symmetry`.

Composition lemmas are looked up from the operator registry:
`<T>.LessOrEqual` (its `.transitive` and `.reflexive`) for `≤`, and
`<T>.LessThan` (its `.transitive_left`, `.transitive_right`,
`.weaken`) for `<`. Natural's bare `LessOrEqual` inductive is
handled as a special case (its `.transitive` takes proofs swapped).
`=` steps get upgraded to `≤` on the fly via
`Equality.transport_proposition` with motive `λz. a ≤ z` whenever
the chain isn't all-`=`. `≥`/`>` are also surfaced as expression-
level operators (a ≥ b desugars to b ≤ a using the same registry
entry as ≤), so `(h : a ≥ b)` works in theorem types.

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
- **PAdic `(p, primality)` → implicit args.** NOT mechanical after
  all. Two blockers found during a sweep attempt:
    (1) **`Rational.padic_*` and `Rational.sequence.*` callees take
        Rational/sequence args that don't constrain p**, so dropping
        the explicit `(p, primality, …)` prefix at those call sites
        leaves the implicit-args inference with nothing to drive p
        from. `Rational.padic_absolute_value(q : Rational) : Rational`
        is the canonical example — q's type has no p. Need either:
        keep explicit p at those sites, or extend inference to use
        the surrounding type-position context (works less often than
        you'd hope: many sites are in calc steps / let-bindings where
        the expected type is also a plain `Rational`).
    (2) **The `=` desugar elaborates the LHS without an expected
        type**, so even `PAdic.add(x, y) = …` (where x : PAdic(p, _))
        currently fails: inference for `PAdic.add` on the LHS can't
        see the implicit prefix back-propagated from the RHS. A fix
        would either pre-elaborate the RHS first to recover a carrier
        hint, or wire forward inference to use the surrounding
        equality context. The bug pre-dates the recent elaborator
        work; it just didn't matter before because PAdic call sites
        passed `(p, primality)` explicitly.
  Recommended sequence: fix (2) in the elaborator first (general
  win), then migrate the inference-friendly subset (PAdic.{add,
  multiply, negate, subtract} and call sites where p is reachable
  through args), then revisit Rational.padic_* once an expected-type
  back-propagation path exists.
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

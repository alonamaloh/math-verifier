# TODO

Planned work, in rough priority / dependency order. Once an item
lands, delete it from this file — the commit history and the project
state (`README.md`, `CLAUDE.md`) are the record of what was done.

Other living trackers, not duplicated here: `docs/CLEAN_STYLE_PLAN.md`
(clean-style milestone cones), `docs/error_message_inbox.md` and
`docs/error_message_corpus.md` (error-message triage), `docs/freek_100.md`
(famous-theorem checklist), `STRESS_PROBES.md` (diagnostic probes), and
the `PLAN_*.md` design documents.

## Library content

Real is closed under field ops AND the supremum property
(`Real.supremum_exists` in `Real/supremum.math`), so it is a complete
ordered field — fully formalized — with `ComplexNumber` built on top.
Rational is an opaque (Integer numerator, nonzero-Integer denominator)
field-of-fractions quotient.

- **More generic abelian-group / ring / field lemmas** as the
  concrete-carrier proofs surface them. Foundation in
  `Algebra/{group_lemmas,ring_lemmas}.math` covers
  `inverse_identity`, `inverse_operation`, `cancel_left/right`,
  `zero_multiply`, `multiply_zero`, `multiply_negate_left/right`,
  `negate_multiply_negate`. Add more here as concrete-carrier
  proofs find themselves wanting them.

## Trusted base / axioms

- **Demote `Logic.classical_decidable` from axiom to theorem.**
  `Logic.classical_decidable : ∀ P. Decidable P` (in `axioms.math`)
  is redundant — derivable from `Logic.excluded_middle` +
  `Logic.the` (definite description), both already in the trusted
  base. The axiom predates `Logic.the` (description added
  2026-06-12), which is likely why it's still primitive.

  Derivation that works (verified): apply `Logic.the` over the type
  `Decidable(P)` itself with the constantly-`True` predicate.
  Existence of an inhabitant comes from a `claim by cases` split on
  `P` / `Not(P)`, yielding `Decidable.yes` / `Decidable.no`.
  Uniqueness (any two inhabitants of `Decidable(P)` are equal) is by
  case analysis on both: matching yes/yes and no/no cases close by
  reflexivity under definitional proof irrelevance, the cross cases
  are absurd. `Logic.the` then extracts an actual `Decidable(P)`
  value.

  Keep the name `Logic.classical_decidable` so call sites are
  untouched (update references only if the name must change).

  Notes:
    - Behavior-preserving: both the axiom and a `the`-defined term
      are kernel-opaque (no ι-reduction), so `decide` / `cases` on
      the result is equally stuck on a neutral either way. Nothing
      in the elaborator's reduction behavior should change.
    - While editing, fix the axiom's comment. It currently calls the
      decidability axiom "the same content lifted to Type … consistent
      with excluded middle + propositional extensionality." That
      undersells it — lifting `P ∨ ¬P` to a Type-level `Decidable P`
      is *not* derivable from EM + propext alone (the large-elimination
      restriction blocks it); it specifically needs unique choice.
      Reword to "derivable from excluded middle + definite description."
    - After the change, rebuild the full library to confirm nothing
      consuming `classical_decidable` (the `decide` desugaring, the
      bisection in `Real/supremum.math`) breaks.

## Tactics

- **Unify `ring` / `field` / `group` / `monoid` (/ future `semiring`)
  into one `arithmetic_manipulation` tactic.** Instead of the user
  picking the algebraic structure by name, the tactic would inspect the
  operators appearing in the goal and their *registered properties*
  (associativity, commutativity, identity, inverses, distributivity,
  reciprocals), choose the matching canonical form, and normalise both
  sides to compare. The current per-structure tactics already share the
  same skeleton (extract the `=` goal → normalise each side to a
  canonical form via the structure's axioms → chain `L = canon = R`);
  this merges the entry points and the structure detection. Not urgent,
  but the right long-term shape. (Filed 2026-06-19 while adding `group`/
  `monoid`.)

## Elaborator quirks (small open issues)

- **`by_induction … using` (prime_divisor v3 style) needs the
  return-type ascription stripped.** Its last 2 lines remain CIC
  plumbing in an otherwise textbook proof. Until that's fixed, new
  strong-induction proofs should follow v2's style.

- **`by bridge` for pattern-match definitions on quotient reps.**
  Every binary-op respect proof in `Real/` spends ~30 lines
  converting `sequenceFunction(add(rep1, rep2), m)` into
  `sequenceFunction(rep1, m) + sequenceFunction(rep2, m)` via manual
  `cases` + `reflexivity`. Remedy: a tactic that exposes a
  pattern-match definition's β-reduction as a one-step calc rewrite
  when the matched argument is structurally a constructor.

  **Investigated, not landed.** Two routes failed: (a) library-side
  at_make refactor — the kernel does ι-reduce, but `rewrite`'s
  `abstractStructuralOccurrence` matcher does only structural compare
  without reduction, so the rewrite target can't be found inside the
  reduced term. (b) Adding WHNF to the matcher — WHNF stops at the
  outer `Rational.subtract` head and doesn't reach inner
  `sequenceFunction(make(...))` calls. Real fix needs either
  deep-β/ι matching (expensive) or `isDefinitionallyEqual`-based
  matching with unique-occurrence detection (open design question).

- **`well_defined by` obligation bodies get no expected type.** The
  `well_defined by` block of a `by representatives` definition elaborates
  its obligation term bottom-up with no expected type threaded in from the
  generated respect-goal. So the statement-sugar that reads best there is
  unreachable: argument-free `by <lemma>` / a trailing `done` / a final
  stated fact all error "bare claim/done needs an expected type", `take` /
  `suppose` demand explicit annotations, and `↦ by { … }` doesn't parse.
  The only ways to cite the respect lemma cleanly are a full positional
  call (`add_respects(modulus, a, a', b, b, congruentA, reflexive(…))` —
  a raw-CIC leak) or a locally-ascribed block
  (`({ <fact> by reflexive; done by add_respects } : <obligation type>)`,
  which restates the obligation type as verbose machinery). Seen in the
  CIC-leak sweep on `IntegerMod/operations.math` (chose the ascribed block,
  15→1) and `Polynomial/multiplication.math` (left the positional form,
  13→4) — the divergence is purely this missing expected type. Fix: thread
  the generated obligation goal into the `well_defined by` body as its
  expected type, so argument-free `by`/`done`/`take`/`suppose` work there
  directly (and both files collapse to the clean form).

- **`rewrite` outside `calc` — reverse-direction + in-place forms.**
  The 2-arg `rewrite(eq, term)` term-level form covers the
  witness-transport sites. Still missing: a reverse-direction form
  (`← L`) and a "rewrite a hypothesis in place" form for `let` /
  `claim` bindings.

- **`Quotient.mk`-with-ascription in unusual operator positions.**
  Tracking the boundary of where the short form fires. Known
  exemplars: the operand of unary `-`, polymorphic-function args
  without expected type propagation, and
  `Equality.transport_proposition`'s carrier slot. Each one is a
  small inference-driver hole — worth a single consolidated pass
  once a clean unifier extension is on the table.

## Hammer unification — every strategy through the same fact stream

The auto-prover's dispatch in `autoProveClaim` currently has
~8 separate strategies, several of which iterate context but each
over a different slice (local binders only / `lemmaIndex_` only /
implicit kernel reductions only). The split is historical, not
principled. Long-term goal: every strategy that consults context
goes through one unified "fact stream":

- Local binders (hypotheses, `let`/`suppose` values, anonymous
  prior `claim`s in the current block).
- In-module declarations.
- Imported declarations.

Each fact carries a cost (0 for a `by <name>` cite, 1 for a local
binder, 2 for an in-module theorem, 3 for an imported theorem),
and strategies iterate by cost with a budget. Concretely:

- The transitivity bridge currently scans only local binders for
  `H(_, _)` edges; it should also consider relevant library
  lemmas (e.g. `successor_less_or_equal(_, _)`).
- The contradiction strategy currently scans only local binders
  for `(P, ¬P)` pairs; library lemmas like `Natural.zero_not_successor`
  paired with constructive `0 = succ(_)` proofs should count too.
- The transport bridge (local equalities) and the library-rewrite
  bridge (library equalities) should merge into one "context
  equality" strategy. **This is the planned starting point for the
  incremental migration.**

The migration is incremental: validate the abstraction one
strategy at a time, keep the build green throughout. The two
equality bridges are the natural first merge (highest payoff,
existing well-tested machinery on the local side, my recently-
landed library-rewrite bridge has a scope-tracking bug that the
merge would fix).

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

## `ring` / `field` tactics — open follow-ups

Ring v2 (distributivity, AC, 0/1 identity, negation, ±1
cancellation) and the field tactic have landed. Remaining items,
none urgent:

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

- **Logarithmic (binary) representation for Naturals + ring
  coefficients — PERFORMANCE.** `999999999 + 1 = 1000000000` should be
  cheap; today it is catastrophic, for two compounding reasons:
    1. **Kernel Naturals are unary.** The literal `1000000000` is a
       successor chain a billion deep — just *building* the term is
       linear in the value, and def-eq over such chains is O(N²) (see
       the Ring v3 note below: `4999 + 1 = 5000` by reflexivity ≈ 5.5s).
    2. **`ring`'s internal canonical form unit-expands coefficients.**
       `buildCanonicalPolynomial` / `polynomialToSignedMonomials` explode
       a `(signature, coef)` entry into `|coef|` unit monomials, so a
       single coefficient `k` produces a `k`-term sum and an O(k) proof —
       a coefficient of 10⁹ is 10⁹ monomials. There is no upper guard;
       large coefficients simply blow up time and memory.
  The fix is a logarithmic/binary representation on BOTH layers: a
  `BinaryNat` (log-depth arithmetic) underlying numeric literals, and
  `ring` carrying coefficients as binary/`int` values combined via
  `c·m + d·m = (c+d)·m` (one `distributivity_right` step, O(1) in the
  coefficient) instead of unit expansion. This is the same
  binary-literal prerequisite and the same v3 coefficient redesign the
  next item describes — recorded separately here because the *motivation*
  is performance (a hard cliff on big numbers), not just feature
  completeness. Do them together.

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

## Opportunistic — smaller items

- **`Quotient.lift_two`.** Sketched in `Logic/quotient.math` but
  currently rejected by the elaborator with a universe-argument
  mismatch through the nested polymorphic lifts. Manual two-step
  lifts (Integer.add pattern) work fine. Revisit when the universe-
  handling code in the elaborator is more robust.
- **Per-block `open NAMESPACE`** for terser long names like
  `Rational.reciprocal_function_positive_of_positive`. Lower
  priority; the long names are searchable.

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

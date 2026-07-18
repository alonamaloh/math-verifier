# Plan: cast normalization (leaf-cast normal form)

Follow-on to `PLAN_COERCIONS.md` (the coercion-join mechanism, Tier 1
done). The join *inserts* coercions; this plan is about keeping the inserted
casts in a **canonical form** so that equal expressions stay interchangeable.

## The problem: the join is association-sensitive

`+` is left-associative, so a homogeneous lower-type sub-sum gets evaluated
in the lower type and lifted *as a unit*, while an interleaved grouping lifts
each leaf. With `n : Natural`, `x : Real`:

```
1 + x + n   =  (1 + x) + n   →   ι(1) + x + ι(n)        atoms: { ι(1), x, ι(n) }
1 + n + x   =  (1 + n) + x   →   ι(1 + n) + x           atoms: { ι(1+n), x }
```

`1 + n` is Natural+Natural — homogeneous, no cast — so it commits to Natural
addition and the *whole compound* lifts as `ι(1 + n)`. The two forms are
equal mathematically but present `ring` with different atom sets, so **`ring`
cannot prove `1 + x + n = 1 + n + x`** — a trivial commutative-ring identity.
For a "`ring` first" project this is unacceptable. The blast radius is wider
than `ring`: a lemma stated in one grouping won't **unify** against the
other, so hypothesis matching breaks too.

This is unavoidable *at elaboration*: bottom-up, the inner `1 + n` node
cannot know `x` is coming, so it must commit to Natural. The asymmetric term
is inherent to the principle we are keeping (context-independent types). The
fix therefore belongs at a **later normalization layer**, not in the
type-synthesis rule.

## The invariant: casts live at the leaves

Canonical form = every coercion sits on an atom (variable or literal), never
wrapping a compound. `ι(1 + n)` is *not* normal; `ι(1) + ι(n)` is. Driving
casts to the leaves makes both groupings above converge to
`{ ι(1), ι(n), x }` (and, with numeral squashing, `{ 1, ι(n), x }`). This is
exactly Mathlib's `push_cast` direction.

## Why it must be lemma-driven (the monus guard)

You cannot blanket-distribute a cast through every operation. Natural
subtraction is truncated:

```
ι(3 - 5) = ι(0) = 0     but     ι(3) - ι(5) = -2
```

So `ι(a - b) = ι(a) - ι(b)` is **false** for `Natural → Integer`/`Real`.
Distribution is legal *only* through operations where a homomorphism ("move")
lemma is registered: `+`, `·` everywhere; `-` and negation on
Integer/Rational/Real; **not** `-` on Natural. The set of registered move
lemmas *is* the correctness boundary of the normalizer — this is why
`push_cast`/`norm_cast` are lemma-database tactics, not structural
recursions.

## Two implementation options

Both apply the same registered move/squash lemmas; they differ in *when*.

### Option A — prover-side preprocessing (recommended first)

Fold push-cast into the `ring`/`field` normalizer: before it extracts its
atom set, drive all casts to the leaves using the registered move lemmas.
Dissolves the `1 + x + n` vs `1 + n + x` asymmetry **invisibly** — no tactic
appears in the proof text, which keeps proofs reading like mathematics.
Highest value (covers where almost all ring identities go), strict subset of
"implement the tactics," and the term itself is left untouched.

Limitation: only `ring`/`field` benefit. Manual `calc`/`substitute` and raw
hypothesis matching still see `ι(1+n)`.

### Option B — elaboration-time canonicalization (more thorough, more invasive)

When the join would wrap a compound operand, have the elaborator emit the
*distributed* term directly (`ι(1) + ι(n)` instead of `ι(1 + n)`). Legal
because the user wrote no casts — the elaborator merely *chooses* which of
two equal terms to build; no transport/proof obligation is incurred, it just
constructs leaf-cast form. Fixes the asymmetry for **every** consumer at once
(ring, calc, substitute, matching), not just the prover.

The rewrite is a guarded structural recursion on the built term, gated by the
same move lemmas with the same monus exclusion: push `ι` through a node only
where that node's operation has a registered homomorphism for `ι`; otherwise
leave the cast in place. Costs: slightly larger terms; the elaborator gains a
rewriting step.

**Decision:** do Option A first (cheap, invisible, covers the common case),
then reassess whether B is still needed. If hypothesis-matching breakage
shows up early, B is the cleaner root cure. They share all prerequisites, so
A is never wasted work.

## Coherence-lemma audit (the gate)

State of the library as of this plan. Naming convention is
`<coercion>.<op>_preserves`.

### Good news — the move lemmas the `1+x+n` fix needs already exist

Core algebra is **complete** for all three primitive coercions:

| Coercion            | 0 | 1 | + | · | − | negate |
|---------------------|---|---|---|---|---|--------|
| `Natural.to_integer`  | ✓ | ✓ | ✓ | ✓ | — (monus, correctly absent) | n/a |
| `Integer.to_rational` | ✓ | ✓ | ✓ | ✓ | **gap** | ✓ |
| `Rational.to_real`    | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |

(`Natural.to_integer.add_preserves` Integer/embedding.math:46;
`.multiply_preserves` :63; `Rational.to_real.add_preserves`
Real/addition.math:227; `.multiply_preserves` Real/multiplication.math:471;
`.subtract_preserves` Real/negation.math:127; etc.)

So **Option A for `+`/`·` is buildable now** — the exact asymmetry you raised
is fixable with lemmas already in the library.

### Gaps (needed for completeness / the elim direction)

- **Injectivity (elim):** `Integer.to_rational.injective`,
  `Rational.to_real.injective` — MISSING. Needed for the standalone
  `norm_cast` (reflect a goal down to the source type). Not needed for the
  Option-A ring fix.
- **Order on `Integer.to_rational`** (`≤`, `<`) — MISSING entirely.
  (Natural→Integer has `≤`; Rational→Real has `≤`, `<`, and `<`-reflection
  at Real/embedding_order.math:41/59/110.)
- **Reciprocal / division** — MISSING for every coercion. Blocks `field`
  preprocessing on division-heavy goals. Medium priority.
- **`Integer.to_rational.subtract_preserves`** — MISSING (Integer has honest
  subtraction, so this is a valid unconditional law; add it).

### The squash subtlety — RESOLVED (no issue)

Initial worry: the join emits the **raw chain**
`to_real(to_rational(to_integer(n)))`, but the composite lemmas have
`from_natural` in their names — if `from_natural` were a distinct constant,
the lemmas wouldn't fire on the chain.

Checked: **there is no `from_natural` constant.** It is only a naming
convention. The composite lemmas are stated with the surface ascription
`(a : Rational)` / `(a : Real)` for a Natural `a`
(Rational/embedding.math:113–128), which elaborates through the *same*
coercion registry the join uses — so each is literally about the raw chain
`Integer.to_rational(Natural.to_integer(a))`. The join emits exactly that
term, so the composite move lemmas fire directly. **No squash lemmas, no
named-composite emission needed.** Milestone 1 below is therefore moot and
struck.

## Unified target (decided: full unification, Option B)

The numeric tower is currently known to **four overlapping subsystems**: the
coercion registry + join (elaboration), the `castPushToLeaves` prover-side
pre-pass, `ring`'s internal `embeddingChain` + coerced-literal recognition
(ring.cpp:2592–2709), and the scalar operators
(`from_integer_multiply`/`multiply_by_integer`). The target collapses these
to one pipeline:

- **Join inserts** coercions at mixed operands (done).
- **Elaboration normalizes** to cast-normal form (casts at the leaves) by
  calling the `castPushToLeaves` engine at insertion time — keeping only its
  `.term` (this is the Option-B switch the seam was built for). Every
  consumer — `ring`, `field`, `calc`, `substitute`, hypothesis matching —
  then sees one canonical form.
- **`ring` keeps** only its coerced-literal recognition (`ι(k)` → coefficient
  `k`); the prover-side pre-pass is retired (terms arrive normal).
- **Scalar operators deleted**, with `ring`'s now-dead scalar handling.

### Phase 0 findings (instrumented dispatch + ring inventory)

- **The scalar operators are already dead code.** `(2 : Integer) * x`,
  `x * (2 : Integer)`, `x * n`, and `x * (n·m)` (Real×Natural) **all fire
  the join** (`combineOperands`, which runs before the registry lookup) and
  coerce to Real + `Real.multiply`. The `(*) on (Real, Integer)` operators
  are never reached. So the earlier "scalar wins / dispatch-precedence"
  worry was a misdiagnosis — it was a missing-`multiply_associative` import
  in the test, and a misread goal print. Deleting the scalar operators is
  therefore low-risk, not a re-greening hazard.
- **`ring` already recognizes coerced literals** through the full chain:
  `(2 : Integer)` is `Natural.to_integer(succ²(zero))`, so coerced to Real it
  is the chain over a Natural literal, which `tryParseCarrierEmbeddedNaturalLiteral`
  reads as coefficient 2. That is why `scalar_multiply_test` passes even with
  the scalar operators already shadowed.
- **Net:** the real behavioral change is moving compound-cast pushing
  (`ι(n+m)` for *variables*) from ring-time to elaboration-time; the scalar
  deletions are cleanup of already-unreachable code.

### Phases

1. ✅ **Elaboration-time normalization** (commit 304d856) — `castPushToLeaves(...).term`
   after the join's `applyCoercionChain` in `desugarArithmeticOperator` and
   the `=` desugar; ring pre-pass retired. Library + tests green on first
   build (no red period — lemma statements and uses normalize identically).
2. ✅ **Scalar operators + ring's scalar machinery deleted** (commits
   49b511d, 492eefd) — library defs/operators gone; ring's
   `tryParseScalarMultiplyOperator`, `buildCoercedScalarForCarrier`, the
   context name-fields, and the scalar branches in `evalRingMod` /
   `normaliseToRingPolynomial` / `proveEqualsCanonical` removed (−188 lines).
   `ring` keeps only its coerced-literal recognition.
3. ✅ **Re-green** — trivial, as predicted; nothing depended on the shadowed
   scalar path.
4. **Library cast sweep** — delete the now-redundant explicit casts across
   the analysis cone (the payoff). IN PROGRESS — reframed by the B5
   tier3-cast measurement (2026-07-17), see "Tier3-cast absorption
   phase" below.

## Tier3-cast absorption phase (2026-07-17, owner-approved)

B5 classified 408 hinted sites as tier3-cast (largest absorbable
bucket). Clustering: ~110 sites are the analysis cone's
division/reciprocal dances (Real.exponential 32, ℂ exponential/trig
~64); the number-theory cone (GaussianInteger/IntegerMod, `divides`
congruences, `Integer.sign_split`) is a different mechanism family,
deferred.

**Root cause found (6f46f407):** rewriting under `/` is structurally
impossible by transport — the divide proof argument's TYPE mentions
the denominator, so any motive abstracting the denominator is
ill-typed. Every analysis file worked around it with
multiply-through-and-cancel dances. Fix was library-level:
`Real.reciprocal_proof_irrelevant`, `Real.divide_proof_irrelevant`,
`Real.reciprocal_congruence`, `Real.divide_denominator_congruence`
(+ ℚ twin), all automatic. A by-less calc step now rewrites a
denominator (congruence cited goal-driven, `b = c` premise from the
context equation), and the field seat finishes reciprocal-of-product
splits with in-term nonzero proofs. Validated: the four reciprocal
dances in Real/exponential.math collapsed to two-line natural
spellings (−58 lines).

**Second milestone (e214c10e):** `divide_cross_multiply` at ℝ/ℚ (the
canonical a/b = c/d ⇐ a·d = c·b comparison), two elaborator fixes
(the context-equality bridge typechecks its transport — the ill-typed
divide-denominator motive used to escape as a hard kernel error; the
5b premise scan is direction-blind for equality premises via
Equality.symmetry), and the binomial_reciprocal_split dance in
exponential_addition.math collapsed (−33). Corpus grep shows no other
multiply-through dances outside triangular_series (the ℂ exponential
reciprocalOne is already compact).

Remaining in this phase:
- ~~`field` sum-base denominator limitation~~ **FIXED (ff47a2f6):**
  the cofactor synthesis's lead extraction now takes the graded-lex
  maximal monomial of `b·r − 1` instead of bailing on multi-monomial
  relations, so sum bases divide out (standard multivariate division;
  the reduction loop was already general). Partial fractions are a
  one-word `field` proof; triangular_term_telescopes collapsed to the
  5-step natural spelling (−49).
- ~~budget-exhaustion-before-cheap-route~~ **FIXED (23183893):** the
  diff walk now tries cost-gated ring on each interior carrier-typed
  pair before descending (the walk used to descend past ring-provable
  pairs; fingerprint fast-fail keeps misses cheap). AM-GM's inline
  power-congruence fact-hint deleted. The contextEqualityBridge
  79-second pathology is thereby unreached for this class; its
  residual cost on genuinely unclosable goals stays bounded by the
  effort budget as designed.
- (superseded design note, kept for the record) **`field` sum-base
  denominator limitation:**
  `2/(x·(1+x)) = 2/x − 2/(1+x)` is declared FALSE. Diagnosis: the
  clearing routes (cofactor synthesis and monomial contraction,
  ring.cpp ~7403/7822) cancel `bᵢ·rᵢ = 1` only when the base appears
  as whole monomial FACTORS — a base containing a SUM (`1+x`) is
  distributed across monomials by the polynomial expansion, so the
  pairing is unrecoverable at the atom level (atomizing the sum
  instead loses the `B = 1+x` relation partial fractions need). The
  correct fix is standard multivariate reduction modulo the relations
  `bᵢ·rᵢ − 1`: with base polynomial b and lead term ℓ(b), rewrite
  `ℓ(b)·rᵢ → rᵢ·(ℓ(b) − b) + 1` to a fixpoint (degree in ℓ's atom
  strictly drops), then compare; the contraction-proof builder must
  emit one multiplies-fact + ring step per reduction. Blocks the
  triangular_series telescope, whose natural 8-line spelling is
  otherwise ready (probe scratchpad/tri_probe5.math — cross-multiply
  and denominator-congruence steps already close by-less).
- the budget-exhaustion-before-cheap-route failures, seen twice
  (AM-GM :144 power congruence; the by-less cross fact at 181k
  kernel-steps) — the cost-gated-ring backlog item, elaborator-side;
- ~~ℂ coordinate-evaluation rewrite family~~ **MECHANISM FIXED
  (1608ba8f):** ground (zero-binder) facts now register in the
  rewrite index, so `realPart(i) = 0`-style rewrites close by-less at
  diff positions. Guard: entries are never keyed by a numeral pattern
  (hot-bucket flooding regressed series.math's budget); the interior
  diff-ring try is size-capped at 48 nodes. Remaining: the file
  SWEEP of now-redundant hints (exponential_imaginary + trig files,
  ~70 sites);
- reassess the number-theory `divides` family separately.

The pipeline is now unified: **join inserts → elaboration normalizes to
leaf-cast form → ring reads coerced literals as coefficients.** The four
overlapping subsystems are one.

## Implementation status

**The defensive seam is in place.** The reusable core is
`Elaborator::castPushToLeaves(term, localBinders) -> CastNormalForm
{term, proof}` (`src/elaborator/cast_normal.cpp`): it drives coercions to
the leaves and returns both the rewritten term and a proof
`original = term` (null when nothing moved). Option A consumes both fields;
a future Option B would consume only `.term` — so switching is a change of
*caller*, not of the engine. Move lemmas are found by the
`<coercion>.<op>_preserves` naming convention, confined to one lookup; the
monus guard is automatic (no `Natural.to_integer.subtract_preserves` exists,
so Natural `-` is never distributed).

Done:
1. ~~Squash subtlety~~ — RESOLVED (no `from_natural` constant; struck).
2. **`Integer.to_rational.subtract_preserves`** — added
   (Rational/embedding.math), assembled from add + negate.
3. **Option A wired into `ring`** — a guarded pre-pass at the top of
   `elaborateRing` (before the scheme/prefix guard) pushes both endpoints,
   proves the leaf-cast goal recursively (idempotent), and bridges with
   transitivity. No-op when no coercion-over-op is present, so the whole
   existing library re-verifies untouched. Validated:
   `library/Test/cast_ring_test.math` — `1 + x + n = 1 + n + x`, a Natural
   sum compound, a two-hop mixed Rational+Natural distribution, and Integer
   subtraction. Numeral squashing (`ι(1)=1`) turned out **unnecessary** for
   these: identical literal casts appear on both sides, so `ring` matches
   them as equal atoms without collapsing to `Real.one`.

Open / follow-ups:
4. **Multiplication × scalar operators** (discovered). `x * n` for
   `x : Real, n : Natural` does **not** coerce `n` to Real and use
   `Real.multiply`; it hits the pre-existing scalar operator
   `(*) on (Real, Integer)` (`Real/multiplication.math:442-443`), giving
   `Real.multiply_by_integer(x, ι_Integer(n))`. So a multiplicative compound
   like `x * (n * m)` is not in a form `ring` recognizes. This is a
   **dispatch-precedence question independent of cast normalization**:
   should the coercion-join preempt a registered cross-type (scalar)
   operator, or should `ring` learn to treat `multiply_by_integer` as a ring
   op? Decide before extending Option A to `field`/products.
5. **`field` integration** — same pre-pass; needs the reciprocal/division
   move lemmas (currently MISSING for every coercion) and item 4 resolved.
6. **Reassess Option B** (elaboration-time canonicalization) once A is
   proven out on the additive cases in the library sweep.
7. **Standalone `norm_cast` / `push_cast`** (elim/reflection direction) —
   deferred; needs the injectivity and Integer→Rational order gaps filled.

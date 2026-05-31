# PLAN_READABILITY.md — ergonomics & readability program

Status: planning (written 2026-05-31). Audience: a future session (LLM or
human) that will implement these and then rewrite parts of the library to
use them. **Read §1 first** — it is the embodied experience of proving in
this framework, which a fresh session otherwise lacks.

The recent constructions that generated this experience: `IntegerMod` →
generic `RingModulo` (ring mod a principal ideal) → `FiniteField`
(F_{p^k}) → `ComplexNumber` (ℂ = ℝ[x]/(x²+1)), plus the polynomial
division → Bézout → irreducibility tower. See the memories
`finite_fields_status` and `complex_numbers_status`.

--------------------------------------------------------------------------
## 1. THE EXPERIENCE OF PROVING IN THIS FRAMEWORK (read this)

### 1.1 The loop, and what it feels like

The inner loop is: write a `.math` file → `make -j 16 library` (warm
sub-second) → read the one error → fix → repeat. It is tight and the
caching is excellent. A file of 10–20 lemmas usually converges in a handful
of iterations; several substantial files (`degree_product`,
`division`, `degree_function`) verified on the first or second real
attempt. So the system is genuinely productive — the friction below is
real but it is a *tax on an already-working process*, not a wall.

The thing that makes it pleasant is that **the surface language lets you
write the mathematical argument, not the CIC derivation**. A proof reads as
"take representatives, kill the leading term, recurse on the excess
degree," because of `by_representatives`, `calc`, `claim … by …`,
`obtain`, `take`/`suppose`, `decide P { yes … | no … }`, and the
statement-level sugar. When a proof is going well, you are thinking about
the math.

The thing that makes it occasionally maddening is that **a handful of
elaborator realities leak through the math abstraction**, and when they do,
the error often does not name the actual cause, so you drop into
guess-and-check. Those leaks are enumerated below. They are few in number
and highly stereotyped — which is exactly why they are worth fixing
centrally.

### 1.2 What works well (do not regress these)

- **Diff-inferred `by` in `calc`**: you supply only the equation; the
  elaborator finds the single-position congruence slot. This removes an
  enormous amount of `congruenceOf(λz. …)` noise. It is the single best
  ergonomic feature.
- **Bundled `Ring` + flattened projections** (`Algebra/ring_bundle.math`):
  threading one `r : Ring` and citing `Ring.add_associative(r, …)` made the
  generic `RingModulo` feasible at all.
- **Short Quotient forms / `by_representatives` / `construction` /
  `cases … refining`**: "WLOG pick a representative" reads as one line.
- **Error messages where they are good**: the `decide` 5-slot dump, and
  `rewrite`'s "left endpoint does not appear; here are the 6
  (term × endpoint) reduction combos I tried, 0 occurrences each" — these
  pointed me straight at the problem. This is the *standard to hold the
  other errors to.*
- **Abstraction payoff**: `Polynomial.quotient_is_field` was written once
  over an abstract field and reused verbatim for both F_{p^k} (F = F_p)
  and ℂ (F = ℝ). The abstraction boundaries are in the right places.

### 1.3 The friction taxonomy (each with the real instance that bit me)

**(F1) defeq-but-not-structural — the #1 time sink.**
`Ring.multiply(Polynomial.ring(r), x, y)` and `Polynomial.multiply(r, x, y)`
are definitionally equal (the bundle projection δ-reduces), but `rewrite`
and the diff-matcher compare *structurally* and fail to see it. Concretely,
in `Polynomial/bezout.math` and `ComplexNumber/embedding_injective.math`
I had `pEqualsModulusQuotient : p = Ring.multiply(Real.polynomial_ring, …)`
from an `obtain`, but `HasDegree_product` produced
`Polynomial.multiply(Real.ring, …)`; `rewrite` reported "left endpoint does
not appear (0 occurrences in all 6 combos)". The fix I used five-plus times:
insert a bridging `claim X : <the form the matcher wants> by <the proof I
have>;` — the kernel accepts the restatement up to defeq, and now the
matcher sees the right shape. **This bridging-claim dance is pure tax: the
terms are equal, the kernel knows it, only the surface matcher does not.**

Same family: a relation that *hides* the operative term behind a definition
(`Ring.CongruentModulo(s, m, x, y)` unfolds to `Ring.divides(s, m, x + −y)`,
but `rewrite` against the difference fails until you restate the hypothesis
in `divides` form), and ambiguous rewrites when the LHS appears twice
(`successor(dy) ≤ successor(dy)` — had to drop to explicit
`Equality.transport_proposition`).

**(F2) verbosity from no operators on parametrized ops.**
Because `Polynomial.multiply` etc. take an explicit ring argument, there is
no `*`, so the page fills with
`Polynomial.coefficientOf(Real.ring, Polynomial.monomial(Real.ring, a, 0), 0)`
repeated dozens of times. This is the readability complaint, and it *also*
blocks `ring` (next item). `let`-abbreviation helps but interacts poorly
with the structural matchers (a `let` you introduced to shorten a term can
make `rewrite` fail to find it).

**(F3) `ring` does not fire on bundled/parametrized carriers.**
`ring` works on `Integer`/`Rational`/`Real` (concrete carrier, registered
`+`/`*`/`-`, nullary `<C>.is_ring`). It cannot help over a `Ring` bundle
(no operator syntax; instance lookup is by nullary name). So I hand-proved
the whole `Algebra/ring_difference.math` (negate-distribute, telescope,
add-distribute, the multiply-split) and the `(cf)² = −1` derivation in
`ComplexNumber/irreducible.math`. That is the single largest pile of
*avoidable* proof in the recent work.

**(F4) cryptic elaborator failures (cost the most, because the error
misdirects).** These are bugs/sharp-edges, not just missing features:
  - *Partial application of a theorem with trailing args, used as a value*,
    fails with "Application: argument type does not match Pi domain;
    expected `Ring.carrier s`, actual `Ring`." It took binary search to
    learn the cure is **eta-expand** (bind all the args). Hit in
    `RingModulo/basics.math` building the `IsEquivalenceRelation` tuple from
    `CongruentModulo.symmetric(s, m)`.
  - *`by_strong_induction` mis-scopes a large motive*: "unbound internal
    variable r". Cure: drop to explicit `Natural.strong_induction(motive,
    step, n)` with the motive spelled out. Hit in `Polynomial/bezout.math`.
  - *`obtain` inside a `Quotient.induct` lambda* can't read its expected
    type through the un-β-reduced motive application: "cases expression
    needs an expected type from context." Cure: factor the at-representative
    body into its own theorem with an explicit `∃` return type (as
    `IntegerMod.invertible_at_representative` does). Hit in
    `Polynomial/quotient_field.math`.
  - *Anonymous tuple `⟨…⟩` in a `Quotient.sound` / existential-witness
    position* "needs an expected type from context." Cure: ascribe
    `(⟨…⟩ : <the prop>)`. Hit in `RingModulo/operations.math`
    (`modulus_is_zero`) and `Polynomial/quotient_field.math`.

**(F5) motive / elimination plumbing.**
  - `by_induction on n` requires `n` to be a **parameter**, not bound under
    a `(n : Natural) →` in the goal; and any hypothesis whose type mentions
    `n` must be manually moved into the conclusion so the motive abstracts
    it. I restructured several theorems (`degree_function`,
    `division_support` single-point) for this.
  - `decide` / `cases` refine only the **goal**, not already-introduced
    hypotheses. So a hypothesis mentioning the scrutinee must be `intro`'d
    *inside* each branch, or you must remember `cases … refining h`. Easy to
    forget; failure is cryptic.

**(F6) standard-library gaps + discoverability.**
Small facts I needed were missing or in surprising places: `≤`/successor
conversions; `le_add_preserves_left/right` lived in
`Natural/padic_valuation.math`; `Integer.IsNonneg.multiply` lived in
`Rational/positive.math`; ℝ's order layer had **no** multiplicative
positivity at all (I built square-nonneg bottom-up Integer→Rational→Real for
ℂ). With long fully-qualified names and no goal-directed search, I `grep`
constantly. This is a real productivity drag and it especially hurts an LLM,
which otherwise *guesses* lemma names.

### 1.4 What this implies for who can work here

- **Humans**: productive, and the prose sugar is the reason proofs stay
  legible. The cost is carrying the (F1)/(F4)/(F5) rules in your head.
- **LLMs**: productive, but (F1)/(F4)/(F5)/(F6) are precisely the things
  that convert "write the math" into "guess against a misdirecting error,"
  which burns iterations. Every fix below converts a multi-iteration failure
  mode into a first-try success. **Raising the first-try rate is the whole
  game for LLM fluency.**

--------------------------------------------------------------------------
## 2. THE IMPROVEMENT PROGRAM

### STATUS (live)

- **E1 (lemma search) — CLI + error-message surfaces DONE, output
  polished.** The engine is factored into `lemma_search.{hpp,cpp}` (a
  shared TU compiled into both the CLI and the elaborator) so one
  implementation drives both deliveries.
  - **Output quality pass (post-review).** A first cut printed raw CIC
    (`Π(a : Natural). … LessOrEqual (a + b) (c + b)` with `@`-marked
    holes and test-fixture pollution). Fixed to the textbook form:
    `Natural.le_add_preserves_left : (a c b : Natural) → a ≤ c → a + b ≤
    c + b   [needs: a ≤ c]`. Four changes: (1) a surface-arrow signature
    formatter (`formatLemmaSignature` — collapses same-type binder
    groups, renders premises as the `→` chain) replaces the `Π`-soup;
    (2) the printer now infixes the bare top-level `LessOrEqual` /
    `LessThan` (Natural's order relations have no `Carrier.` prefix, so
    the suffix heuristic missed them); (3) `[needs: …]` premises are
    demoted from Internal- to User-origin free variables so they read in
    the lemma's own names without the `@` leak marker; (4) `library/Test/`
    fixtures are excluded from CLI results (they flooded e.g. `=` goals).
  - **Surface #1 (error messages) — DONE.** When `autoProveClaim` fails
    (a `done`/`okay`/bare-`claim`, or a non-equality calc step), the
    elaborator appends "search by conclusion shape — candidates" with the
    top 5 lemmas whose conclusion matches the goal, each with its
    signature and `[needs: …]`. Best-effort (try/catch; empty result →
    no text), so it never masks the base error. This is the
    highest-value surface for LLM fluency: the real lemma name arrives
    exactly where a wrong guess would otherwise be made. Regression test
    in `runLemmaSearchTests`.
    - **Unimported lemmas tagged with `(needs import X)`.** The search
      runs over the WHOLE library (a `LibrarySearchIndex` lazily built by
      the verify-with-cache driver — only on a failure, so the happy path
      pays nothing; confirmed full-build time unchanged at ~4.9s). A hit
      already in `environment_` prints untagged; one that is not in scope
      gets a `(needs import <module>)` line. So the suggestions are no
      longer bounded by what you imported — `a + b ≤ c + b` now surfaces
      `Natural.le_add_preserves_left … (needs import
      Polynomial.division_support)` as the top hit. Injected via a
      `std::function<const LibrarySearchIndex*()>` provider through
      `elaborateModule` (nullptr on the test / legacy path → in-scope
      search only).
  `kernel search` subcommand (main.cpp):
  - `--goal "(a c b : Natural) → a + b ≤ c + b"` — conclusion-unifies
    mode (apply?-style). Free variables are written as leading binders;
    the engine peels every lemma's leading Pis as metavariables,
    head-filters by conclusion head, first-order-matches the conclusion
    (with a kernel-defeq fallback so `successor(k)` matches `1+k`), and
    ranks by (proposition obligations, then unbound data parameters,
    then matched-constant specificity). Each hit prints its full
    signature, `file:line`, and `[needs: <unproved hypotheses>; N free
    parameters]`. Acceptance test 1 passes: `le_add_preserves_left` is
    the top hit; acceptance test 2: `Integer.IsNonneg.multiply` is the
    top hit for `Integer.IsNonneg(x * y)`.
  - `--mentions a,b,c` — Coq-`Search` mode (lemmas whose statement
    mentions all named constants), ranked by specificity.
  - Loads all `.mathv` under `--cache-root` (default `build`); builds a
    name→source map for the `file:line` column (grepped lazily per
    shown hit). Unit tests in `runLemmaSearchTests` (in-memory env, no
    build cache needed). The engine is factored as `computeGoalHits`
    (pure) + a print wrapper, so the **next step — surface #1, pushing
    the top 3–5 hits into a failing `by`/`done`/`rewrite` error
    message** — can reuse `computeGoalHits` from the elaborator. That is
    the highest-value surface for LLM fluency and is the remaining E1
    work.
- **A1 — DONE.** Operators `+`/`-`/`*` on `RingModulo` (via re-indexing the
  quotient over a new `CommutativeRing` bundle, which lets `multiply` drop
  its explicit commutativity arg), on the abstract `Ring.carrier`, and on
  `CommutativeRing.carrier`. The implicit-recovery-through-projection works,
  incl. through definition-alias carriers (`FiniteField(p,f)`,
  `ComplexNumber`) via a single-δ-step head unfold in the elaborator.
- **A2 — DONE, for `CommutativeRing.carrier(c)`.** `ring` drives a goal over
  an abstract bundled commutative ring (operation "scheme" = namespace +
  structure prefix; matchers/builders thread the prefix; open-over-binders
  so the index is a free var; close before return). The `ring` law
  dependency is now documented at `RingLawNames`, and the dev-history
  `v1`/`v2` names are retired.
- **B1 — DONE.** `rewrite` locates its endpoint up to definitional
  equality via a bounded `isDefinitionallyEqual`-at-same-arity fallback
  (`abstractDefeqOccurrence`) after the structural combos. Dissolves the
  bridging-`claim` tax (F1); two real bridges deleted as the regression
  proof (`embedding_injective` `pEqualsPolyMultiply`, `bezout`
  `xAsRingAdd`). NB finding #3 below is RESOLVED: the bounded-defeq walker
  beat a hand-written structure-projection normaliser (full WHNF
  over-reduces past the projected field; the kernel's defeq gives a sound
  yes/no, so no custom reducer was needed).
- **B2 — DONE.** `change T;` (active `note goal`) — replace the goal by a
  defeq spelling.
- **#21 (ring cross-pair cancellation) — DONE.** `proveMultiplyMerge`
  routes the p·q expanded products through the shared
  `proveSignedMonomialSumEqualsCanonical` (extracted from the additive
  merge), so `(a+b)(a−b)=a²−b²` and same-sign coef>1 collisions close.
- **C1 — DONE.** `cases`/`by_induction` auto-generalize: a try-then-revert
  wrapper (`elaborateCasesExpression`) reverts scrutinee-dependent in-scope
  hypotheses into the motive (via the existing `refining` telescope) when
  the plain elaboration fails. Zero-regression (existing proofs take the
  no-revert path). Covers plain `cases` and constructor `by_induction`;
  `Natural/cancellation.math` dropped an explicit `refining`. ALSO wired
  for the lemma-based path (`by_strong_induction` / `by_induction …
  using`) via a try-then-revert wrapper that validates the plain result
  with `inferType` (that path defers typechecking to the kernel boundary,
  so the mismatch is a `TypeError`, not an in-elaboration
  `ElaborateError`). C2's cases-side is subsumed by this; C3 (β/WHNF of
  the expected type before an anonymous tuple reads its motive) was
  already present (`elaborateAnonymousTuple` WHNFs).
- **Track D re-audit (2026-05-31).** Re-tested the F4/Track-D failure
  modes against the current elaborator before writing the error
  messages, since A/B/C may have dissolved them:
  - *Partial-application-as-value* (`CongruentModulo.symmetric(s, m)` in
    a tuple slot): **RESOLVED** — now verifies (the defeq check
    eta-expands the partial application). The D bullet is moot; no error
    message needed.
  - *Inline `Equality.symmetry(…)` as a calc `by`* (B4): **RESOLVED** —
    both the bare `by Equality.symmetry(eq)` (diff-inference wraps the
    congruence at the symmetric orientation) and
    `by congruenceOf(f, Equality.symmetry(eq))` verify. B4 and its D
    error-message bullet are moot.
  - *`by_strong_induction` mis-scopes a large motive* (D3 / F4 bullet 2):
    **WAS STILL LIVE → FIXED this session.** Root cause was NOT a motive
    over-abstraction but a representation bug in
    `elaborateByInductionUsingInner`: `inferTypeInLocalContext` returns
    the post-motive remaining type in OPENED form (outer binders as
    Internal free variables), and a sub-term of it (`ihTypeAfterSubject`)
    was embedded as the IH lambda's domain in the returned *closed*-form
    term — leaving any outer binder the motive mentions (e.g. `r`)
    dangling as "unbound internal variable r". Fixed by
    `closeOverLocalBinders` on the inferred type before extraction. Only
    bit when the motive references an outer binder, so the existing
    motive-free `by_strong_induction` tests never caught it. Regression
    tests (6)/(7) added to `Test/by_strong_induction_test.math`. The D
    error-message bullet for this is now moot — the construct works
    directly. **Opportunity:** `Polynomial/bezout.math` can drop its
    explicit `Natural.strong_induction(motive, step, n)` back to
    `by_strong_induction on bound …` (the original cure is no longer
    needed); deferred as a separate proving-ground change.
  - *Anonymous-tuple / `obtain` needs expected type* (remaining F4
    items): not individually re-verified; C3 already records the
    `elaborateAnonymousTuple` WHNF path as present. Low value; left as
    error-message polish if it resurfaces.
- **Findings that revise this plan:**
  1. **A2 does NOT retroactively simplify `ring_difference.math` /
     `RingModulo` respect-lemmas.** Those are stated over a *plain*
     `(s : Ring)` and are deliberately commutativity-free
     (`difference_multiply_split`), so `ring` (a commutative-ring tactic)
     cannot reprove them without strengthening their hypotheses. A2 is
     forward-looking. **Retire** the §4 acceptance item
     "`difference_multiply_split` reproved as `:= ring`."
  2. **`ring`'s `proveMultiplyMerge` cross-pair-cancellation case is
     unimplemented** ("not yet supported") and is *carrier-independent* —
     it blocks `(a+b)*(a+b)`-style expansion for every carrier, including
     the ℂ `i²=−1` / `modulus.math` steps in the §5 acceptance snapshot.
     That snapshot is unreachable until this is fixed (separate from A2).
  3. **B1 needs a *bounded* "structure-projection normalisation," not WHNF.**
     The failing endpoint is `Ring.multiply(Polynomial.ring(r), x, y)` vs the
     term's `Polynomial.multiply(r, x, y)`. Full `weakHeadNormalForm` of the
     endpoint over-reduces *past* `Polynomial.multiply` into its convolution
     body, so it still doesn't match. The right primitive resolves a
     structure projection on a (δ-unfolded) constructor —
     `Ring.<field>(Ring.make(…), args)` ↦ `<field>(args)` — and STOPS, not a
     general WHNF. Reusing `decide`'s `abstractStructuralOccurrenceWithWHNF`
     does not help: it only bridges *same-head* applications. B1 remains TODO.

Four tracks. A and B together are aimed squarely at the user's goal:
"liberate the user from having to know anything about defeq-vs-structural
and motive-plumbing." A is the readability headline; B dissolves (F1); C
dissolves (F5); D dissolves the misdirection in (F4). They are largely
independent and can land in any order, but the recommended sequence is in
§4.

### Track A — Operator overloading for parametrized operations (+ `ring`)

**Goal.** Write `x + y`, `x * y`, `-x`, `x - y` for `Polynomial`,
`RingModulo`, `IntegerMod`, `PAdic`, and for an abstract `Ring`/bundle
carrier — and have `ring`/`field` fire on all of them.

**A1 — make the structure argument implicit & inferable; register
operators.**
- The operator-declaration code at `elaborator.cpp:929
  elaborateOperatorDeclaration` *already* peels leading `{implicit}` Pi
  binders before validating the two operand slots (`declaredImplicitCount`
  loop at ~`:951`). Dispatch keys on the **head Constant** of each operand
  type (`typeHasHeadName`), so `Polynomial`, `RingModulo`, `IntegerMod`, and
  the projection head `Ring.carrier` are all valid LHS/RHS names.
- Therefore the blocker is only that `Polynomial.add(r, …)` /
  `RingModulo.multiply(s, comm, m, …)` / etc. take the ring/structure args
  **explicitly**. Change those operations to take them as `{…}` implicits
  recovered from the operand type:
    - `Polynomial.add {r : Ring} (x y : Polynomial(Ring.carrier(r), Ring.zero(r)))`
      — `r` is solved from `x`'s type by first-order unification of
      `Polynomial(Ring.carrier(?r), Ring.zero(?r))` against `x`'s type.
      (This is the same implicit-from-type-arg machinery already used
      elsewhere; confirm it inverts the `Ring.carrier(?r)` projection —
      it should, by congruence on the projection application.)
    - For `RingModulo.multiply`, the commutativity proof currently rides
      along as an explicit arg; to get a clean binary operator it must
      become implicit too (or be eliminated — see "Field/CommutativeRing
      bundle" below). The cleanest fix is a **`CommutativeRing` bundle** so
      multiply needs no separate commutativity argument.
- Register: `operator (+) on (Polynomial, Polynomial) := Polynomial.add`,
  `operator (+) on (Ring.carrier, Ring.carrier) := Ring.add`, etc.
- **Verify** at `elaborator.cpp` the call-site dispatch path (search around
  `:3789` "operator-dispatched calls") inserts the peeled implicits by
  unifying against the operand types. If it does not yet recover implicits
  for the dispatch function, that is the one new piece of A1.

**A2 — make `ring`/`field` accept parametrized & abstract instances.**
- Current behavior: `ring` v2's derived-lemma path looks up the instance by
  *name* as a **nullary** `<carrierName>.is_ring` (`elaborator.cpp:12732`,
  applied with no args at `:12748`; mirror code for negate/zero lemmas at
  `:13592`). This works for `Integer`/`Rational`/`Real` and **breaks** for
  `Polynomial.is_ring(r)` (parametrized: under-applied) and for
  `Ring.carrier(s)` (no such name).
- Fix: route `ring`'s instance lookup through the **same parametrized /
  local-instance resolution that already exists** for hand-cited structure
  lemmas (`canonicalInstanceRegistry` + the Stage-3/local-instance follow-on
  at `elaborator.cpp:17374`). Concretely: given the goal's carrier head,
  (a) if a parametrized `instance` is registered (e.g. `IntegerMod.is_ring`,
  `Polynomial.is_ring`), instantiate its leading parameter from the
  carrier's own type argument; (b) if the carrier is abstract
  (`Ring.carrier(s)`), use the unique in-scope `s : Ring` and its
  `Ring.is_ring(s)` projection. Feed the resulting fully-applied IsRing term
  where `:12748` currently puts the nullary constant.
- Once A1+A2 land, `ring` proves the bulk of `ring_difference.math`, the
  polynomial coefficient algebra, and the ℂ `(cf)²=−1` step. **This is the
  "(3) gives us (1)" the user asked about — true, but A2 is the part that is
  *not* automatic from operators and must be built.**

**Acceptance tests (add to `library/Test/`):**
- `x + y` / `x * y` / `x - y` elaborate for `p q : Polynomial(integerRing)`
  and for `x y : RingModulo(s, m)` with `s` a variable.
- `theorem _ (s : Ring) (x y z : Ring.carrier(s)) : (x + y) + z = x + (y + z) := ring`
  succeeds (abstract bundle carrier).
- `Algebra/ring_difference.math`'s `difference_multiply_split` reproved as
  `:= ring`.

**Risks.** Implicit-recovery through the `Ring.carrier` projection; operator
parsing precedence already exists (parser.cpp:1514+); main work is
elaborator-side implicit insertion + the A2 instance plumbing.

### Track B — defeq-aware rewriting (dissolve F1)

**Goal.** The user never has to insert a bridging `claim` to make two
definitionally-equal spellings match.

**B1 — `rewrite` locates its endpoint up to controlled definitional
reduction.** Today the subterm search is structural with a fixed menu of
6 (term × endpoint) × (unreduced / WHNF / deep-β) combos (visible in the
error). Extend the search to also try **δ-unfolding of projections/aliases**
(`Ring.add(Polynomial.ring(r), …)` ↦ `Polynomial.add(r, …)`) and
**ζ-unfolding of `let`s** when locating the LHS. This is the precise fix for
the `bezout`/`embedding_injective` bridging-claims. Keep it bounded
(unfold only heads that block a match) so it stays fast.

**B2 — add `change`/`convert` (a.k.a. `show`).** A statement
`change <T'>;` that replaces the current goal/term type by any
*definitionally equal* `T'`, checked once by `isDefinitionallyEqual`. This
gives the user an explicit, one-line escape hatch for the rare residual
mismatch, instead of the ad-hoc `claim X : T' by <proof>` pattern. (We
already have `note goal : T` which *checks* defeq but does not *change* the
working type; `change` is the active version.)

**B3 — diff-inferred `by` congruence also up to defeq.** The calc
diff-matcher already uses `isDefinitionallyEqual` at the leaf compare, but
it walks Application spines structurally and stops when heads differ (e.g.
`Ring.subtract` vs `Ring.add` after δ). Allow it to WHNF/δ both endpoints
when the heads differ before giving up. (This is why I wrote all calc
endpoints in `add/negate` form rather than `subtract` in
`ring_difference.math`.)

**B4 — calc `by` should accept an inline `Equality.symmetry(…)`.**
*(Migrated from the former `PLAN_QUOTIENT_NOISE_REDUCTION.md` findings — hit
repeatedly across the lifted-law proofs and again this session.)*
`congruenceOf(f, Equality.symmetry(…))` with the symmetry written **inline**
does NOT elaborate as a calc `by` step — the step's diff-inference interferes
— though the same term works in an ordinary (non-calc) position. The standing
workaround is to bind the symmetry to a `claim` first, then
`congruenceOf(f, thatClaim)`. The diff-matcher should handle an inline
`Equality.symmetry` argument (try the symmetric orientation, which it already
does for bare equations, even when the proof is wrapped). Until then, Track D
should at least make the failure name this cause and suggest the
`claim`-binding.

**B5 — reverse-direction congruence folds in `calc`.** *(Also migrated from
the QUOTIENT findings.)* A reverse-direction congruence fold inside a `calc`
is fragile; the reliable idiom today is to prove the all-forward
"expanded ⇒ folded" direction and wrap the whole `calc` in a single
`Equality.symmetry`. A `by reverse <lemma>` step (or making the diff-matcher
try both orientations per step) would remove a lot of boilerplate in
quotient-law proofs.

**Acceptance tests.** Re-prove `Polynomial.gcd_bezout`'s `mDividesX`,
`ComplexNumber.divides_modulus_low_degree_zero`'s `degreePEquation`, and
`ComplexNumber.modulus_irreducible`'s `aNonzero` **without** any bridging
`claim`; and re-prove one quotient-law fold (e.g. in
`Polynomial/commutative.math`) without the wrap-the-whole-calc-in-symmetry
idiom.

### Track C — elimination / induction ergonomics (dissolve F5)

**C1 — `by_induction` / `by_strong_induction` auto-generalize.** When the
induction subject is bound under a Pi in the goal, or hypotheses in scope
mention it, automatically generalize (revert) them into the motive and
re-introduce them in each case. This removes the "move `n` and its
hypotheses into the conclusion by hand" chore and would have prevented the
`by_strong_induction` "unbound internal variable" failure (also fix that
motive-construction bug regardless — Track D).

**C2 — `decide` / `cases` refine in-scope hypotheses by default** (or via
`decide … refining h₁, h₂`). Today only the goal is refined; a hypothesis
mentioning the scrutinee silently keeps its old type and the next step fails
cryptically. Refining the hypotheses (the convoy/transport the user would
write by hand) removes a class of surprises and the need to `intro` inside
branches.

**C3 — `obtain`/anonymous-tuple expected-type inference through
un-β-reduced motives.** β-reduce the expected type before deciding whether
an `obtain` (or `⟨…⟩`) can read its motive. This removes both the
"factor the at-rep body into its own theorem" workaround (F4) and several
of the `(⟨…⟩ : T)` ascriptions.

### Track D — error messages (dissolve the misdirection in F4)

These are cheap relative to their value; each turns a binary-search session
into a one-line fix.

- **Partial-application-as-value**: when a function value handed to a
  higher-order slot still has unfilled *non-implicit* trailing Pi binders
  and the type mismatch traces to them, say so: "‘…symmetric(s, m)’ is
  partially applied (2 of 4 explicit args); eta-expand it." (The current
  message blames an unrelated `Ring.carrier s` vs `Ring`.)
- **defeq-but-not-structural in `rewrite`** (until B lands): when the
  endpoint is *definitionally* present but not structurally, say "found
  `<LHS>` only up to unfolding `Ring.multiply`/`Polynomial.ring`; restate
  with `change` or a bridging claim," and print the defeq form. This is
  exactly the missing hint.
- **`by_strong_induction` motive failure**: catch the internal
  unbound-variable case and emit "could not build the strong-induction
  motive over `<n>`; the goal/an in-scope hypothesis mentions a variable not
  abstracted — use explicit `Natural.strong_induction(motive, step, n)`."
- **anonymous tuple / `obtain` needs expected type**: name the construct and
  suggest the ascription form, with the expected proposition printed.
- **inline `Equality.symmetry(…)` in a calc `by`** (until B4 lands): when a
  calc step's `by` proof is a `congruenceOf`/symmetry that fails only because
  it is inline, say "bind the `Equality.symmetry(…)` to a `claim` first, then
  use it in the `by`" rather than a generic type-mismatch.

### Track E — discoverability

#### E1 — Lemma search by goal shape

**The problem.** `grep` searches by name/substring, but when you are stuck
you rarely know the name — you know the *shape of what you need to
conclude*. Every discoverability pain this session was of that form: goal
`a + b ≤ c + b` wanting *whatever proves it* (`Natural.le_add_preserves_left`,
hiding in `padic_valuation.math`); "is there nonneg·nonneg for Integer?"
(`Integer.IsNonneg.multiply`, hiding in `Rational/positive.math`); "does ℝ
have square-nonneg?" (no → build it). The connection is between a lemma's
*conclusion* and the *goal*, which strings cannot see. This is the
`exact?` / `apply?` / `Search` family from Lean/Coq.

**The engine (largely already exists).** A function
`candidates(goalType) → [ranked lemmas]`:
1. **Head-filter**: index every declaration by the head Constant of its
   conclusion (`LessOrEqual`, `Equality`, `Ring.divides`, …) — cheap first
   cut. The auto-prover *already builds and queries such an index*
   (`autoProveCalcStep` / lemma-index lookup in `elaborator.cpp`); the work
   is generalizing it from "close this calc step" to "answer an arbitrary
   goal query," not building it from scratch.
2. **Unify with holes**: treat the lemma's universally-quantified variables
   as metavariables and unify its conclusion against the goal; on success it
   is a candidate, and its remaining hypotheses are "what you would still
   have to supply."
3. **Rank**: by specificity (how much head structure matched), fewest
   leftover hypotheses, then whether it is in an already-imported module.

**Two query modes** over the same index:
- **conclusion-unifies-with-goal** — "what proves `a+b ≤ c+b`?" The
  apply?-style mode; the one used most.
- **mentions-these-symbols** — "lemmas whose statement involves both `monus`
  and `LessOrEqual`." The Coq-`Search` mode; strictly better than grep
  because it is over *parsed conclusions*, not raw text. This is the "where
  does the lemma live" answer.

**Surfaces (one engine, more than one delivery).** In priority order:
1. **Pushed into error messages (highest value, esp. for an LLM).** When a
   `by`/`done`/`okay` auto-prove fails, or a `rewrite` fails, the elaborator
   already holds the goal type and the index — append the top 3–5 ranked
   candidates with full signatures + `file:line`. Zero extra round-trips:
   the suggestion arrives exactly where the author is already looking. This
   converts an LLM's "guess a plausible-but-wrong name, burn an iteration"
   into a one-shot.
2. **Pull CLI subcommand `kernel search`** (sits alongside `kernel verify` /
   `kernel deps`). `kernel search --goal "a + b ≤ c + b"` and
   `kernel search --mentions monus,LessOrEqual`; loads the cache, prints
   ranked matches. For when a lemma is *anticipated* mid-composition rather
   than after a failure; one Bash call, usable anytime, and it answers the
   negative case ("nothing matches → build it") which stops fruitless
   hunting.
3. *(Optional, for humans)* an in-language `search;` / `hint;` statement
   that prints candidates for the current goal at elaboration — the
   interactive analogue of #2. Lower priority (overlaps the CLI).

**Output format is part of the spec.** Each hit must be *directly usable*,
or it just sends you back to grep: full signature + `file:line` + the
leftover hypotheses. E.g.
```
Natural.le_add_preserves_left (a c b : Natural) : a ≤ c → a + b ≤ c + b
    Natural/padic_valuation.math:1096   [needs: a ≤ c]
```

**Caveats / design constraints.**
- *Flooding*: `exact?`-style search over an equality goal matches everything
  ending in `=`. Mitigate by requiring head-symbol match, ranking by
  specificity, and capping output (≤5 in errors, ≤~20 in CLI), preferring
  imported modules.
- *The negative answer is a feature*: "no match" is what tells you to build
  the lemma (as with `Real.square_IsNonneg`) instead of hunting.
- *It finds, it does not close*: this is search, not a hammer/auto-prover —
  it returns the lemma and you apply it. That keeps it cheap and
  predictable, which is what the inner loop needs.

**Acceptance tests.**
- `kernel search --goal "a + b ≤ c + b"` (with `a c b : Natural`) lists
  `le_add_preserves_left` in the top hits.
- A deliberately-failing `… by done` over goal `Integer.IsNonneg(x * y)`
  surfaces `Integer.IsNonneg.multiply` in the error.
- `kernel search --goal "Real.IsNonneg(Real.multiply(t, t))"` over a library
  *without* `Real.square_IsNonneg` returns no hits (the useful negative).

#### E2 — bundles + standard-library organization

- A `CommutativeRing` / `Field` bundle, so constructions thread one value
  instead of `(r, commutativity, inverseExistence)` (this also lets
  `RingModulo.multiply` drop its explicit commutativity arg, which Track A1
  needs for a clean binary operator).
- A coherent, discoverable `Natural` order/arithmetic API (monotonicity,
  add-cancel, `≤`/successor conversions, totality consequences) in
  predictable places, and per-carrier order/positivity — promote ℝ
  multiply-positivity / square-nonneg out of `ComplexNumber/real_positivity.math`
  into `Real/order*`.

--------------------------------------------------------------------------
## 3. PRECISE ANSWER: "does Track A give us the abstract `ring` for free?"

Mostly, **with one bounded caveat**:
- Operator overloading (A1) supplies the *surface syntax* `x + y` for
  `Ring.add(r, x, y)` etc., which `ring` requires (it only recognizes
  operator-spelled expressions). Necessary, and largely already-supported
  (the registrar peels implicits today).
- But `ring`'s instance resolution currently assumes a **nullary**
  `<C>.is_ring`. For parametrized (`Polynomial`, `IntegerMod`) and abstract
  (`Ring.carrier(s)`) carriers it must be upgraded to instantiate/resolve a
  *parametrized or local* instance (A2). The plumbing to do this already
  exists for hand-cited lemmas (`canonicalInstanceRegistry` + local search)
  — A2 is wiring it into `ring`, not inventing it.
- And note: operators do **not** by themselves dissolve F1
  (defeq-vs-structural) or F5 (motive plumbing). Those are Tracks B and C.
  Operators *reduce the frequency* of F1 (one spelling `+` instead of two),
  but the structural matchers still need B to truly free the user.

--------------------------------------------------------------------------
## 4. SEQUENCING & THE LIBRARY-REWRITE PROVING GROUND

Recommended order (each independently shippable):
1. **A1** (operators + implicit structure args) — biggest readability win,
   self-contained, and unblocks A2.
2. **A2** (`ring` over parametrized/abstract carriers) — deletes the most
   hand-proof.
3. **B1/B2** (defeq-aware `rewrite` + `change`) — deletes the bridging-claim
   tax.
4. **D** (error messages) — cheap, do alongside whatever track is active.
5. **C** (elimination ergonomics) — deeper elaborator work; do after A/B.

After A1+A2 land, **rewrite these files as the proving ground** (they are
the ones that paid the tax, so they are the regression suite):
- `Algebra/ring_difference.math` → most lemmas become `:= ring`.
- `RingModulo/operations.math`, `RingModulo/ring.math` → operators in the
  statements; respect/law proofs shrink.
- `Polynomial/*` coefficient algebra and `ComplexNumber/irreducible.math`,
  `ComplexNumber/modulus.math` → operators + `ring` for the Real algebra.
Keep the old proofs in git history; the diff *is* the readability evidence.

After B lands, sweep for bridging `claim`s introduced only to satisfy a
structural matcher and delete them (grep for the comment pattern
"defeq" / "bridging" / claims that restate a hypothesis in a `divides` or
`Polynomial.multiply` form).

--------------------------------------------------------------------------
## 5. ACCEPTANCE SNAPSHOT (before → after we want)

Before (today, `ComplexNumber/modulus.math`):
```
= Real.add(
      Polynomial.coefficientOf(Real.ring,
          Polynomial.multiply(Real.ring, Complex.x, Complex.x), 2),
      Polynomial.coefficientOf(Real.ring, Polynomial.one(Real.ring), 2))
      by Polynomial.coefficientOf_add(Real.ring,
             Polynomial.multiply(Real.ring, Complex.x, Complex.x),
             Polynomial.one(Real.ring), 2)
```
After (target):
```
= coefficientOf(Complex.x * Complex.x, 2) + coefficientOf(1, 2)
      by coefficientOf_add(…)        -- or closed by `ring`/auto-prover
```

Before (today, the recurring F1 fix):
```
claim pEqualsPolyMultiply : p = Polynomial.multiply(Real.ring, Complex.modulus, quotient)
    by pEqualsModulusQuotient;        -- bridging claim, pure tax
… rewrite(Equality.symmetry(pEqualsPolyMultiply), …) …
```
After (target): `rewrite` finds the endpoint up to defeq; the claim is gone.
```

The north star: a proof author — human or LLM — should be able to write the
mathematics and have it accepted on the first try, never reasoning about
"is this the structural or the definitional spelling" or "is my induction
variable a parameter." Tracks A–D each remove one reason they currently
must.

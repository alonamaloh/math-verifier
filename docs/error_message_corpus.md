# Error-message corpus

A living catalogue of elaborator/parser error messages we have found
confusing, the circumstances that produced them, and a diagnosis of what
the problem *really* was. It exists so that improving error messages is
**data-driven** (real failures we hit) rather than guesswork, and so that
each improvement is measured and protected against regression.

## How this works

- **Capture first (frictionless):** when you hit a confusing error, run
  `scripts/record_error.sh <file.math> ["note"]`. It appends the verbatim
  output + a blank diagnosis to `docs/error_message_inbox.md` (an
  append-only scratch log) so nothing is lost while context is fresh.
- **Triage into this catalogue:** once an inbox entry is understood,
  promote it to an entry below — a minimal trigger, the verbatim message,
  the *true* diagnosis, a rubric score, and (if known) a better message —
  then delete it from the inbox.
- **When a message is fixed**, add a paired regression case under
  `library/ErrorTest/`: a broken `<name>.math` plus a `<name>.expected`
  sidecar listing substrings the message MUST contain. `make error-tests`
  asserts each file fails to verify and that its message still says the
  informative thing. (Those files are excluded from `make library`/`tests`.)
- A not-yet-fixed message can still get a harness case whose `.expected`
  locks the *current* text (so drift is caught); update it to the better
  text when the fix lands. Mark such entries **PENDING** here.

## Rubric (score each message 0/1 on five axes)

1. **Cause, not symptom** — does it name the actual fault, or just where a
   bad term was finally rejected?
2. **Right location** — does it point at the source line the user must
   change (the citation/binder), not a distant enclosing theorem?
3. **Actionable** — does it suggest a concrete fix?
4. **User-facing types** — does it print types as the user wrote them
   (folded definitions, `∣`/`≤` notation), not raw kernel/unfolded forms?
5. **No jargon leak** — no internal term-kind names, metavariable gensyms,
   or de Bruijn indices in the user-visible text.

## Catalogue

### 1. Cited lemma can't be applied → bare-lemma fallback — FIXED (fix #1)

- **Trigger:** `claim T by L` / `done by L` / `goal by L` where `L`'s
  arguments can't be inferred (e.g. a higher-order explicit arg), **or**
  `L` is simply the wrong lemma. Repros:
  `library/ErrorTest/higher_order_explicit_cite.math`,
  `library/ErrorTest/wrong_lemma_cite.math`.
- **Was (symptom):**
  ```
  the proof of theorem 'X' does not have its declared type
    declared type:        <goal>
    but this proof has type: (predicate : …) → … → <conclusion>
  ```
  Scored 0 on cause, location (points at the theorem, not the `claim`),
  and actionable. The bare `(a) → (b) → …` function type was the only clue.
- **Diagnosis:** `recoverClaimHint` (the recovery path after
  `autoFillHintForClaim` throws) ran `coerceToExpectedTypeViaDiff` and
  returned its result **without checking it had the goal type**; the
  un-bridged bare lemma then failed the enclosing typecheck far away.
- **Now:** `recoverClaimHint` verifies the recovered term is defeq to the
  goal; if not it throws at the claim site, naming the hint, showing
  `goal:` and the hint's (folded) type, and explaining that the arguments
  couldn't be inferred / the conclusion doesn't unify. (inference.cpp.)
- **Still open:** the deeper inference limit — a higher-order *explicit*
  argument is genuinely uninferable; making such args implicit (so normal
  unification solves them) would let more citations succeed, not just fail
  better. See `Natural.least_witness_minimal` (deferred refactor).

### 2. Reserved word used as an identifier — FIXED (fix #2)

- **Trigger:** a binder named with a reserved word, e.g.
  `theorem f (witness : Natural) : …`. Repro:
  `library/ErrorTest/reserved_word_binder.math`.
- **Was (symptom):**
  ```
  parse error: expected at least one name in binder … (got 'witness')
  ```
  Scored 0 on cause and actionable: never said `witness` is *reserved*.
  Recurs often (`witness`, `goal`, `done`, `okay`, `note`, `change`,
  `suppose`, `take`, `claim`, …); hit twice in one session while authoring
  error-test files themselves.
- **Diagnosis:** `parseExplicitBinder` broke its name loop on a non-
  identifier token and, finding no names, reported the generic message —
  never noticing the offending token was a keyword.
- **Now:** when the binder has no names and the next token is a keyword,
  the parser says `'witness' is a reserved word and cannot be used as a
  binder name — choose another name`. (parser.cpp, using `isKeyword`.)
- **Still open (minor):** only the empty-binder case is covered; a keyword
  as a *later* name (`(a witness : T)`) still gives a generic "expected ':'
  in binder". Low frequency.

### 3. Goal printed unfolded — FIXED (fix #3, Approach A)

- **Trigger:** any error whose goal flowed through an eliminator motive
  (e.g. an `obtain`), which δ-unfolds a `definition`-headed goal. Repro:
  `library/ErrorTest/unfolded_goal_display.math`.
- **Was (symptom):** `Exists.{0} Natural (λ q. n = d * q)` where the source
  said `d ∣ n`. Scored 0 on axis 4.
- **Now:** `errors.cpp`'s `refoldForDisplay` walks the term bottom-up and,
  at each CLOSED subterm, re-folds a transparent `definition`'s body back
  to `Name(args)` — accepted ONLY when `Name(args)` round-trips defeq to
  the subterm (so a fold is never wrong; at worst it declines). The
  printer then renders the registered notation, so the goal shows `d ∣ n`
  (added `∣` for `.divides` to printer.cpp's operator table). Display-only;
  never touches elaboration. The `.expected` asserts both `d ∣ n` present
  and `Exists.{0}` absent (harness supports `!`-prefixed negative lines).
- **Deferred — Approach B (provenance quoting, user's idea):** remember
  the **exact surface string / source span** the user wrote for a type
  annotation and quote it verbatim (e.g. `-- as written: d ∣ n`). Wins
  where folding can't: literal fidelity (`2` vs `successor(successor 0)`),
  user-defined notation the printer doesn't know, and synthesised
  sub-goals (`d ∣ 0` in a refining arm) where quoting the original `d ∣ n`
  helps the user locate the code even though it's a transformed goal —
  ideally with a note explaining the transformation. Needs surface end-
  positions (nodes carry only start now). Revisit once we see, in
  practice, that re-folding leaves real gaps.

### 4. `done`/`goal`/`okay` silently weaker than `claim` in refining arms — FIXED

- **Trigger:** a `cases … refining h` arm closed with `done by L` when the
  arm's goal is headed by a `definition` (unfolded by the motive). Repro:
  `library/Test/done_by_in_refining_test.math`.
- **Was:** fell back to the bare lemma (see entry 1) — but the deeper
  surprise was that `claim P by L` worked in the same spot while `done by
  L` didn't, an undocumented asymmetry one would "learn" as a quirk.
- **Now:** `autoFillHintForClaim` also matches the WHNF-reduced conclusion
  cursor, and `matchAgainstPattern` descends into `Lambda`; the closers
  behave identically to `claim`. (induction.cpp, diff_bridges.cpp.)

### 5. `claim False by <neg-lemma>` stalled on `Not` — FIXED

- **Trigger:** citing a lemma whose conclusion is `¬P` (`Not(P)` =
  `P → False`) to prove `False`. Repro:
  `library/Test/claim_false_by_negation_test.math`.
- **Was:** bare-lemma fallback — the Pi-peel stopped at the `Not`-headed
  conclusion and never reached `False`.
- **Now:** the peel loop unfolds a non-Pi cursor once to expose a hidden
  Pi. (induction.cpp.)

### 6. Non-terminating elaboration → OOM, no message — PARTIALLY FIXED

- **Trigger:** `cases`/`by_induction` with a scrutinee-dependent
  hypothesis on the plain (non-refining) path used to loop, growing memory
  until the machine died — the worst failure mode (no error at all).
- **Now:** that specific loop is routed to refining + a re-entrancy depth
  cap (cases.cpp). **Still open:** a *global* elaboration fuel/recursion
  cap so any runaway becomes a normal error rather than an OOM. Always
  guard manual repros with `( ulimit -t 90; ./kernel verify … )`.

### 7. `?` holes don't fill anonymous-tuple proof slots — PENDING (surprise)

- **Trigger:** `⟨proof, ?⟩` for an `And`/`Exists` — the `?` for the second
  component is not auto-discharged (`could not infer hole(s) at position
  1` from `And.introduction`), although `?` *does* fill constructor
  argument positions (e.g. `StrictComparison.below(…, ?)`).
- **Diagnosis:** `?` is goal-driven *argument* inference (unify from other
  args), not an auto-prover request; in an `And.introduction` slot there's
  nothing to unify against. The inconsistency (works for some constructor
  positions, not tuples) is the real papercut.
- **Wanted:** either make `?` invoke the auto-prover in proof positions, or
  emit a message saying so and suggesting `claim <component> by …`.

### 8. Misspelled / unknown cited lemma name — FIXED (fix #4)

- **Trigger:** `claim T by Natural.add_comutative` (a typo). Repro:
  `library/ErrorTest/unknown_lemma_name.math`.
- **Was:** after fix #1, this produced the generic "the
  `Natural.add_comutative` citation does not prove this goal … check the
  lemma name" — masking the real cause (no such lemma exists). Fix #1's
  recovery catches re-elaboration's "unknown identifier" and replaced it
  with the generic message. Scored 0 on cause.
- **Now:** recoverClaimHint first checks whether a QUALIFIED cited name
  (contains `.`) resolves to a declaration; if not, it throws "unknown
  lemma `Natural.add_comutative` in `by` citation — no declaration by that
  name is in scope". Restricted to qualified names AND not-a-local-binder
  so it never false-flags a local hypothesis cited in `by` (e.g. a
  destructured ring-bundle field like `addIdentityRight`) or an overload
  alias. (inference.cpp.) `.expected` asserts the unknown-lemma text and
  that the generic "citation does not prove this goal" is absent.
- **Possible follow-up (deferred):** a "did you mean …?" suggestion via
  edit-distance over declaration names — only if it proves worth it.

### 9. Ambiguous premise discharge in `obtain by` / `cases by` — FIXED (fix #5)

- **Trigger:** an argument-free `obtain ⟨…⟩ by L` / `cases by L { … }`
  where L's premise pattern is matched by SEVERAL in-scope hypotheses
  that pin different lemma arguments. Repros:
  `library/ErrorTest/cases_by_ambiguous_premise.math`,
  `library/ErrorTest/obtain_by_ambiguous_premise.math`.
- **Was (symptom):** the discharge silently took the most-recent match
  (recency heuristic), and the wrong instantiation surfaced far away —
  a branch type-mismatch (`this case gives: b = Integer.zero` against
  `expected: a = Integer.zero`) or a wrong obtained equation feeding a
  later step. Scored 0 on cause and location; the conventions doc said
  "must be unambiguous" but nothing enforced it.
- **Diagnosis:** `inferCallWithHoles` step 5c (match-and-unify) committed
  the first hypothesis that unified, and steps 5d/5e (backward chaining)
  could likewise guess; for these citation forms there is NO downstream
  goal that validates the choice, so the guess is unchecked.
- **Now:** the `SurfaceCiteInferred` elaboration (the obtain-by/cases-by
  desugar) sets `requireUnambiguousDischarge_`; at search depth zero,
  step 5c then COLLECTS all matching hypotheses instead of committing the
  first. One match (or several with identical instantiations) commits as
  before; conflicting matches defer the slot, suppress backward chaining,
  and the failure reports at the citation site: the premise pattern (with
  holes shown as `?`), every candidate hypothesis with its type, and the
  fix ("pass the lemma's arguments explicitly"). Claim/calc citations are
  untouched — they keep the recency heuristic because a goal validates
  the outcome downstream (and proofs depend on that backtracking).
  Three library sites that had been silently lucky (division.math,
  multiply_bounds.math, prime_split.math) were made explicit.
- **Still open:** the inbox's "even better" idea — use the expected
  return type of the `cases` arms to disambiguate before erroring —
  is unimplemented (it would need the arm types threaded into the
  citation; the explicit form costs one line and is clearer anyway).

### 10. Proof-term `by` hint failures masked by the citation message — FIXED (fix #6)

- **Trigger:** `claim P by (x) ↦ { … }` (or a block / ring / field hint)
  whose BODY contains a failing inner step, typically deep inside a
  `cases`/`by_induction` nest. Repro:
  `library/ErrorTest/lambda_hint_inner_error.math`.
- **Was (symptom):** "the `by` hint citation does not prove this goal"
  with the whole Pi-typed claim as the goal and no inner detail. Scored
  0 on cause and location. Cost: the extract-a-helper-theorem workaround
  (done repeatedly during the Wilson/Euler sessions purely to see the
  real error).
- **Diagnosis:** the claim flow's catch sent every failure to
  `recoverClaimHint`, which for a proof-term hint can only re-elaborate
  the identical term — failing identically and replacing the genuinely
  informative inner error with the generic citation message. (Also fixed
  here: the doubled article "the the `by` hint".)
- **Now:** `hintShapeIsProofTerm` (lambda / let-block / ring / field):
  when such a hint's own elaboration throws, the inner error propagates
  unmasked, carrying its own claim line, goal, and cited-type details.
  Citation-shaped hints keep the recovery path and its message.
- **Related (fix #7, same session):** Pi-typed goals are now citable
  argument-free — `citePiGoalByIntroduction` introduces the goal's
  binders and runs the full citation machinery on the core goal, which
  removed the `(z)(mem) ↦ { done by Lemma }` wrapper idiom from six
  library sites (see `library/Test/pi_goal_citation_test.math`).

### 11. `by substituting <lemma>` did not infer arguments — FIXED (fix #8)

- **Trigger:** `by substituting Natural.add_zero` (a QUANTIFIED equation
  cited by name) on a calc step / claim whose goal contains an instance
  of the lemma's conclusion. Repro (now the passing feature test):
  `library/Test/substituting_lemma_test.math`.
- **Was (symptom):** "`by substituting`: the supplied expression's type
  is not an equality `a = b`" — literally correct (the type is a Pi
  chain ENDING in an equality) but unhelpful: no why, no fix. The trap
  was the asymmetry: `by <lemma>` and the unnamed `by substitution` both
  infer arguments; `by substituting <lemma>` alone did not.
- **Diagnosis:** `elaborateClaimBySubstitution`'s narrowed form fed the
  citation's type straight to `extractEqualityComponents`, which only
  accepts a concrete `Equality(A, x, y)`.
- **Now:** `collectQuantifiedSubstitutionCandidates` (claim.cpp): when
  the cited type is a Pi chain ending in an equality, its LHS/RHS
  patterns are matched against the goal's Application subterms
  (`matchAgainstPattern` — the single-lemma analogue of
  `collectLibraryEqualitiesAt`, but driven by the cited proof term, so
  non-indexed lemmas and Pi-typed local hypotheses qualify); each
  complete match instantiates a substitution candidate for the ordinary
  bridge. When no instance occurs in the goal, the error names the
  citation, says it is a quantified equation with N outstanding
  argument(s), and points at both ways out (apply explicitly / unnamed
  `by substitution`). ErrorTest:
  `substituting_lemma_no_occurrence.math`.
- **Limits:** all lemma binders must be bound by matching ONE side
  (propositional preconditions are not discharged from hypotheses here,
  unlike the indexed path), and the instance must occur in the GOAL —
  a reverse rewrite whose structured side appears only in the result
  (e.g. introducing `n + 0` out of `n`) still needs explicit arguments.

### 12. Statement-pass errors lost their location (printed at 1:1) — FIXED

- **Trigger:** a kernel TypeError thrown while elaborating a theorem
  STATEMENT (binder types + declared type) — e.g. `p + q` at
  `(p q : Polynomial(Real, Real.zero))`, where operator dispatch passes
  `Real.zero` (type `Real`) where a `Ring` is expected (see corpus #13's
  dispatch note). Repro: `library/ErrorTest/statement_error_location.math`.
- **Was (symptom):**
  ```
  file.math:1:1: type error: Application: argument type does not match Pi domain
    expected type: Ring
    actual type:   Real
  ```
  No declaration name, no line, raw kernel wording. Scored 0 on cause,
  location, actionable, jargon. Found in practice by bisecting the file
  theorem by theorem (2026-06-12, ℂ coordinates).
- **Diagnosis:** `elaborateDefinition` wrapped only the proof BODY in the
  `catch (TypeError) → rethrowKernelError` chain; a TypeError from
  statement elaboration unwound past every context frame to the driver,
  whose bare-TypeError printer hardcodes `1:1`.
- **Now:** the statement is elaborated under its own
  `theorem 'X' (statement)` frame anchored at the declared type's source
  span, with the rethrow inside that frame's scope (statements.cpp); the
  statements-only pass (`MATH_STATEMENTS_ONLY`) has the same wrapping;
  and `elaborateTopStatement` re-anchors any TypeError that still
  escapes a declaration handler (`topStatementErrorAnchor`), so a bare
  kernel TypeError can never reach the driver's 1:1 printer. The error
  now reads `file.math:27:13: elaborate error: theorem 'X' (statement)`
  + the friendly "this argument has the wrong type…" rendering.
- **Related residual fixed in the same push:** `unknown identifier 'X'
  at line N, column C` carried its position only in the message TEXT;
  the `ElaborateError` now carries it structurally too, so the header
  matches (inference.cpp).

### 13. Citation matching blind to `Ring.carrier(r)` ≡ concrete carrier — FIXED

- **Trigger:** citing a lemma stated over `Ring.carrier(r)` /
  `Ring.zero(r)` (e.g. `Polynomial.Coefficients.multiply_one_left`)
  argument-free at a goal spelled with the concrete carrier
  (`ExtensionallyEqual(Real, Real.zero, multiply(Real.ring, …), …)`).
  Repro (now the passing feature test):
  `library/Test/citation_carrier_defeq_test.math`.
- **Was (symptom):** "the `…multiply_one_left` citation does not prove
  this goal" — while the SAME claim worked with explicit arguments
  (defeq application checking) and completely BARE (auto-prover search).
  Hint-less was strictly MORE capable than hinted, inverting the hint
  model; the redundancy checker's "redundant `by`" was the only
  discovery mechanism. (2026-06-12, ℂ coordinates.)
- **Diagnosis:** the first-order matcher walks the conclusion spine
  left-to-right, so `Ring.carrier(BV r)` is matched against `Real`
  while `r` is still unbound (the binding argument
  `multiply(Real.ring, …)` comes later); the canonical-bundle registry
  had no `(Ring, Real)` entry (`Real.ring` is not
  `instance`-registered), and no subject-side reduction can fix a stuck
  projection-of-metavariable.
- **Now:** `matchAgainstPattern` defers a structure-bundle projection of
  an unbound metavariable (pattern `S.field(BV slot)` where `S.carrier`
  exists) and verifies it by definitional equality once the rest of the
  match binds the slot (`matchAgainstPatternWithDeferredProjections`,
  diff_bridges.cpp); a bound slot's projection resolves by the same
  defeq on the failure path, subsuming the old
  registered-canonical-bundle special case. Wired into the citation flow
  (`autoFillHintForClaim`); gated to structure projections so the
  prover's hot failure paths are untouched (ungated cost 2x on
  Real/supremum; gated, build time within noise).
- **Boundaries (documented behaviour, not bugs):**
  - NOT general higher-order unification — function-parameter lemmas
    keep needing positional citation (Miller-pattern gap).
  - ζ-opacity is a SEPARATE seam: a lemma conclusion spelling out the
    list a local `let` abbreviates (`multiply_one_left`'s cons-spine vs
    a let-bound `one`) still fails to cite — same family as the
    2026-06-11 let-opacity inbox entries (still open).
  - Operator dispatch's `Ring` asymmetry (`p + q` at
    `Polynomial(Integer, …)` but not `Polynomial(Real, …)`) is NOT this
    seam: dispatch infers `{r : Ring}` from a type template where `r`
    occurs only under projections, so deferral has nothing to bind it
    with — the canonical-bundle registry is the mechanism there.
    RESOLVED at the library level: `instance Real.ring`
    (ComplexNumber/basics.math), pinned by
    `Test/real_ring_dispatch_test`. (The full dispatch trace lived in
    PLAN_ELABORATOR_SEAMS.md, executed and retired 2026-06-12 — see git
    history. Short version: operator target resolution is symmetric;
    the asymmetry was filling the implicit `{r : Ring}`, where the
    canonical-bundle registry is the only mechanism, and on a registry
    miss the single-filler fallback knowingly hands the kernel a junk
    argument for it to reject.)

### 14. Unknown lemma in a calc-step citation against a stale cache — RESOLVED

- **Trigger (2026-06-12, exp push):** citing a brand-new lemma with
  explicit arguments inside a calc step while the dependency's `.mathv`
  was stale (the lemma absent from the loaded cache). The calc-step path
  reported "the hint's arguments could not be inferred…", sending the
  author down a unification rabbit hole, while a scratch probe honestly
  said `unknown identifier`.
- **Re-checked after fixes #4/#12/#13:** an unknown qualified name cited
  in a calc step now reports
  `file.math:11:17: elaborate error: unknown identifier 'X' at line 11, column 17`
  — unknown-name detection precedes unification on this path too.
- **Still open (nice-to-have):** the "(the module cache for X may be
  stale — rebuild with make)" hint when the name exists in source but
  not in the loaded environment; low value now that the message names
  the identifier honestly.

### 15. `obtain`/`choose` type-inference through an opaque quotient — PENDING

- **Trigger (2026-06-16, Rational → opaque field-of-fractions migration):**
  destructuring an existential whose type must be *inferred* from an
  application, when that type folds through an **opaque** quotient. E.g.
  `obtain ⟨N, h⟩ from sIsCauchy(ε, εPos)` where
  `sIsCauchy : Rational.sequence.IsCauchy(s)` reduces to
  `… → ∃ N. … abs(s(m) - s(n)) < ε`, and `<`/`abs` fold through the now-opaque
  `Rational` (via `Rational.IsNonneg = Quotient.lift(…)`). `choose … from …`
  fails identically. Many sites in `Real/{addition,multiplication,absolute_value,
  order,sequence}.math`.
- **Was (symptom):**
  ```
  library/Real/sequence.math:83:3: elaborate error: theorem
    'Rational.sequence.negate_is_cauchy'
    this argument has the wrong type for the function it is given to
      the function expects: Quotient.{0} RationalRepresentative RationalEquivalent
      but this argument is: Rational
  ```
- **Diagnosis:** `obtain`/`choose` synthesise the source's type bottom-up;
  inferType WHNF-reduces the existential body, whose order relations fold to
  `Quotient.lift(…, x)` with `x : Rational`. Hard opacity (`isHardOpaqueConstant`)
  blocks the inferType-application bridge that would unfold `Rational` to
  `Quotient(RationalRepresentative, RationalEquivalent)`, so the lift's domain
  stays the raw `Quotient …` while the argument is the opaque `Rational` — and
  the two no longer unify. Giving the type **top-down** sidesteps the
  synthesis entirely: `claim h : ∃ … by <source>;` then
  `obtain ⟨…⟩ from h` checks the source against the stated type and verifies.
- **Score:** cause **0** (reports the unify symptom, not "can't infer the
  source's type through an opaque head"), location **0** (points at the
  enclosing theorem's first line, not the `obtain`/`choose` keyword), actionable
  **0** (no hint to annotate the type), user-facing-types **0** (prints the
  *unfolded* `Quotient.{0} RationalRepresentative RationalEquivalent` — the very
  form opacity exists to hide — while the user only ever wrote `Rational`),
  jargon **0** (`Quotient.{0}` leaks the universe-annotated internal head). 0/5.
- **Better message:** at the `obtain`/`choose` site —
  "cannot infer the type of `<source>`: it reduces through the opaque
  `Rational`, exposing a `Quotient.lift` whose domain can't be matched while
  `Rational` is sealed. State the result type explicitly —
  `claim <name> : <type> by <source>; obtain ⟨…⟩ from <name>` — or ascribe
  `(<source> : <type>)`." And print `Rational`, not its unfolded quotient.

### 16. `by substituting` silently stalls on an opaque head deep in the goal — PENDING (good-ish)

- **Trigger (2026-06-16):** `done by substituting absZero` (with
  `absZero : abs(Real.zero) = Real.zero`) to close
  `abs(Real.partialSum(s, 0)) ≤ Real.partialSum(…, 0)`. `Real.partialSum(s, 0)`
  is defeq `Real.zero`, but `Real.zero` is a `Quotient.mk` over an opaque-`Rational`
  sequence, so deep-WHNF stalls before surfacing `abs(Real.zero)`.
- **Message (verbatim, the helpful part):**
  ```
  `by substituting <eq>` couldn't close the goal.
  Direction search:
      rhs → lhs: 0 occurrences (surface or deep-WHNF)
      lhs → rhs: 0 occurrences (surface or deep-WHNF)  …
  ```
- **Diagnosis:** genuinely informative — it told me the rewrite endpoint never
  appeared in either direction, which correctly pointed at "the goal isn't
  reducing to the shape my equation mentions" (deep-WHNF stalling on the opaque
  `Rational` inside `Real.zero`), and I switched to an explicit `calc` with the
  defeq step written out. Score: cause **1**, location **1**, actionable **1**
  (the "add `by <proof>`" tail), types **1**, jargon **1**. 5/5 — keep as a
  positive exemplar; the only gap is it can't *know* an opaque head blocked the
  reduction, which would have named the cause directly.

### 17. `decide` without `import Natural.classical_decidable` — FIXED

- **Trigger:** the `decide` tactic in a module that does not (transitively)
  import `Natural.classical_decidable`. Repro:
  `library/ErrorTest/decide_missing_classical_decidable.math`.
- **Was (symptom):**
  ```
  elaborate error: unknown identifier 'Logic.classical_decidable' at line N
  ```
  Scored 0 on cause and actionable: `decide` desugars to
  `cases Logic.classical_decidable(P)` (cases.cpp), so the failing name is one
  the user never typed — a baffling "unknown identifier" pointing at a `decide`
  for a name that isn't in the source. Newly possible because
  `Logic.classical_decidable` was demoted from a universally-imported axiom in
  `axioms.math` to a theorem in `Natural.classical_decidable` (it needs
  `Natural`), so it is no longer in every module's import closure.
- **Diagnosis:** `elaborateIdentifier`'s unknown-identifier throw (inference.cpp)
  reported the desugared name verbatim with no hint about where it now lives.
- **Now:** the throw special-cases `Logic.classical_decidable` and appends
  "is a theorem in `Natural.classical_decidable` (the `decide` tactic desugars
  to it) — add `import Natural.classical_decidable`". Score: cause **1**,
  location **1** (points at the `decide`), actionable **1**, types n/a,
  jargon **1**.
- **Note:** a general "relocated foundational name → import hint" table would
  scale this if more names move out of `axioms.math`; one special-case is enough
  for now (it's the only such name the `decide` desugar emits).

# Plan: make CIC an implementation detail

**Vision.** A user writing mathematics in this language should never need to
know it is built on the Calculus of Inductive Constructions. CIC is the
substrate, not the surface — like assembly under C. A small, explicitly
designated **foundational layer** of `.math` files is permitted to drop to
raw CIC primitives (`Quotient.*`, `unfold`, explicit motives, `Sort`/
universe handling) in order to scaffold the nicer tools. Everything above
that layer should read as mathematics, and — crucially — *fail* as
mathematics: a stuck proof should produce a math-shaped error, never a
`Pi`/`Sort`/`BoundVariable` message.

**Core principle: the kernel is a trusted re-checker, not a diagnostician.**
Like a typed bytecode verifier behind a language front-end, the kernel
exists to *confirm soundness* of what the elaborator already established —
it should never be the *first* thing to find a problem, and therefore never
the thing that reports one to a user. Every user-facing error must originate
in the elaborator or the auto-prover. **A kernel error reaching the user is
a defect**, in one of two forms: an elaborator bug that produced an
ill-formed term, or a *deferral gap* where the elaborator built a term and
let the kernel type-check it first instead of checking it itself. The work
is to eliminate both, not to prettify the kernel's wording after the fact.

**Two audiences, two bars.**
- **Using** existing structure (proving theorems about Real, groups, …):
  the bar is "CIC never appears, in code *or* in errors." Currently ~80–85%.
- **Building** new structure (defining a quotient type, an opaque def, a
  new theory): the bar is "CIC appears only briefly, at a clean, marked
  boundary." Currently ~50%.

The stronger dream — CIC invisible even to the foundation-builder — is
**asymptotic**, not fully reachable: CIC's `Prop`/`Type`/universe structure
and its elimination restrictions are load-bearing semantics, not cosmetic
noise. This plan drives the *reachable* dream hard and documents the
irreducible remainder honestly.

---

## 0. Cross-cutting: define the boundary and measure the leak

Before changing anything, make the goal measurable. Without this, "feels
like math" stays a vibe.

### 0.1 Declare the foundational layer
- Add a manifest (`docs/foundational-layer.md` + a machine-readable list)
  naming every file allowed to use raw CIC vocabulary — the "assembly
  zone." Candidates: `library/axioms.md`, `Logic/quotient`, `Logic/sigma`,
  the carrier+equivalence+lift files for each constructed type (Integer,
  Rational, Real, Polynomial, …), and the opaque-definition characterizing-
  lemma files.
- Everything **not** on the list is "user space" and must stay CIC-free.

### 0.2 A leak linter (`scripts/cic_leak_report`)
- Scan user-space `.math` files for CIC-vocabulary tokens: `Quotient.`,
  `unfold `, `congruenceOf`, `transport_proposition`, explicit
  `Equality.symmetry`/`.transitivity` (where `calc`/auto should suffice),
  `Sort`, universe annotations, `False.eliminate_proposition`, the `¬¬`
  idiom, function-wrapping-for-`cases`.
- Emit a per-file and total count. Wire into `make` as a non-failing
  report first; later a ratchet (count may not increase).
- This is the north-star dashboard for the whole plan.

### 0.3 An error-provenance audit
- **Tag kernel-originated errors.** Mark every `TypeError` thrown by the
  kernel (vs. one authored by the elaborator/auto-prover) with a provenance
  flag. A kernel-tagged error that reaches top-level user output — i.e. was
  *not* intercepted and re-authored by the elaborator — is a **defect**.
- A corpus of ~30 representative *mistakes* (apply a non-function, wrong
  arity, type mismatch, missing premise, bad induction motive, …), each
  with its current error captured in a golden file.
- The audit passes when no golden error is kernel-tagged (equivalently: none
  contains CIC vocabulary, since only the kernel speaks it). This makes
  "kernel error reached the user" a CI-detectable regression, not a hope.

**Deliverables:** foundational-layer manifest; `cic_leak_report`; error
golden corpus. **Acceptance:** baseline numbers recorded; CI shows them.

> **Status — DELIVERED (2026-06).**
> - Manifest: [`docs/foundational-layer.md`](docs/foundational-layer.md) +
>   machine-readable [`scripts/foundational_layer.txt`](scripts/foundational_layer.txt)
>   (axioms + `Logic/` + each type's carrier file; 20 files).
> - Leak linter: [`scripts/cic_leak_report`](scripts/cic_leak_report),
>   `make leak-report` / `make leak-ratchet`. **Baseline: 681 token
>   occurrences across 110 user-space files.**
> - Error corpus: [`scripts/error_corpus/`](scripts/error_corpus/) (30
>   mistakes + goldens), `make corpus` / `make corpus-audit`. **Baseline:
>   18 of 30 kernel-tagged (CIC leak), 12 math-shaped, 0 non-erroring.**
>   `corpus-audit` is the WS1 acceptance gate (red today). Provenance is
>   read off the `"kernel: "` prefix per Appendix A — no kernel change
>   needed yet.

---

## Phase 1 — Diagnostics & hardening (cheapest, highest perceived gain)

### WS1. Make the elaborator authoritative at the kernel boundary
The felt "CIC-ness" of errors is not a *wording* problem to be fixed by a
translation pass — it is a *provenance* problem. The CIC-shaped messages
this session surfaced — *"function is not of Pi type," "argument type does
not match Pi domain," "body type does not match declared type," "bare
BoundVariable reached inferType"* — all came from the kernel being the
**first** thing to type-check a term the elaborator had already built. The
fix is to make the elaborator check it *first*, with a math-level message,
so the kernel only ever confirms (and never reports). Note these are **not**
auto-prover paths: the auto-prover's "can't close this goal" text is already
math-shaped. These come from the *other* path — elaborating an explicit term
or finalizing a definition.

Two buckets, two fixes:

- **Bucket A — elaborator bugs (malformed terms).** "bare BoundVariable
  reached inferType" and friends: the elaborator produced an ill-formed
  term. These must never be user-facing. Fix the bug; catch the class with
  the WS8 assertions. Any that escape render as a generic "internal error,
  please report" — never CIC vocabulary.

- **Bucket B — deferral gaps (the real work).** Close every site where the
  elaborator builds a term and lets the kernel type-check it first:
  - **Application** (`f(x)`): before assembling the `Application`, check
    that `f`'s type is a function type and that `x` matches its domain;
    emit a surface error on failure ("you're applying this as a function,
    but it has type `T`" / "this expects an argument of type `A`, got `B`").
    Closes "not of Pi type" and "argument type does not match Pi domain."
  - **Definition finalization** (`addDefinition`): compare the proof's
    inferred type to the declared theorem type in the elaborator, as a
    surface-level diff, before handing it to the kernel. Closes "body type
    does not match declared type."
  - **Ascription, `cases` motive**: same discipline — the elaborator owns
    the check and the message.
  Where the elaborator already intercepts a kernel `TypeError` (the
  `rethrowKernelError` path), it currently passes the kernel's *wording*
  through; those sites re-author the message in surface terms instead.

- **Provenance gate (the backstop).** With WS0.3's kernel-tag in place,
  assert at the top-level error boundary that no kernel-tagged error
  reaches the user. This converts every remaining deferral gap into a
  failing test that points at exactly the unclosed site — so the gaps get
  found and closed incrementally rather than by guesswork.

This is more work than a rendering pass, but it is the *right* work: it
removes the cause (the kernel diagnosing) rather than the symptom (its
wording). It is mostly **gap-closing**, not a second type-checker from
scratch — the elaborator already calls `inferType`/`isDefinitionallyEqual`
in most places; WS1 is about making it do so at the *remaining* boundaries
and own the message there.

- **Acceptance:** the WS0.3 audit shows zero kernel-tagged errors reaching
  the user across the mistake corpus; the provenance gate is enforced in CI.

> **Status — acceptance met (2026-06).** Corpus 31/31 math-shaped, 0
> kernel-tagged; `make check` (= tests + corpus-audit + leak-ratchet) is
> the enforced gate. Closed gaps:
> - **Definition finalization** — `checkDefinitionWellFormedOrThrow` runs
>   addDefinition's three checks (name / declared-type-is-a-type /
>   body-matches-type) in the elaborator first, on every definition, and
>   reports as mathematics; the kernel only confirms. Genuine first-check.
> - **Calc step** and **pattern-match case body** — both already *detected*
>   the mismatch in the elaborator but laundered it through
>   `rethrowKernelError`; now throw surface errors directly.
> - **Application family** ("not of Pi type" / "argument … Pi domain") —
>   re-authored at the single `rethrowKernelError` chokepoint into surface
>   wording, covering every path that funnels through it. An *unmapped*
>   kernel message keeps the literal `kernel:` prefix, so the audit still
>   catches new leaks.
> - **Printer** — function types render `A → B` / `(x : A) → B`, never `Π`.
>
> Remaining follow-ups (not blocking acceptance):
> - **Bucket A (WS8)** not yet done: malformed-term assertions / the
>   `coerceToExpectedTypeViaDiff` contract.
> - **Universe rendering (WS6)**: errors can still show `reflexivity.{0}`
>   and the lemma-search index prints `Type _auto_u_0`.
> - The corpus is a 31-case sample; grow it as new gaps surface.

### WS8. Representation-contract documentation + assertions
(Started already: the CLOSED-vs-OPENED-over-local-binders note and
`assertClosedOverLocalBinders` at `inferTypeInLocalContext`.) Generalize:
- Document, at each term-mover's definition, which representation it
  consumes and produces (`elaborateExpression`, `autoProveClaim`,
  `autoFillHintForClaim`, `coerceToExpectedTypeViaDiff`, open/close helpers).
- Pin `coerceToExpectedTypeViaDiff`'s contract: it currently *can return a
  malformed term* for diffs it cannot handle (the symmetry-flip bug). Make
  it total-or-throws, or assert its output type at the source.
- Thread the `where`-tagged `assertClosedOverLocalBinders` through the other
  boundaries, so an escaping bound variable is caught where produced.
- **Why in Phase 1:** these assertions are the safety net that makes the
  riskier elaborator surgery in Phases 2–3 (auto-unfold, quotient sugar)
  debuggable instead of producing deep kernel crashes.
- **Acceptance:** no user-facing "bare BoundVariable"; contract comments at
  every mover; the leak linter's internal-crash category is empty.

> **Status — substantially done (2026-06).**
> - `coerceToExpectedTypeViaDiff` pinned: `acceptCoercionIfClosed` rejects a
>   non-closed strategy result (O(1) guard), warns, and falls back to the
>   unwrapped term — the symmetry-flip → bare-BoundVariable class can no
>   longer crash the kernel. 0 warnings across library+tests.
> - **No user-facing "bare BoundVariable":** all `internal:` kernel errors
>   now render at the `rethrowKernelError` chokepoint as a generic
>   "internal error … please report it" (raw detail → stderr), never CIC
>   vocabulary.
> - Contract comments added on `autoProveClaim` / `autoFillHintForClaim`
>   (the CLOSED/OPENED note already covered the open/close helpers).
> - *Remaining (low priority):* thread `assertClosedOverLocalBinders`
>   through more boundaries beyond the coerce guard. The bug-prone mover is
>   already guarded, so this is defensive depth, not a gap.

---

## Phase 2 — Everyday-proof leverage

### WS2. Eliminate user-visible `unfold` at opacity boundaries
`unfold Real.IsNonneg in (…)` is the clearest CIC leak in *ordinary*
proofs — the opacity work this session put ~30 of them across Real/
Rational/PAdic order theory, well outside the foundational layer.

- **Characterizing-lemma registration.** Let an `opaque definition` declare
  its intro/elim characterizing lemmas. The elaborator auto-applies them at
  the fold/unfold boundary instead of the user narrating `unfold`.
- **Narrow auto-unfold.** When a leaf defeq check fails with one side
  headed by the opaque constant and the other being its unfolding, retry
  that *single* check with the constant transparent — never during general
  WHNF (which is exactly what opacity must prevent). This is a bounded,
  localized transparency, mirroring the manual wrap's scope.
- **Migration:** redo the `IsNonneg` opacity with zero use-site `unfold`;
  only the intro/elim lemmas themselves unfold.
- **Risk:** over-unfolding regressions → guard with the existing opacity
  tests + the leak linter.
- **Acceptance:** `unfold` count in user space → 0; `opaque.md` rewritten so
  the discipline is "declare characterizing lemmas," not "wrap each site."

### WS5. Finish transport / congruence
Extend the `by (<fact>)` / diff machinery we just built so the cases that
currently fall back to explicit lemmas disappear:
- Symmetry orientation (`by (a = b)` closing `b = a`).
- Multi-position congruence (more than one differing slot).
- Bounded combining: apply a one-step lemma whose premises are all
  present, so a stepping-stone fact closes a step without naming the lemma
  (the gap that sent us to `recalling`).
- **Acceptance:** the symmetry + stepping-stone tests that fail today pass;
  a measured drop in explicit `congruenceOf`/`transport_proposition`.

> **Status — in progress (2026-06).**
> - **Symmetry orientation DONE.** `tryDiffApplyUserProof`'s symmetric-match
>   branch was doubly broken (double-close of already-closed endpoints →
>   the historic "bare BoundVariable" malformed term, *plus* wrong
>   Equality.symmetry argument order) and had never run (calc matches
>   forward). Fixed: `theorem t (h : a = b) : b = a := h` and the
>   `by (a = b)` cited-fact form now close the flipped goal. Surfaced by the
>   WS8 coerce guard catching the malformed term in the wild. Tests in
>   `symmetry_flip_test`.
> - **Multi-position congruence (all facts in context)** already works via
>   the auto-prover.
> - **Migration sweep ESSENTIALLY DONE.** Equality.symmetry in user space
>   **184 → 119**; by-step sites **57 → 13**; total leak 681 → 616
>   (LEAK_BUDGET ratcheted to 616). ~20 files cleaned, including the big
>   three fully (group_lemmas 11, ring_lemmas 7, multiply_laws 11) and
>   group_action/irreducible (5 each). Pattern: structure a claim to match
>   the lemma's *un-flipped* conclusion (so bare `by <lemma>` infers args)
>   and let the body/case coercion do the final flip; ring-identity calc
>   steps go bare; remove → build → revert the congruence-nested ones.
>   **Last 13 cleared via a deeper fix.** Root cause: `tryDiffApplyUserProof`
>   has two callers passing `userProofType` in different representations —
>   the body/coercion path CLOSED (de Bruijn), the calc-step path OPENED
>   (named Internal FreeVariables). The symmetric-flip branch builds
>   `Equality.symmetry` directly from the endpoints, correct only when
>   CLOSED; for the calc caller the opened `@a`/`@e` leaked in (rejected by
>   `containsFreeVariable` → kept explicit symmetry). Fix: normalize the
>   endpoints to CLOSED at entry (`closeIfOpened`). All by-step sites then
>   flip; cleared by hand (some nested `by (calc …)` need parens to delimit
>   the inner calc from the outer). **User-space `by Equality.symmetry`: 0.**
>   Equality.symmetry total 184 → 109 (remaining are non-by-step: existential
>   `⟨⟩` components and other term positions that genuinely don't flip).
>   Leak total 681 → 606.
> - **Blocking bug FIXED (the leak).** Removing the explicit symmetry at a
>   calc step whose flip sits *under a congruence* (e.g. `epsilon - halve =
>   (halve + halve) + -halve`, where subtract WHNF-unfolds during the diff
>   descent) made `tryDiffApplyUserProof`'s symmetric-match + congruence
>   wrapping emit a term with an escaped *Internal FreeVariable* →
>   `kernel: unbound internal variable`. `tryDiffApplyUserProof` now rejects
>   a free-variable-containing result (`containsFreeVariable`; the
>   `maxFreeBoundVariable`/`inferType` guards missed it — opening over the
>   local binders re-supplies a same-named free var), and the calc-step
>   rewrite/diff fallbacks wrap their inference. Such a step now gives the
>   clean WS1 "different relation than the step claims" error. Regression:
>   corpus `calc_congruence_flip_unsupported`. The flip itself stays
>   *unsupported* for these sites (they keep explicit symmetry) — only the
>   leak is fixed; correct congruence-flip building is a deeper follow-up.
> - *Remaining:* **bounded combining** — a single cited fact bridging a
>   multi-position goal with the other facts pulled from context.

### WS4. Auto-prover completeness for "obvious" steps
Every step a mathematician calls trivial should close with no hint.
`autoProveClaim` is strong (equality battery, transitivity, context match,
library scan, conj/disj intro, contradiction) but not complete.
- Improve conclusion-shape lemma retrieval (the lemma index).
- Add bounded forward chaining (depth-1 lemmas with all premises in scope).
- **Hard constraint:** the prover is already perf-gated (redundant-by
  checks run behind flags). Every completeness gain must come with a
  measured time budget; no across-the-board slowdown of `make library`.
- **Acceptance:** the leak linter's "`by <lemma>` that the prover could
  close by-less" category shrinks, tracked as a metric.

---

## Phase 3 — Close the construction leak

### WS3. First-class quotient types
Today, constructing a quotient (Real, Rational, Integer, F_p, …) means
hand-writing the carrier, equivalence, and `Quotient.lift`/`.sound`/
`.induct`, and downstream code still names `Quotient.*` (short forms help
but don't hide it). The worst case is a binary operation: `Integer.add`
(`library/Integer/addition.math`) costs **six declarations** — the
componentwise formula, two per-argument respect lemmas each split into a
Natural-level kernel plus a destructure wrapper, an `add_after_first`
helper, an `add_after_first_respects` lemma, and finally `add` itself as a
nested `Quotient.lift`. The mathematical content is one line ("add the
difference-pairs componentwise; well-defined because the sums respect the
relation"); everything else is CIC bookkeeping forced by the absence of a
binary lift primitive.

#### The semantic spine: "pick a representative" is two distinct acts
This distinction is *mathematical*, not CIC noise, so the surface should
preserve it rather than paper over it:
- **In a proof** (goal is a `Proposition`): a representative may be picked
  *freely*, with no obligation — proof irrelevance means the proof can't
  observe which one. This is `Quotient.induct` / `by_representatives`, and
  it already reads well.
- **In a definition** (building a *value*): a representative may be used,
  but the author owes a proof that the result is independent of the choice
  — `Quotient.lift`, where the respect-proof is load-bearing content, not
  boilerplate.

**Design rule.** "Pick a representative" is always a *binder that scopes a
body*, never an expression that returns a value. A function
`representative_of(x) : T` must not exist — it is exactly the unsound
operation the kernel deliberately omits (`Logic/quotient.math:16-19`).
Mathematicians obey this too ("pick a representative `a` of `x`; … *and the
result is independent of the choice*"); the language just makes the
parenthetical a checked obligation.

#### Surface constructs
- **Quotient formation** — one declaration desugaring to the existing
  primitives, replacing the type def + `construction` intro + bundled-and-
  registered `IsEquivalenceRelation` instance that
  `library/Integer/basics.math:94-115` writes by hand:
  ```
  quotient Integer := IntegerRepresentative by IntegerEquivalent
    with equivalence ⟨…reflexive, …symmetric, …transitive⟩
    where class of (a b : Natural) := from_difference(a, b)
  ```
  Generates the carrier `definition`, the registered `equivalence`
  `instance` (so `Quotient.exact` resolves automatically), and the named
  class-former `construction`.
- **Representatives in proofs** — already ~80% done via
  `by_representatives`; remaining work is naming uniformity with the
  `class of` form. Low effort.
- **Define-by-representatives for functions** — the real prize. Write the
  per-representative formula plus a **mandatory** `well_defined by`:
  ```
  definition Integer.add : Integer → Integer → Integer
    by representatives ⟨a, b⟩, ⟨c, d⟩ ↦ from_difference(a + c, b + d)
    well_defined by Integer.add_respects

  theorem Integer.add_respects := …          -- proved right here
  ```
  The elaborator generates **one** well-definedness obligation as math —
  "if `⟨a,b⟩ ~ ⟨a',b'⟩` and `⟨c,d⟩ ~ ⟨c',d'⟩` then
  `⟨a+c,b+d⟩ ~ ⟨a'+c',b'+d'⟩`" — and synthesizes the entire nested-lift /
  `induct` / `sound` apparatus. Six declarations and zero `Quotient.` tokens collapse
  to one definition + one genuinely mathematical lemma. The obligation
  shape adapts to the codomain: a relation `R(f…, f…)` when the result is
  itself a quotient (elaborator inserts `Quotient.sound`), plain equality
  `f(…) = f(…)` when it is an ordinary type. We deliberately do **not**
  hide the well-definedness proof — that is the content a textbook also
  pauses on; we hide only the lift cascade.
- **Equality-of-classes** sugar hiding `Quotient.sound` — a `calc`/proof
  step reading "the classes are equal *since* `⟨a,b⟩ ≈ ⟨c,d⟩`", supplying
  the relation proof; the elaborator picks `sound`. (`Quotient.exact` is
  already near-invisible via implicit `T`/`R`/`equivalence`.)

#### `well_defined`: mandatory, name-or-inline, prove-after
- **Always required.** No omitted/implicit form, so the *claim* of well-
  definedness is never silent and sits at the definition site, matching how
  a careful text reads ("…this is well-defined (Lemma 2.4)").
- **Accepts an inline proof term** (one-liners) **or a name** (heavier
  proofs).
- **A named obligation may be proved on either side, with "right after" as
  the idiom.** "Before" is a trivial lookup. "After" needs deferred
  finalization: the respect proof is a genuine argument inside the `lift`
  term, so the kernel can't seal the value until it exists. The elaborator
  therefore (1) computes the obligation's *type* from the formula and
  registers `Integer.add` as **pending** keyed on the name, (2) elaborates
  the following `theorem` against that auto-generated goal, (3) finalizes
  the pending definition once the proof is added. The only new user-visible
  rule: `Integer.add` cannot be *used* in the gap between its definition
  and its obligation proof — and the error there is math-shaped ("not yet
  well-defined; prove `Integer.add_respects` first"), never CIC. Nothing
  normally lives in that gap.
- **Why this is safe (proof irrelevance).** The obligation lands in `Prop`,
  and the kernel's `lift`-on-`mk` reduction ignores the proof argument
  (`Logic/quotient.math:9-13`). *Which* proof discharges `well_defined`
  never affects how `Integer.add` computes, so deferring finalization can't
  change the definition's meaning — only satisfy the kernel's bookkeeping.
- **Open sub-decision (for implementation, not now):** whether the
  obligation `theorem` must restate its type or may be written bare
  (`theorem Integer.add_respects := <proof>`). Lean: optional, checked-if-
  present.

#### Boundary, migration, acceptance
- All four constructs live in the elaborator and desugar to today's
  primitives — **no kernel change**. The one defining file per type stays
  on the foundational-layer manifest and may keep `Quotient.` as an escape
  hatch; everything downstream hits zero `Quotient.`/`unfold` tokens.
- **Migration:** re-express one constructed type (Integer is the hardest
  case because of binary `add`; clearing it means the n-ary ring laws
  follow — Rational is a gentler alternative) with zero `Quotient.` tokens
  outside the one definition file.
- **Acceptance:** a *new* quotient type + its basic theory provable with the
  token `Quotient` appearing only in the foundational layer.

### WS6. Universe transparency
- Audit where `Sort`/levels surface (errors, definitions needing
  annotations).
- Strengthen inference so ordinary library files need no universe
  annotations; suppress universe detail from errors unless genuinely
  ambiguous (ties to WS1).
- **Acceptance:** no universe annotations in user space; no `Sort`/level in
  the error golden corpus.

---

## Phase 4 — The foundational remainder (ongoing, partly irreducible)

### WS7. A `Prop`/`Type` story
The known quirks (`~/.../memory/kernel_quirks.md`): no large elimination
from `Prop`, function-wrapping for `cases`-on-expression, the `¬¬` dance,
identical-printed-type universe confusion.
- **Hide what's mechanical:** auto-insert the function-wrapping for
  `cases`-on-expression; keep widening the classical/`decide` bridge so the
  `¬¬` dance stays out of user proofs.
- **Name what's semantic:** where a CIC restriction genuinely blocks a
  construction, emit a *math-facing* explanation ("a proof can't be used to
  build data here") rather than a CIC error — this is WS1 applied to the
  elimination rules.
- **Document the irreducible:** a short "what CIC still imposes" note, so a
  foundation-builder hits a *documented, expected* wall, not a surprise.
- **Acceptance:** each known quirk is either auto-handled or produces a
  clear surface explanation; the wall is documented, not jagged.

---

## Sequencing rationale & estimated movement

| Phase | Workstreams | "Using" | "Building" |
|-------|-------------|---------|------------|
| baseline | — | ~82% | ~50% |
| 1 | WS1 authoritative kernel boundary, WS8 hardening, WS0 metrics | ~88% | ~55% |
| 2 | WS2 kill-`unfold`, WS5 transport, WS4 prover | ~95% | ~65% |
| 3 | WS3 quotient types, WS6 universes | ~97% | ~80% |
| 4 | WS7 Prop/Type | ~98% | ~85% (asymptote) |

Do Phase 1 first: it is the cheapest, lowest-risk, and most *perceptible*
(every stuck user immediately sees math instead of CIC), and WS0/WS8
establish the measurement and safety net the later, riskier surgery needs.

## Risks
- **Over-unfolding (WS2)** — the exact failure opacity prevents; gate behind
  leaf-only transparency + opacity tests.
- **Prover slowdown (WS4)** — perf-sensitive; budget every gain.
- **Quotient-sugar scope (WS3)** — a large surface+elaborator change; land
  behind a migration of one type before generalizing.
- **Asymptote (WS7)** — set expectations: the foundation-builder's CIC
  exposure shrinks to a documented minimum but does not vanish.

## Definition of done (north star)
1. **Using corpus** — a representative theorem set with a *zero* leak-linter
   count, enforced in CI.
2. **Building test** — define a fresh quotient type and its basic theory
   with no `Quotient.`/`unfold` outside its one foundational file.
3. **Error audit** — the mistake corpus is entirely CIC-free.
4. **Foundational layer** — the manifest is bounded and shrinking; all
   files above it are CIC-free in both code and diagnostics.

---

## Appendix A — WS1 implementation notes (concrete deferral sites)

Captured while the elaborator internals were warm (the `by (<fact>)`
session). Line numbers are approximate — grep the quoted strings.

### The provenance chokepoint already exists
`rethrowKernelError` (`elaborator.cpp:906`) is the **single** place a kernel
`TypeError` is converted into a user-facing `ElaborateError`. It already:
- prefixes the message with `"kernel: "`,
- surface-renders the embedded `expectedType`/`actualType` via
  `prettyPrintForDisplay` (so the *types* are already math-shaped),
- anchors the source position at the innermost frame.

What it does **not** do is re-author the kernel's *message text* — it passes
`error.what()` through verbatim. So **the `"kernel: "` prefix is the
de-facto provenance tag** WS0.3 asks for: any user-facing error containing
`"kernel: "` is a deferral gap. Cheap first move: assert/lint that no error
shown to a user contains `"kernel: "`, then drive that count to zero.

Call sites that funnel into it (each a deferral point to audit):
`elaborator.cpp:1408, 1850, 1884, 2349, 2816, 2822, 2825, 3595, 8626, …`
(grep `rethrowKernelError`). Each wraps a `try { …kernel call… } catch
(TypeError&)` — i.e. a spot where the elaborator hands the kernel a term and
lets it check first.

### Bucket B — the three CIC-shaped messages and their sources
- **"Application: function is not of Pi type"** — `kernel.cpp:1794`, thrown
  by `inferType` on an `Application` whose function's type isn't a `Pi`.
  Elaborator path: `SurfaceApplication` dispatch at `elaborator.cpp:1691`
  builds the application and defers. *Fix:* before assembling, check the
  function's inferred type WHNFs to a `Pi`; else surface error ("you're
  applying this as a function, but it has type `T`").
- **"Application: argument type does not match Pi domain"** —
  `kernel.cpp:1801`. *Fix:* check the argument's type against the (meta-
  substituted) domain in the elaborator. Note there is **already a
  precedent**: `elaborator.cpp:18887–18895` pre-empts exactly this message
  in the `cases`/refining path — model the general fix on it.
- **"addDefinition: body type does not match declared type"** —
  `kernel.cpp:1889`. The elaborator should compare the proof's inferred type
  to the declared theorem type itself (a surface diff) before calling
  `addDefinition`. This is the "body doesn't match" leak from the Rational
  opacity work.

### Bucket A — malformed terms (never user-facing)
- **"internal: bare BoundVariable reached inferType"** — `kernel.cpp:1675`.
  An elaborator bug producing an ill-formed term (hit this session via
  `coerceToExpectedTypeViaDiff` returning a malformed result on a symmetry
  diff). `assertClosedOverLocalBinders` already guards
  `inferTypeInLocalContext`'s entry (`elaborator.cpp`, search the helper);
  thread it through the other movers and pin
  `coerceToExpectedTypeViaDiff`'s contract (WS8).

### What is already surface-good (don't touch)
- Embedded type rendering: `prettyPrintForDisplay` /
  `prettyPrintInLocalScope`; `Sort 0` already prints as `Proposition`
  (`printer.cpp:114`).
- Auto-prover failure text: `autoProveClaim`'s "no in-scope hypothesis
  matches… no library theorem with this conclusion shape applies" and
  `couldNotProveStepHint`. These are the bar; WS1 brings the term-elaborator
  and definition paths up to it.

### Suggested first PR (Phase 0 + start of WS1)
1. Lint: no user-facing error contains `"kernel: "` (turns every deferral
   gap into a failing case in the WS0.3 corpus).
2. Close the **application** gap (`elaborator.cpp:1691`) — highest-frequency
   source, and `18887` shows the pattern.
3. Close the **addDefinition** gap.
Leave WS2+ for later phases; these three make the common leaks math-shaped.

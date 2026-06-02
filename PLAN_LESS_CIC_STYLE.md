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
but don't hide it).

- **Surface construct:** `definition Real := quotient of CauchySequence by CauchyEquivalent`
  desugaring to the existing primitives, and generating math-named
  operations:
  - the constructor (`mk`, already short-formed),
  - a `by_representatives` eliminator under a math name,
  - **define-by-representatives** for functions: write `f` on a rep + a
    respect proof; the lift is synthesized and hidden,
  - **equality-of-classes** sugar hiding `Quotient.sound` ("these two
    representatives are equal because `~` holds").
- **Migration:** re-express one constructed type (Rational is a good size)
  with zero `Quotient.` tokens outside the one definition file.
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

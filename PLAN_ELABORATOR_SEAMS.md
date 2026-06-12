# PLAN: two elaborator seams — error locations & citation defeq

Scoped infrastructure work that gates the ℂ analysis layer and the
"templates" (generic quadratic-extension / valued-field) direction.
Decided 2026-06-12 after the ComplexNumber coordinate port hit both
seams; the complex-exponential push resumes when this lands.

Two fixes, in order of increasing risk. A third item is investigation
only. Both bugs have verbatim entries in `docs/error_message_inbox.md`
(2026-06-12, "ℂ coordinates"); move them to `docs/error_message_corpus.md`
with resolutions when done.

---

## Fix A (low risk): statement-pass errors lose their location

### Symptom (reproduced 2026-06-12)

```
library/ComplexNumber/defining_polynomial_vanishes.math:1:1: type error: Application: argument type does not match Pi domain
  expected type: Ring
  actual type:   Real
```

No declaration name, no line, no offending expression. The actual culprit
was `p + q` in the STATEMENT of `coordinatesOfPolynomial_add` with binders
spelled `Polynomial(Real, Real.zero)` — found by bisecting the file
theorem-by-theorem. Any error whose location prints as `1:1` has lost its
position.

### Where

- The kernel throws `TypeError("Application: argument type does not match
  Pi domain")` at `src/kernel/kernel.cpp:1874` — kernel TypeErrors carry
  types but no surface location.
- `src/elaborator/internal.hpp:508` re-renders kernel TypeErrors for
  display ("this argument has the wrong type for the function it is given
  to") — this path plainly CAN run (the derivative-era errors show it),
  so find why the statements pass bypasses it.
- The statements-only pass is selected via `MATH_STATEMENTS_ONLY`
  (`src/main.cpp:5490`, `src/elaborator/internal.hpp:100`). Hypothesis:
  during statement elaboration (signature/Pi-telescope checking) the
  TypeError escapes without being wrapped in the elaborate-error context
  stack that proof-body errors get (the "theorem 'X' / claim at line N"
  breadcrumbs), so the driver reports it at file scope with a default
  SourceLocation (1:1).

### Fix

Wrap statement elaboration (the per-declaration signature pass) in the
same error-context mechanism proof bodies use, so every escaping
TypeError/ElaborateError gains at least:
  - `theorem '<qualified name>'` (or definition/axiom) breadcrumb, and
  - the source span of the declaration header (better: of the application
    being elaborated, if the surface node is at hand when the kernel call
    is made).
Also audit: grep the driver for other places a default `SourceLocation`
can reach the printer; any error that would print `1:1` on a non-empty
file should be impossible by construction.

### Acceptance

- The repro above reports the file, the theorem name
  (`coordinatesOfPolynomial_add`-equivalent), and a line inside its
  statement; the friendly "this argument has the wrong type…" rendering
  from internal.hpp:508 is used (not the raw kernel string).
- New corpus/error-test entry per the `docs/error_message_corpus.md`
  workflow (the error-test suite from the usability campaign).
- No library/test regressions (pure reporting change).

---

## Fix B (the big one): citation matching can't see defeq that prover
## search can

### Symptom (reproduced 2026-06-12, twice)

With `k : Polynomial.Coefficients(Real)` and facts in scope:

```
claim Polynomial.ExtensionallyEqual(Real, Real.zero,
          Polynomial.Coefficients.multiply(Real.ring, one, k), k)
    since Polynomial.Coefficients.multiply_one_left;       -- FAILS
```
```
  the `Polynomial.Coefficients.multiply_one_left` citation does not prove this goal
    goal:        … ExtensionallyEqual Real Real.zero (Real.ring * one k) k
    `…multiply_one_left` has type: (r : Ring) → … ExtensionallyEqual (Ring.carrier r) (Ring.zero r) …
```

The same claim:
  - with explicit arguments `by multiply_one_left(Real.ring, k)` — WORKS
    (application typechecking is defeq);
  - completely BARE — WORKS (auto-prover search applies the same lemma).

So `Ring.carrier(Real.ring) ≡ Real` and `Ring.zero(Real.ring) ≡ Real.zero`
(both plain ι-reductions of a projection applied to `Ring.make(...)`) are
visible to application checking and to search, but invisible to the
citation matcher. Consequences observed in practice:
  - hint-less is strictly MORE capable than hinted — inverts the hint
    model and fights the style guide (which wants `since <lemma>`);
  - the redundancy checker's "redundant `by`" finding was the only
    discovery mechanism;
  - it blocks the generic/"template" direction: any lemma stated over
    `Ring.carrier(r)` is uncitable at concrete instances.

Same root cause family as the stale-cache confusion already fixed in
message only (2026-06-12 inbox entry, "arguments could not be inferred"
when the lemma was UNKNOWN — re-check that unknown-name detection now
precedes unification; if not, fold it into this fix).

### Where

- The first-order matcher: `matchAgainstPattern(pattern, subject,
  binderCount, bindings, piDepth)` in `src/elaborator/internal.hpp:1923`,
  ~24 call sites across `src/elaborator/*.cpp` (citations in
  inference.cpp, claim.cpp; calc steps; rewrite; lemma_index/lemma_search
  use a fingerprint-y variant — check whether the lemma INDEX also needs
  the same normalization so search and citation agree).
- The citation failure message: `src/elaborator/inference.cpp:848–880`.

### Design

On rigid–rigid mismatch inside `matchAgainstPattern`, before failing,
attempt a BOUNDED reduction step on whichever side is reducible, then
retry the node:

1. Scope of reduction — deliberately narrow, not full whnf:
   - ι-reduce a projection/eliminator applied to a literal constructor
     (`Ring.carrier(Ring.make(T, …)) → T`, `Ring.zero(Ring.make(…)) → z`);
   - δ-unfold a definition whose body is a constructor application
     (`Real.ring → Ring.make(…)`) ONLY when it feeds case (a) — i.e.
     unfold-then-project, the exact `Ring.carrier(Real.ring) → Real`
     chain. (A reducibility whitelist keyed on "definition with
     constructor-headed body" avoids unfolding e.g. recursive functions
     and keeps the matcher fast and predictable.)
2. Apply the same normalization to BOTH pattern and subject heads
   (the seam appears in both directions: lemma-side `Ring.carrier(r)`
   with `r := Real.ring` bound by an earlier slot, and goal-side
   concrete spellings).
3. Memoize per-node within one match attempt if profiling demands it;
   measure before adding caches.
4. Leave higher-order/Miller gaps alone — this fix is NOT general
   defeq-unification, just projection-chain transparency. Function-
   parameter lemmas keep needing positional citation (documented
   behaviour, see `lemma_search_tool` / Miller notes).

Decide-and-document: does the fix also apply to the metavariable
OCCURS/range check and to `referencesAnyBoundInRange` interplay
(internal.hpp:1932)? Bindings produced after normalization must be
expressed in the subject's scope exactly as before.

### Risks & mitigations

- **Performance**: matching runs in hot loops (lemma index sweeps).
  Mitigate: reduction attempted only on the failure path of a node, the
  whitelist above, and compare wall-clock of `make -j 16 library` before
  vs after (warm). Watch for new "expensive by-less proof step" warnings
  appearing/disappearing.
- **Behaviour change / over-matching**: previously-failing citations now
  succeed — that is the point — but previously-AMBIGUOUS situations may
  change (ambiguity-as-error machinery from the usability campaign).
  A full clean rebuild re-verifies every proof; treat any new ambiguity
  errors as findings to triage, not auto-fix.
- **Whole-library reverify + OOM**: kernel/elaborator edits invalidate
  every `.mathv`. Use `.mwatch.sh` watchdog; see
  `build_oom_and_cache_invalidation` memory. Validate with clean
  `make -j 16 library` AND `make -j 16 tests`.
- The elaborator class is mid-refactor (`elaborator_split_status`
  memory): prefer extending in place over starting a module extraction
  in the same change.

### Acceptance

- New feature test `library/Test/citation_carrier_defeq_test.math`:
  a goal stated with `(Integer, Integer.zero)` spelling citing
  `Polynomial.Coefficients.multiply_one_left` argument-free via `since`
  and via `by` (note: ℤ has the same seam — the GaussianInteger originals
  always cited positionally; ℤ makes a lighter test than ℝ).
- The ComplexNumber workaround sites can be (but don't have to be)
  reverted to `since <lemma>` form:
  `library/ComplexNumber/defining_polynomial_vanishes.math` (3 bare
  claims + 3 bare calc steps in `coordinatesOfPolynomial_times_x`),
  `library/ComplexNumber/reconstruction.math` `x_times_make` (3
  positional claims). Reverting at least one site IS the end-to-end test.
- Full library + tests green; build time within noise of baseline.
- Inbox entries promoted to corpus with the resolution recorded.

---

## Item C (investigation only — do NOT fix unless trivial):
## operator dispatch through the same defeq

`p + q` dispatches at `(p q : Polynomial(Integer, Integer.zero))`
(GaussianInteger files) but NOT at `Polynomial(Real, Real.zero)`
(the Fix-A repro), where the resolver apparently passes the carrier
type itself as the `Ring` argument. Explain the asymmetry (an
Integer-specific instance? registration order? `dispatch.cpp`), write
the finding into the plan/corpus, and decide whether Fix B's
normalization belongs in dispatch too. The carrier-spelling convention
(`Polynomial(Ring.carrier(Real.ring), …)`, used by all ComplexNumber
files) remains the documented style either way.

### FINDING (2026-06-12, investigated alongside Fix B — explained, not fixed)

The asymmetry is **an Integer-specific instance registration**, nothing
in `dispatch.cpp`'s ordering:

1. Target resolution is symmetric. `desugarArithmeticOperator`
   (desugar_equality.cpp) finds `Polynomial.add` from the registry key
   `(+, Polynomial, Polynomial)` for BOTH spellings.
2. The asymmetry is in filling `Polynomial.add`'s implicit `{r : Ring}`:
   the left operand's type is unified against the declared
   first-explicit-argument template
   `Polynomial(Ring.carrier(r), Ring.zero(r))` via `matchAgainstPattern`.
   At the node `Ring.carrier(BV r)` vs the concrete carrier, the
   canonical-bundle registry decides: `(Ring, Integer) →
   Integer.ring_bundle` is registered (`instance Integer.ring_bundle`,
   Algebra/integer_domain.math), so ℤ resolves; **`Real.ring` is defined
   (ComplexNumber/basics.math) but never `instance`-registered**, so
   `(Ring, Real)` misses and unification fails.
3. The "passes the carrier type itself" symptom is the explicit
   single-filler fallback at desugar_equality.cpp (`// Fall back to the
   single-filler heuristic for safety`): it knowingly applies a junk
   filler (the last argument of the operand's type — `Real.zero`, whose
   type `Real` is what the kernel then reports against the expected
   `Ring`) and lets the kernel typecheck catch it. With Fix A that
   kernel error is now anchored at the declaration instead of 1:1.

**Does Fix B's normalization belong in dispatch? No.** Fix B's deferral
works because a lemma's *conclusion* contains a binding argument
(`multiply(Real.ring, …)`) that pins `r`, after which the deferred
projection nodes verify definitionally. A dispatch *type template*
`Polynomial(Ring.carrier(r), Ring.zero(r))` mentions `r` only under
projections — there is nothing to defer against, so deferral would end
with `r` unbound and fall back to the same registry miss. The registry
IS the mechanism for recovering a bundle from a concrete carrier.

**The available fix is a library one-liner, deliberately not applied
here:** `instance Real.ring` makes `p + q` dispatch at
`Polynomial(Real, Real.zero)` (verified empirically, 2026-06-12, probe
with the instance + `p + q` statement). Whether ℝ should register its
bundle — and the ComplexNumber files then shed the
`Polynomial(Ring.carrier(Real.ring), …)` carrier spelling — is a
library-design decision for the complex-exponential push to make. Until
then the carrier-spelling convention remains the documented style.

---

## Validation protocol (both fixes)

1. `make -j 16 library` and `make -j 16 tests` from a CLEAN cache —
   elaborator changes re-verify everything; expect minutes, run the
   watchdog.
2. Error-test suite green (corpus workflow in
   `docs/error_message_corpus.md`).
3. Redundancy-check spot-run on 2–3 analysis files to confirm no new
   expensive-step warnings.
4. Commit separately: Fix A, then Fix B, then any workaround reverts.

## Memory/notes to read first

- `kernel_quirks`, `elaborator_split_status`,
  `build_oom_and_cache_invalidation`, `elaborator_usability_campaign`
  (error-test mechanics), `real_analysis_arc` (the 2026-06-12 sections
  record both seams with context).
- `docs/error_message_inbox.md` — the two 2026-06-12 "ℂ coordinates"
  entries are the source of truth for the symptoms.

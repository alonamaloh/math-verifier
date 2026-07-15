# Investigation handoff — the "Spans fold-desync" citation bug

**Status:** root cause pinned, NOT fixed. Kernel/library are at a clean green
commit; no source changes are staged. This file is the complete handoff.

## The observable symptom

`X by <Lemma>` / `done by <Lemma>` fails when `<Lemma>`'s conclusion is a named
predicate that δ-unfolds to `Or`/`∀`/`Exists`/`And` — e.g. `VectorSpace.Spans`
(`∀ v. v = 0 ∨ ∃ …`). The error reads:

```
the `Subspace.spans_of_value_covered` citation does not prove this goal
  goal:        VectorSpace.Spans (λ …)
  `…` has type: VectorSpace.Spans f (Subspace.vector_space f V subset sub) (NaturalsBelow 1) (λ …)
  its conclusion is about `Or` but the goal is about `VectorSpace.Spans` …
  the `by` proof elaborated but has type: VectorSpace.Spans f (…) (…) (λ …)
```

It bit `LinearMap.appended_images_span` in `library/Algebra/rank_nullity.math`;
the workaround there was to prove `Spans` via an explicit `take x` block instead
of citing the lemma. The goal is to remove that class of workaround.

## THE ROOT CAUSE (pinned by instrumentation — do not re-derive)

The `"conclusion is about Or"` message is a **downstream symptom**. The real bug
is UPSTREAM of the citation dispatch:

**The goal (and the theorem's declared type) `Spans(fam)` is built as the
malformed partial application `App(Spans, fam)` — the leading implicit arguments
`{f}{V}{I}` are NEVER inserted.** `Spans` expects `{f}{V}{I}(family)`; the stored
goal applies it to just `fam`, i.e. `fam` lands in the `{f : Field}` slot.
`inferType` on that goal throws *"Application: argument type does not match Pi
domain — expects Field"*.

Verified by dumping the application spine at the last-ditch citation path
(`src/elaborator/inference.cpp`, the `try` block that starts ~line 1405 with
`coerceToExpectedTypeViaDiff` / prints `"the \`by\` proof elaborated but has
type"`):

```
TERMTYPE head=VectorSpace.Spans nargs=4   (f, Subspace.vector_space…, NaturalsBelow 1, λ)
GOALOPEN  head=VectorSpace.Spans nargs=1   (just λ)
defeq = 0
```

So `isDefinitionallyEqual(termType, goal)` is `false` purely because the goal is a
1-arg malformed application while the term is the correct 4-arg one. Any
citation-level "accept if defeq" or head-matching fix is defeated by this: the
declared type itself is malformed, so accepting the correct term just moves the
failure to the theorem's final declared-type check (*"expects Field"*).

### Why implicit insertion fails here

`Spans`'s implicit `{V}` must be solved from the family's codomain:
`carrier(?V) ≟ codomain(fam)`. When the family is built with `Subtype.make(…)`,
its codomain is a raw `Subtype(carrier(W), subset)`, and solving `carrier(?V) ≟
Subtype(carrier(W), subset)` is a higher-order inversion (invert `carrier`) the
elaborator does not do. Instead of erroring OR keeping `?V` as a metavar, it
emits the implicit-less `App(Spans, fam)`.

### The two sub-cases (important — they behave differently)

1. **Family codomain is a raw `Subtype`** (inline `Subtype.make` lambda, or a
   param declared `… → Subtype(carrier V, s)`): `{V}` is un-inferrable ⇒ the
   DECLARED TYPE itself is malformed ⇒ the theorem is genuinely un-declarable
   this way. A citation fix cannot save it; this input arguably SHOULD error
   clearly ("could not infer implicit space of `Spans`").
2. **Family codomain is a literal `carrier(SomeSpace)`** (e.g. a param typed
   `NaturalsBelow(r) → carrier(Subspace.vector_space(W, image, imgSub))`): `{V}`
   IS inferred ⇒ declared type is well-typed (nargs=4) ⇒ the citation SHOULD
   succeed. **This is the case worth fixing at the citation level.** (The current
   `rank_nullity` spanning lemma is this shape but ALSO trips a separate issue —
   see "third overlapping issue" below — which is why `take x` was kept.)

## Candidate fixes (in priority order)

- **(Primary, the real fix) Insert leading implicits when the goal/declared type
  is constructed from the surface conclusion.** Find WHERE a claim's / theorem
  conclusion's goal is built from the surface `Spans(fam)` and ensure standard
  implicit-argument insertion runs (insert `{f}{V}{I}` as metavars, solve what
  can be solved, keep the rest as metavars — do NOT emit `App(Spans, fam)`).
  Start points: `src/elaborator/statements.cpp` (theorem-type / conclusion
  elaboration, e.g. around the "leading implicit `{…}` binders in the SURFACE
  type" comment ~line 903), and `src/elaborator/dispatch.cpp:489` ("insert the
  implicit prefix as metavariables and solve them"). Grep for where the goal for
  a `done`/claim is created. If the goal carries proper metavars, the citation
  symptom likely vanishes on its own.
- **(Helps case 1's declaration, general) carrier-inversion in unification.**
  Teach the unifier to solve `carrier(?V) ≡ Subtype(carrier(W), s)` as
  `?V := Subspace.vector_space(W, s, ?p)` (`?p` a proof-irrelevant hole), because
  `carrier(Subspace.vector_space(W,s,p))` reduces to `Subtype(carrier(W), s)`.
  Makes even the raw-`Subtype`-codomain families inferrable.
- **(Safety net, cheap) fail loudly.** If a leading implicit stays unsolved when
  building a goal/declared type, raise `"could not infer implicit {V} of Spans —
  annotate the family's type"` instead of producing a malformed application (and
  instead of the misleading `Or`-vs-`Spans` message downstream).
- **(Citation-level, only helps case 2) spine-prefix acceptance.** In
  `inference.cpp`'s last-ditch, if the elaborated term's type head == goal head
  and every argument the goal SUPPLIED (outermost-first prefix) is defeq to the
  term type's corresponding argument, accept the term. I implemented this; it
  correctly stops rejecting case 2, but is moot until case 2's goal is well-typed
  AND the third issue below is resolved. Keep as a fallback, not the main fix.

## A THIRD, overlapping issue (do not conflate with the above)

Even with a well-typed `carrier`-codomain family, `done by
spans_of_value_covered(subset, sub, TaFamily, coveredFact)` also fails on the
`covered` ARGUMENT: the lemma expects `covered : ∀ x. … InSpanOf((i)↦
Subtype.value(TaFamily(i)), value x)` but `coveredFact` supplies `InSpanOf((j)↦
T(aFamily(j)), …)`. These are defeq (`value(TaFamily j)` reduces to `T(aFamily
j)`) but the function-argument check does not accept the higher-order defeq under
the binder. This is friction item #2 from the session (arguably an inherent
limit), separate from the implicit-insertion bug. A full "remove the `take x`
workaround" needs BOTH resolved.

## Reproductions (self-contained; verify with the cache)

Run: `./kernel verify --source REPRO.math --output /tmp/out.mathv --cache-root
build/library` (library must be freshly built by the kernel under test).

### Repro A — well-typed declaration, inline `Subtype.make` family (case 2 / the real shape)
```math
module Test.faithful
import Logic.basics
import Logic.exists
import Equality.basics
import Natural.basics
import Set.subtype
import Set.finite
import Algebra.field
import Algebra.vector_space
import Algebra.subspace
import Algebra.linear_combination
import Algebra.span
import Algebra.rank_nullity

theorem faithful {f : Field} (V : VectorSpace(f))
        (subset : Set(VectorSpace.carrier(V))) (sub : IsSubspace(V, subset))
        (covered : ∀ (x : VectorSpace.carrier(Subspace.vector_space(V, subset, sub))).
            Subtype.value(x) = VectorSpace.zero(V)
            ∨ VectorSpace.InSpanOf(
                  (i : NaturalsBelow(1)) ↦ Subtype.value(Subtype.make(VectorSpace.carrier(V), subset,
                      VectorSpace.zero(V), IsSubspace.contains_zero(sub))),
                  Subtype.value(x)))
        : VectorSpace.Spans((i : NaturalsBelow(1)) ↦ Subtype.make(VectorSpace.carrier(V), subset,
              VectorSpace.zero(V), IsSubspace.contains_zero(sub))) := {
  done by Subspace.spans_of_value_covered(subset, sub,
      ((i : NaturalsBelow(1)) ↦ Subtype.make(VectorSpace.carrier(V), subset,
          VectorSpace.zero(V), IsSubspace.contains_zero(sub))),
      covered)
}
```
Current behavior: `"conclusion is about Or …"`. Desired: compiles.

### Diagnostic technique that worked
Temporarily add, in `inference.cpp` at the last-ditch `try` block (before
`coerceToExpectedTypeViaDiff`), a spine dump of `inferType(directElaborated)` and
`goalOpened` (walk `Application` nodes, print `headConstantName` + arg count +
`prettyPrintInLocalScope`). That is how the nargs=1-vs-4 mismatch was found.

## Validation plan (the "doesn't break anything" gate)
1. Land the repro(s) as permanent tests (`Test/…` if it should pass, or
   `ErrorTest/…` if the chosen behavior is a clear error message).
2. `make -j 16 tests` AND `make -j 16 export-check` green (an elaborator change
   re-verifies the WHOLE library — always cap memory: `ulimit -v 12000000`, or
   16000000 for export-check).
3. Axiom inventory unchanged (export-check prints it).
4. **Acid test:** in `library/Algebra/rank_nullity.math`, revert
   `LinearMap.appended_images_span`'s `take x` block to a clean `done by
   Subspace.spans_of_value_covered(...)` and confirm it compiles — proves the fix
   hits the real case, not just the repro. (Needs the third issue handled too.)
5. Redundancy / clean-check pass; commit kernel + tests + simplified proof.

## Owner constraints
- NEVER edit `.math`/source with sed/perl/python — use the Edit tool. (Scratch
  repro files under a scratchpad are fine.)
- Always `ulimit -v` kernel/make runs.
- `make -j 16 library` from repo root; a `.cpp` change re-verifies everything.

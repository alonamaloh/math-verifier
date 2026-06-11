# Error-message inbox (append-only capture log)

Raw, untriaged captures of error messages we hit while working — recorded
by `scripts/record_error.sh <file.math> [note]` so nothing is lost while
the context is fresh. This file is a SCRATCH log, not a curated document.

Workflow:
1. Hit a confusing (or surprisingly good) error → `scripts/record_error.sh
   path/to/repro.math "what I was trying to do"`. It appends the verbatim
   output plus a blank `diagnosis:` here.
2. When you understand it, **promote** it into
   `docs/error_message_corpus.md` (diagnosis + 5-axis rubric score +
   status), and delete the inbox entry.
3. When fixed, add a regression case under `library/ErrorTest/` and run
   `make error-tests`.

Keep entries here only until triaged — the corpus is the durable record.

<!-- captures are appended below this line -->

### library/ErrorTest/probe_obtain_arity.math — 2026-06-07 22:28:55 (exit 1)
note: obtain with too many components (∃q.n=d*q has 2, gave 3)
```
$ ./kernel verify --source library/ErrorTest/probe_obtain_arity.math --cache-root build
library/ErrorTest/probe_obtain_arity.math:1:1: elaborate error: cases at line 7: index 0 of scrutinee type must be a local variable
```
diagnosis: the `obtain ⟨q, r, extra⟩` pattern has MORE components than the
  existential provides (∃q. n=d*q = ⟨witness, proof⟩, 2 components); the extra
  destructure of the equality proof fails, surfacing the internal refining
  message "index 0 of scrutinee type must be a local variable". Real problem =
  destructuring-pattern arity mismatch. Wanted: "obtain pattern has 3 components
  but `d ∣ n` provides 2". FIX UNCERTAIN (obtain → nested-cases desugar) — collect more.
rubric (0/1): cause · location · actionable · folded-types · no-jargon

---

### library/ErrorTest/probe_hole_in_tuple.math — 2026-06-07 22:33:27 (exit 1)
note: ? in an And-tuple proof slot (entry #7); contrast: ? works in constructor arg positions
```
$ ./kernel verify --source library/ErrorTest/probe_hole_in_tuple.math --cache-root build
library/ErrorTest/probe_hole_in_tuple.math:7:3: elaborate error: theorem 'ErrorTest.p'
  call to 'And.introduction' at line 8: could not infer hole(s) at position 1
  expected return type: And (zero ≤ a) (zero ≤ a)
  Provide the missing argument(s) explicitly to disambiguate.
```
diagnosis: TODO — what was the *real* problem?
rubric (0/1): cause · location · actionable · folded-types · no-jargon

---


### Real/continuity.math (mid-development) — 2026-06-11 (hand-recorded, IVT push)
note: citation unification does not see through a local `let` abbreviation
```
library/Real/continuity.math:95:3: elaborate error: claim at line 106
  ...
  the `Rational.minimum_positive` citation does not prove this goal
    goal:        Rational.zero < delta
    `Rational.minimum_positive` has type: (a : Rational) → (b : Rational) → Rational.zero < a → Rational.zero < b → Rational.zero < (Rational.minimum a b)
  the hint's arguments could not be inferred from the goal or discharged from context, ...
```
diagnosis: `delta` was `let delta : Rational := Rational.minimum(fDelta, gDelta);`
  — ζ-tracked, kernel-transparent, but the goal-driven citation unifier matches
  SYNTACTICALLY and never unfolds the let, so `zero < delta` fails against
  `zero < minimum(a, b)`. The message shows goal + lemma type (good) but the
  *cause* — "the goal contains a let-bound abbreviation the matcher does not
  unfold" — is invisible; user must guess. Fix options: ζ-expand let-bindings
  during citation unification (preferred — `let` is documented as transparent),
  or say so in the message. Same root cause also breaks `cases`/`obtain`
  normalization (next entry).
rubric (0/1): cause 0 · location 1 · actionable 0 · folded-types 1 · no-jargon 1

---

### Real/intermediate_value.math (mid-development) — 2026-06-11 (hand-recorded, IVT push)
note: obtain/cases scrutinee normalisation stops at a local `let`-bound Set
```
library/Real/intermediate_value.math:1:1: elaborate error: cases scrutinee at line 78: type's head is not an inductive constant after normalisation
```
diagnosis: `obtain ⟨_, yRest⟩ from yInCandidates;` where
  `yInCandidates : y ∈ candidates` and `candidates` was a local
  `let candidates : Set(Real) := Real.intermediate_value_candidates(f, a, b);`.
  WHNF unfolds Set.member → candidates(y) and then stops: the let-binder is
  not δ-unfolded, so the And never surfaces. Replacing the let with the full
  definition application fixed it. Also: error location is 1:1 + "line 78",
  not the obtain's column; "inductive constant" is kernel jargon; no hint that
  the let was the blocker. (Same ζ-opacity family as the citation entry above.)
rubric (0/1): cause 0 · location 0 · actionable 0 · folded-types 1 · no-jargon 0

---

### Real/intermediate_value.math (mid-development) — 2026-06-11 (hand-recorded, IVT push)
note: `claim X by decide P { … }` (and `by { decide … }`) rejected as a failed *citation*
```
library/Real/intermediate_value.math:69:3: elaborate error: claim at line 92
  ...
  the `by` hint citation does not prove this goal
    goal:        f c ≤ Real.zero
  the hint's arguments could not be inferred from the goal or discharged from context, ...
```
diagnosis: the claim's `by`-payload was a structural proof form
  (`decide P { | yes … | no … }`), not a citation — but the hint parser/
  dispatcher fell through to the citation path and reported a unification
  failure with no inner detail. Wrapping in `{ … }` failed identically.
  `by cases { case P as h: … case Not(P) as h2: … }` is the supported
  spelling and worked. Either support `decide` as a claim-hint (it is the
  documented canonical classical case-split), or have the error say
  "`decide` is not a claim hint — use `by cases { case P … case Not(P) … }`".
rubric (0/1): cause 0 · location 1 · actionable 0 · folded-types 1 · no-jargon 1

---

### (warning, not error) refining-list names count as unused — 2026-06-11 (IVT push)
note: `claim xNotZero : …;` followed by `cases x refining xPositive, xNotZero { … }`
  still warns `unused name xNotZero` — usage in a `refining` list is not counted
  as a use. (Serendipitously the fact was prover-derivable and got deleted, but
  the false positive stands: a name consumed ONLY by `refining` should count.)

---

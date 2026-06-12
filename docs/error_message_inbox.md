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

### (performance, not message) `by substituting <name>` re-runs the full prover per direction — 2026-06-12 (ℂ polish)
note: a calc step `= Product.make(x, y - Real.zero) by substituting firstZero`
(with `firstZero : x - Real.zero = x` in context) tripped the
expensive-by-less warning at ~77K kernel-steps. MATH_PROFILE_AUTOPROVER
showed TWO armed top-level autoProveClaim calls per such step, each
sweeping contextFactMatch over ~400 candidates (~1.2 s) before
equalityBattery closed via `ComplexNumber.product_eta`. The narrowed
`by substituting` path (claim.cpp, tryCloseAndBuild) re-proves each
rewritten-goal candidate with the auto-prover, and the warning
attributes the cost to the step line as if it were by-less. The SAME
step as `since firstZero` closes in microseconds via the
context-fact-plus-congruence bridge. Two asks: (a) `by substituting`
with a DIRECTLY-supplied equality whose rewrite makes the endpoints
structurally equal should not need a prover call at all; (b) the
expensive-step warning should say which HINT path burned the steps
rather than calling a hinted step "by-less".
diagnosis: understood (see note); fix is an elaborator change, not made
during the polish pass. Workaround applied throughout: prefer
`since <fact>` for single-fact rewrites.
rubric (0/1): cause 0 · location 1 · actionable 1 · folded-types 1 · no-jargon 1

---

### Citation boundary: ring argument only under projections — 2026-06-12 (ℂ polish)
note: `= Real.zero since Ring.zero_multiply_left` on a step
`Real.zero * coeff(…) = Real.zero` fails: the lemma is
`(r : Ring) → (x : Ring.carrier(r)) → Ring.multiply(r, Ring.zero(r), x) = Ring.zero(r)`,
and `r` occurs ONLY under projections in the conclusion — the
deferred-projection matcher (corpus #13) never gets a binding for the
slot, and the carrier-registry last resort only fires for `.carrier`
heads. The error message itself is the GOOD side-by-side relation
print. Possible extension if this recurs: resolve an unbound deferred
slot by trying each registered bundle of the structure and accepting a
unique defeq-verified candidate (reject-on-ambiguity). For now such
steps go bare (the prover closes them) or cite positionally.
rubric (0/1): cause 1 · location 1 · actionable 1 · folded-types 1 · no-jargon 1

---


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
### Redundancy checker aborts whole-file on expensive in-isolation re-proof — 2026-06-11 (#42 push)
2026-06-12 (+1, ℂ-completeness push): same abort on
ComplexNumber/completeness.math under --check-redundant-by — the in-isolation
re-proof of a strict `<` calc step explodes into an
`And(Not(modulus(…) = ε), modulus(…) ≤ ε)` goal and exhausts the budget;
whole-file report lost. Plain verify is green.
note: `--check-redundant-by` on Real/limits.math, Real/series.math,
Real/negation.math errors out mid-file:
```
error: claim `…`: the auto-prover gave up after exhausting its effort budget …
```
diagnosis: the checker re-proves each hinted site WITHOUT its hint; when
that in-isolation re-proof exceeds the budget on a pre-existing expensive
site, the failure propagates as a hard error and the whole file's report
is lost (sites after the expensive one are never tested). Wanted: treat
budget-exhaustion during checking as "hint is load-bearing, not
redundant" (a finding of the GOOD kind, or silence) and continue.
rubric (0/1): cause 0 · location 1 · actionable 0 · folded-types 1 · no-jargon 1

---
### (good message) `since FACT` on a calc step that needs FACT + a congruence — 2026-06-12 (exp push)
note: writing `≤ pS(abs∘s, pred) + abs(s(pred))   since IH` (IH plus an
add-congruence) failed with a model error message:
```
this step's justification proves a different relation than the step claims
  this step claims:    A + c ≤ B + c
  but its proof shows: A ≤ B
```
both relations printed side by side made the fix (`by
Real.add_preserves_LessOrEqual`, IH consumed from context) obvious in one
read. This is the shape more hint errors should have.
rubric (0/1): cause 1 · location 1 · actionable 1 · folded-types 1 · no-jargon 1

---
### `--check-redundant-calc-steps` splice re-elaboration trips on `a − b` vs `a + (−b)` and hard-errors — 2026-06-12 (|z| triangle push)
note: on ComplexNumber/triangle_inequality.math the plain verify and both
`--check-redundant-by` / `--check-redundant-by-non-eq` pass clean, but
`--check-redundant-calc-steps` aborts with:
```
elaborate error: theorem 'ComplexNumber.inner_product_bound'
  this argument has the wrong type for the function it is given to
    the function expects: … = re(z)·im(w) + -(im(z)·re(w))
    but this argument is: … = re(z)·im(w) - im(z)·re(w)
```
diagnosis: the checker re-elaborates the calc with a step spliced out; a
synthesized argument is compared STRUCTURALLY against the expected type,
and the kernel-defeq pair `a - b` / `a + (-b)` fails that comparison. The
failure then propagates as a hard error for the whole file instead of
"step not redundant, continue". Same wanted-behavior as the 2026-06-11
budget-exhaustion entry: any failure during in-isolation re-proof should
read as "step is load-bearing" and the sweep should continue.
rubric (0/1): cause 0 · location 1 · actionable 0 · folded-types 1 · no-jargon 1

---
### Constructor name in a non-first pattern slot silently binds a variable — 2026-06-12 (binomial push)
note: in a multi-pattern theorem `| successor(i), zero => …` the second
pattern `zero` is parsed as a FRESH BINDER named `zero` (shadowing the
constructor), not as the constructor pattern. The arm then proves a
statement about a variable, and the failure surfaces as the baffling
"expected: X / but this case gives: X" with byte-identical printouts
(the goal has the variable `zero : Natural` in context; the arm's calc
mentions the real constructor via numerals). Cost: ~5 rounds of
debugging. Wanted: either support constructor patterns in later slots,
or reject/warn when a pattern variable shadows a constructor of the
scrutinee's type. (Workaround that landed: pattern on the first argument
only; recurse on the second via a helper theorem that takes the previous
row as a Pi-hypothesis.)
rubric (0/1): cause 0 · location 0 · actionable 0 · folded-types 1 · no-jargon 1

---
### Redundancy checker false positive: Pi-hypothesis instantiation — 2026-06-12 (binomial push)
note: --check-redundant-by flagged `by previousRow(successor(m))` on a
claim as redundant, but the by-less claim FAILS in plain verify ("no
in-scope hypothesis matches structurally") — the fact in context is a
Pi (n : Natural) → …, and the prover does not instantiate it at
successor(m) outside checker mode. Checker and prover disagree; the
finding cost a verify round-trip.
rubric (0/1): cause 0 · location 1 · actionable 0 · folded-types 1 · no-jargon 1

---

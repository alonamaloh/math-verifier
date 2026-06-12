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
### (RESOLVED 2026-06-12 — cache-owner guard + AutoProverBudgetError catches; Real/limits, Real/series, Real/negation, ComplexNumber/completeness all sweep clean) Redundancy checker aborts whole-file on expensive in-isolation re-proof — 2026-06-11 (#42 push)
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
is lost (sites after the expensive one are never tested).
2026-06-12 (+1): on the same Real/limits.math the abort can also surface
as a citation error ("the `by` hint citation does not prove this goal",
at monotone_bounded_converges' tuple-hint claim) — plain verify is green,
so checker-mode state (budget guard or speculative re-elaboration)
corrupts a later REAL elaboration, not just its own report. Wanted: treat
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
### (RESOLVED 2026-06-12 — same kernel-cache poisoning root cause; triangle_inequality.math sweeps clean under --check-redundant-calc-steps) `--check-redundant-calc-steps` splice re-elaboration trips on `a − b` vs `a + (−b)` and hard-errors — 2026-06-12 (|z| triangle push)
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
### (RESOLVED same day) redundant-`by` warning didn't say WHICH claim — 2026-06-12 (binomial push)
note: with several multi-line claims in a row, `N: redundant \`by\` on
\`claim\`` pointed at a line that visually belonged to the PREVIOUS
claim's `by`, and I removed the wrong hint (which then failed plain
verify — initially misdiagnosed as a checker false positive on
Pi-hypothesis instantiation; the checker was right all along, the
flagged hint was the NEXT claim's recursive call, provable from the
auto-generated induction hypothesis). FIXED: named claims now carry
their binding name onto the claim node (parser), and the warning prints
`redundant \`by\` on \`claim NAME\``; also added MATH_DEBUG_REDUNDANT=1
to dump the checker's re-proof term + binder context.
(Test/redundant_by_named_claim_test.math)
rubric (0/1): cause 1 · location 1 · actionable 1 · folded-types 1 · no-jargon 1

---
### (RESOLVED same day — see the kernel-cache-poisoning entry below; the "exit 0" claim was a pipe-measurement error, real exit was 1) --check-redundant-by hard-errors (exit 0!) on And.introduction-for-`<` final terms — 2026-06-12 (exp corollaries)
verbatim:
```
library/Real/exponential_algebra.math:99:3: elaborate error: theorem 'Real.exponential_positive'
  the proof of theorem 'Real.exponential_positive' does not have its declared type
    declared type:        (x : Real) → Real.zero < (Real.exponential x)
    but this proof has type: (x : Real) → And (Real.zero ≤ (Real.exponential x)) (Not (Real.zero = (Real.exponential x)))
```
note: plain verify is GREEN — the theorem ends `And.introduction(…)` for a
`Real.zero < exp(x)` goal, and `LessThan` unfolds to exactly that `And`
(same final-term shape as Real.multiply_positive, which the checker
handles). Under `--check-redundant-by` the in-isolation re-elaboration
loses the defeq coercion and reports the whole THEOREM as type-incorrect,
then silently abandons the remaining sites in the file (the last two
theorems of exponential_algebra.math were never checked — discovered only
by copying them into a probe file). Worse, the process still EXITS 0, so
`.mark_redundant.py` reports success. Same wanted-behavior as the
budget-exhaustion entries: any failure during in-isolation re-proof should
read as "site is load-bearing, continue", and a checker abort should be
loud. (+1 budget-abort instance the same session: testing removal of
`by Real.add_preserves_LessThan` in a `<` calc step dies with the
"auto-prover gave up after exhausting its effort budget" hard error at
1:1 instead of "not redundant".)
rubric (0/1): cause 0 · location 1 · actionable 0 · folded-types 1 · no-jargon 1

---
### Hint citation won't flip an equality inside Not — 2026-06-12 (exp corollaries)
verbatim:
```
  the `Real.exponential_nonzero` citation does not prove this goal
    goal:        Not (Real.zero = (Real.exponential x))
    `Real.exponential_nonzero` has type: (x : Real) → Not ((Real.exponential x) = Real.zero)
```
note: the MESSAGE is good (both types shown side by side, cause obvious).
The gap is prover capability: the bare claim auto-closes (the prover finds
the lemma by index and flips the inner equality), but an EXPLICIT
`since/by <lemma>` citation of the very same lemma fails — citation
unification doesn't try symmetry inside `Not(a = b)`. So the author must
choose between an unexplained bare claim and a wrong-feeling failure when
naming the reason. Wanted: citation matching tries the symmetric form of a
`Not`-wrapped (or any) equality, mirroring what the auto-prover already does.
rubric (0/1): cause 1 · location 1 · actionable 1 · folded-types 1 · no-jargon 1

---
### (RESOLVED same day — root cause was kernel-cache poisoning by the lemma-search snapshot environment) --check-redundant-by aborts + misleading boundary type error — 2026-06-12
note: the two entries above from today (the And.introduction-for-`<`
hard error under --check-redundant-by, and the budget-abort at a `<`
calc step) had ONE root cause, and it was not the checker's error
handling: the kernel's WHNF / defeq-true / inferType caches are keyed
by expression only, but their answers depend on the Environment. The
failing-proof error enrichment (lemma search) queries the SECOND,
whole-library, bodyless snapshot environment — so every speculative
re-proof failure (which the checker produces by the dozen) interleaved
the two environments and cross-poisoned the caches (e.g.
`Rational.to_real` δ-unfolds in the module environment but is stuck in
the snapshot; 6357 poisoned hits measured in one checked file). A later
boundary defeq then read a poisoned entry and reported a kernel-TRUE
equality (`And(…)` vs `<`, one δ apart) as false. FIX:
`ensureKernelCacheOwner` in kernel.cpp — every cache consult checks the
requesting environment (address + declaration count) and self-wipes on
change; plus a belt-and-suspenders epoch guard that stops caching of
results influenced by in-flight loop-detection short-circuits.
Regression: Test/redundant_check_cache_isolation_test.math + the
`checker-tests` make target (runs it under --check-redundant-by).
Likely also explains the earlier "STALE CACHE makes citations of new
lemmas fail" and "--check-redundant-calc-steps hard-errors on
kernel-defeq a−b vs a+(−b)" entries — RE-TESTED after the fix:
ComplexNumber/completeness.math (the budget-abort instance) and
Real/square_root.math under --check-redundant-by
--check-redundant-calc-steps both sweep clean now. A second,
independent gap fixed in the same pass: the calc-step speculative
re-proof sites in calc.cpp caught ElaborateError/TypeError but NOT
AutoProverBudgetError, so a budget trip during a `<`-step re-proof
(--check-redundant-by-non-eq) escaped as a hard error at 1:1 and
aborted the file (the claim-site checks in induction.cpp already
caught all three). All speculative sites now treat any failure as
"hint is load-bearing, continue".
CORRECTION to today's earlier entry: the checker did NOT exit 0 on the
hard error — it exits 1; the 0 was my measurement error (`$?` read
after a pipe reports the pipe's last command).
Debug knobs added while bisecting (kept, all opt-in):
MATH_KERNEL_CACHE=0 (disable kernel caches in verify),
MATH_WHNF_CACHE_VERIFY=1 (recompute every WHNF cache hit, flag
mismatches), MATH_DEFEQ_POISON_CHECK=1 (retry top-level defeq falses
with cleared caches, flag flips).
rubric (0/1): cause 1 · location 1 · actionable 1 · folded-types 1 · no-jargon 1

---
### Stack-overflow segfault instead of fuel error when kernel caches are disabled — 2026-06-12
note: `MATH_KERNEL_CACHE=0 ./kernel verify … --check-redundant-by` on
Test/redundant_check_cache_isolation_test.math dies with SIGSEGV
(exit 139), no output. The cached WHNF wrapper is also where the
in-flight loop detection lives, so with caches disabled a reduction
cycle (or very deep speculative-search recursion) recurses until the
stack overflows — the per-call fuel counter doesn't save it because
the depth accumulates across mutually-recursive isDefEq/WHNF/inferType
frames that each start with fresh fuel. Only reachable via the new
diagnostic knob (verify previously hard-enabled the cache), so low
priority — but a segfault is never the right failure mode; loop
detection could move into the uncached path, or a recursion-depth
counter could turn this into a TypeError.
rubric (0/1): cause 1 · location 0 · actionable 1 · folded-types 1 · no-jargon 1

---

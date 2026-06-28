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

### `claim by cases` can pick a higher-order IH instead of the local disjunction — 2026-06-20 (baby `Or` cleanup)
note: while rewriting `Natural.lt_trichotomy` from raw
`Or.introduceLeft/Right` branches to proposition arms, this local setup:

```
let predecessorComparison : predecessor < b ∨ predecessor = b ∨ b < predecessor := IH(b);
claim by cases {
  in (predecessor < b) as predecessorLessThanB: ...
  in (predecessor = b) as predecessorEqualB: ...
  in (b < predecessor) as bLessThanPredecessor: ...
}
```

failed with:

```
library/Natural/order.math:186:3: elaborate error: theorem 'Natural.lt_trichotomy'
  this argument has the wrong type for the function it is given to
    the function expects: Natural
    but this argument is: predecessor < b ∨ predecessor = b ∨ b < predecessor
```

The source of the case split should have been the local disjunction
`predecessorComparison`, but the search also saw the induction hypothesis
`IH : (b : Natural) → predecessor < b ∨ predecessor = b ∨ b < predecessor`
and appears to have tried to use the goal proposition itself as IH's
argument. The error blames the theorem and prints a generic application
type mismatch, not "`claim by cases` chose/considered the wrong disjunction
source." Factoring the step into a helper with an explicit disjunction
parameter avoided the higher-order IH in scope.
diagnosis: `claim by cases` source search should prefer exact in-scope
disjunction facts over functions returning disjunctions, and failures from
candidate application should name the candidate and the case-split source
search rather than surfacing as a generic function-argument mismatch.

---

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
### (RESOLVED — bug-fix marathon, 2026-06-12 evening) Every open inbox bug swept
note: one session fixed, with regressions/probes for each (commits
8345f26..eddf60a): the cache-off SIGSEGV (pointer-identity progress
checks in matchAgainstPattern — terminated only by cache-stabilized
pointers; plus depth guards, 512MB worker stack, flip-guard RAII);
`by substituting` re-proof cost (reflexivity fast path + the
expensive-step warning now names the hint path); refining-list names
count as uses; citation symmetry-flip inside Not (the
exponential_algebra `since` is restored); pattern variables shadowing
a constructor of the slot's type are rejected with a naming error;
let-opacity in citation matching (fallback ζ-unfold pass);
projection-only deferred slots resolve via try-each-bundle
unique-candidate; universe keyword max -> MaxUniverse (max is an
ordinary overload now, `overload max := Natural.maximum`); ring's
misleading "FALSE as a polynomial" on structureless carriers and the
non-equality-goal message both rewritten (ErrorTests added); stale
dependency caches now fail loudly at load (mtime vs source, iface
sibling rule); and the 574 MB ring_test cache was the serializer
expanding the expression DAG to a tree — format v7 backreferences
shrink it 431x (whole cache tree now 10 MB), with hash-consing enabled
for exactly that target (7.6 GB -> 545 MB RSS). Bare C++ self-tests
now run in `make check` (three drifted expectations fixed).
Still open (projects, not bugs): tactic-level compact ring
certificates; auto-prover fingerprint plan.

---

### (capability gap, not message) `ring` / citation matching don't β-reduce a function-valued `let` — 2026-06-12 (ℂ functional equation)
note: with `let aModulus : Natural → Real := (k : Natural) ↦ abs(a(k));`
a goal `abs(a(i)) * X = X * aModulus(i)` fails under `by ring` ("not
equal as commutative-ring expressions") even though `aModulus(i)` is
`(λk. abs(a k)) i` which β-reduces to `abs(a(i))`. The new ring
ζ-unfold (zetaUnfoldLetBinders) substitutes the let VALUE but the result
is the un-β-reduced application `(λk. abs(a k)) i`, so ring sees two
distinct atoms and the fingerprint says FALSE. Same gap bites `since
<lemma>` citation matching and argument inference: `since
ComplexNumber.modulus_nonneg` can't unify `Real.zero ≤ aModulus(i)` with
the lemma conclusion (needs the explicit `by …modulus_nonneg(a(i))`).
Workarounds used: (a) commute in the un-let form then a by-less `=` step
folds to the let (the by-less defeq path DOES β-reduce); (b) pass
explicit args through a let. FIX: have zetaUnfoldLetBinders (or the ring
normaliser's atom canonicaliser) β-normalise after substitution, so a
function-let applied to args reduces to the body. Would make
function-valued `let` abbreviations first-class for ring/citation.
diagnosis:

### (wrong-lemma resolution) bare `claim Real.zero ≤ aModulus(i);` proves the WRONG nonneg fact — 2026-06-12
note: in cauchy_product_converges, two Pi-facts share the shape
`(i : Natural) → Real.zero ≤ <modulus>(i)`: one for aModulus, one for
bModulus. Making `claim Real.zero ≤ aModulus(j) by …modulus_nonneg(a(j));`
into a BARE `claim Real.zero ≤ aModulus(j);` (the redundant-by checker
said the `by` was redundant) made the build FAIL with
  kernel: Let: value type does not match declared type
    expected type: Real.zero ≤ (aModulus j)
    actual type:   Real.zero ≤ (bModulus j)
— the by-less auto-prover discharged the bare claim with the bModulus
nonneg witness (identical shape, found first), producing a term of the
wrong type that the surrounding `let` then rejected. Two issues: (1) the
redundant-by checker's speculative re-proof and the in-place by-less
proof disagree (checker false-positive), and (2) the by-less prover
should prefer a candidate whose conclusion matches the DECLARED claim
type exactly, not just up to the relation head. Kept the explicit hint.
diagnosis:

### (false positive) redundant-by flags a self-recursive pattern-match call — 2026-06-12
note: inside the pattern-match definition of
`ComplexNumber.cauchy_product_exchange`, the recursive `claim exchangeTail
: … by ComplexNumber.cauchy_product_exchange(a, b, p);` is flagged
"redundant `by` — auto-prover closes the goal without help". But removing
it (or making it `since`) fails with "unknown lemma
`ComplexNumber.cauchy_product_exchange`" — the theorem's own name is NOT
in the by-less prover's scope during its definition. So the checker's
speculative environment (which apparently HAS the name) diverges from the
real elaboration environment. The redundant-by check should run in the
same environment the proof elaborates in, or skip recursive self-calls.
diagnosis:

---

## diff-congruence defeq-check on a head-changing rewrite reduces deeply (OOM)
(2026-06-13, found proving Real.cosine_two_negative)

A calc step `… = … by <eq>` whose `<eq>` rewrites a subterm `f(args)` to a
differently-headed `g(…)` runs `isDefinitionallyEqual(f(args), g(…))` while
LOCATING the diff. That WHNF-reduces `f(args)`. For a thin definition over
something heavy this runs away: `Real.cosineCoefficient(Real.one, 2)`
unfolds to `realPart(exponentialTerm(i·1, 4))` — a degree-4 complex power
over a RingModulo quotient — and either hits "kernel reduction recursion
exceeded the depth bound (500)" or OOMs (7–8 GB) when the bound is higher.
Indices 0/1 (powers 0/2) stay shallow, so the bug only fires on the deeper
instance.

Worse: when an explicit `by <hint>`/citation FAILS, the elaborator falls
back to the full auto-prover search, and on these heavy terms THAT search
is what OOMs — so a mis-stated hint surfaces as an OOM, not a located
"hint does not prove goal" error. That cost a long debugging session.

Wishlist: (a) cap / short-circuit the diff-locating defeq check (treat a
head mismatch as "this is the diff" without fully reducing, or bound the
reduction); (b) when a by-hint fails, don't fall back into an unbounded
search on terms with non-reducing-cheaply heads — fail with the located
error instead; (c) honor MATH_AUTOPROVE_BUDGET inside intra-step kernel
reductions (today the budget is step-counted at the prover level and an
allocation-heavy single reduction blows memory before it trips).

Workaround that works today: rewrite with `substituting <eq>` (syntactic,
no defeq reduction); bridge lemma indices with `by (ring : 2 = 2*1)` since
the citation matcher won't reduce `2*1`→`2` either.

### RESOLVED 2026-06-13 (commit 071c3ee)
Fixed at the kernel + elaborator level:
- `isDefinitionallyEqual` now answers a conservative `false` on
  depth/fuel exhaustion (new `KernelResourceExhausted`, a `TypeError`
  subtype caught only by isDefEq) instead of throwing — coercion / the
  diff-walk fall through to structural strategies rather than aborting.
- the calc-step coercion gates and the diff-walk endpoint probes run with
  a bounded fuel (`kDefeqProbeFuel`); the final per-step acceptance check
  stays full-fuel as the deep-defeq backstop.
Cold-cache `by <eq>` over a heavy subterm now succeeds / fails fast (≈1MB)
instead of OOM/depth-error. RESIDUAL: a warm-cache, whole-file reduction
that materialises an enormous *cached* WHNF normal form still costs GBs —
a kernel-caching concern (cap cache by term size?), distinct from the probe
behaviour; the `substituting` idiom avoids it.

### named-arg `Lemma(a := a)` whose param name equals an in-scope local silently falls back to positional, with an opaque message at the WRONG line — 2026-06-15 (Phase-0 ring_lemmas)
note: in `Algebra/ring_lemmas.math` `Ring.negate_multiply_negate`, the calc `=` step
`= negate(multiply(a, negate(b))) by Ring.multiply_negate_left(a := a, b := negate(b))`
failed with:
    elaborate error: theorem 'Ring.negate_multiply_negate'
      this argument has the wrong type for the function it is given to
        the function expects: Type 0
        but this argument is: carrier
The named argument `a := a` (lemma param `a` collides with the in-scope local
`a`) silently resolved as POSITIONAL, feeding the value `a` (type `carrier`)
to the lemma's first param `carrier : Type(0)` — hence "expects Type 0, but
argument is carrier". Three problems: (1) names neither the named-arg-resolution
failure nor the offending `a := a`; (2) the location points at the enclosing
`let ⟨…⟩ := ringProof` rather than the calc step containing the call; (3) the
real one-line reason was buried under a large dump of folded bundle types
(`IsRing carrier add …`, `_tupleRest_86_86_5 : And …`). `Lemma(x := b)` (no
collision) resolves fine, so the trigger is param-name == local-name. Cost
many edit/build cycles to localise.
diagnosis:
rubric (0/1): cause 0 · location 0 · actionable 0 · folded-types 0 · no-jargon 1

### argument-free `by <Lemma>` in an `=` calc step says "proves a different relation" and dumps the un-applied Pi-type, not the actionable "apply it" — 2026-06-15 (Phase-0 ring_lemmas)
note: `= zero by Ring.zero_multiply` (argument-free) in a calc `=` step failed:
    this step's justification proves a different relation than the step claims
      this step claims:    (multiply zero b) = zero
      but its proof shows: (carrier : Type 0) → … → IsRing … → (x : carrier) → (multiply zero x) = zero
The `=`-step diff-inference doesn't instantiate an argument-free citation (it
works for ≤/∣ steps, for claims, and for a final `done by`, but NOT for `=`
steps — see proof-style.md). The message shows the un-applied Pi-type (a useful
tell) but never states the fix: "an `=` step needs the lemma applied — write
`by Lemma(arg := …)` or supply the data argument." This is the single biggest
blocker to cite-only over abstract bundles; closing the underlying gap (let an
`=` step instantiate an argument-free citation from its endpoints) would remove
it. Worth a targeted hint even before the gap is closed.
diagnosis:
rubric (0/1): cause 1 · location 1 · actionable 0 · folded-types 0 · no-jargon 1

### RESOLVED (whole-conclusion case) 2026-06-15 — argument-free `by <Lemma>` on an `=` calc step
The "argument-free `by <Lemma>` in an `=` calc step" gap above is FIXED for the
case where the lemma's CONCLUSION is the whole step equality: calc.cpp now
routes such a citation through `autoFillHintForClaim` (the same goal-driven
instantiation `claim … by L` / `done by L` use), gated on (Equality step, Pi-typed
proof, relation mismatch) so it's purely additive — the full library re-verified
unchanged. `Ring.{zero_multiply,multiply_zero,multiply_negate_left,…}` now cite
argument-free on `=` steps over the abstract ring bundle.
RESIDUAL: a CONGRUENCE `=` step (lemma matches a SUBTERM, e.g. `negate(·)` over
`multiply_negate_right`) still can't be cited argument-free over an abstract
bundle — `tryApplyBareLemmaToDiff` discharges only PROPOSITIONAL non-conclusion
args from context, not the bundle's DATA args (`carrier`/`add`/`zero`/`one`,
absent from the conclusion). Those stay applied (one site in ring_lemmas). A
deeper fix would infer non-proposition data args by type-match in the congruence
discharge.

### (follow-up to the above residual) why the congruence-over-bundle data-arg inference is non-trivial — 2026-06-15
Tried fixing the RESIDUAL by switching tryApplyBareLemmaToDiff's side-condition
discharge from a defeq CHECK to a `unifyConstructorParameters` against the
candidate bundle hypothesis (to pin carrier/add/zero/one from `IsRing(carrier,…)`).
It can't work: `unifyConstructorParameters` has a SOUNDNESS guard
(`!containsValueArgumentFreeVar(target)`, unification.cpp) that refuses to bind a
metavar to a target containing a local-binder free variable — and carrier/add/zero
ARE opened local binders, so the guard (correctly) blocks the binding. The right
fix is to route the differing SUBTERM through `autoFillHintForClaim` (the full
goal-driven inference that already solves the whole-conclusion case), then wrap
with the congruence diff bridge.

### RESOLVED 2026-06-15 — argument-free CONGRUENCE citation over an abstract bundle now works
Implemented the "right fix" above: `tryApplyBareLemmaToDiff` (diff_bridges.cpp), at
each level of its diff descent, now builds the level's subterm equality goal and
hands it to `autoFillHintForClaim` (the same goal-driven instantiation the
whole-conclusion case uses), then wraps the result via `tryDiffApplyUserProof`. So
`= negate(negate(multiply(a,b))) by Ring.multiply_negate_right` — a `negate(·)`
CONGRUENCE over the lemma — now cites ARGUMENT-FREE over the abstract ring bundle;
the bundle's data args (carrier/add/zero/one) are back-inferred from the in-scope
`IsRing` hypothesis. ring_lemmas `negate_multiply_negate` step 2 is now bare.
ROOT-CAUSE LESSON (the bug that cost the most): when hand-building an `=` goal to
feed a matcher, the carrier TYPE argument must be closed into the SAME
closed-over-local scope (`closeOverLocalBinders`) as the BV endpoints — exactly as
calc.cpp builds a step goal. My first cut passed the raw `inferTypeInLocalContext`
result (OPENED, carrier as a free variable); it printed identically but failed to
structurally match the `BV` the bundle hypothesis carries, so the data args never
pinned and the inner match silently fell through. Mixed opened/closed scope in a
single term is the trap. (`autoFillHintForClaim` itself was correct all along.)

### RESOLVED 2026-06-15 — argument-free citation now sees THROUGH a recursive-definition redex
`by List.length_prepend` (argument-free) on a step whose list argument is a REDEX —
`List.length(Natural, List.range_down(successor(k)))`, where `range_down(successor(k))`
only REDUCES to a `List.prepend(…)` — failed: the lemma conclusion
`List.length(A, List.prepend(A, head, tail))` couldn't be matched against the
unreduced goal. Two layers to it:
(1) the conclusion matcher (`matchAgainstPattern`) DOES δι-unfold a subject on head
    mismatch, and WHNF correctly exposes the `prepend`; but
(2) WHNF brings the tail back as the raw recursor IH (`Natural_recursor(… k)`), while
    the OTHER side of the goal pins the same lemma slot to the FOLDED `range_down(k)`.
    Folded vs unfolded are definitionally equal but structurally different, so the
    slot's consistency check (`structurallyEqual`) rejected the (correct) match.
FIX: when the structural consistency check on an already-bound slot fails, fall back
to a δ/ι-aware `isDefinitionallyEqual` (empty context — free BVs act as opaque atoms;
same idiom as the projection-resolution pass). Purely additive (only reached after
the structural check fails) and sound (accepts only genuinely-equal terms). Now
`map_length` / `range_down_length` cite `List.length_prepend` / `List.length_empty`
fully argument-free over the map/range_down redex.

### GOTCHA (not a bug) 2026-06-15 — `1 + n` is NO LONGER defeq to `successor(n)` under opaque `add`
`Natural.add` is now an `opaque definition`, so `1 + n` (= `add(1, n)`) does NOT
WHNF-reduce to `successor(n)`; `Natural.one_add : 1 + a = successor(a)` is a real
(propositional) lemma proved `by unfolding Natural.add`, not a reflexivity. The
CLAUDE.md convention note calling them "both kernel-defeq" is STALE under the Lux
opacity transition. Practical consequence hit while de-cascading `Lists/{distinct,
pairing}`: `length_prepend` yields `1 + |tail|`, but the Peano/order lemmas
(`zero_not_successor`, `successor_injective`, `successor_le_cancel`,
`not_less_or_equal_successor_zero`, `less_or_equal_predecessor_less_or_equal`) are
all `successor`-phrased and will NOT match a `1 + n` form. Bridge explicitly with a
`= successor(…) by Natural.one_add` calc step, or stay in `1 + n` and use the
`1 + n`-native lemmas (`Natural.add_cancel_left`, `Natural.add_left_le_cancel`). The
new congruence-citation feature makes the `one_add`/`length_prepend` bridges cite
argument-free even under `successor(·)` / `1 + ·` (e.g. pairing.math's six-step
length-bound calc).

### `calc` step `by <lemma>` not recognised when subtraction doesn't surface as `+ -` — 2026-06-16 (Rational opaque migration)
note: in `Rational/order_multiplication.math`, the step
`calc epsilon - Rational.halve(epsilon) = (halve + halve) + -halve by Rational.halve_doubled(epsilon)`
failed with "this step's justification proves a different relation than the
step claims / proof shows: halve + halve = epsilon". The diff-inference for the
step couldn't localise the `epsilon` vs `halve+halve` difference because the LHS
`a - b` (Rational.subtract) wasn't reduced to `a + -b`, so the top-level heads
(`subtract` vs `add`) mismatched and no single-subterm bridge was found. Writing
the RHS with `-` and closing the next step `by ring` fixed it. The message is
accurate about the relation mismatch but gives no hint that the obstacle is an
unreduced `subtract` head / that `ring` or an explicit `+ -` would bridge.
diagnosis:

### `choose <v> as <c> from <hypothesis>` doesn't count the `from`-source as a use — 2026-06-17 (obtain→choose sweep)
note: converting `claim h : ∃… by src; obtain ⟨v, c⟩ from h;` to
`claim h : ∃… by src; choose v as c from h;` makes `h` fire the unused-name
warning ("unused name `h` — the auto-prover consumes this fact by type-match,
so the name is dead weight"). But `choose v as c from h` DOES reference `h` —
it's the destructure source. The usage tracker apparently doesn't count a
`choose … from <name>` source as a use of that name, so the only
warning-free spellings are (a) anonymous `claim ∃… by src;` + `choose v such
that <pred> as c;` (scope-scan), which forces re-spelling the whole predicate,
or (b) accept the spurious warning. Counting `from <name>` as a name-use would
remove the false positive and let the readable single-spelling form stay clean.
This bites every opaque-Rational existential workaround (~10 sites in
Real/{addition,multiplication,sequence,absolute_value,order}).
diagnosis: usage tracker for the unused-name lint should treat a
`choose … from <ident>` (and likely `obtain … from <ident>`) source as a
reference to <ident>.

### Redundancy checker over-reports a `by` that's only redundant in isolation — 2026-06-17 (polish of de-plumb + Set/finite)
note: `--check-redundant-by` flags each `by`/claim by re-proving that ONE site
with its hint removed but every OTHER hint present. In `below_unshifts`
(Set/finite_sum) the inner `claim successor(monus(value,m)) ≤ n by { calc …;
claim }` is reported redundant, but actually removing it makes the proof fail
(`elaborate error: claim at line N`) — it only "closes without help" in the
checker's run because the *sibling* `claim successor(value) ≤ m+n;` is still
there to feed it, and the auto-prover happens to reach it from that. So a
batch of by-less edits guided by the report can over-remove: each looked
redundant alone, but they were collectively load-bearing. Same shape bit the
`group_lemmas` `inverse_operation` nested calc (two associativity steps each
flagged, but removing both broke the second). diagnosis: the report is a
per-site lower bound, not a jointly-safe set; the workflow (re-run after each
edit, restore on breakage) already absorbs this, but a note in the checker
output — "redundant given the other hints; removing several at once may not be
safe" — would set expectations. A stronger checker could re-verify with ALL
flagged hints removed and only report the ones still redundant jointly.

## quotient bridge mis-infers the equivalence relation from the proof's type; error blames the enclosing theorem with raw `T → Set T`

*(Salvaged from the `rational-field-of-fractions` branch, observed 2026-06-15
under the old name `Quotient.sound`; the bridge is now
`Quotient.equivalent_implies_equal`, but the instance-based relation-inference
hazard below is unchanged — both `IntegerEquivalent` and `RationalEquivalent`
are still registered as `instance`s, so re-verify under the current API.)*

Scenario (`Rational/enumerable.math`, ℚ as the field of fractions of ℤ): a
quotient bridge call left `T`/`R` to be inferred, and was given a proof term
that is an **Integer** equality. The reported error pointed at the enclosing
theorem with an argument-type clash:

```
elaborate error: theorem 'Rational.is_enumerable'
  this argument has the wrong type for the function it is given to
    the function expects: RationalRepresentative → Set RationalRepresentative
    but this argument is: Integer → Set Integer
```

Diagnosis: with the proof an *Integer*-equality term and `IntegerEquivalent`
registered as an instance, `R` unified to `IntegerEquivalent`
(`Integer → Set Integer`) instead of `RationalEquivalent`. The message then
reports the *downstream* argument clash, not the actual fault.

Rubric: (1) cause-not-symptom **0** — never says "couldn't infer the quotient
relation R" / "ambiguous equivalence instance"; (2) location **0** — points at
the enclosing `theorem`, not the bridge citation or the mis-typed proof; (3)
actionable **0** — no "pass `T` and `R` explicitly"; (4) user-facing types
**0** — prints the relation as `T → Set T` (a relation is
`T → T → Proposition`; `Set T` leaks); (5) jargon **0/1**.

Better message sketch: "couldn't infer the quotient equivalence relation: the
proof you gave has type `… = …` over `Integer`, so `R` was inferred as
`IntegerEquivalent`, but the goal is an equality over `Rational`
(`RationalEquivalent`). Pass `T` and `R` explicitly." — and point at the
bridge citation token, not the enclosing theorem.

## `witness v with (A ∧ B)` silently no-ops inside a `by cases` arm → bare "argument is Proposition"

Observed 2026-06-20 cleaning `Algebra/associate` / `Algebra/unique_factorization`
(FTA cone). `witness v with (<conjunction proposition>)` is supposed to
auto-prove the conjunction from context and inject the `Exists`. It works at
theorem-body top level, but inside a `claim by cases { in (P): … }` arm (or
other nested position) the bare-proposition coercion's prefilter
(`barePropositionCouldFire` in coercion.cpp — requires the written prop
*structurally* equal to the expected ∃-body) doesn't fire, so the proposition
reaches the kernel as a term where a proof was expected:

```
elaborate error: case for 'Exists.introduce' of 'Exists'
  …
  this argument has the wrong type for the function it is given to
    the function expects: And (Ring.IsUnit (IntegralDomain.ring d) c) (q = …)
    but this argument is: Proposition
```

Diagnosis: the message says "argument is Proposition" but never that the
*auto-prove-the-proposition coercion* was skipped (prefilter missed it because
the spelling used the `s := ring(d)` alias, not structurally equal to the
expected `ring(d)`-spelled body). The fix the user needs is "assemble it as a
named `claim X : A ∧ B; witness v with X`" — undiscoverable from the text.

Rubric: cause-not-symptom **0**; actionable **0**; location **1** (right token).
Better: "the `with` proposition couldn't be coerced to a proof here (auto-prove
only fires when it's structurally the expected type); state it as a `claim`
first, or write the proof explicitly." Deeper fix: route the `with`-proposition
through the full `autoProveClaim` (it already proves such conjunctions as a bare
`claim`), so the inline form is as strong as the named-claim form.

## redundant-`by` check flags a hint whose by-less re-proof is *expensive* (50k steps), contradicting the expensive-step warning

Observed 2026-06-20, `unique_factorization` helper. A calc step substituting a
`choose`-condition conjunction leg (`q = p1·c`) ran a 50183-kernel-step by-less
search (→ "expensive by-less proof step" warning). Adding `by qEqualsP1c` made
it fast, but then `--check-redundant-by` flagged that very hint as redundant
("auto-prover closes it without help"). So the two checks give opposite orders
on the same step. Per proof-style.md the redundant check is meant to fire only
when the by-less re-proof is "near-free"; 50k steps is not. Either the redundant
check should treat an expensive by-less re-proof as non-redundant (and say
"kept: by-less costs N steps"), or both should agree. Workaround that satisfied
both: an anonymous standalone `claim q = p1 * c;` re-exposing the leg as a
cost-1 equality, so the by-less step is cheap *and* hint-free. (Root cause of
the expense: the new conjunction-leg decomposition in `collectContextEqualities`
multiplies candidate equalities when many conjunctions are in scope.)

## (RESOLVED 2026-06-21 — all three gaps closed; `Logic/quotient.math` now drops every workaround and the clean phrasing verifies) `since`/`by` citation gaps surfaced rewriting Quotient.equal_implies_equivalent (2026-06-21)

Resolution:
- **Gap 1 (universe inference).** `elaborateIdentifier` now fills a bare
  universe-polymorphic citation's universe arguments with placeholder
  parameters (`allowImplicitCitationLevels_`); `matchAgainstPattern` treats a
  placeholder level as a wildcard, and `completeCitationFromBindings` resolves
  each to a concrete level from the recovered argument bindings' inferred types
  — the citation-path analogue of the value-argument universe inference at the
  ordinary application path. `done since IsEquivalenceRelation.reflexive` (no
  `.{u}`) now works.
- **Gap 2 (unpinned middle binder).** Already closed by commit f3c25b6 ("shift
  ambient bound-vars when matching a cited local hypothesis"). The direct
  `done since IsEquivalenceRelation.transitive` for goal `R(x, y2)` discharges
  both premises from the in-scope `R(x, y1)` / `R(y1, y2)` with no `recalling`.
- **Gap 3 (argument-position block lambda).** Stage-2 universe inference in the
  application dispatcher (`dispatch.cpp`) used to elaborate every value argument
  with no expected type; it now walks the universe-instantiated signature and
  feeds each argument its declared parameter type, so an inline block-bodied
  `Quotient.lift` respect proof receives the respect-Pi codomain as its goal.
  The `let respectsR : … := { … }` hoist is no longer needed.

Regression coverage: `library/Test/citation_universe_inference_test.math`.

Original report follows.

Spike: rewrote `Logic/quotient.math`'s `equal_implies_equivalent` from raw
plumbing (`let ⟨…⟩ := equivalence`, positional `propositional_extensionality`,
raw `rewrite`) to the mathematician's argument. Three elaborator gaps blocked
the most direct phrasing; each has a workaround, but closing them would let such
proofs read more directly.

### Gap 1 — `since`/`by` does not infer universe arguments
Citing a universe-polymorphic lemma needs the level supplied by hand:
`done since IsEquivalenceRelation.transitive.{u}` works, but bare
`since IsEquivalenceRelation.transitive` errors:
```
elaborate error: constant 'IsEquivalenceRelation.transitive' requires 1
universe argument(s); supply them explicitly with .{...}
```
The universe is recoverable from context (the goal/operands fix `T : Type(u)`),
exactly as it is for an ordinary application. The citation path should infer
`.{u}` the way application elaboration does, instead of demanding it be written.

### Gap 2 — citation matcher can't recover an *unpinned middle* binder (prover can)
`done since IsEquivalenceRelation.transitive` for goal `R(x, y2)` fails:
```
the `IsEquivalenceRelation.transitive` citation does not prove this goal
  goal: R x y2
  the hint's arguments could not be inferred from the goal or discharged from
  context, or its conclusion does not unify with the goal
```
Transitivity's conclusion `R(a, c)` pins `a, c` from the goal but leaves the
middle `b` free; premise-recovery does not discover `b = y1` from the in-scope
`R(x, y1)` / `R(y1, y2)`. Workaround: `… recalling (R(y1, y2))` (pins `b`).
KEY OBSERVATION: the bare auto-prover DOES find it — `claim R(x,y1) → R(x,y2);`
(no hint) closes by search. So the gap is the *targeted citation matcher's*
premise discharge for an unpinned binder, not a prover weakness (same root as
the earlier `by primeDivides` premise-discharge failure in factorization_list).
Closing it (have `since`/`by` run the same context search the bare prover does
when a binder is unpinned by the conclusion) would remove the need for
`recalling` and for many explicit positional calls.

### Gap 3 — a block-bodied lambda passed as an argument loses its expected type
Writing the `Quotient.lift` respect proof inline as
`(y1 y2)(rel) ↦ { … ; done since Equality.propositional_extensionality }`
fails: the final `done` reports "bare `claim`/`done` needs an expected type from
context (none available)", because the argument's expected type (the lift's
respect-Pi codomain `R(x,y1) = R(x,y2)`) is not pushed into the block. Workaround:
hoist to a typed `let respectsR : ∀ … := { … }` — the annotation supplies the
goal, so the block's intros and final `done` typecheck. Ideally the expected
type of an argument position would flow into a block-bodied lambda there too.

## `absurd(…)` inside a lambda body mis-frames a captured-variable goal → "unbound internal variable" at kernel verify (2026-06-21)

Repro (minimal): a vacuous-implication proof where `absurd` produces the
codomain of a lambda whose expected type is an outer parameter.

```
theorem repro (A C : Proposition) (notA : Not(A)) : A → C :=
  (a : A) ↦ absurd(notA(a))      -- goal of the body is `C` (a captured param)
```
yields, at the final `./kernel verify` pass (not at elaboration):
```
elaborate error: theorem 'repro'
  kernel: unbound internal variable: C (in-scope: A C notA a)
```
Hit while cleaning `Logic/excluded_middle.math`
(`Logic.not_implies_implies_and_not`, the `Not(antecedent)` arm). That file no
longer exercises the bug — the arm now closes with a bare `done` (the auto-prover
finds the contradiction) — so the `repro` above is the standalone witness.
Writing the False-eliminator explicitly (`False.eliminate_proposition(C,
notA(a))`) is the manual stand-in for positions where `done` doesn't apply.

diagnosis: `desugarAbsurd` (desugar_eliminators.cpp) is the only consumer that
*splices* the goal `expectedType` verbatim into its output term
(`False.eliminate_proposition(expectedType, falseProof)`), so it is uniquely
sensitive to the exact de-Bruijn frame of `expectedType`. The value it receives
is `elaborateLambda`'s `expectedBody` — the expected Pi codomain peeled at
inference.cpp:2096 via `weakHeadNormalFormForcingOpaqueHead(pi->codomain)`. That
peeled codomain is correct for type *comparison* (what every other body consumer
uses it for — coerceToExpectedTypeViaDiff, constructor-param inference), but its
frame is off by the lambda's own binders when spliced into a CLOSED-over-
`extended` term: a captured outer variable (`C`) lands at the wrong index and
reads as unbound. Note a blanket `openOverLocalBinders(expectedType, …)` in
desugarAbsurd is NOT the fix — it regresses the cases-arm path (where absurd is
*not* under an extra lambda and `expectedType` is already in the arm frame), so
the two paths deliver `expectedType` in different frames. Real fix likely lives
in elaborateLambda: hand the body an `expectedBody` that is consistently CLOSED
over `extended` (lift/adjust the peeled codomain by the lambda binders), so
absurd's splice is correct without special-casing. Worth doing before the Real
analysis files (absurd-under-a-binder is common there).

## argument-free citation of `multiply_by_nonneg_left` mis-resolves the goal's `*` operator (2026-06-21)

Cleaning Real/multiplication.math: converting
`by Rational.LessOrEqual.multiply_by_nonneg_right(a, b, c, premA, premB)` to the
argument-free `by Rational.LessOrEqual.multiply_by_nonneg_right` WORKS (both
premises discharged from context, incl. `0 ≤ |…|` auto-found). But the
*`_left`* sibling fails: for goal `(succ K : Rational) * |x| ≤ (succ K) * δ`,
```
the hint's arguments could not be inferred ...
  goal: Rational.from_integer_multiply (Natural.to_integer (successor K)) (…) ≤ …
```
The citation reconstructs the goal's `(succ K : Rational) * …` with the
Integer×Real scalar operator `Real.from_integer_multiply` instead of
`Rational.multiply`, so the conclusion `c * a ≤ c * b` never unifies. The `right`
form (`a * c ≤ b * c`) avoids it because the overloaded factor is in a different
position. Workaround: keep the `_left` calls fully positional. Real fix: the
argument-free citation's goal/operator elaboration should respect the Rational
multiply already present rather than re-resolving the `·` overload to the
Integer-scalar variant.

## (observation, not an error) bare auto-proved claims feeding `choose`/positional args flag unused-name

Recurring while cleaning the Real cone: `claim h : ∃…  by <lemma>(…); choose v
from h;` flags `h` as unused ("auto-prover consumes this fact by type-match"),
because `choose`'s `from h` is found by type, not by the name. Likewise a bare
`claim h : T;` whose only consumer is a positional `F(…, h)` arg. The clean
escape that works: drop the name and use the most-recent-∃ form
`claim ∃…; choose v such that <pred> as p;` (anonymous claim → no name to flag),
or anonymize the claim and let a bare downstream step find it by type. This is
why Real/multiplication.math (~10 such claims) needs the anonymize-and-such-that
sweep before it is unused-name-clean.

## `by_induction` 1+n form: mixed `case zero:` + `case step(k):` → unhelpful "expects exactly" message

Hit repeatedly while converting legacy inductions to the successor-free form
ONE clause at a time (change `case successor(k):`→`case step(k):` but not yet
`case zero:`→`case base:`, or vice versa). The message:
```
library/.../foo.math:80:3: elaborate error: by_induction (1+n) at line 80
  theorem 'Foo.bar'
  by_induction (1+n form) expects exactly `case base:` and `case step(k):` clauses
```
diagnosis: correct cause but not actionable enough. The block already routed
to the 1+n path (it saw a `step`/`base` clause), then rejected the sibling
`case zero:`/`case successor(...)`. The message should NAME the offending
clause and suggest the rename, e.g. "found `case zero:` in a 1+n block — the
1+n form uses `case base:` / `case step(k):`; rename `zero`→`base` (and
`successor(k)`→`step(k)`)". As written it doesn't say which clause is wrong or
that base/step and zero/successor are different vocabularies, so on a big proof
you re-scan every clause. (Axes likely lost: actionable, right-location.)

## (resolved, for data) `refining` silently dropped by the 1+n path → confusing downstream type mismatch

Before commit 46c0ce0, `by_induction on n with IH refining h { case base /
case step(k) }` elaborated but reported, deep in the assembled term:
```
this argument has the wrong type for the function it is given to
  the function expects: j < n
  but this argument is: j < (successor zero) + predecessor
```
diagnosis: the TRUE cause was that `elaborateByInductionOnePlus` ignored
`cases.refiningNames`, so the refined hypothesis `h` stayed pinned at the
original `n` while the step goal was at `1 + predecessor`. The message blamed a
user argument (symptom) instead of saying "`refining` is not supported here" or
applying it. Now fixed (refining works in the 1+n path), so the message no
longer appears — recorded only as a data point: a silently-ignored surface
feature produces a maximally-confusing symptom error. Lesson for future
surface features: if a clause/modifier can't be honored on a code path, reject
it explicitly rather than dropping it.

---

## `calc` leading term defaults a bare numeral to Natural (2026-06-26)

`calc 0 ≤ abs(f(x)) < …` fails with:

```
this argument has the wrong type for the function it is given to
  the function expects: Natural
  but this argument is: Real
```

**Diagnosis.** The calc elaborator elaborates the leading term (`0`) in
isolation, *before* the first relation pins the carrier — so `0` defaults to
Natural, the first relation resolves to `Natural.LessOrEqual`, and the
Real-typed RHS then mismatches. A bare `0 ≤ abs(f(x))` written as a plain
operator expression coerces fine (combineOperands joins the operands); only
the calc leading position misses it. Workaround in use: `calc (0 : Real) ≤ …`.
**Fix worth doing:** elaborate the first calc relation as a coercion-joined
binary op (so the leading `0` gets the carrier from the other operand). The
error is also misleading — it blames the RHS ("argument is Real") when the
real culprit is the under-typed leading `0`.

## redundant-`by` check vs. performance-load-bearing hints (2026-06-26)

`--check-redundant-by` flags a `by <lemma>` as redundant whenever the
auto-prover *closes* the step without it — but it does not check *cost*.
Several `by Real.less_than_add_of_positive` hints on `x < x + 1` roof steps
were flagged redundant; removing them made the step an *expensive by-less
proof step* (710k kernel-steps) or pushed the next step past the budget
("gave up"). So the two checks disagree: one says "remove", the other (on
removal) says "add a reason". The triage answer is `since`, but that mislabels
plumbing as illumination. **Suggestion:** have the redundant-`by` check also
report the by-less cost, or suppress the redundant flag when the by-less cost
exceeds a threshold — otherwise the polish loop round-trips (add `by` →
"redundant" → remove → "expensive" → re-add).

## `done by <lemma>` (args dropped) — misleading "about Exists" message (2026-06-26)

Closing `Real.HasDerivativeAt.subtract` with `done by Real.HasDerivativeAt.add`
(no positional args) fails with:

```
its conclusion is about `Exists` but the goal is about `Real.HasDerivativeAt`
— this lemma does not target this goal (check the lemma name)
```

The lemma name is correct; the real problem is that the second function
argument (`(y) ↦ -g(y)`) can't be inferred from the goal's `f y - g y`
(it needs `f y + (-g y)`), so the match never reaches the `HasDerivativeAt`
head and falls back to comparing the unfolded `Exists` bodies. A bare `done`
*does* close it (the full search supplies the instantiation). The message
"check the lemma name" sends you down the wrong path — the lemma is right, the
inferred argument is wrong.

### Redundancy checker emits a spurious "elaborate error" on generic-lemma steps — 2026-06-28 (manifest-wide redundant-by sweep)
note: running `kernel verify --source FILE --cache-root build --check-redundant-by
--check-redundant-by-non-eq` over the clean manifest, two files print a full
"elaborate error" block even though they verify fine in the normal build
(`make clean-check` GREEN) and the kernel still exits 0:

- `library/Real/continuity.math:291` — `Real.ContinuousAt.multiply` step:
  ```
  this step's justification proves a different relation than the step claims
    this step claims:    |f y| * |g y - g x| ≤ fRoof * |g y - g x|
    but its proof shows: (x y c : Real) → x ≤ y → IsNonneg c → x * c ≤ y * c
  ```
- `library/Rational/order_multiplication.math:440` — `Rational.value_at_zero_is_add_one`
  via `Rational.fraction_equal`: "the conclusion shape fits, but an argument
  could not be inferred …".

In both, the flagged step is justified by a GENERIC lemma applied so that the
auto-prover must instantiate/discharge from context. The normal verify does
this fine; the redundancy check's re-elaboration of the step reports a mismatch
(it seems to compare the lemma's raw Π-type against the step relation instead of
the instantiated conclusion). The error is non-fatal (exit 0) but noisy and
alarming during a polish sweep — it looks like the file is broken when it isn't.
diagnosis (PARTIAL, 2026-06-28):
- `continuity.math:291` — **RESOLVED.** This was the non-`=` redundancy probe
  running `tryContextFactMatch` instead of the real by-less `autoProveClaim`;
  that targeted matcher mis-elaborated the `ContinuousAt.multiply` step. The
  budget-bug fix (probe now mirrors the by-less path) removed it.
- `order_multiplication.math:440` — **STILL OPEN, different mechanism.** Here the
  theorem `value_at_zero_is_add_one` proves its goal under `unfold
  StrictPositiveRational.value, Integer.to_rational in { … }`; the closing
  `done since fraction_equal` needs `value(make(K,0))` to REDUCE to a
  `fraction(...)`. Under `--check-redundant-by` a speculative probe earlier in
  the body appears to leave shared state mismatched so that reduction no longer
  fires at line 444 and the citation match fails. The leading hypothesis is
  OPACITY-STATE, not the WHNF/defeq cache: the probe's lemma search runs against
  a bodyless snapshot with default opacity and the `unfold`'s Transparent
  override for `value`/`to_rational` is not restored on return (so `value` is
  seen Opaque → stuck → no `fraction`). RULED OUT: wiping the kernel caches in
  the `RedundancyBudgetGuard` destructor (mirrors the `unfold … in` cache
  invalidation at dispatch.cpp:378) did NOT fix it — pointing at the opacity
  FLAG / snapshot environment, not a stale cache entry. Next: audit how the
  speculative lemma-search saves/restores `unfoldedInThisDeclaration_` opacity
  overrides across the snapshot-environment boundary.

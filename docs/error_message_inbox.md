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


### library/ErrorTest/probe_substituting_lemma_no_args.math — 2026-06-09 01:36:38 (exit 1)
note: argument-free substituting of a lemma that still needs its arg
```
$ ./kernel verify --source library/ErrorTest/probe_substituting_lemma_no_args.math --cache-root build
library/ErrorTest/probe_substituting_lemma_no_args.math:12:1: elaborate error: claim by substitution at line 12
  claim at line 12
  calc step 1 at line 12
    context:
      n : Natural
  calc block at line 11
    context:
      n : Natural
    goal: n + zero = n
  theorem 'ErrorTest.q'
  `by substituting`: the supplied expression's type is not an equality `a = b`
```
diagnosis: `substituting <expr>` wants a concrete equality term, but
  `Natural.add_zero` is a FUNCTION `(a : Natural) → a + 0 = a` — only equal to
  an equality AFTER applying it. So the diagnosis ("not an equality") is
  literally correct but unhelpful: it doesn't say *why* (a partially-applied
  lemma) or what to do. Real intent was "rewrite by add_zero, infer the arg
  from the target". Two fixes: (a) when the supplied expression is a function
  whose RESULT type is an equality, say so — "`Natural.add_zero` still expects
  1 argument (`a : Natural`); apply it, or use `by Natural.add_zero` /
  `by substitution` to infer it". (b) `substituting` could itself accept a
  lemma and infer the arguments by matching its conclusion against the calc
  step's diff, like `by <lemma>` already does. NOTE the asymmetry worth
  recording: `by <lemma>` and the unnamed `by substitution` BOTH infer
  arguments, but `by substituting <lemma>` does not — that inconsistency is the
  trap a user falls into.
rubric (0/1): cause · location · actionable · folded-types · no-jargon

---

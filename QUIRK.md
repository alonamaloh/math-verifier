# Elaborator quirks worth investigating

Working notes for things that look like bugs / surprises in the
elaborator. The goal is to come back to these in a dedicated session
once we have more context. Each entry: symptom, root cause hypothesis,
attempted fixes, and the workaround the library currently uses.

## claim-anonymous-self-recursion

### Symptom

Inside the body of a recursive pattern-match theorem, the anonymous
form `claim T by V;` (where `V` calls the in-progress theorem) fails
with `type error: undefined constant: <theorem name>`. The legacy
named form `claim NAME : T by V;` succeeds with the same `V`.

Reproducer (from `library/Natural/divide.math:282`):

```math
theorem Natural.monus_le_self
        : (n d : Natural) → Natural.monus(n, d) ≤ n
  | zero, d => …
  | successor(k), d =>
      (cases d {
         | zero => …
         | successor(j) => {
             -- WORKS:
             claim recursion : Natural.monus(k, j) ≤ k
               by Natural.monus_le_self(k, j);
             -- FAILS with "undefined constant: Natural.monus_le_self":
             -- claim Natural.monus(k, j) ≤ k
             --   by Natural.monus_le_self(k, j);
             claim by substituting Natural.monus_succ_succ(k, j)
           }
       } : Natural.monus(successor(k), d) ≤ successor(k))
```

### Root-cause hypothesis

Two desugaring paths:

- **Legacy** `claim NAME : T by V;` desugars (in `parser.cpp` legacy
  claim branch ~line 1038) to a `TypedLet` wrapper with
  `wrapper.value = V` as a **raw expression**. Fold-back produces
  `SurfaceLet{name, type=T, value=V}`. Elaboration of `SurfaceLet`
  (`elaborator.cpp:~3655`) calls
  `elaborateExpression(*let->value, localBinders, letType)` and
  **stores the elaborated value** in the let-binder — no explicit
  `inferTypeInLocalContext` call. The kernel typechecks the stored
  value later (at the point where the surrounding theorem definition
  is `addDefinition`-ed, by which time the theorem's signature is
  presumably present in the env via some pattern-match-elaboration
  forward-declaration).

- **Anonymous** `claim T by V;` desugars (`parser.cpp:842`) to a
  `TypedLet` wrapper with `wrapper.value = claimExpression` (a
  `SurfaceStructuredClaim` wrapping `V` as `byHint`). Fold-back
  produces `SurfaceLet{name=_claim_anon_…, type=T, value=SurfaceStructuredClaim{…}}`.
  Elaboration of the structured claim
  (`elaborator.cpp:elaborateStructuredClaim` ~line 4367) elaborates
  the byHint **without** an expected type and immediately calls
  `inferTypeInLocalContext(hintTerm)` to feed
  `autoFillHintForClaim`. **That `inferType` call** is where the
  kernel barfs: the in-progress constant isn't in the env yet.

So the legacy path defers kernel typecheck of `V`; the anonymous path
type-checks `V` mid-elaboration.

### Attempted fix (didn't work; reverted)

In `elaborateStructuredClaim`, try elaborating the byHint with
`goalClosed` as expected type. If that succeeds, return the hintTerm
directly — skip `inferTypeInLocalContext` and `autoFillHintForClaim`.

Result: my debug print confirmed elaboration **succeeds** in the
with-expected-type path. But the build then fails with a **different**
error:

```
elaborate error: case for 'successor' of 'Natural'
  cases expression at line 283
  case for 'successor' of 'Natural'
  theorem 'Natural.monus_le_self' (pattern-match form)
  kernel: undefined constant: Natural.monus_le_self
```

So the cases-elaboration in the pattern-match path does its own
kernel typecheck of the arm, and **that** check fails on the same
constant. My fix only addressed `inferTypeInLocalContext` inside the
claim — it didn't address the surrounding cases-elaboration's check.

This suggests the real fix is upstream: pattern-match elaboration
should add a forward-declaration of the theorem to the kernel env
**before** elaborating its body, so any subsequent kernel typecheck
during body elaboration can resolve the self-reference. The legacy
path works because it never triggers a kernel typecheck during body
elaboration (the let-store path defers everything).

### Workaround in the library

Use `let _NAME : T := V;` instead of `claim T by V;` or `claim NAME : T by V;`:
- `let` goes through the same raw-expression path as legacy named claim
  (no extra `inferTypeInLocalContext`), so the recursive constant
  doesn't trip up elaboration.
- `_`-prefix suppresses the unused-name lint.

Three sites currently use this workaround. Search for "QUIRK.md" comments:

```
library/Natural/divide.math:289    -- claim-anonymous-self-recursion
library/Natural/padic_valuation.math:1403  -- claim-anonymous-self-recursion
library/Real/supremum.math:559     -- claim-anonymous-self-recursion
```

### Where to look when fixing

- `elaborator.cpp:elaboratePatternMatchDefinition` (~line 1273): does it
  add the in-progress theorem to the kernel env via a forward-decl?
  If not, that's the fix.
- `elaborator.cpp:elaborateStructuredClaim` (~line 4367): the
  `inferTypeInLocalContext(hintTerm)` call at ~line 4441 is the
  trigger. If pattern-match adds the forward-decl, this call would
  succeed and the workaround can be removed.
- `kernel.cpp:1627`: where "undefined constant" is thrown.

## nested-claim-by-cases-expected-type

### Symptom

In `library/Natural/padic_valuation.math:614`, the body of a
proof-of-negation uses `function (h : prime ∣ a' * b') => { … claim
by cases { … } }`. Wrapping this in anonymous `claim prime ∤ (a' *
b') by <function>;` works during elaboration but the nested `claim
by cases` then can't see the expected type it needs to motive-
abstract over.

(I confirmed this empirically: switching from `let _notDivProduct :
T := <function>;` to anonymous `claim T by <function>;` fails. I
didn't reduce a minimal repro for this one yet — the failure happens
deep inside the nested cases-of-disjunction elaboration.)

### Root-cause hypothesis

Same family of issue as above: the anonymous-claim path elaborates
the byHint without propagating useful context (here, an expected
type that the nested `claim by cases` motive needs). Fixing the
self-recursion issue above by routing through the same raw-let path
might also fix this — worth retesting once the upstream fix lands.

### Workaround in the library

Same `let _NAME : T := V;` shape. One site:
`library/Natural/padic_valuation.math:620` (around the
`notDivProduct` name).

## How to use this file

When a new quirk shows up that's worth a dedicated session, add an
entry with the four sections (symptom, hypothesis, attempts,
workaround). Don't fix in the same session that found the quirk
unless the fix is genuinely localised — otherwise the investigation
sprawls.

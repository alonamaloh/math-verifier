# Elaborator quirks worth investigating

Working notes for things that look like bugs / surprises in the
elaborator. The goal is to come back to these in a dedicated session
once we have more context. Each entry: symptom, root cause hypothesis,
attempted fixes, and the workaround the library currently uses.

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

`elaborator.cpp:elaborateStructuredClaim` (~line 4421) elaborates
the byHint **without** an expected type:

```cpp
ExpressionPointer hintTerm =
    elaborateExpression(*claim.byHint, localBinders);
```

The legacy let path passes `letType` as the expected type, which
flows into the lambda body (`function (h) => block`) — that gives
the nested `claim by cases` a non-empty expected type to motive-
abstract over. The anonymous path swallows that context.

Naive fix (always pass `goalClosed` as expected type for byHint)
isn't safe: a partially-applied lemma like `claim P by And.left(h)`
naturally has type `(B : Proposition) → And(A, B) → A`, not `P`, and
`autoFillHintForClaim` is the thing that bridges the gap. Forcing
the expected type at the elaborate-byHint step would break that.

Possible targeted fix: when `claim.byHint` is syntactically a
`SurfaceLambda` (or a block expression that desugars to one), pass
`goalClosed` as the expected type. For everything else, keep the
current "elaborate then auto-fill" path. Worth trying — the lambda
heuristic is narrow enough to avoid the partial-application failure
mode.

(Was previously bundled with the now-resolved `claim-anonymous-
self-recursion` quirk, on the hypothesis that one fix would address
both. The self-recursion fix landed but does NOT cure this one —
confirmed by switching the workaround at padic_valuation.math:620
back to anonymous form and watching the build fail with `claim by
cases ... needs either a proposition or an expected type from
context`.)

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

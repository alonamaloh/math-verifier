# Elaborator context vs kernel context

*Internals note. Not needed to write proofs — this is about how the
elaborator threads context, for anyone working on the elaborator/kernel
themselves.*

When a proof is elaborated there are **three** distinct "context-like"
things plus the **goal**. They are easy to conflate (and the names don't
help), so this note pins down what each one is, who owns it, and how they
relate.

## The three structures + the goal

1. **Global declarations — `Environment`** (`src/kernel/kernel.hpp`),
   held as the elaborator member `environment_`. Every `Axiom` /
   `Definition` / `Inductive` / `Constructor` / `Recursor` brought in by
   imports, plus the declarations of the current module as they are
   elaborated, plus the operator / overload / instance / coercion
   registries. This is the "global part" of the context.

2. **Local hypotheses — `localBinders` (`std::vector<LocalBinder>`)**.
   The local proof context: theorem parameters/hypotheses, and every
   binder introduced inside the proof (`λ`, `take`, `suppose`, `let`,
   stated propositions, `<chain> as`). Each `LocalBinder` is `{name, type, value,
   valueIsProof}` (`src/elaborator/term_utilities.hpp`).

   **It is a flat vector threaded as a parameter, not stored state.**
   `elaborateExpression(expr, localBinders, expectedType)` takes it by
   const-ref; introducing a binder means calling deeper with a *copy that
   has one more entry appended*; leaving the binder's scope is just the
   recursion returning. There is no explicit push/pop of local
   hypotheses — the call stack *is* the block nesting. (See the
   open question below.)

3. **Kernel context — `Context = std::vector<ContextEntry>`**
   (`src/kernel/kernel.hpp`). What the **kernel** needs to typecheck a
   subterm or decide a definitional equality under local hypotheses.
   `ContextEntry` is `{name, type, origin, value}`.

   **This is not a peer of the other two — it is a derived view of
   `localBinders`.** It is never stored. Every time the elaborator calls
   into the kernel (`isDefinitionallyEqual(environment, context, …)`, a
   subterm typecheck, …) it *rebuilds* a fresh `Context` from the current
   `localBinders` via `buildContextFromLocalBinders`
   (`src/elaborator/term_utilities.cpp`). The kernel never sees a
   `LocalBinder`; the elaborator never persists a `Context`.

4. **The goal — `expectedType`**. Passed as a **separate parameter** to
   `elaborateExpression`; it is *not* part of any context. `claim P;`
   elaborates its body against a temporarily-switched expected type `P`,
   proves it, and appends the resulting proof to `localBinders`; closing a
   block proves the block's expected type.

### Aside: the diagnostics-only frame stack

There is *also* an explicit stack, `contextFrames_` (the RAII `Frame` /
`FrameSnapshot` types in `src/elaborator/internal.hpp`). Each frame
snapshots `{description, a copy of localBinders, expectedType, line}`.
**This exists only to render error breadcrumbs** — "where you were and what
you were trying to prove" at every level of nesting. It is not the working
context; the working context is the `localBinders` *parameter*. Don't
confuse the two.

## Why `LocalBinder` and `ContextEntry` differ — the projection seam

The two binder types are intentionally *not* the same shape, because the
`value` field serves different consumers:

- `ContextEntry.value` exists **only** so the kernel can ζ-reduce a
  let-bound name while deciding a *type-level* definitional equality.
- `LocalBinder.value` additionally feeds the **elaborator's own**
  structural matchers — the auto-prover's `zetaUnfoldLetBinders`, the
  lemma index, hypothesis matching — which work on closed terms without
  going through the kernel.

`buildContextFromLocalBinders` is the **one place** that translates
elaborator binders into kernel entries, and therefore the one place to
express *"what does the kernel actually need to see?"*. It currently makes
one such decision: a **proof-valued** let (its declared type is a
`Proposition`, flagged `LocalBinder::valueIsProof`) has its `value`
**dropped** from the `ContextEntry` — ζ-substituting a proof can never
decide a type-level equality, but carrying it makes every defeq under the
binder pay an O(proof-size) substitution. The elaborator's matchers still
see that proof value via the `LocalBinder`. (Commit history: "omit
proof-valued lets from the kernel Context".)

**Design guidance:** keep `localBinders` as the single source of truth and
let `buildContextFromLocalBinders` be the explicit, documented view that
decides what the kernel sees. Resist introducing a *second*,
independently-mutated kernel context — the two would drift. If more
divergences like `valueIsProof` accumulate, that is the signal to promote
this function from "flat copy with one special case" to a clearly-stated
projection policy, not to fork the data structure.

## Open question: append-and-recurse vs. an explicit loop

Today, a block of statements (`claim …; … ; <conclusion>`) is elaborated
by **recursion**: each `claim` appends a binder and calls deeper to
elaborate the rest of the block under the extended `localBinders`. So the
local context is an immutable vector re-threaded at each step, and "frames"
pop implicitly when the recursion returns.

This is correct and has real virtues — binders cannot leak past their
scope, and exception unwinding cleans up for free — but it does **not**
match the natural mental model: *a mutable local context that you `push` a
proof onto when you see a `claim`, iterating over the block's statements in
a loop, then prove the goal at the end.* The two are equivalent in the way
tail recursion and a loop are equivalent.

If/when we revisit this, the candidate refactor is: iterate the statements
of a block in an explicit loop over a mutable context stack with explicit
`push`/`pop` (or scope guards), so the code reads the way the algorithm is
usually described. The cost to weigh is losing the "scope safety for free"
that the threaded-parameter form gives — an explicit stack must guarantee
pop-on-exception (RAII) and must not let a binder escape. No change is
planned yet; this note records the intent to examine it.

## See also

- `src/elaborator/term_utilities.{hpp,cpp}` — `LocalBinder`,
  `buildContextFromLocalBinders`, `zetaUnfoldLetBinders`.
- `src/kernel/kernel.hpp` — `ContextEntry`, `Context`, `Environment`,
  `isDefinitionallyEqual`.
- `src/elaborator/internal.hpp` — `Frame` / `FrameSnapshot`,
  `elaborateExpression` signature.

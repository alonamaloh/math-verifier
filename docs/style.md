# Style guide

The overriding goal: **a proof reads like what a mathematician would write
in a textbook**, with the kernel doing the typechecking. Optimize for
readability, not terseness. (Depth: `docs/conventions/`.)

## Naming

- **No abbreviations in declared identifiers**: `representative`, not
  `rep`. Use namespaces for brevity (`Natural.divides`), not truncation.
  Local-variable abbreviations are fine.
- Numerals `0`/`1`/`2` over `zero`/`successor(zero)`; `1 + n` over
  `successor(n)` in expressions.

## Let the prover work

- **Default to the auto-prover** (a by-less `calc`/`claim` step). Reach for
  a hint only when it fails.
- When you do hint, **justify the step by its reason, not the plumbing
  lemma**. Prefer `since <lemma>` for an illuminating reason (the IH, the
  operative lemma) — kept for the reader even if the prover doesn't need it
  — over a bare closer.
- **`ring` / `field` first** for any commutative-ring / field identity.
  Reach for hand-written associativity/congruence only after they fail.

## Don't call proof lemmas

- **Never apply a proof lemma to positional arguments** (`Foo.bar(a, b,
  proof)`, even `Foo.bar(proof)`). State the fact and cite it: `claim T by
  Foo.bar;` (arguments inferred, premises discharged from context), or
  chain it through `calc`. This is the single biggest readability lever;
  `scripts/cic_leak_report` counts every such call.
- **Recursion is `by_induction`**, so the recursive call is the local `IH`,
  not a self-call to the theorem.

## Avoid raw CIC

These are kernel bureaucracy a mathematician would never write — the
linter counts them, and there is always a math-like form:

| Instead of | Write |
|---|---|
| `congruenceOf(f, eq)` | a one-step `calc f(a) = f(b)` (diff-inference) |
| `rewrite(eq, term)` | `claim … by substituting eq` |
| `Equality.symmetry(eq)` | a reversed by-less `calc` step |
| `transport_proposition(…)` | `substituting`, or an element-interface lemma |
| a positional lemma call | `claim … by <lemma>` / `done by <lemma>` |
| raw `Subtype.make(…)` | the structure's `construction`/intro form |

## Closers & names

- Close the goal with `done` / `okay` (≡ `claim goal`); `goal` alone is not
  a closer.
- **Name a `claim`/`calc … as` only if you reference the name.** A dead
  name is noise — drop it (anonymous `claim T;` / `calc …;`); the
  auto-prover still finds the fact by type. Verify with
  `make … --check-redundant-by` (unused-name + redundant-`by` warnings).

## Mechanics

- **Wrap at column 140**, and only when the line genuinely needs it.
- **Build with `make -j 16 library`** (never bare `make`); validate
  elaborator changes with a clean `make tests`.
- **Commit coherent pieces often**; working directly on `main` is fine.

## The smell test

If a proof looks like term-soup — nested positional calls, `congruenceOf`,
raw `rewrite`, anonymous `Or.introduceLeft(…)` chains — rewrite it as the
mathematician's sentence: state each fact, justify it by its reason, and
let `claim`/`calc`/`done`/`by_induction` carry the structure.

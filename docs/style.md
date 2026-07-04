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
- **The by-less prover sees only `automatic` lemmas** (plus the local
  context and the ring/field/equality battery) — it no longer sweeps every
  imported lemma. So the threshold for a `by` is now sharp and mechanical:
  **add `by <lemma>` exactly when the lemma is *not* `automatic`**, and
  otherwise leave the step bare. Don't annotate a step the prover already
  closes — `by triangle_inequality`, `by weaken`, `by add_preserves` are
  the kind of "obvious" facts a mathematician never spells out; if
  they're `automatic`, drop them. When a *non*-automatic lemma is needed
  at many sites and is itself obvious, prefer **marking it `automatic`**
  over naming it at every call (mind the prover-perturbation risk — test
  the whole build). A redundant `by` is kept only for the rare
  *non-obvious strategic reason* that genuinely helps the reader
  (accepting the checker's warning); never for routine plumbing.
  (`since`, the old exempt-explanation keyword, has been removed.)
- **`ring` / `field` first** for any commutative-ring / field identity.
  Reach for hand-written associativity/congruence only after they fail.

## Don't call proof lemmas

- **Never apply a proof lemma to positional arguments** (`Foo.bar(a, b,
  proof)`, even `Foo.bar(proof)`). State the fact and cite it: `claim T by
  Foo.bar;` (arguments inferred, premises discharged from context), or
  chain it through `calc`. This is the single biggest readability lever;
  `scripts/cic_leak_report` counts every such call.
- **Recursion is `by induction`**, so the recursive call is the local `IH`,
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
| **`claim T by calc …`** | **a bare `calc …;`** (or `calc … as NAME;`) |
| raw `Subtype.make(…)` | the structure's `construction`/intro form |
| `⟨pA, pB⟩ : A ∧ B`, `⟨v, p⟩ : ∃…` | see "Connectives aren't tuples" |
| `Not(a = b)`, `¬(a = b)` | `a ≠ b` (the operator desugars to it) |

`a ≠ b` is the surface spelling of `Not(a = b)`; prefer it everywhere — in
hypotheses, claims, and goals — over the raw `¬(…)` / `Not(…)` forms.

**Never write `claim … by calc …` (or `claim NAME : T by calc …`).** This is
an anti-pattern, with no exceptions. A `calc` at statement position *is*
already a claim: it binds its `first <relation> last` endpoints into context
(anonymously, found by type-match), so wrapping it in a `claim` only restates
what the chain concludes — pure repetition, and the linter counts it as a CIC
leak (`claim-by-calc`). Write the bare `calc …;`, and add `as NAME` only when a
later step references the result *by name*. The same goes for the whole-proof
case: when a `calc` is the entire proof, return it directly (`:= calc …`),
never `:= { claim goal by calc … }`. Full mechanics: `conventions/calc-and-rewrite.md`.

## Connectives aren't tuples

`And` and `Exists` happen to be single-constructor inductives, but a reader
should never see the `⟨…⟩` tuple encoding of a logical connective. (Genuine
data records — `Ring`, a quotient representative, `Subtype` — **are** tuples;
`⟨…⟩` and `by_representatives x as ⟨a, b⟩` are fine for those.)

- **Build `A ∧ B`**: state the parts and let the prover conjoin — bare `done`,
  or `claim A by …; claim B by …; done`. Not `⟨proofA, proofB⟩`.
- **Build a bundle from named proofs** (`IsField`, `IsEquivalenceRelation`, …):
  `claim <proofTerm>;` for each component, then `done`. `claim` accepts a
  *proof* (a lemma/hypothesis) and introduces its type as the fact, so you cite
  the names without restating the long types — and the exact-typed facts let
  `done` conjoin them directly. So `claim Rational.is_commutative_ring; claim
  Rational.zero_not_equal_one; claim …; done`, not
  `⟨Rational.is_commutative_ring, …⟩`.
- **Build `∃ x. P`**: `witness v with <proof of P(v)>`. Not `⟨v, proof⟩`.
- **Destructure `∃`**: `choose v such that P from h`. `obtain ⟨…⟩` / `let ⟨…⟩`
  are the same tell — avoid them.
- **Use an `∧` hypothesis**: the prover already has both legs in context, so
  cite the fact / `done` — don't `let ⟨a, b⟩ := h` to name them.
- **Project one axiom from a bundled proof** (e.g. associativity out of an
  in-scope `IsGroup`/`IsRing`): a bare `done` — the prover decomposes the
  conjunction and finds the leg.

Audit with `make anon-tuple-report` (type-aware; opt-in via
`MATH_CHECK_ANON_TUPLES=1`). `make check` enforces it: `clean-anon-ratchet`
fails if the manifest's connective-`⟨…⟩` count exceeds `CLEAN_ANON_BUDGET`, so a
new one can't land in the clean set. Depth: `conventions/proof-style.md`.

## Layer the file

Keep proof-assistant machinery out of the mathematical proof. Standard
shape: **definition/construction → boundary lemmas → representation-level
kernel → thin adapter → public theorem.** Every lifted operation publishes a
representative-computation boundary lemma; consumers compare opaque-quotient
values through those lemmas, never `Quotient.class_of`/the bridge directly;
state the math lemma in boundary terms and quarantine the `cases` bridge in a
thin adapter. Name vacuous constructions (empty-type bijections, …) behind the
concept. Lead comments with the math; pull kernel/elaborator mechanics into a
`-- Implementation note:` aside. Depth: `conventions/proof-style.md`.

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
raw `rewrite`, `⟨…⟩` over an `And`/`Exists`, `cases <proof> { | Or.introduceLeft
… }` over a disjunction, anonymous `Or.introduceLeft(…)` chains — rewrite it as
the mathematician's sentence: state each fact, justify it by its reason, and let
`claim`/`calc`/`done`/`by induction`/`choose`/`witness`/`done by cases { … }`
carry the structure.

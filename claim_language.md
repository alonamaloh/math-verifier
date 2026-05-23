# Claim language: design plan

A higher-level surface language for proofs, compiling to the existing CIC kernel via the existing elaborator. Drafted 2026-05-13.

## Goal

A surface language in which mathematicians and LLMs can write proofs that read roughly like textbook proofs at the chosen granularity, with the option to drill into any step and see more detail in the same language.

## Why not just sugar on top of Lean

Lean's surface syntax is already reasonably close to what a human can comfortably type. The remaining gap between a Lean tactic script and a textbook proof is not syntactic — it's that mathematicians' proofs are information-dense because the reader fills in routine bookkeeping: witness destructuring, bound discharging, transport spelling, transitivity invocations. A genuinely higher-level language has to push that bookkeeping onto the *elaborator*, not just shorten the syntax for it.

## Core ideas

### Claim-based proofs

Each line is a CLAIM. The elaborator's job is to verify the claim from prior claims, the local context, and the library. Verification may invoke automation (the "hammer"). When the hammer succeeds, the line stands as written. When it fails, the user (or LLM) attaches detail.

### Footnotes

A claim that the hammer cannot close on its own may be paired with a footnote: a sequence of smaller claims and lemma applications that justifies it. The footnote is written in the **same language** as the main proof, just at finer granularity. Footnotes nest: a claim inside a footnote may itself have a footnote.

This makes proofs **fractal**: the same artifact reads as a one-page textbook proof at the top level and as a fully spelled-out formal proof at the leaves. The author picks the granularity; the reader picks the zoom.

### Rigid syntax

One form per concept. No English synonyms (no `hence` vs `thus` vs `therefore`). C-shape: braces, semicolons, named keywords. The language is small — probably 20-30 primitives total: `claim`, `witness`, `destructure`, `by_cases`, `by induction`, `apply`, `suffices`, `contradiction`, `unfold`, `rewrite`, `calc`, and a handful more. Errors are local and specific.

### Hammer + footnote separation

The hammer may search expensively. The footnote, once written, is a deterministic record of how the search closes the claim: a list of intermediate claims and lemma applications. Re-verification is fast — no search. Footnotes are kernel-verified, so a buggy hammer cannot smuggle in unsoundness.

## Worked example

```
theorem has_prime_divisor(n: Nat, h: 2 ≤ n): ∃ p. prime(p) ∧ p ∣ n {
    by strong_induction on n with ih;
    by_cases on prime(n) {
        case yes as p_n:
            witness n with ⟨p_n, divides_reflexive(n)⟩;
        case no as np_n: {
            claim ∃ d. 2 ≤ d ∧ d < n ∧ d ∣ n;
                -- footnote:
                apply prime_or_proper_divisor(n, h);
                case prime: contradiction with np_n;
                case composite as ⟨d, h_lo, h_hi, h_div⟩: witness d;
            destructure as ⟨d, h_lo, h_hi, h_div⟩;
            claim ∃ p. prime(p) ∧ p ∣ d by ih(d, h_hi, h_lo);
            destructure as ⟨p, h_p, h_pd⟩;
            witness p with ⟨h_p, divides_transitive(h_pd, h_div)⟩;
        }
    }
}
```

Compare with the current ~50-line `Natural/prime_divisor.math`. The shape of the proof is visible at a glance, and every line is a recognizable mathematical move.

## Build phases

### Phase 1 — Surface syntax, zero hammer

Parser for the new language. Desugaring to the existing CIC kernel via the existing elaborator. Every claim must come with enough detail (named lemmas, explicit witnesses) for the elaborator to construct the kernel term directly — no automated search yet.

What Phase 1 delivers:

- Implicit arguments at theorem call sites.
- Anonymous constructor notation (`⟨…⟩` for `Exists`, `And`, etc.).
- `destructure as ⟨…⟩` and `let ⟨…⟩ := …` for eliminator chains.
- `by_cases` and `by induction` as structural primitives.
- `witness <expr> with <proof>` for `Exists.introduce`.
- `apply lemma(args)` for direct lemma invocation.
- `claim X by <proof>` as the basic unit.

Test target: rewrite `Natural/prime_divisor.math` and a few smaller files in the new syntax. Measure compression and readability. Estimate: 3-5x shorter from syntax alone, with no automation.

### Phase 2 — Trivial hammer

A claim without a footnote tries, in order:

1. Reflexivity (`rfl`).
2. Match against an in-scope hypothesis.
3. Apply each imported lemma whose conclusion type unifies with the goal.

Closes roughly 30-50% of one-step claims. Errors say "couldn't close from {context}; tried: lemma X, lemma Y, ...".

### Phase 3 — Structured hammer

Definitional unfolding, one-step equality rewriting, depth-2 lemma chaining, narrow decision procedures (e.g. linear arithmetic on `Natural`). At this point most arithmetic and order claims close without footnotes.

### Phase 4 — LLM in the loop

Failed claims invoke an LLM with `(context, goal, available_lemmas, why_it_failed)`. The LLM proposes intermediate claims as a footnote. Each suggestion is kernel-verified — no trust in the LLM for soundness, only for usefulness. The user can accept, edit, or request another proposal.

### Phase 5 — Auto-collapse

As the hammer improves, previously-detailed footnotes may become closable by the hammer directly. The system can suggest "this footnote is now redundant — fold it?". Proofs monotonically shrink toward the highest-level form the current hammer supports.

Every phase produces a usable system. Each phase makes the average proof shorter; none invalidates earlier proofs.

## Design decisions still open

- **File extension.** Probably `.proof`, so the new language can coexist with `.math` during the transition.
- **Trace format for footnotes.** Plain proof text is the source of truth. Whether to cache a context+lemma hash for change detection is a later question.
- **Stability under library refactor.** Frozen-with-rename-tracking vs. regenerate-on-miss. Probable default: frozen, with a lint pass that re-runs the hammer when context hashes change.
- **Notation.** ASCII vs. Unicode. Probably both, with ASCII forms for everything.
- **Universe handling.** Fully implicit at the surface; the elaborator infers and reports.
- **Module system.** Reuse the existing `import` mechanism from `.math`.

## Phase 1 starting moves

1. Pick the file extension and tokens.
2. Sketch the grammar (BNF or similar).
3. Build the parser.
4. Build the desugaring layer mapping each surface construct to a kernel term via the existing elaborator.
5. Transcribe one short `.math` file (e.g. `Equality/basics.math` or `Logic/basics.math`) to validate the design.
6. Transcribe `Natural/prime_divisor.math` as the main proof-of-concept.

## Phase 1 grammar (concrete starting subset)

Implementation strategy: extend `.math` additively rather than introduce a new file extension. The new constructs are extra forms alongside the existing ones; old files keep working. A `.proof` extension may follow once the new forms have displaced the old.

New syntactic forms, MVP slice:

```
// New theorem body form: a block of statements ending in a final expression.
theorem_decl_block
        := "theorem" qualified_name universe_params?
           "(" binder ")" * ":" expression
           "{" statement* expression "}"

statement
        := let_stmt | cases_stmt

let_stmt
        := "let" pattern (":" expression)? ":=" expression ";"

cases_stmt
        := "cases" expression "{" case_clause+ "}"

case_clause
        := "case" pattern "=>" (expression | block_expression)

block_expression
        := "{" statement* expression "}"

// Patterns extend the existing pattern grammar with anonymous tuples.
pattern
        := bare_name | constructor_pattern | tuple_pattern
tuple_pattern
        := "⟨" pattern ("," pattern)* "⟩"

// New atomic expression: anonymous tuple. Desugars per expected type.
tuple_expression
        := "⟨" expression ("," expression)* "⟩"
```

Desugarings:

- `⟨a, b⟩` at expected type `And(A, B)` desugars to `And.introduction(a, b)`. At `Exists(A, P)` desugars to `Exists.introduce(a, b)`. At any other single-constructor inductive, applies that constructor (with parameters inferred). N-ary tuples right-associate: `⟨a, b, c⟩` is `⟨a, ⟨b, c⟩⟩`.
- `let ⟨x, y⟩ := h; rest` where `h : And(A, B)` desugars to `And.eliminate(A, B, GoalType, fun x y => rest, h)`. For `Exists`, to `Exists.eliminate(...)`. The goal type is the type of the surrounding block.
- `cases h { case Ctor(args) => body; ... }` where `h : I(...)` desugars to `I.eliminate` (the convention-named eliminator) or to the kernel recursor with appropriate motive. The motive's return type is the expected type of the surrounding block. Case bodies see the destructured names.

Out of MVP scope (will follow in subsequent slices):

- `claim` / `apply` / `witness` / `suffices` / `contradiction` / `by induction` block forms.
- Implicit arguments at theorem call sites.
- Footnotes.
- Any hammer.

## Phase 1 implementation status (landed 2026-05-13)

The MVP slice above is implemented end-to-end. The surface forms shipped:

- Anonymous tuple expression `⟨a, b, ..., n⟩` desugaring per expected
  type to the unique constructor (right-associating for K=2 constructors
  when N > 2 — handles nested Exists/And uniformly).
- Anonymous tuple pattern `⟨a, b, ..., n⟩` with the same right-associate
  rule for destructuring.
- `cases scrutinee { | pattern => body  | pattern => body ... }` as an
  expression. Non-indexed inductives only. Goal-type from the
  surrounding expected type.
- `let ⟨pat, pat, ...⟩ := value in body` — single-clause `cases` sugar.

Test: `library/Natural/prime_divisor_v2.math` proves the same
`has_prime_divisor` theorem as the original `prime_divisor.math` in
67 lines vs 170 — 2.5× compression, with the proof's structure
(strong induction, prime/composite split, destructure-and-recurse)
visible at a glance.

A related bug in the elaborator's `buildCaseLambda` was uncovered and
fixed in the same change: the per-arg "is recursive" detection was
running after parameter substitution, which false-positived when a
parameter value happened to share its head with the inductive (e.g.
matching on `And(A, And(B, C))` made And.introduction's second arg
appear recursive). The detection now uses the original constructor
type.

Next slice candidates: implicit arguments at theorem call sites
(removes the motive/IH boilerplate still visible in `prime_divisor_v2`),
plus a statement-level proof block to introduce `claim`/`apply`/
`witness`.

## Phase 2 updates (landed 2026-05-13)

### Phase 2.0 — Arity-based inference at theorem call sites

Generalised the constructor parameter inference to all
Axiom/Definition (theorem) calls. When the user supplies strictly
fewer value arguments than the declaration's leading Pi count AND an
expected type is in scope, the elaborator fills in the missing leading
arguments via backward-forward unification.

Concretely, `Natural.divides_transitive(p_div_d, d_div_n)` now expands
to the full 5-arg call with prime/divisor/subject inferred from the
proof arguments' types and the expected return.

Two unifier bugs surfaced and fixed:

- Application-case head check: the unifier had been pointwise-aligning
  two Application chains without first verifying their function-chain
  heads match, which let `Natural.divides(_, _)` "unify" against
  `Exists(Natural, _)` and assign metavariables to wrong-typed targets.
- Under-binder assignment: the unifier refused all metavariable
  assignments when descended into a binder, even when the target's
  free Bound vars all referenced outside the binder. Now assigns
  with a shift-back when safe.

### Phase 2.1 — Explicit implicit binders `{x : T}`

Surface syntax for `{x : T}` and `{x y z : T}` binders in lambdas, Pi
types, definitions, theorems, and inductives. The elaborator tracks
the leading implicit count per declaration and engages inference
whenever the user provides exactly `totalPi - implicitCount` arguments
— independent of whether arity-based inference would have engaged.

Restriction (Phase 2.1): implicit binders must form a leading
consecutive prefix; interleaved `{...}` and `(...)` is rejected.

Restriction (Phase 2.1): when an implicit binder has type `Type`
(introducing an auto-bound universe parameter), the user must call
with explicit `.{u}` universe arguments. Combining leading-arg
inference with universe-arg inference at the call site is a separate
slice.

### Phase 2.2 — Motive abstraction in `cases`

When a `cases` expression's scrutinee is a local variable, the motive
now abstracts over that variable so that the case bodies see a goal
specialised to the constructor they handle. This is what makes
induction-by-cases sound:

  theorem reflexive (n : Natural) : n = n :=
    cases n {
      | zero => reflexivity(zero)
      | successor(k) => reflexivity(successor(k))
    }

For non-variable scrutinees the previous shift-by-one behaviour is
preserved.

### Phase 2.3 — IH naming in `cases` patterns

A `cases` pattern over a recursive inductive may now bind names to
the induction hypotheses produced for each recursive constructor
argument:

  cases a {
    | zero => reflexivity(zero)
    | successor(predecessor, ih) => congruenceOf(successor, ih)
  }

For a constructor with N value arguments of which R are recursive,
the pattern accepts either N names (no IH access, auto-generated
internal names) or N + R names (trailing R name the IH binders in
declaration order). Combined with 2.2 this is enough to replace
many pattern-match-definition uses with the more compositional
`cases` form.

### Phase 2.4 — Statement-level proof blocks

New theorem body form: `{ let pat := v; …; final_expr }`. Each `let`
statement is semicolon-terminated and may use either typed-name form
(`let x : T := v`) or anonymous-tuple destructure (`let ⟨a, b⟩ := v`).
The block desugars at parse time to a nested `let-in` chain ending in
the trailing expression. `{ … }` blocks also work as expression
atoms, so the same syntax appears inside case clauses.

Library impact: `Natural/prime_divisor_v3.math` proves the prime-
divisor theorem in 60 lines (vs 71 for v2, 170 for the original
eliminator-chain version). The remaining bulk is the explicit motive
lambda passed to `Natural.strong_induction` and its step's IH-type
spell-out — both of which would require motive inference (a form of
higher-order pattern unification) to eliminate.

### Phase 2.5 — Miller-pattern higher-order unification

The unifier now handles the canonical Miller-pattern case: when the
pattern is `App(FreeVar(metavar), Bound(k))` with `k` referring to a
binder the unifier has descended into, it solves the metavariable by
abstracting the target over that bound variable. This unlocks
predicate inference for implicit binders like `{P : T → Proposition}`:

  theorem nat_ind {P : Natural → Proposition}
          (zero_case : P(zero))
          (step : (k : Natural) → P(k) → P(successor(k)))
          (n : Natural) : P(n) := …

  -- caller omits P; it is inferred from step's type
  theorem n_equals_n (n : Natural) : Equality(Natural, n, n) :=
    nat_ind(
      reflexivity(zero),
      fun (k : Natural) (ih : Equality(Natural, k, k)) =>
        congruenceOf(successor, ih),
      n)

Restriction (Phase 2.5): only the unary case is implemented
(metavariable applied to one bound variable). Multi-argument
abstractions and motive inference for theorems whose body needs
expected-type propagation through a Lambda with a metavar-headed
return type remain unsupported.

### Phase 2.6 — Indexed-inductive support in `cases`

`cases` now works on indexed inductives like `LessOrEqual(s, b)` and
`Equality(A, x, y)`. The motive is constructed by wrapping the body
in one Lambda per index (in scrutinee order, outermost first), and
the recursor is applied to the index values in the same order before
the scrutinee.

Restriction (matches the pattern-match-definition rule): each index
value in the scrutinee's type must be a distinct local-binder
BoundVariable.

  theorem LessOrEqual.invert (s b : Natural) (h : LessOrEqual(s, b))
        : Or(s = b, ∃ p. b = succ(p) ∧ s ≤ p) :=
    cases h {
      | LessOrEqual.reflexivity(n) => Or.introduceLeft(reflexivity(n))
      | LessOrEqual.step(small, large, sub) =>
          Or.introduceRight(Exists.introduce(large, …))
    }

## Phase 3 — Statement-form surface and aggressive auto-prover (planned 2026-05-22)

### Why a new phase

Phases 1 and 2 got us to "the kernel bureaucracy mostly hides itself
once you write the right calls" — implicit args, anonymous tuples,
`cases` with motive abstraction, statement-level blocks. The remaining
gap to *textbook* style is two-fold:

1. **Statement-form proofs** — a textbook proof is a sequence of
   English-flavoured statements (`Suppose ε > 0. Choose N such that
   …. Then for all n ≥ N, …`), not a tree of nested expression
   forms. Phase 1's `claim … by …` is the right idea but we never
   wired the surrounding constructs (`suppose`, `choose`, `let`-for-
   ∀-intro, `it suffices to show`).
2. **Aggressive auto-prover** — most lines in textbook proofs are
   closed by the reader filling in routine algebra/congruence/
   transitivity. To match that, every `by`-less slot (not just calc
   steps) needs to run the same battery: `ring`, diff-inferred
   congruence, hypothesis match, lemma-index lookup, eventually
   `linarith`/`tauto`/`decide`.

### Vision

A surface where the user never writes `congruenceOf`,
`Equality.transport_proposition`, `Equality.transitivity`,
`Quotient.lift` boilerplate, or any other CIC plumbing. Proofs read
as a sequence of `claim`s, `calc`s, `suppose`s, `choose`s, and
`let`s. The kernel is still doing the work; the user just doesn't
see it.

Same fractal property as Phase 1: the user can drill into any step
by attaching `by <explicit-proof>` when the auto-prover can't close
it. Failed steps produce diagnostics good enough that the user knows
which lemma to add.

### Surface decisions

#### Claims — `T as name by proof`, not `name : T by proof`

The old `claim name : T by proof;` overloaded `:` (type ascription,
binder type, return type, hypothesis type). New form:

```
claim T as name by proof;     -- named binding
claim T by proof;              -- anonymous (auto-prover in scope by type-match)
claim T;                       -- by inferred; auto-prover runs at top level (option b)
```

Reads as math: "the proposition `T`, call it `name`, follows by
`proof`." Consistent with the existing `calc … as name;` form. The
`claim` keyword stays required for now; may become optional later
since a bare statement at block position is unambiguous.

#### `suppose` — hypothesis introduction at block head

```
suppose P as hyp;
…
claim Q by …;
```

If the block ends with a claim of type `Q`, the whole block proves
`P → Q`. Only at the head of a block — a mid-block `suppose` has no
clear "stop supposing" point.

Reductio ad absurdum is the special case: `suppose ¬P as hyp; …;
claim false by …;` proves `P`. Classical LEM is on by default; the
auto-prover bridges `¬¬P → P` silently. The kernel doesn't change —
the auto-prover just gains one more rewrite it knows.

`by reductio_ad_absurdum { suppose ¬P as hyp; …; claim false by …; }`
is sugar for the same shape with documented intent.

#### `let` — object introduction

`let ε > 0;` works ONLY when a `convention` has established `ε`'s
type. Without a matching convention, the user writes:

```
let ε ∈ ℝ with ε > 0;
```

`∈` unifies type-membership and set-membership at the surface (the
kernel doesn't care — both desugar to a binder plus a hypothesis).
`with` matches the existing `cases … with`, `convention … with`
keywords. `such that` rejected as too long for the same role.

#### `choose` — ∃-elimination

```
claim Exists(N, sequence_eventually_bounded_after(N)) by …;
choose N such that sequence_eventually_bounded_after(N);
```

`choose` keeps its own keyword rather than folding into `suppose`
with destructuring — `choose N such that P(N)` reads more clearly
than `suppose ⟨N, hyp⟩ : ∃ N. P(N)`.

#### Biconditional — no special syntax

Prove `P → Q` and `Q → P` as two separate (suppose-headed) blocks.
The auto-prover combines them into `P ↔ Q` when the user states
that claim.

#### Cases vs. suppose

`suppose` is for single hypothesis introduction. Case analysis goes
through `by cases { … }`, which gets its own slot in the order of
work below.

#### Other forms in scope

- `it suffices to show …` — goal rewriting against a known reduction.
- `by cases { … }` — proves any proposition by case analysis.
- `by induction { … }` — strong induction by default.

### Auto-prover scope — option (b)

Every `by`-less slot is a tactic call site, not just calc steps.
Concretely: `claim T;` with no `by` fires the same dispatch as a
calc step's auto-close path.

Dispatch table (additive — each entry tries independently and stops
on first success):

1. **Local hypothesis match** — already wired.
2. **Lemma-index lookup** — already wired.
3. **Reflexivity** — already wired in many places.
4. **Diff-inferred congruence** — already wired in calc; lift to
   top-level by treating `claim T;` as a one-step calc whose
   endpoint we're trying to reach.
5. **`ring`** — wire into the dispatch (currently only fires when
   explicitly invoked as `by ring`).
6. **Symmetry under `Iff`** — for the auto-combination of P→Q and
   Q→P into P↔Q.
7. **Future**: `linarith`, `tauto`, `decide`, then the full
   "obviously" umbrella.

Goal: existing library proofs that currently use explicit
`congruenceOf` / `Equality.transitivity` / `Equality.transport_proposition`
should re-typecheck after stripping those calls.

Tradeoff: failure diagnostics get worse — "I tried 6 tactics, none
closed this" doesn't tell the user which one was *almost* right.
Need to track which tactic got furthest on a failed step so the
error message can point at the most promising near-miss. Worth
designing now rather than retrofitting.

### Deferred to later phases

- **WLOG** — sugar for `by cases { case x ≤ y => … | case y < x =>
  by symmetry of the goal, reduce to the first case }`. Surface
  shape: `wlog x ≤ y by <symmetryProof>;`. The user supplies the
  symmetry proof; the elaborator handles the case split and reduction.
  Defer until the surface stabilises and we have feedback.
- **Math-flavoured errors** — the fully math-rephrased version is
  research-grade. Tractable subset (pretty-printed goals + a small
  template library for common shape mismatches like "proved x ≤ y
  but need x < y") can come later.
- **Notation extensibility** — current notation suffices for now.
- **`claim` as an optional keyword** — revisit once we see how dense
  real proofs get.

### Order of work

1. **Auto-prover expansion (this phase's first step)** — option (b)
   at top-level `claim` slots; add `ring` and diff-inferred
   congruence to the dispatch; record "most promising near-miss"
   for failed steps. Validate by stripping explicit `congruenceOf`
   calls from a representative library file and re-typechecking.
2. **Statement-form features** — `suppose`, `choose`, `let ε > 0` /
   `let ε ∈ ℝ with …`, `it suffices to show`. Mostly parsing +
   desugaring; the auto-prover already covers the proof obligations.
3. **`by cases` / `by induction`** — strong induction by default;
   `by cases` for arbitrary props. Self-contained, builds on (1) for
   subgoal closure.
4. **"Obviously" umbrella** — extend dispatch with `linarith`,
   `tauto`, `decide`. The make-or-break automation for textbook
   fidelity.

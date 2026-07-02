# PLAN_LANGUAGE_IMPROVEMENTS.md — the declarative endgame

This plan distills a design review of the surface language (July 2026)
into concrete workstreams. The organizing principle, stated once:

> **Every block in the language announces or concludes with an explicit
> proposition.** A proof is a sequence of stated facts; the elaborator's
> job is to verify each stated fact and to silently discharge the facts
> a mathematician wouldn't bother to state. Nothing is ever proved that
> isn't on the page — but plumbing that carries no mathematical content
> should never be on the page either.

The plan has three parts: (A) the statement language — collapsing the
construct zoo into a small core; (B) the auto-prover — a tiered,
deterministic discharge engine that eliminates breadcrumb claims without
reintroducing global theorem search; (C) supporting work — lints,
diagnostics, documentation, migration.

Workstreams are ordered by leverage. Within each item: motivation,
design, implementation notes, and open decisions. Anything marked
**DECIDE** needs a human call before implementation.

---

## Part A — the statement language

### A1. Keyword-free claims and calc (drop `claim` and `calc`)

**Motivation.** In this language every stated proposition is verified,
so the `claim` keyword adds no information. A textbook proof is
literally a sequence of stated propositions; the keyword is filler.
Similarly, a sequence of relations *is* a calc chain — blackboard
notation needs no announcement.

**Design.**
- A bare statement `P;` at statement position: elaborate the
  expression, inspect its type `T`.
  - If the expression **is a proposition** (its type is a sort of
    Prop): hand `P` to the auto-prover; on success add `P` to the
    local context.
  - If the expression **is a proof** (`T : Prop`): add `T` to the
    local context directly.
  - Anything else (e.g. an under-applied lemma of Π type): error,
    phrased as a failed claim, not as a raw elaboration error (see C2).
- A relation chain `a R₁ b R₂ c … ;` (inline or with the current
  multi-line calc layout, minus the `calc` keyword): each adjacent pair
  is a step closed by the auto-prover or by an attached `since`/`by`;
  the outer relation between the endpoints (strongest relation in the
  chain, current calc rules) enters the local context. A single
  relation is a one-step chain — `claim` and `calc` genuinely merge
  into one construct.
- **Block endings.** A block may end by restating the goal (or
  something the prover bridges to it). This is the "therefore, P. ∎"
  ending; it also makes `done` unnecessary in the common case. Keep
  `done` as a synonym for "the goal, restated" during migration.
- **Rhetorical connectives as noise words.** `then`, `hence`,
  `therefore`, `note that` parse before any bare statement and are
  semantically identical to it, except: connectives that imply
  consequence (`then`, `hence`, `therefore`) hint the prover to try
  the most recently established facts first. This gives proofs the
  rhythm of prose at zero semantic cost, and gives LLMs harmless
  places to put connective tissue they emit anyway.
- **Keep `suppose` mandatory.** Assumption is the one speech act that
  genuinely differs from assertion. Never infer it.

**Implementation notes.**
- The proposition-vs-proof dispatch is type-directed and decidable;
  the subtlety is error messaging (C2).
- `calc … as NAME` survives as `<chain> as NAME;` for the rare case a
  later step references the name textually; the lint for unused names
  stays.

**DECIDE:** whether `claim`/`calc` remain parse-accepted (linted) or
are removed outright after migration.

---

### A2. Statement-addressable hypotheses (names become optional)

**Motivation.** Mathematicians refer to facts by restating them ("but
m ≥ 1"), not by identifier. LLMs are good at restating propositions
and bad at inventing and consistently reusing spellings like
`mGeqNs`. Once facts can be referenced by statement, most binder
names, `as NAME` clauses, and re-derivation claims disappear.

**Design.**
- Anywhere a proof term/hypothesis is expected, a proposition in that
  position means "the in-scope fact with this statement" — matched up
  to defeq (and, after A6, up to cast normalization).
- **Ambiguity is an error.** If two distinct hypotheses match, reject
  loudly and ask for a name — mirroring the canonical-embeddings
  principle (never silently pick).
- Names remain available and are pure documentation.
- Inside `by cases` branches (A4): referencing an outer fact by name
  or statement silently transports it along the branch's case
  equation (this replaces `refining`).

**Implementation notes.** The local-hypothesis matcher in the calc
auto-prover is most of the lookup; subtree hashes give O(1) candidate
filtering. Defeq-equality of statements must use the existing kernel
defeq, not syntactic equality.

---

### A3. `suppose … for proving / for contradiction` — hypothetical reasoning

**Motivation.** "Suppose for contradiction" is negation introduction;
"to show Q, suppose P" is implication introduction. Both are distinct
speech acts from case analysis, and both should announce their exit
before the reader enters the block.

**Design.** One grammar: `suppose P for <exit> { … }`.
- `suppose P for contradiction { … }`: block must reach
  `contradiction` / `False`. Establishes `¬P`. If `¬P` closes or
  prover-bridges to the current goal (e.g. via trichotomy: goal
  `n < m`, supposition `m ≤ n`), the block is the whole proof;
  otherwise `¬P` enters the context and the proof continues. Note the
  bridge is where classical double-negation elimination silently
  enters — acceptable in this library, but the elaborator should know
  it's doing it.
  The `for contradiction` marker is **mandatory** (a block that turns
  out to be a reductio only at its last line is a bait-and-switch, and
  the marker enables the precise error "supposition was to be refuted,
  but block concludes P").
- `suppose P for proving Q { … }`: block proves Q under P; establishes
  `P → Q` in context (or closes the goal if it bridges). The
  `for proving Q` clause is **optional** — with A1's restate-the-goal
  ending, `suppose P { …; Q }` is already unambiguous — but when
  present it is checked against the block's conclusion, and it pins
  the expected type from the first line (better bridging, better
  errors). Lint: suggest adding the announcement when a block exceeds
  a length threshold.
- **`take` analog:** `take x : T for proving Q(x) { … }` establishes
  `∀x. Q(x)`. If `suppose` gets exit annotations and `take` doesn't,
  someone will trip on the asymmetry. The combined header "let x be
  arbitrary with P(x); we show Q(x)" is the two-statement sequence
  `take x : T; suppose P(x) for proving Q(x) { … }`.
- **One hypothesis per `suppose`.** Resist `suppose P, Q for proving R`
  (ambiguous between `P → Q → R` and `P ∧ Q → R`); nest instead.
- **Relation to `suffices`:** keep both, keep them crisp. `suffices P
  by <justification of P → goal>` changes the goal (backward);
  `suppose … for proving` never changes the goal, it only adds a fact
  (forward). Also add `suffices … by definition of X` to replace the
  `unfold X in (lambda …)` proof-header idiom.

---

### A4. `by cases` — the only case analysis in proofs

**Motivation.** The current zoo (`cases` with patterns, `cases … with
eq`, `cases … refining`, `decide`, proof-side if-then-else,
single-constructor `cases`) does four different jobs. Sorted
semantically: propositional split, structural split, destructuring,
and case-knowledge propagation. Structural split is a special case of
propositional split ("n is zero or a successor" *is* a proposition);
destructuring isn't case analysis at all (one branch); propagation
should be automatic, not syntax.

**Design.** The favored form generalizes to be the *only* form:

```
prove <fact> by cases {
  case <prop1>: <proof of fact under prop1>
  case <prop2>: <proof of fact under prop2>
}
```

- Proves `<fact>` in every branch, discharges exhaustiveness
  (`prop1 ∨ prop2 ∨ …`) via the auto-prover, adds `<fact>` to context.
  With A1, `prove <fact>` can be just the bare fact followed by
  `by cases`.
- **`otherwise:`** clause for the complement of the other cases —
  makes exhaustiveness trivially `P ∨ ¬P` and **deletes `decide`
  entirely**.
- **Structural cases with witness binders:**
  `case n = successor(k) for some k: …`. The elaborator recognizes
  constructor-coverage shapes and emits the recursor. Per-inductive
  coverage lemmas (`Natural.cases_covered : ∀n. n = 0 ∨ ∃k. n =
  successor(k)`) are auto-generated at inductive-declaration time so
  exhaustiveness stays out of the trusted base.
- **Substitution rule (load-bearing):** when a case proposition is a
  constructor equation, the elaborator *substitutes* it into the goal
  and into any referenced hypotheses — not merely makes it available —
  so the kernel can ι-reduce. This is what lets `refining` and
  `cases … with eq` be deleted rather than kept as escape hatches. It
  must be reliable, not best-effort, or users will fall back to raw
  recursors.
- Exhaustiveness obligations should almost always discharge silently
  (totality/trichotomy lemmas live in the Part-B rule index); when
  they don't, the error must name the gap: "cases not shown
  exhaustive: missing m = n".
- **Induction as a variant, not a fifth construct:**

```
by induction on n {
  case n = 0: …
  case n = successor(k) for some k, with IH : P(k): …
}
```

  Same clause syntax plus a recursion permit; strong induction changes
  what IH quantifies over. Replaces `by_induction`/
  `by_strong_induction` blocks (keep the old spelling as sugar if the
  migration is heavy). The induction variable keeps its name — no
  `subject` renaming.
- **Lint (both directions):** a `cases` branch consisting solely of a
  contradiction should be a `suppose … for contradiction` folded into
  the other branch; a refuted supposition never used afterward is a
  vestigial detour.

**Settled: clause keyword is `case P:`, with `otherwise:` for the
complement.** (Decided July 2026; do not relitigate.) Rationale:
(1) "Case 1: m ≤ n" is the literal textbook idiom — `case` is read
correctly on first sight by mathematicians and LLMs, `in` has no
prose antecedent; (2) `case …: / case …: / otherwise:` self-labels
when skimming a long proof, and with A1 removing most keywords the
survivors carry more structural-signaling load; (3) the colon can
terminate the proposition, so no mandatory parentheses — arms with
binders stay clean (`case n = successor(k) for some k:`);
(4) consistency with the existing `by_induction` arm syntax
(`case zero:`), which matters once induction is unified as a `by
cases` variant. `case` is contextual — only recognized at
statement-head inside a `by cases` / `by induction` block — so it
needs no global reservation and cannot collide with identifiers.
The older `in (P):` experiments should be migrated, not kept as a
synonym.

---

### A5. `obtain` / `take … as` — destructuring, unified

**Motivation.** `obtain`, `choose N as h from e`, `choose N such that
P(N)`, and single-constructor/quotient `cases` all destructure. Three
overlapping spellings plus one masquerading case-analysis.

**Design.**
- One construct: `obtain <witnesses> with <property>;` — witness names
  first, property stated inline (and thereafter statement-addressable
  per A2), source inferred by type-match against in-scope facts, with
  `from <fact-or-name>` for disambiguation.
  Example: `obtain k with m = 2 * k;` (source: the in-scope `2 ∣ m`).
- Patterns flatten **nested ∃/∧ in one step**:
  `obtain m, n with 1 ≤ m ∧ 1 ≤ n ∧ m*m = 2*(n*n) from solutionExists;`
  Conjunctions added to context are also registered
  conjunct-by-conjunct (already implemented — keep).
- Quotient representatives get the mathematical name:
  `take x as representative (a, b);` — replacing constructor-spelled
  `cases x { | Representative.make(a,b) => … }` for the
  single-"branch" use. `by_representatives` and quotient `cases`
  forms route here.
- `choose` survives, if at all, as a linted synonym.

---

### A6. First-class `eventually` quantifier

**Motivation.** Every limit argument currently pays the
N₁/N₂/maximum(N₁,N₂)/re-derive-N≤m tax by hand. This is the
highest-leverage single addition for Real, PAdic, ComplexNumber — a
lightweight, hardcoded fragment of filters; the general theory is not
needed.

**Design.**
- `eventually (m). P(m)` ≡ `∃N. ∀m ≥ N. P(m)`; a first-class binder
  form the elaborator understands.
- Elaboration rules: (i) closed under ∧ — combining k eventual
  hypotheses takes max of thresholds invisibly; (ii) goal position:
  `eventually (m): { … }` / `eventually (m): <calc>` proves an
  eventual goal from eventual hypotheses, entering a scope where each
  eventual hypothesis is usable at the bound variable `m`;
  (iii) hypothesis position: `choose N with eventually (m). Q(m) from
  h;` when the threshold itself is needed.
- Monotone: `eventually P` + `∀m. P(m) → Q(m)` (or a prover-bridgeable
  gap) gives `eventually Q`.
- Library side: define the predicate in `Real/sequence.math` (or a
  new `Logic/eventually.math` generic over an ordered index), prove
  the ∧-closure and monotonicity lemmas the elaborator emits.
- Sugar worth considering after the core lands:
  `for sufficiently large m: …` as a prose spelling of the goal form.

---

### A7. Small statement forms

- **`contradiction` terminal.** Bare `contradiction` closes any goal
  when in-scope facts are jointly absurd, via a small refutation kit:
  `x < x`, `successor(k) ≤ k`, `P` with `¬P`, constructor
  disjointness, `0 = successor(_)`, plus one round of the Part-B
  linear tier. `contradiction with <fact>` names the clashing fact
  for the reader (statement-addressable per A2). Deletes the
  "restate absurdity, then `done`" pattern.
- **`from <fact>: <instance>;`** — restate a hypothesis after
  substituting in-scope equations into it; the elaborator checks the
  stated form is reachable by rewriting. Replaces most
  `by substituting` incantations with the transformed statement
  itself on the page.
- **`since <lemma>` as a whole proof body** — the prover does the
  logical plumbing between the goal and the lemma's form: intros,
  ∃/∧ flattening, `Or.self`, argument discharge from context. Pure
  logic-shuffling with no mathematical content should never be on the
  page. (`sqrt_two_irrational := since no_double_square`.)
- **Hypothesis discharge at call sites.** When applying a lemma or an
  IH, arguments whose types are propositions already in scope (up to
  defeq / cast-normalization) are filled automatically;
  `no_smaller_solution(n, k)` supplies `n < m`, `1 ≤ n`, `1 ≤ k` from
  context. This generalizes `?` from goal-driven to context-driven.
- **`let` in definition bodies + module-local `open`.** Definitions
  like `bisectionStepWithDec` repeat 4-line subexpressions; allow
  `let` in definition bodies and a file-scoped
  `open Real.BisectionInterval` so a file about X can write
  `left(state)`.
- **Piecewise definitions only.** Pattern matching and if-then-else
  survive exclusively in definitions (computation), never in proofs.
  Optionally adopt piecewise syntax (`… if P(x)` / `… otherwise`) so
  definitions share the case vocabulary without sharing machinery.

---

## Part B — the auto-prover: tiered, deterministic discharge

**Constraint (hard-won):** global search over imported theorems was
removed for performance. Do not reintroduce it under another name.
The replacement insight: breadcrumb claims fall into a few *judgment
families*, each with a deterministic, syntax-directed procedure linear
in the term. Search appears only in the last, budgeted tier.

### B1. Tier architecture

Cheapest first, strict budgets, first success wins:

| Tier | Procedure | Cost |
|------|-----------|------|
| 0 | Context lookup (stated + derived facts; conjunct index) | O(1) via hash-indexed context |
| 1 | Defeq / reflexivity | existing |
| 2 | Ground evaluation (literal comparisons, arithmetic) | linear |
| 3 | Cast normalization (B3), then retry 0–2 | linear |
| 4 | Sign/judgment recursion (B2) | linear, no backtracking |
| 5 | Single-position-diff rewrite index (existing) — **extended to order relations** (B4) | existing |
| 6 | Budgeted linear-arithmetic combiner over context facts | metered |

- **No separate memo cache — derived facts enter the local context.**
  Side conditions repeat constantly (`0 ≤ secondSum` should be proved
  once), but a dedicated cache would be a shadow context with its own
  scope stack and hash index. Instead: every fact the prover
  discharges is recorded as an **anonymous fact in the local
  context**, and the **hash index over the context is a general
  feature** — the same structure serves A2 statement-addressable
  references, tier-0 lookup, conjunct-splitting, and reuse of
  discharged side conditions. One blackboard; stated and derived
  facts live on it identically; scope safety is inherited from the
  context's existing block discipline for free.
  - **Insertion depth — one rule:** a derived fact is inserted at the
    level of the deepest local binder/hypothesis its proof term
    references. **Closed goals are the degenerate case, not an
    exception:** a proof with no local dependencies falls through
    every block and the theorem's parameters to the enclosing
    environment — the same place declared theorems live — so tier-2
    facts like `Rational.zero < Rational.one` persist file-wide, and
    `.mathv` persistence is just the environment's existing
    serialization applying to one more entry. ("Closed" means closed
    over *locals*; references to global constants are satisfied at
    the environment level by construction, and `.mathv` is per-file
    with its imports, so persistence stays coherent.)
  - **Staging:** the full dependency-depth scan is not
    launch-blocking. Ship with two insertion levels — current depth,
    or environment when the proof is locally closed (the scan that
    finds nothing, trivially cheap) — and generalize to exact-depth
    insertion later if profiling shows sibling-branch re-derivation
    matters. Re-derivation is cheap anyway: tiers 0–4 are linear and
    deterministic. Same rule throughout, implemented at increasing
    resolution.
  - **Dedup:** never insert a derived fact whose statement is
    hash-equal to an existing context entry, so derived facts cannot
    create A2 ambiguity. (For Props, proof irrelevance would make a
    duplicate harmless anyway; not inserting is cleaner.)
  - **Visibility:** the context now holds facts the user never
    wrote. Everything that prints context — error breadcrumbs,
    `--explain`, the goal-state printer — must tag derived facts and
    fold them by default, or failing proofs drown in `0 ≤ …` trivia
    that was never on the page.
  - **Representation note:** hash lookup must respect binder depth —
    with de Bruijn indices, equal hashes at coincidentally equal
    depths can denote different statements. Keying within the
    context's scope structure (a per-level map, not one flat map)
    handles this implicitly; alternatively hash a level/free-variable
    rendering.
- Tiers 0–4 are deterministic and linear — the latency cliff of
  global search structurally cannot recur. Tier 6 is the only genuine
  search and it is metered.

### B2. The judgment-rule index (tier 4)

- Generalize the rewrite-lemma index: at declaration time (and
  `.mathv` load), lemmas whose conclusion has shape `0 ≤ f(…)`,
  `0 < f(…)`, `f(…) ≠ 0`, `IsNonneg(f(…))`, etc. self-register in a
  bucket keyed by **(judgment, head symbol of subject)**.
- Discharge is recursion on the goal's subject term: at each node,
  dispatch by head symbol to the (single) registered rule, recurse on
  its premises. Lean's `positivity` design; one pass, no backtracking.
- **Admission criterion (the load-bearing constraint):** a lemma
  registers as a rule only if each premise's subject is a **proper
  subterm** of the conclusion's subject. This guarantees structural
  descent — a procedure, not a search. Lemmas failing the criterion
  keep their explicit `since`, and each such survivor is a diagnostic
  pointing at a lemma worth restating in dischargeable form.
- **Conflicts are declaration-time errors:** two rules for the same
  (judgment, head) pair → reject, mirroring the two-embeddings-reject
  principle. Dispatch stays choice-free.
- Also index totality/trichotomy lemmas (`a ≤ b ∨ b < a`, constructor
  coverage) under a coverage judgment — this is what makes A4's
  exhaustiveness obligations discharge silently.

### B3. Cast normalization (tier 3)

- Each registered canonical embedding carries a **morphism packet**:
  preservation lemmas for `0`, `1`, `+`, `*`, `≤`, `<` (and
  reflection where true). Declaring an embedding without its packet
  is a warning; the packet slots are named so the elaborator finds
  them without search.
- A `norm_cast`-style pass rewrites goals/hypotheses to canonical cast
  placement; afterwards other tiers operate as if casts weren't
  there. Canonicity of embeddings ⇒ no choice points ⇒ deterministic.
- This alone collapses chains like
  `IsNonneg((m : Rational)) → 0 ≤ (m : Rational) → (0:Real) ≤ (m:Real)`
  to nothing.

### B4. Order automation at parity with equality (tier 5 extension)

- Index monotonicity lemmas (`Π…, a ≤ b → f(…a…) ≤ f(…b…)`) by head
  symbol exactly as rewrite lemmas are indexed; single-position-diff
  `≤`/`<` calc steps then close by-less, the way `=` steps already do.
- Result: in analysis files, `since Rational.add_preserves_LessThan`
  and kin disappear from calc chains; `since` survives only where it
  carries mathematical content — which is the explicitness philosophy,
  not a compromise of it.

### B5. Explainability and regression safety

- `--explain` mode: for any silently discharged obligation, print the
  tier and rules that fired. Failure messages name the gap in the
  recursion: "couldn't establish 0 ≤ firstSum: no (0 ≤ ·, partialSum)
  rule registered" / "premise 0 ≤ s(k) unresolved".
- **Materializer** (inverse of the redundancy lint): a tool that
  rewrites a file inserting the explicit `since` clauses the prover
  found, so a proof can be pinned down against future prover changes.
  With more elaborator search, proof-maintenance brittleness is the
  real risk (never soundness — everything still emits kernel-checked
  terms); the materializer is the mitigation.
- **Validation before building:** instrument the current library's
  `claim … since` lines and classify by absorbing tier. Expectation
  from review: tiers 2–4 absorb well over half, dominated by
  partialSum/power/abs sign lemmas and to_real transport. Build this
  classifier first; it prioritizes everything else in Part B.

---

## Part C — supporting work

### C1. Synonym reduction

One canonical spelling per intent; others parse-accepted + linted
during migration, then removed. Current pairs to resolve: `by` vs
`since` (proposal: `since <lemma>` = citation/hint, `by { … }` =
sub-proof; a `since` the prover didn't need is lint-removable, a `by`
is not); `obtain`/`choose`/`take as` (→ A5); `take` vs raw `↦`
lambdas at proof top level (→ `take`; lambdas only in terms);
`decide` (→ deleted by A4 `otherwise`); `done` (→ restate-the-goal,
A1); the `done by substituting X unfolding Y` sub-language (→ A7
`from`, `suffices by definition of`).

### C2. Error messages for the keyword-free world

- Bare-statement failures always phrase as "couldn't establish:
  ⟨stated proposition⟩ — nearest registered rules / candidate lemmas:
  …", regardless of whether the failure was elaboration, dispatch, or
  a missing premise. A typo that flips proposition↔proof-term must
  not surface as a raw type error.
- Ambiguous statement-address (A2): list the matching hypotheses,
  ask for a name.
- `suppose … for proving Q` mismatch: "block concludes P, announced Q".
- Exhaustiveness gap (A4): name the missing case.

### C3. Lemma discovery for LLMs

Expose the rule/lemma indexes as a CLI: given a goal (or a file
position), print candidate lemmas with signatures, ranked by the same
head-symbol match the prover uses. LLMs iterate extremely well against
this + the existing breadcrumbed error format; they iterate poorly
when discovery requires grepping.

### C4. Documentation as the single source of truth

`LANGUAGE.md` must be **complete** — it currently omits `since`,
`witness`, `given`, `done`, the `substituting/unfolding` grammar. For
LLM writability, completeness of the one in-context spec beats
elegance. After each Part-A construct lands: update `LANGUAGE.md`,
`docs/reference.md`, `docs/tutorial.md` in the same commit; add
`library/Test/` feature files per construct.

### C5. Structure-parameter consistency

`Algebra/group_lemmas.math` mixes explicit five-parameter headers
(`right_inverse_unique`) with implicit ones (`cancel_left`) in the
same file. Whichever convention wins (implicits + `convention`
headers, or bundled structures), the inconsistency is worse than
either choice. Sweep the Algebra layer to one convention; explicit
carrier/op/identity/inverse/proof call sites are a raw-CIC tell.

### C6. Migration mechanics

- Old spellings parse + lint for one full library sweep; scripted
  rewrites where mechanical (`claim P since L;` → `P since L;`;
  `decide P { yes h => A | no h => B }` → `by cases { case P: A
  otherwise: B }`; breadcrumb-claim deletion driven by the B5
  classifier).
- The redundancy tooling becomes the style enforcer in the
  keyword-free world: distinguish "unused and unenlightening"
  (delete) from "unused but reader-load-bearing" (keep; the old
  `note`) — operationally, whatever the author keeps after a
  `--check-redundant` pass.
- Editor/highlighting: with keywords gone, layout and punctuation
  carry structure; update the editor recipes so statements,
  justifications, and block structure are visually loud.

---

## Suggested order of implementation

1. **B5 classifier** (instrument existing `claim … since` lines) — it
   sizes and prioritizes everything in Part B. Cheap.
2. **B1–B3** (tier skeleton + memoization; sign index; cast
   normalization) — kills the breadcrumb-claim complaint at its root.
3. **A1** (keyword-free claims/calc) — the biggest visible change;
   depends on B for the bare statements to actually discharge.
4. **B4** (order automation in calc) — transforms the analysis files.
5. **A2 + A7-contradiction** — statement addressability and the
   `contradiction` terminal; large readability gain, moderate cost.
6. **A3 + A4 + A5** (suppose-for / by-cases / obtain) — the construct
   distillation; includes deleting `decide`, `refining`, `with eq`.
7. **A6** (`eventually`) — library + elaborator; unblocks rewriting
   Real/PAdic/ComplexNumber proofs at a fraction of current length.
8. **C1–C6** interleaved throughout; C4 with every landed construct.

## Reference target

`sqrt_two_irrational.math` after steps 1–6 (the agreed idealized form —
keep this in the repo as the acceptance test for the migration):

```
theorem Natural.two_divides_root (m : Natural) (squareEven : 2 ∣ m * m)
        : 2 ∣ m :=
  since Natural.prime_divides_product

theorem Natural.no_double_square (m n : Natural)
        (mPositive : 1 ≤ m) (nPositive : 1 ≤ n)
        : m * m ≠ 2 * (n * n) := {
  by_strong_induction on m with no_smaller_solution;
  suppose m * m = 2 * (n * n) as equation;

  2 ∣ m  since Natural.two_divides_root;
  obtain k with m = 2 * k;

  suppose k = 0 for contradiction {
    then m = 2 * 0 = 0;
    contradiction with 1 ≤ m
  };
  hence 1 ≤ k;

  from equation: (2 * k) * (2 * k) = 2 * (n * n);
  hence n * n = 2 * (k * k);

  suppose m ≤ n for contradiction {
    then m * m ≤ n * n < 2 * (n * n) = m * m;
    contradiction
  };

  contradiction with no_smaller_solution(n, k)
}

theorem Natural.sqrt_two_irrational
        : ¬ ∃ (m n : Natural). 1 ≤ m ∧ 1 ≤ n ∧ m * m = 2 * (n * n) :=
  since Natural.no_double_square
```

And the analytic acceptance test, `LessOrEqual_of_pointwise_lower`
(currently ~50 lines), after step 7:

```
theorem Real.LessOrEqual_of_pointwise_lower
        (s : Natural → Rational) (sIsCauchy : IsCauchy(s))
        (B : Real)
        (pointwiseLower : ∀ (n : Natural). B ≤ (s(n) : Real))
        : B ≤ Real.limit(s, sIsCauchy) := {
  take B as representative (b, bIsCauchy);
  suffices ∀ ε > 0. eventually (m). -ε < s(m) - b(m)
      by definition of Real.LessOrEqual;
  take ε > 0;

  choose N with eventually (m). abs(s(m) - s(N)) < ε/2
      from sIsCauchy;
  eventually (m). -ε/2 < s(N) - b(m)
      since pointwiseLower(N), by definition of Real.LessOrEqual;

  eventually (m):
    -ε = -ε/2 + -ε/2
       < (s(m) - s(N)) + -ε/2
       ≤ (s(m) - s(N)) + (s(N) - b(m))
       = s(m) - b(m)
}
```

Principles that must survive every step: the trusted base is the
kernel (every construct and every tier emits kernel-rechecked terms);
embeddings and dispatch rules are canonical, never searched; ambiguity
is always a loud error, never a silent pick; and nothing appears on
the page that a mathematician wouldn't write — in either direction.

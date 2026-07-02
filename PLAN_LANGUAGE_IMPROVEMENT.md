# PLAN_LANGUAGE_IMPROVEMENT.md — the declarative endgame

This plan distills a design review of the surface language (July 2026)
into concrete workstreams. It is now the **single forward plan for the
language**: it absorbs `PLAN_LUX_TRANSITION.md` (the 2026-06 transition
plan, largely landed — see the lineage section at the end) and
`PLAN_INTERFACE_IMPLEMENTATION.md` (the 2026-06-21 sealed-structures
design, now Part D). The organizing principle, stated once:

> **Every block in the language announces or concludes with an explicit
> proposition.** A proof is a sequence of stated facts; the elaborator's
> job is to verify each stated fact and to silently discharge the facts
> a mathematician wouldn't bother to state. Nothing is ever proved that
> isn't on the page — but plumbing that carries no mathematical content
> should never be on the page either.

The plan has four parts: (A) the statement language — collapsing the
construct zoo into a small core; (B) the auto-prover — a tiered,
deterministic discharge engine that eliminates breadcrumb claims without
reintroducing global theorem search; (C) supporting work — lints,
diagnostics, documentation, migration; (D) interface and implementation
— module-level abstraction barriers so a type's construction is a sealed
detail behind an axiomatic interface.

Workstreams are ordered by leverage. Within each item: motivation,
design, implementation notes, and open decisions. Anything marked
**DECIDE** needs a human call before implementation.

---

## Status ledger

Implementation spans many sessions. **Every session that works on this
plan updates this table before it ends** (status + commits); deeper
findings go into the owning section as a dated note. Steps refer to
the suggested order at the end of the plan.

| Step | Workstream | Status | Record |
|------|------------|--------|--------|
| 1 | B5 classifier (instrument hinted claims/calc steps) | **done** | 2026-07-02; `MATH_CLASSIFY_HINTS` + `scripts/hint_classification_report.py`; findings in B5 (64.6% absorbable of 5807 sites) |
| 2 | B1–B3 tier skeleton, context index, cast tier | **in progress** | tier-4 sign index v1 (21b1cb4) + v1.1 IsNonneg/alternatives/form-bridges: closes-today 36.2%→42.3% (+352 sites). B3 cast retry landed (test-proven; yield compounds with future families). Per-key vectors landed. **B1 stage-1a memo tried and REVERTED (73ae506): A/B showed zero effect — the 2026-06-27 perf session already satisfied tier-0's speed rationale (derivative ~4.9s, continuity ~1.3s, full re-verify 25.5s wall today). B1's remaining value = the A2 statement-address spine + derived-fact blackboard, not speed.** Next: `= 0` zeroness family, A2 spine design |
| 3 | A1 keyword-free claims/calc | not started | |
| 4 | B4 order automation in calc | not started | |
| 5 | A2 statement addressability + A7 `contradiction` kit | not started | |
| 6 | A3/A4/A5 construct distillation | not started | |
| 7 | A6 `eventually` | not started | |
| 8 | C1–C6 (continuous; C4 with each construct) | **in progress** | C1 elaborator side done 2026-07-02 (cb21629: since = unexempted synonym of by); next: the since→by sweep + breadcrumb deletion (elaborator-driven rewrite per C6, scoped to the clean manifest first) |
| 9 | D: sealed structures (Phase 0 ℝ prototype first) | **spike done; design decided** | Phase-0 flip-measure-revert 2026-07-02 (7-file bill; the Real quotient-alias elaborator gap = Phase 1's first item); interface = closure-not-minimality, LUB canonical + Cauchy exported (D7) |
| 10 | A8: Fold library → binder form → recognizer → series | **in progress** | step 1a done (42e9865): indexedAggregate `_zero`/`_one`/`_shift`. **Step 1b done (0cb6791): `Algebra.Fold(op, id, f, start, count)` with the full unconditional lemma set (zero/add_one/one/split/shift/pointwise) + the indexedAggregate bridge; consumers untouched.** Next: op registry (`instance` precedent), re-home partialSum/Ring.Sum (step 1c), then the explicit binder form |

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

**DECIDED-BY-DEFERRAL (owner, 2026-07-02):** the question of whether
`claim`/`calc` stay parse-accepted is answered by the migration
itself. Current expectation: they add no value and are removed
outright once the sweep is done. If specific proofs read worse
without them, revisit then — with the evidence in hand — and keep one
or both. Do not relitigate before the migration.

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

**Interface interplay (Part D):** over a sealed `Natural` (D4) the
structural clause is spelled `case n = k + 1 for some k:` and routes
through the *exported* induction/coverage principle, never the
constructor; the auto-generated coverage lemmas of this section become
interface obligations. Same clause grammar, one more reason the
recursor-emission must be principle-driven rather than
constructor-driven.

---

### A5. `obtain` / `take … as` — destructuring, unified

**Motivation.** `obtain`, `choose N as h from e`, `choose N such that
P(N)`, and single-constructor/quotient `cases` all destructure. Three
overlapping spellings plus one masquerading case-analysis.

**Design (DECIDED 2026-07-02: the surviving keyword is `choose`).**
The original objection was never to a keyword — it was to `⟨w, p⟩`
angle-bracket patterns revealing that `∃`/`∧` are tuples under the
hood. The unified construct states the property as a proposition, so
both spellings were acceptable; `choose … such that` wins on prose
("choose ε > 0 such that …" is the textbook idiom for the dominant
use, existential instantiation) and on migration cost (the library
already speaks it; `obtain` is a residue). The consciously accepted
cost: the intro/elim pair is asymmetric (`witness E with P`
introduces, `choose w such that P` eliminates).

- One construct for LOGIC: `choose <witnesses> such that <property>
  [as <name>] [from <fact-or-name>];` — witness names first, property
  stated inline (and thereafter statement-addressable per A2), source
  inferred by type-match against in-scope facts when `from` is
  omitted. Example: `choose k such that m = 2 * k;` (source: the
  in-scope `2 ∣ m`). After A2, `as <name>` is pure documentation.
- Witness lists flatten **nested ∃/∧ in one step**:
  `choose m, n such that 1 ≤ m ∧ 1 ≤ n ∧ m*m = 2*(n*n) from
  solutionExists;`. Conjunctions added to context are also registered
  conjunct-by-conjunct (already implemented — keep).
- **The Prop/data boundary, made explicit:** `choose` is for `∃`/`∧`
  elimination only. A genuine data record IS honestly tuple-shaped,
  so pattern binders (`let ⟨a, b⟩ := r;`, `take x as ⟨a, b⟩`) remain
  the right destructuring there — revealing real structure leaks
  nothing false. The angle-bracket ban is a ban on spelling LOGIC as
  tuples, not on destructuring data.
- Quotient representatives get the mathematical name:
  `take x as representative (a, b);` — replacing constructor-spelled
  `cases x { | Representative.make(a,b) => … }` for the
  single-"branch" use. `by_representatives` and quotient `cases`
  forms route here.
- `obtain` parses as a linted synonym for one sweep, then is removed.

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
  (iii) hypothesis position: `choose N such that eventually (m). Q(m)
  from h;` when the threshold itself is needed.
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
- **`by <lemma>` as a whole proof body** — the prover does the
  logical plumbing between the goal and the lemma's form: intros,
  ∃/∧ flattening, `Or.self`, argument discharge from context. Pure
  logic-shuffling with no mathematical content should never be on the
  page. (`sqrt_two_irrational := by no_double_square`.)
- **Hypothesis discharge at call sites.** When applying a lemma or an
  IH, arguments whose types are propositions already in scope (up to
  defeq / cast-normalization) are filled automatically;
  `no_smaller_solution(n, k)` supplies `n < m`, `1 ≤ n`, `1 ≤ k` from
  context. This generalizes `?` from goal-driven to context-driven.
  *Gap found and FIXED same day (2026-07-02):* citation
  premise-discharge used to scan LOCAL hypotheses only — `by
  pointwiseEqual` couldn't discharge `start ≤ start + c` even though
  `Natural.less_or_equal_add_right` is automatic. Now both discharge
  paths (`completeCitationFromBindings` step (c) and
  `inferCallWithHoles` step 5b) fall back to a budget-capped bare
  prover for fully-determined Proposition premises, gated off the
  speculative context scan (which both bounds cost and breaks the
  prover→scan→citation recursion). Feature test:
  `Test/citation_automatic_discharge_test.math`; the scaffolding
  claim in `Fold_pointwise` is gone.
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

### A8. Ellipsis notation for folds and series

(Contributed 2026-07-02; specified to implementation depth.) The
one-sentence summary: **the general term is the definition; the
prefix terms are verification.** Everything else follows from taking
that sentence seriously.

#### 1. Motivation

Mathematicians write `1 + 2 + ... + n = n(n+1)/2`, not
`Fold(+, identity, 1, n, λk. k) = n(n+1)/2`. Blackboard ellipsis is
normally too ambiguous to formalize (`2, 4, 8, ...` — powers of two or
even numbers?), but a small discipline removes the ambiguity entirely:
the term after the ellipsis, written with an explicit variable, IS the
general term; the concrete terms before the ellipsis exist only so a
reader (and the elaborator) can confirm they instantiate it. Under
that rule the notation is not a heuristic — it is a deterministic
surface form for an ordinary fold, and it can appear in statements,
in calc chains, in goals, and in printed output.

A trailing ellipsis extends the notation to infinite series
(`1/2 + 1/4 + ... + 1/2^n + ...` — the limit of the partial folds).
This is a genuine semantic extension, not sugar, and is treated
separately in §6.

#### 2. Surface syntax

##### 2.1 Finite folds

```
<t₁> <op> <t₂> [<op> <t₃>] <op> ... <op> <general>
```

- `<op>` is one binary operation, the same at every position,
  drawn from the registered fold-capable operations (§4). Mixed
  operators in one ellipsis expression are a parse error.
- `<t₁> … <tₖ>` are the **prefix terms**: concrete expressions, at
  least one, typically two or three. They contain no occurrence of
  the index variable.
- `...` is a literal token (also accept the Unicode ellipsis `…`).
- `<general>` is the **general term**: an expression containing at
  least one variable that does not occur in the prefix terms. It is
  the anchor of the whole notation.

Examples that must parse and elaborate:

```
1 + 2 + ... + n
1 + 2 + 3 + ... + n
2 + 4 + ... + 2 * n
1 + 3 + 5 + ... + (2 * n - 1)
1 * 2 * ... * n                       -- factorial as a fold
f(1) + f(2) + ... + f(n)
1/1 + 1/2 + ... + 1/n                 -- general term 1/n, index n itself
a(0) + a(1) + ... + a(n)              -- starting index 0
x + x^2 + ... + x^n                   -- index in the exponent
```

##### 2.2 Infinite series (trailing ellipsis)

```
<t₁> <op> <t₂> <op> ... <op> <general> <op> ...
```

Same shape, with a final `<op> ...` after the general term. See §6
for the (restricted) contexts where this form is legal.

##### 2.3 The explicit form

The ellipsis form is sugar over an explicit surface form, which must
exist independently — as the escape hatch when inference fails or is
ambiguous, and as the documented meaning of the sugar:

```
sum k from 1 to n of f(k)
product k from 1 to n of f(k)
fold (<op>) k from i₀ to n of f(k)      -- general registered op
```

(Exact keyword spelling is a surface decision for the implementer to
propose; the requirement is that an explicit binder form exists, is
documented in LANGUAGE.md, and that the ellipsis form is defined by
translation into it.)

#### 3. Recognition and elaboration algorithm

(DECIDED 2026-07-02, replacing the earlier fresh-variable/probe
draft after working the example corpus of §3.3.) Two complementary
mechanisms, both deterministic, tried in order:

**Mechanism 1 — anti-unification (structural anchors, symbolic
bounds).** Match the LAST prefix term `tₖ` against the general term
`g` (it is the term most likely to share `g`'s shape). The positions
where they differ must all hold one consistent pair
(`⟨value at tₖ⟩`, `⟨value at g⟩`) =: (jₖ, hi); the term function `f`
is `g` with those positions abstracted; `lo := jₖ − (k−1)` (numeral
arithmetic, k small). Then verify the earlier prefix terms downward:
`t_{k−1} ≡ f(lo + k − 2)`, …, `t₁ ≡ f(lo)`, each by defeq → tier-2
ground evaluation → **one pass of registered characterizing
equations** (the rewrite index; bounded and index-driven, not search
— this is what lets `x ≡ x^1` and `1 ≡ x^0` verify against opaque
`power`). This mechanism is the one-metavariable case of
`matchAgainstPattern` and handles symbolic bounds
(`a(m) + a(m+1) + … + a(n)` → lo = m), shared-parameter indices
(`binomial(n,0) + … + binomial(n,n)` — no fresh variable exists),
and ground ranges (`1 + 2 + … + 10`).

**Mechanism 2 — the 0/1 evaluation probe (arithmetic anchors).**
When anti-unification fails structurally (`2 + 4 + … + 2*n`: the
numeral `2` is not literally `2*⟨_⟩`), abstract `g` over its fresh
variable and test `f(0) ≡ t₁` and `f(1) ≡ t₁` by ground evaluation,
verifying the rest of the prefix for whichever start matches.
Starting indices beyond {0, 1} are not probed in v1.

**Ambiguity is a loud error** at every stage, per the house rule:
two consistent (lo, hi) readings, or both probe starts matching
(possible with a single prefix term: `0 + … + k*(k−1)` matches
lo = 0 and lo = 1), name every surviving candidate and point at the
explicit binder form. Zero candidates: "general term does not
generate the prefix", showing the nearest-miss `f(lo), f(lo+1)`
against the written terms.

**Upper bounds and the half-open rule.** The written general term is
the last term, so the range is inclusive lo..hi with **count
`(1 + hi) ∸ lo`** — monus, whose clamping gives exactly the right
empty range when a symbolic lo exceeds hi. One special case, decided:
an upper bound of the syntactic shape `E − 1` is **half-open
notation** — range [lo, E), count `E ∸ lo` — so that
`a(0) + a(1) + … + a(n-1)` denotes the empty sum at `n = 0` (the
naive inclusive reading gives count 1 there: `1 + (0∸1) ∸ 0 = 1`,
which is wrong). Literal lo ∈ {0, 1} yields monus-free counts
(`1 + n` and `n`); symbolic lo keeps the monus in the count slot
only, and peel lemmas surface `lo ≤ hi` side conditions exactly
where the mathematics needs them.

##### 3.1 Upper bound, precisely

The written general term is the fold's **last term**, so the fold's
range is `v = i₀ … V` where `V` is the value of the index variable as
it appears free in the surrounding statement. Concretely: in
`1 + 2 + ... + n`, the index variable is `n` itself and the range is
`1 … n`. In `1 + 3 + ... + (2*m - 1)`, the index variable is `m`, the
range is `1 … m`, and the term function is `λm. 2m − 1` — note the
**stride comes for free**: no stride-inference machinery exists or is
needed, because anchoring on the general term makes "odd numbers" a
term function over a unit-step index. Implementers must NOT add
consecutive-difference stride guessing; it reintroduces exactly the
ambiguity this design eliminates.

##### 3.2 Degenerate ranges

The displayed prefix does not constrain the range. `1 + 2 + ... + n`
shows three terms but denotes `Fold(+, id, 1, n)`, which is
meaningful at `n = 1` (one term) and `n = 0` (empty fold = the
operation's identity, so `0`, and the identity `0 = 0·1/2` still
holds). Document this in LANGUAGE.md — it occasionally surprises —
and make the pretty-printer's behavior at small symbolic ranges
consistent (§8).

##### 3.3 Example corpus (the seed for the feature-test file)

| expression | mechanism | reading |
|---|---|---|
| `1 + 2 + ... + n` | anti-unify (`1` vs `n`) | lo 1, hi n, f = id |
| `a(0) + a(1) + ... + a(n)` | anti-unify | lo 0, hi n |
| `a(m) + a(m+1) + ... + a(n)` | anti-unify | symbolic lo = m; count `(1+n) ∸ m`, empty when m > n for free |
| `a(0) + ... + a(n-1)` | anti-unify + half-open rule | count n; empty at n = 0 |
| `2 + 4 + ... + 2*n` | probe (f(1) = 2) | lo 1, hi n |
| `1 + 3 + 5 + ... + (2*n - 1)` | probe (monus ground-evaluates) | lo 1, hi n |
| `1/1 + 1/2 + ... + 1/n` | anti-unify (`1/1` vs `1/n`) | the written `1/1` is what makes the shape visible — the discipline matches practice |
| `x + x^2 + ... + x^n` | anti-unify on `x^2`, verify `x ≡ x^1` via characterizing equation | lo 1, hi n |
| `binomial(n,0) + ... + binomial(n,n)` | anti-unify (no fresh variable exists) | lo 0, hi n, f = λv. binomial(n,v) — the binomial-theorem display |
| `1 + 2 + ... + 10` | anti-unify | ground range; harmless, allowed |
| `a(1,1) + ... + a(n,n)` | anti-unify, consistent pair at both positions | the diagonal, λv. a(v,v) |
| `n + (n-1) + ... + 1` | — | rejected in v1 by the downward verification (t₁ ≠ f(lo)); see §10 for the future-work door |

#### 4. Elaboration target and library work

The ground-truth form is a single generic fold over a registered
operation:

- **DECIDED (2026-07-02): `Fold(op, identity, f, i₀, count)` — lower
  bound plus COUNT, recursion on the count.** This is the only
  convention with no monus and no side conditions in the definition
  or the characterizing lemmas (peel-last
  `Fold(f, i₀, 1+c) = Fold(f, i₀, c) op f(i₀+c)`, peel-first
  `Fold(f, i₀, 1+c) = f(i₀) op Fold(f, 1+i₀, c)`, empty
  `Fold(f, i₀, 0) = identity` — all unconditional), while keeping
  `i₀` as DATA in the term, which makes the §8 printer trivial
  (read i₀ and count off the term) instead of pattern-extracting
  offsets from a lambda body. The display semantics stay inclusive
  `f(i₀) op … op f(hi)`; the count is the kernel spelling only.
  Rejected alternatives, for the record: a two-ended inclusive
  primitive (monus or `i₀ ≤ N` guards infect every lemma, and the
  half-open rule of §3 has no home — it gets `a(0)+…+a(n-1)` wrong
  at n = 0); offset-in-the-term-function over the existing
  count-only fold (works, but buries i₀ in a lambda the printer
  must reverse-engineer forever); Ring.Sum's inclusive-from-f(0)
  form (cannot represent the empty range at all — it is the problem,
  not a candidate). `Algebra.indexedAggregate` becomes the `i₀ = 0`
  instance; `Real.partialSum`/`partialProduct` re-home mechanically;
  `Ring.Sum(f, n)` retires as `Fold(f, 0, 1 + n)`, turning the
  off-by-one bridge lemma into a definition.
- **Fold-capable operation registry.** An operation qualifies by
  registering (op, identity, associativity proof). `+` and `*` on
  each numeric carrier register at instance-declaration time.
  Registration without an identity/associativity certificate is an
  error. Two registrations for the same operator symbol on the same
  carrier: declaration-time error (canonical, never searched).
- **Characterizing lemmas, registered in the rewrite index** — this
  is what makes the notation usable in proofs rather than merely
  pretty in statements:
  - `Fold(op, f, i₀, i₀) = f(i₀)` (singleton)
  - `Fold(op, f, i₀, N+1) = Fold(op, f, i₀, N) op f(N+1)` (peel last)
  - `Fold(op, f, i₀, N) = f(i₀) op Fold(op, f, i₀+1, N)` (peel first)
  - `Fold(op, f, i₀, i₀−1) = identity` (empty range, however ranges
    are represented)
  - index-shift / split-range lemmas as needed by the library.

  With these in the index, the calc step every induction proof needs
  closes by-less. **Acceptance test** (must verify with no `since` on
  the first step):

  ```
  1 + 2 + ... + (n + 1)
     = (1 + 2 + ... + n) + (n + 1)
     = n * (n + 1) / 2 + (n + 1)        -- IH, statement-addressable
     = (n + 1) * (n + 2) / 2            -- ring
  ```

  The proof reads in the same notation as the statement. That is the
  whole payoff; if this calc needs annotations, the feature has
  failed its purpose.

#### 5. Where the notation may appear

Finite ellipsis folds are ordinary terms: legal in theorem
statements, definitions, calc steps, `suppose` headers, anywhere a
term of the carrier type is legal. They are pure sugar — no
proposition is generated by the notation itself beyond the shape
verification at elaboration time (which is a compile-time check, not
a proof obligation).

#### 6. Trailing ellipsis: infinite series

A trailing `<op> ...` changes the meaning from a value to a **limit
of partial folds**, and limits are partial — `1/2 + 1/4 + ... +
1/2^n + ...` has a value; `1 + 1/2 + ... + 1/n + ...` does not. To
keep partiality out of the term language, version 1 restricts the
form:

**Rule: an infinite-series expression is legal only as one full side
of a relation, and the whole relation elaborates as a proposition.**

- `t₁ op … op g op ... = S` elaborates to
  `ConvergesTo(λN. Fold(op, f, i₀, N), S)`.
- `t₁ op … op g op ... = infinity` elaborates to
  `TendsToInfinity(λN. Fold(op, f, i₀, N))`.
  `infinity` (and `∞`) is a **contextual keyword** legal only in this
  position; it is never a term of Real, and using it elsewhere is a
  parse error with a message saying so.
- Both target predicates are library definitions on sequences
  (`Real/sequence.math` has the substrate; `eventually` from A6 is
  the natural vocabulary for their definitions).
- Consequences of the restriction, stated so the implementer doesn't
  "fix" them: `(1/2 + 1/4 + ...) + 1` is illegal in v1 (no series in
  term position); `... = S` with `S` itself a series is illegal
  (one side only); inequalities `t₁ + ... + g + ... ≤ B` are
  **rejected in v1** (DECIDED 2026-07-02 — see the v2 note below for
  why the question largely evaporates later).

**Deferred (v2) — and the extended-reals direction (owner,
2026-07-02).** The v2 design should be built on a two-point
completion ℝ̄ = ℝ ∪ {−∞, +∞} (order and limits only — ℝ̄ is not a
ring; `ring`/`field` never touch it; ±∞ case splits are A4 `by
cases` + tier-4 food). What it buys, precisely:
- **One limit predicate instead of two.** `ConvergesTo` and
  `TendsToInfinity` unify into convergence in ℝ̄'s order topology;
  `… = infinity` stops being a keyword hack and becomes an ordinary
  equation inside the predicate (`infinity` is just a term of ℝ̄).
- **On the monotone/nonneg fragment the totality questions
  evaporate**, exactly as hoped: a series with eventually-nonneg
  terms ALWAYS has a value in [0, +∞] (monotone convergence), so
  nonneg series can eventually be a TOTAL function into [0, ∞] —
  term position legal with NO convergence side conditions on that
  fragment (the measure-theory move; cf. mathlib's ℝ≥0∞ experience,
  where this totalization is what makes series automation pleasant).
  The signed case then routes through absolute convergence. On this
  fragment the candidate inequality readings (∀N over partial sums /
  limit ≤ B / limsup ≤ B) all coincide — which is why deciding the
  v1 reading would have been wasted work. Note this needs only
  ADDITION and sup on [0, ∞], both total without any convention.
- **ℝ̄ arithmetic stays PARTIAL (owner, 2026-07-02).** No `0·∞ = 0`
  convention — it is as unmathematical as `1/0 = 0`, which this
  library already refuses. Undefined combinations (`∞ − ∞`, `0·∞`,
  `∞ + (−∞)`) carry proof obligations that the operation makes
  sense, in the same spirit as honest division's nonzero
  obligations — and dischargeable by the same machinery: a tier-4
  `IsFinite`-style judgment family mirrors the structural `nonzero`
  tactic, so the obligations stay off the page in the common cases.
  Accepted cost, stated honestly: more side conditions than the
  convention route (mathlib chose totality for a reason), but the
  house already made this trade for `/` and built the discharge
  machinery that makes it pleasant; consistency wins.
- **What does NOT evaporate:** oscillating series
  (`1 − 1 + 1 − …`) have no limit even in ℝ̄, so a single total
  "value of any series" remains impossible — defining it as limsup
  would make `1 − 1 + 1 − … = 1` a true equation, which is worse
  than partiality. Hence the trailing-ellipsis form stays a
  RELATION-position proposition in v2 too; what changes is that the
  predicate is one, the ±∞ equations are honest, and the nonneg
  fragment gets total term-position sums.
- Implied library ladder: ℝ̄ with order + the ℝ ↪ ℝ̄ embedding
  packet (B3), limsup/liminf (independently wanted for analysis),
  the unified limit predicate, then [0,∞]-valued total sums.
  Convergence side conditions for the general signed term-position
  case stay a tier-4 judgment family
  (`(ConvergesTo, power)` geometric rules etc.) as previously
  sketched. Do not build any of this in v1.

#### 7. Interaction with the rest of the plan

- **Tier-2 dependency.** Steps 3–4 of the recognition algorithm are
  ground evaluation — precisely Part B's tier 2. Implement B1/B2's
  evaluation tier before this feature; the shape check then costs
  nearly nothing and shares its code.
- **Rewrite index (B2/B4).** The characterizing lemmas of §4 register
  exactly like any other rewrite/monotonicity lemma. No new index
  machinery.
- **Keyword-free calc (A1).** Ellipsis terms inside relation chains
  must parse unambiguously: the chain separators are the relations
  (`=`, `≤`, …) and the ellipsis operator is arithmetic (`+`, `*`),
  so there is no grammar conflict, but add parser tests for an
  ellipsis fold as a calc endpoint on both sides.
- **Statement-addressable facts (A2).** A fact stated with ellipsis
  notation and the same fact stated with explicit `Fold` must be the
  same fact for context lookup — guaranteed if the sugar desugars at
  parse/elaboration time and hashing happens on kernel terms (it
  does).
- **`--explain` / errors (C2).** Every error from §3 must show the
  candidate term function and the evaluated prefix side by side.

#### 8. Printing (round-trip)

Goals, errors, and `--explain` output involving `Fold` should print
in ellipsis form whenever a faithful rendering exists — users write
in this notation and must not debug in another one. Printing rule:
render `Fold(op, λv. g, i₀, N)` as `g[v↦i₀] op g[v↦i₀+1] op ... op
g[v↦N]` with the first two terms ground-evaluated for display, i.e.
`1 + 2 + ... + n`, provided the evaluated prefix terms are small
literals; otherwise fall back to the explicit binder form. Never
print a prefix the recognizer of §3 would not re-accept
(round-trip property: parse(print(e)) elaborates to e). Add a
round-trip test over the library's fold expressions.

#### 9. Errors (all must exist, with these shapes)

1. Mixed operators: "ellipsis requires a single operation; found `+`
   and `*`".
2. No index candidate: "general term contains no variable absent
   from the prefix; write the explicit form".
3. Prefix mismatch: "general term `2*k` with start `k = 1` generates
   `2, 4, 6, ...` but the prefix is `2, 4, 7`" — show generated vs
   written.
4. Ambiguity: "ambiguous between index `m` (start 1) and index `j`
   (start 0); write the explicit form" — list every surviving
   candidate.
5. Unregistered operation: "`⊕` is not registered as fold-capable;
   register (op, identity, associativity) or use explicit recursion".
6. Series in term position (v1): "an infinite series may only appear
   as one side of a relation".
7. `infinity` outside a series relation: "'infinity' is only legal as
   the right-hand side of a series relation".

#### 10. Non-goals for v1 (do not build)

- Stride inference from consecutive differences (§3.1 — the general
  term already carries the stride).
- Series in term position; algebra on series expressions (§6, v2).
- Double/nested ellipses (`(1+..+n) * (1+..+m)` is fine — two
  independent folds — but `a(1,1) + ... + a(n,m)` matrix-style is
  out).
- Ellipsis over **relations** (`a(1) ≤ a(2) ≤ ... ≤ a(n)` as sugar
  for a monotonicity ∀). This is a genuinely good future feature and
  composes with B4, but it elaborates to a ∀-statement, not a fold —
  a separate plan item, not a rider on this one.
- **Descending ranges — not in v1, door explicitly open (owner,
  2026-07-02).** The motivating display is the polynomial:
  `a(n)*x^n + ... + a(1)*x^1 + a(0)*x^0`, and the harder textbook
  form `a(n)*x^n + ... + a(1)*x + a(0)`, whose trailing terms only
  match the general term through characterizing equations
  (`x^1 = x`, `a(0)*x^0 = a(0)` via power_one/power_zero/multiply
  laws) — i.e. the same normalization-assisted verification §3
  already uses, pointed at the tail instead of the head. Note the
  kernel form doesn't care about direction (a descending display is
  `λj. f(hi ∸ j)` reindexing — recognizer/printer work only), so
  nothing decided now forecloses it. In v1, reject with a clear
  message; the §3 downward verification already rejects it
  automatically (t₁ ≠ f(lo)).

#### 11. Suggested implementation order

**Groundwork survey (2026-07-02).** The generic fold largely EXISTS:
`Algebra.indexedAggregate(A, op, identity, s, n)` (aggregation.math:32)
is carrier-generic with loose `(op, identity, laws)` arguments, and
`Real.partialSum`/`partialProduct` are already thin instances of it;
`Ring.Sum` (ring_summation.math:19) is a second, bundled fold with an
INCOMPATIBLE range convention (inclusive `0..n` vs count-based `k<n`;
bridge lemma `Real.partialSum_eq_ring_sum` carries the off-by-one).
Step-1 work is therefore: (a) unify on one convention with a genuine
`i₀` lower bound (no existing fold has one); (b) add the missing named
characterizing lemmas — singleton and peel-first exist only on
`Ring.Sum` (`Ring.Sum.shift`), empty-range is definitional-but-unnamed
everywhere; peel-last (`_add_one`) and split exist on all three;
(c) build the fold-capability registry on the `instance` precedent
(`instance CommutativeRing.is_ring`, keyed by carrier — see
commutative_ring_algebra.math:69) — no `(op, identity, associativity)`
registry exists today, laws travel as per-lemma hypotheses;
`congruence_under_binder Ring.Sum := Ring.Sum.extensional`
(ring_summation.math:64) is the precedent for registering fold lemmas
into elaborator machinery. ~19 files consume partialSum/Product, ~15
consume Ring.Sum — the re-expression sweep is real but bounded.

1. Generic `Fold` + operation registry + characterizing lemmas in the
   library; re-express `partialSum`/`partialProduct`/`aggregation`
   over it. (Pure library work; independently valuable.)
2. Explicit binder form (`sum k from … to … of …`) in the surface
   language, elaborating to `Fold`.
3. Register characterizing lemmas in the rewrite index; make the §4
   acceptance calc close by-less **using the explicit form**.
4. Ellipsis recognizer (§3) desugaring to the explicit form; error
   suite of §9.
5. Printer round-trip (§8).
6. Trailing-ellipsis series relations (§6 v1).

Each step lands with LANGUAGE.md/reference.md updates and a
`library/Test/` feature file, per C4.

#### 12. Acceptance criteria

- `theorem Natural.triangular_sum : (n : Natural) → 1 + 2 + ... + n =
  n * (n + 1) / 2` states, and its induction proof's peel-last calc
  step closes with no `since` (§4).
- `1 * 2 * ... * n` proves equal to `factorial(n)` by induction with
  the same by-less peel step.
- `1/1 + 1/2 + ... + 1/n + ... = infinity` states and elaborates to
  `TendsToInfinity` of the harmonic partial sums (proving it is
  library work, not part of this feature's acceptance — and the
  library already proves harmonic divergence, so the existing theorem
  can be restated in the new notation as the test).
- Every error in §9 is exercised by an `ErrorTest/` file.
- Round-trip test passes over all fold expressions in the library.

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

**Tier-0 implementation staging (design note, 2026-07-02).** The
obstacle: `localBinders` is a plain `std::vector<LocalBinder>` passed
by value/reference through every elaboration path — there is no
single push/pop chokepoint to hang an incremental index on, and
`collectLocalBinderFacts` (prover.cpp) currently rebuilds the fact
list, WHNF-decomposing every conjunction hypothesis, on EVERY
auto-prover call (the measured dominant cost in ε-δ files). Staged
plan that avoids an elaborator-wide refactor:
1. **Memoized fact collection, keyed by binder-prefix hash.** Compute
   a running order-sensitive hash of the binder types; cache
   decomposed fact lists per (depth, prefix-hash). Binder vectors
   grow monotonically within a block, so a cache hit on a prefix
   reuses its facts and decomposes only the new binders. Pure
   retrofit inside `collectLocalBinderFacts`; no caller changes.
2. **Statement-hash lookup map on top** of the cached fact list
   (statement hash → fact), giving O(1) tier-0 lookup — and this
   same map IS the A2 statement-address structure and the
   derived-fact blackboard's spine (one structure, three consumers,
   as designed above). Respect the de Bruijn depth caveat: key
   within the per-depth cache, not one flat map.
3. **Push/pop discipline (RAII context object) only if profiling
   still demands it** after 1–2 — i.e., only if hashing the binder
   vector itself shows up hot. Do not start with the invasive
   refactor.

*Correction (2026-07-02, A/B-measured):* stage 1 was implemented and
REVERTED — it has zero effect, because the 2026-06-27 perf session
(context memoization + fused binder opening, see the
`verification_perf_autoprover_scan` memory) already removed the
scan's hot cost; the fact-list rebuild itself is cheap. So tier-0's
PERF motivation is already satisfied; what remains valuable here is
stage 2 — the statement-hash lookup structure — justified as the A2
statement-address spine and the derived-fact blackboard, not as an
optimization. Build it when A2 lands, not before.

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

**v1 landed (2026-07-02, commit 21b1cb4).** Judgments: `0 ≤ f(…)`,
`0 < f(…)`, `f(…) ≠ 0` over Constant-headed or numeral subjects;
registration hooks `registerAlgebraicShape` (so seeding and fresh
declarations share one funnel); admission = sign-judgment premises on
bare lemma binders; conflicts first-wins-and-counted (the
declaration-time error waits for a library duplicate cleanup); tactic
sits after `localFactExactMatch`; `MATH_SIGN_INDEX_DEBUG` traces rule
firings. Feature test: depth-3 recursion through an opaque wrapper.
Measured day-one yield (classifier, library-only): closes-today
36.2% → 39.1% (+180 sites); tier-4 sign 312 → 263, sign-cast
217 → 147. The residue decomposes as: (a) ~90 sites of
IsNonneg-form plumbing (`IsNonneg_of_LessOrEqual_zero` and kin) —
extend the judgment vocabulary to unary predicates and route across
the bridge lemmas; (b) the sign-cast bucket, blocked on tier 3
(subjects carrying non-numeral casts don't match rules stated on the
bare carrier); (c) `f(…) = 0` zeroness equalities (the classifier
counts them sign-shaped; a `zero` judgment family would take them);
(d) whatever the conflict counter is masking — audit it.

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

**Findings (2026-07-02 — the classifier ran over the full library).**
Instrument: `MATH_CLASSIFY_HINTS=1` (hooks at the hinted-claim and
hinted-calc-step elaboration sites; shape features + a budget-capped
speculative by-less re-proof), aggregated by
`scripts/hint_classification_report.py`. **5807 hinted sites**
(2811 `since` / 2996 `by`; 3387 claims / 2420 calc steps), bucketed
first-match-wins:

| bucket | sites | share | dominated by |
|---|---|---|---|
| closes-today (budget-capped bare re-proof succeeds) | 2101 | 36.2% | inline terms, `LessThan.weaken`, `IsNonneg` bridges, bare `IH` |
| B4 order calc step | 305 | 5.3% | `add_preserves_LessOrEqual/LessThan` family, `multiply_by_nonneg`, `triangle_inequality` |
| tier 2 ground | 345 | 5.9% | `two_positive`, `zero_less_one`, `to_real.positive_preserves`, `False` |
| tiers 3+4 sign-through-casts | 217 | 3.7% | `divide_positive`, `absolute_value_nonneg`, `factorial_cast_positive` |
| tier 4 sign | 312 | 5.4% | `IsNonneg` bridges/`IsNonneg.multiply`, `modulus_nonneg`, `square_IsNonneg` |
| tier 3 cast | 473 | 8.1% | cast-bearing equalities/existentials, `sign_split` |
| **absorbable total** | **3753** | **64.6%** | |
| unabsorbed | 2054 | 35.4% | inline sub-proof terms (586), `IH` citations, abstract-ring plumbing, `le_through_max_*` |

Reading, against the expectations above:
- **The tier-2–4 + B4 prediction is confirmed in composition**: the
  sign/cast buckets are dominated by exactly the predicted families
  (divide/abs/factorial-cast positivity, `to_real` transport), and
  the B4 bucket is almost entirely `add_preserves_*` monotonicity —
  but their combined share is ~23%, not "over half". The bulk
  absorber is **closes-today at 36%**: hints today's prover already
  discharges near-instantly. Under C1's role split those become
  lint-removable citations wholesale — so C1 + the lint, not new
  tiers, deletes the single biggest slice.
- **The unabsorbed third decomposes on sight**: inline `<term>`
  sub-proofs (the hint IS the proof — correctly on the page), `IH`
  citations (A2 statement-addressability's target), abstract-carrier
  associativity/commutativity plumbing (`ring`'s domain, invisible to
  head-symbol indexes), and `Natural.le_through_max_*` threshold
  juggling (A6 `eventually`'s target, 28 sites in this bucket alone).
- **Caveats**: buckets are shape-classified upper bounds (tier 4's
  yield depends on B2 rule coverage); generic-relation calc steps
  (`∣`/`⊆`) are labeled `=` by the instrument; `closes-today` uses
  the 1000-step redundancy budget, so slower-but-provable sites land
  in other buckets.
- **Priority confirmed with one amendment**: B3+B2 first (1002
  sign/cast sites), then B4 (305 steps, a dozen lemma families to
  index), then the tier-2 evaluator (345). The amendment: schedule
  the C1 `since`-role decision early, because the closes-today slice
  (2101) is gated on it, not on any tier.

---

## Part C — supporting work

### C1. Synonym reduction

One canonical spelling per intent; others parse-accepted + linted
during migration, then removed.

**DECIDED (2026-07-02): `by` and `since` unify on `by`.** With
`automatic` scoping the silent prover is boring by construction
(standard tactics over local + `automatic` facts, `--explain` as the
accountability backstop), so "kept explanation, exempt from the
redundancy lint" no longer earns a keyword. `since` becomes a linted
synonym for one sweep, then dies; `byIsExplanation` /
`stepProofIsExplanation` and the redundancy exemption are deleted
from the elaborator. The citation-vs-sub-proof distinction the old
proposal wanted is already carried by the hint's SHAPE (identifier vs
`{ … }` block) — the lint can differentiate without a second keyword.
A reader-load-bearing redundant justification migrates to a stated
fact (A1) or to `note P [by V];`, the designated verified comment.
Consequence to schedule deliberately: un-exempting the former `since`
sites makes `--check-redundant-by` flag the whole closes-today bucket
(~42% of hinted sites) — that IS the C6 breadcrumb-deletion
work-list, scoped per the clean manifest.

Remaining pairs: `obtain`/`choose`/`take as` (→ A5, decided);
`take` vs raw `↦` lambdas at proof top level (→ `take`; lambdas only
in terms); `decide` (→ deleted by A4 `otherwise`); `done` (→
restate-the-goal, A1); the `done by substituting X unfolding Y`
sub-language (→ A7 `from`, `suffices by definition of`).

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

(The load-bearing lessons here are inherited from the Lux transition,
which executed a sweep of this shape in June 2026.)

- **The cost model: touch the bulk exactly once.** The analysis bulk
  (`Real/` + `ComplexNumber/`, ~40% of the library) must be migrated in
  ONE coordinated pass after the constructs are settled on smaller
  layers — sweeping construct-by-construct re-touches the same proof
  bodies repeatedly, and each extra touch re-derives the same reasoning
  in a changing syntax. Corollary: land the A-constructs first, sweep
  second.
- **Strictly bottom-up by dependency layer**, `make -j 16 tests` green
  after each coherent group, one reviewable commit per group:
  Natural/Integer/IntegerMod → Rational → Lists/Set → Polynomial →
  Real/ComplexNumber/GaussianInteger. The June sweep confirmed no file
  is a self-contained migration — interface changes cascade both down
  (structural matchers in consumers) and up (lemmas stated in the old
  form) — so partial-layer migrations strand consumers.
- **The mechanical/semantic split.** Syntax mapping (`claim P since L;`
  → `P since L;`; `decide P { yes h => A | no h => B }` → `by cases {
  case P: A otherwise: B }`; numeral rewrites; tuple sugar) absorbs
  ~60–70% of per-file churn and is safe to automate because the kernel
  re-checks every rewrite — a wrong transform fails to verify, the
  safety net is exact. The semantic residue (choosing minimal citation
  sets, characterising lemmas, restructuring term-position helpers) is
  human/LLM work under any strategy. Breadcrumb-claim deletion is
  driven by the B5 classifier.
- **The rewriter is the elaborator, not a text script.** Ad-hoc
  sed/perl passes over `.math` files are banned (they make a mess);
  mechanical rewrites ride the parser/elaborator, which is also the
  only thing that can respect nesting, comments, and layout.
- The redundancy tooling becomes the style enforcer in the
  keyword-free world: distinguish "unused and unenlightening"
  (delete) from "unused but reader-load-bearing" (keep; the old
  `note`) — operationally, whatever the author keeps after a
  `--check-redundant` pass.
- Editor/highlighting: with keywords gone, layout and punctuation
  carry structure; update the editor recipes so statements,
  justifications, and block structure are visually loud.

---

## Part D — interface and implementation (sealed structures)

(Absorbs `PLAN_INTERFACE_IMPLEMENTATION.md`, 2026-06-21, and the
opacity workstream of the Lux transition. The discipline is the
disciplined-C++ one: consumers compile against a header; the
translation unit is never seen.)

### D1. Goal and principle

Give the library true **abstraction barriers**: a type and its
operations are presented to consumers as an *axiomatic interface* — a
fixed set of operations and proven properties — while the construction
lives behind a seal the rest of the library cannot see through.

- Consumers see ℝ the way Spivak presents it — a complete ordered field
  with a ℚ ↪ ℝ embedding — and nothing else. Swapping the Cauchy
  construction for Dedekind cuts must be invisible to every consumer.
- Consumers see `Natural` through `0`/`1`/`+`/`*`/`<`/induction and a
  lemma collection from which anything they need is provable;
  **`successor` is not exported at all.** The implementation file uses
  it heavily — that is its job.

**Sealed, proven, not assumed.** The interface's "axioms" are theorems
*proved about the construction*, then sealed. The interface costs zero
trust: it hides representation and proofs; it admits nothing. This is
strictly better than an axiomatic foundation — the ergonomics of
axioms with the soundness of a construction.

### D2. Where we already are

The library has been converging on this by convention; Part D makes it
a checkable artifact. Already in place: `opaque definition` +
characterising lemmas (`docs/conventions/opaque.md`); Integer and
Rational as opaque quotients behind `difference_equal` /
`fraction_equal` boundaries; algebraic bundles as the semantic version
(an abstract `Ring` consumer can only use the axioms); and the
`successor`-outside-`Natural/` campaign as a lint-enforced prototype of
exactly this barrier. Two opacity spikes measured the retrofit cost
(sealing `Natural.LessThan`: 3 files broke; sealing `Natural.multiply`:
8 home-file unfolds + 2 downstream files) — every break a mechanical
defeq-exploit fix, none structural. **Transform, do not greenfield.**

What's missing: (a) sealing the *carrier type itself* (so the quotient
cannot be unfolded or `by_representatives`-ed), (b) bundling a whole
interface — type + operations + obligations — as one importable unit
with real operators rather than bundle-projection noise, (c)
kernel-level rather than lint-level enforcement.

### D3. Surface design

Two module kinds plus a sealing relation. The interface module declares
the public view — abstract `type`, abstract operation `constant`s,
operator wiring, optionally transparent derived definitions, and
theorem *signatures* (the obligations):

```
interface module Real
  type Real
  constant Real.zero : Real
  constant Real.add  : Real → Real → Real
  constant Real.LessOrEqual : Real → Real → Proposition
  constant Rational.to_real : Rational → Real
  operator (+) on (Real, Real) := Real.add
  …
  definition Real.LessThan (x y : Real) := Real.LessOrEqual(x, y) ∧ x ≠ y
  definition Real.IsSupremum (S : Set(Real)) (s : Real) := …

  theorem Real.is_ordered_field : IsOrderedField(Real, …)
  theorem Real.complete : ∀ (S : Set(Real)). Real.IsNonempty(S) →
            Real.HasUpperBound(S) → ∃ (s : Real). Real.IsSupremum(S, s)
  theorem Rational.to_real.preserves_add : …    -- the hom + order + injectivity packet
```

What the interface exports is decided by CLOSURE over consumer needs,
not minimality (see the D7 decision): theorems consumers genuinely
reach for (density, Archimedean, Cauchy completeness) may be exported
alongside the core even though they are derivable, because they are
proved either way and buildability is the criterion. Whole-theorem
consumers like IVT stay outside. The acceptance test (D6) is
accordingly closure — no consumer needs anything off the list — which
is what the Phase-0 spike measured.

The implementation module provides the opaque construction and
discharges every obligation:

```
implementation module Real.cauchy implements Real
  definition Real := Quotient(CauchyRationalSequence, CauchyEquivalent)
  definition Real.add := …
  theorem Real.is_ordered_field := <proof using representatives>
  theorem Real.complete := <the Cauchy-completeness proof>
```

`implements` is checked at module load: every interface constant/type
has a matching definition of definitionally-equal type; every theorem
signature has a matching proof; the set is complete. Downstream,
`import Real` sees only the interface view — bodies sealed (no
δ-reduction), carrier never unfolding to the quotient. The
implementation module is not on the ordinary import path.

### D4. Eliminator export — the Natural interface

ℝ has no eliminator problem (nothing eliminates a real). `Natural` is
the opposite: **induction IS the interface.** The interface exports an
induction principle stated without the constructor; the implementation
discharges it with the raw recursor:

```
interface module Natural
  type Natural
  constant Natural.zero : Natural
  constant Natural.add  : Natural → Natural → Natural
  -- NB: successor is NOT exported. Naturals are built from 0, 1, +.

  theorem Natural.induction
        : ∀ (P : Natural → Proposition).
            P(0) → (∀ (k : Natural). P(k) → P(k + 1)) → ∀ (n : Natural). P(n)
```

`by induction on n { case n = 0: … case n = k + 1 for some k, with
IH : P(k): … }` (A4's unified clause syntax) desugars to the exported
principle; `| successor(k) =>` patterns disappear from user space. This
is the deep resolution of the successor-confinement campaign: the lint
barrier becomes a kernel barrier, and the one construct the lint could
never remove — constructor patterns — is removed by the eliminator
export. Recursive *definitions* in user space ride the numeral-pattern
recursion (`0` / `1 + n` patterns, already landed) re-based on the
exported recursor.

Semantics: **module-scoped opacity** (a body transparent inside its
implementation module, opaque everywhere else — a small generalization
of the existing per-definition flag) plus the obligation check (reusing
the ordinary theorem-signature match). No kernel-soundness change; the
kernel still checks every proof in full.

### D5. Enforcement: the kernel seal retires the lints

The leak/successor linters are advisory; a sealed type is enforced by
the kernel — a consumer *cannot* δ-unfold ℝ to the quotient even by
accident. Once a type is sealed, its lint retires. **Interim ratchet
(until then):** re-arm the leak-report baseline after each migration
group and wire a no-increase check into `make check` — carrier
constructors outside the owning module, non-opaque definitions outside
the foundational allowlist, opacity piercings: the number only goes
down.

### D6. Phased plan

- **Phase 0 — sealed-ℝ prototype with today's machinery (no language
  change).** Make the carrier and operations opaque outside their
  defining files, route consumers through the field/order/completeness
  theorems, and re-verify the whole IVT cone (`intermediate_value.math`
  + imports) using only the interface: no `by_representatives`/`cases`
  on a Real, no `CauchyRationalSequence` reached through ℝ. Files that
  break enumerate exactly the missing boundary lemmas — that list is
  the deliverable, and it sizes Phase 1 before any syntax is built.
  *Survey result (2026-07-02): the boundary already holds by
  convention.* Every construction-piercing site sits inside Real/'s
  own ~20 construction/boundary files (22 Real-destructures across 11
  of them; 72 `CauchyRationalSequence.make` sites); the other 24
  Real/ files, the IVT cone, exponential, and all of ComplexNumber/
  contain ZERO construction vocabulary. So Phase 0 needs no consumer
  rewrites — the risk surface is only whatever consumers currently
  get from transparent δ-reduction rather than stated theorems, which
  the opacity flip will enumerate directly.
  *Spike result (2026-07-02: flipped `Real` to `opaque definition`,
  keep-going build, then reverted).* **7 files fail, everything else —
  including all of ComplexNumber/ — verifies.** Two failure shapes:
  (a) construction files (`addition`, `embedding_order`, `field`,
  `triangular_series`-adjacent): declared type says `Real` /
  `Rational.to_real(…)`, the proof's inferred type spells the reduced
  `Quotient.class_of(…)` form — home-file reconciliation, the
  mechanical `unfolding`/boundary-lemma bill;
  (b) consumers (`continuity`, `derivative`, `limits`): "the function
  expects `Quotient.{0} CauchyRationalSequence CauchyEquivalent` but
  this argument is `Real`" — an imported interface type carries the
  REDUCED spelling, i.e. the opaque-quotient-alias machinery that
  already serves Integer/Rational does not engage for `Real`'s alias
  in the interface-normalization path. (b) is an ELABORATOR gap, not
  proof debt, and is the concrete first work item of Phase 1; fix it
  and the Phase-0 bill shrinks to the handful of home-file
  reconciliations in (a). Cost measured: bounded and small, matching
  the `Natural.multiply` spike precedent.
- **Phase 1 — language support** (`interface module` /
  `implementation module … implements`, scoped opacity, obligation
  check, export view); migrate the ℝ prototype onto it.
- **Phase 2 — eliminator export**, then seal `Integer` (already an
  opaque quotient; modest eliminator needs).
- **Phase 3 — `Natural`** (D4): the hardest and last, where this part
  and the successor campaign converge. Prep work already queued:
  sealing `Natural.multiply`/`factorial` behind characterising lemmas
  (reference implementation exists on the field-of-fractions branch).
- **Phase 4 — the rest**: ℂ on a sealed ℝ, finite fields, polynomials.

### D7. Costs, risks, open questions

- **Loss of defeq.** Every ι/δ-reduction consumers lean on becomes a
  propositional boundary lemma — the same bill Integer/Rational already
  paid, just larger. Phase 0 measures it; the mitigation is a generous,
  well-named boundary-lemma set published *with* the interface.
- **Numerals.** `0`/`1`/`2`/`k + 1` for sealed types must elaborate via
  interface constants, not constructors, and `ring`/`field` must still
  see numerals. Note the Part-B interaction: over a sealed `Natural`,
  tier-2 ground evaluation cannot ι-reduce — it must be lemma-emitting.
- **Tactics over sealed carriers.** `ring`/`field` already work over
  abstract bundles, so the path exists; verify they fire through the
  interface axioms.
- **Interface minimality vs convenience — DECIDED (owner,
  2026-07-02): buildability wins.** Nothing is ever assumed — every
  interface entry is proved from the construction — so the question
  was only which proved statements to export. The criterion is "easy
  to build on top of," not axiomatic purity: the interface is the
  CLOSURE of what consumers actually need (operationally: the
  headline theorems the construction files already export — exactly
  what the Phase-0 spike validated), not a minimal axiom set.
  Concretely for completeness: **LUB (Spivak's form) is the
  canonical completeness statement, and Cauchy completeness is
  exported alongside it** — both proofs already exist
  (supremum.math, cauchy_complete.math), so this costs nothing
  today; the eventual nicety is re-deriving Cauchy completeness over
  the interface rather than the construction (cauchy_complete.math
  is already construction-vocabulary-free, so this is nearly true
  now). A future alternative implementation discharges LUB and
  derives Cauchy via the (then-generic) equivalence. The minimal
  core (ordered field + LUB + embedding packet) remains identified
  — not as the export boundary, but as the statement of the
  categoricity theorem below. Extension discipline unchanged:
  extend the interface and discharge the new obligation, never
  bypass it.
- **Uniqueness.** A complete ordered field is unique up to unique
  isomorphism; stating (eventually proving) categoricity makes "swap
  the construction" a theorem rather than a hope.

### D8. Integration with Parts A–C

- **A4:** structural-case exhaustiveness lemmas are interface
  obligations; clause syntax `case n = k + 1 for some k:` routes
  through the exported principle (note in A4).
- **B1/B2:** interface theorems are the natural `automatic` set —
  stated in dischargeable (proper-subterm-premise) form they feed the
  tier-4 judgment index directly; implementation internals are never
  automatic. An interface style rule: prefer stating obligations in
  rule-admissible form.
- **B3:** the embedding hom/order packet in an interface (`to_real.
  preserves_*`) IS the morphism packet cast normalization consumes —
  one declaration serves both.
- **C6:** interface conversion of a layer and its syntax migration are
  the same touch — schedule them together so the bulk is still touched
  once.

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
9. **Part D** runs as a second track: **Phase 0 (sealed-ℝ prototype)
   is library-only and can start immediately** — its
   missing-boundary-lemma list is cheap information, like the B5
   classifier. The `Natural.multiply`/`factorial` sealing (Phase-3
   prep) likewise. Language support (D Phases 1–2) waits for A4 so the
   eliminator export and the unified `by cases` land as one design;
   Phase 3 (`Natural`) comes after the A-construct sweep so the bulk
   is touched once (C6 cost model).
10. **A8** (ellipsis folds/series): its steps 1–3 (generic `Fold` +
    registry + characterizing lemmas, explicit binder form) are
    independently valuable and can start any time; the ellipsis
    recognizer waits for the tier-2 evaluator (step 2 above), and the
    series relations (§6) wait for A6 (step 7).

## Reference target

`sqrt_two_irrational.math` after steps 1–6 (the agreed idealized form —
keep this in the repo as the acceptance test for the migration):

```
theorem Natural.two_divides_root (m : Natural) (squareEven : 2 ∣ m * m)
        : 2 ∣ m :=
  by Natural.prime_divides_product

theorem Natural.no_double_square (m n : Natural)
        (mPositive : 1 ≤ m) (nPositive : 1 ≤ n)
        : m * m ≠ 2 * (n * n) := {
  by_strong_induction on m with no_smaller_solution;
  suppose m * m = 2 * (n * n) as equation;

  2 ∣ m  by Natural.two_divides_root;
  choose k such that m = 2 * k;

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
  by Natural.no_double_square
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

  choose N such that eventually (m). abs(s(m) - s(N)) < ε/2
      from sIsCauchy;
  eventually (m). -ε/2 < s(N) - b(m)
      by pointwiseLower(N), by definition of Real.LessOrEqual;

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

---

## Review pins (2026-07-02 code-check)

A read of the current elaborator/parser against this plan confirmed
its factual claims and produced these amendments; treat them as part
of the design:

1. **A4:** keep `refining` / `cases … with eq` parse-accepted until
   the substitution rule survives the full migration (~85 uses).
   Substitution into arbitrary hypothesis types has historically hit
   opacity walls; delete the escape hatches only after the general
   rule is proven on the whole library.
2. **A2 × B1:** dedup is hash-based but statement-matching is
   defeq-based, so a user-stated fact and a silently derived one can
   both match. Rule: statement-addressing prefers user-stated facts;
   ambiguity errors fire only on ties among user-stated ones.
3. **B1:** derived environment-level facts never export across the
   file boundary — whether a file verifies must not depend on what
   side conditions another file's proofs happened to derive.
4. **A1:** rhetorical connectives may affect which proof is found and
   how fast, never *whether* one is found. Pin this as an invariant or
   the "noise word" story is false.
5. **B2 boundary rule, explicit:** fact *search* is scoped by
   `automatic`; syntactic *indexes* may be global (precedent: the
   rewrite index already seeds from every imported equality lemma).
6. **Tier 6** must respect the unary-coefficient ceiling of the ring
   normaliser (proof size O(Σ|coefficient|)) — meter it accordingly,
   or gate on the symbolic-coefficient rewrite.
7. **A7:** `decide` disappears from the proof surface; the value-level
   machinery underneath `if … then … else` in definitions survives.
8. **DECIDED (owner, 2026-07-02):** both convention questions are
   settled — `by`/`since` unify on `by` (C1), and the destructuring
   construct keeps `choose … such that` with `obtain` retired (A5).
   See those sections for the rationale and consequences.

---

## Lineage, document map, and the Lux rename

**Folded into this plan and deleted** (git history is the record):

- `PLAN_LUX_TRANSITION.md` (2026-06) — the transition executed and
  merged to main 2026-06-19. Landed and recorded there: the induction
  keystone, the opacity spikes (→ D2's "transform, do not greenfield"),
  the cite-only validation (superseded by the `automatic`-tier model
  Part B builds on), the baby library, the bottom-up sweep discipline
  (→ C6). Its `1 + n`-keystone framing was reframed 2026-06-22 into
  "confine the constructor asymmetry to the `Natural/` floor" — whose
  final form is D4's kernel seal.
- `PLAN_INTERFACE_IMPLEMENTATION.md` (2026-06-21) — now Part D,
  updated with the A4/B/C6 integration points.

`LUX_PLAN.md` (the old destination spec) is already gone; this
document is the destination spec. Still-current companions:
`LANGUAGE.md` (the as-is idiom reference — C4's completeness target),
`PLAN_KERNEL.md`, `PLAN_COERCIONS.md`, `PLAN_CAST_NORMALIZATION.md`
(B3's precursor), `PLAN_AUTOPROVER_FINGERPRINT.md` /
`PLAN_READABILITY.md` / `PLAN_LESS_CIC_STYLE.md` (shipped-infrastructure
records).

**The rename.** The language becomes **Lux** when the reference target
above verifies in its idealized form (end of step 6) — the moment the
surface actually looks like the new language. Renaming earlier would
brand transitional syntax and force a second identity migration; at
the gate, docs, error messages, and editor recipes migrate once.

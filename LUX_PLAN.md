# LUX — a higher-level proof-description language

Design conclusions from the design conversation. **Lux** is a surface
language for stating and proving mathematics whose goal is that a working
mathematician can be fully productive **without ever learning CIC**. The
kernel still checks CIC; Lux is the C to the kernel's assembly. The
overriding value is the same as the rest of this project: proofs read like
a textbook, and the foundation never pokes through except where it is
genuinely a mathematical choice.

## Reference points

The honest analogues are **Mizar** and **Isabelle/Isar** — declarative
proof languages over a foundation that practitioners use without thinking
about that foundation — with **Dafny** as the cautionary tale: pushing
everything through a clever prover makes users form a mental model of the
prover and hit flaky timeouts. Lux takes the Mizar promise: the checker is
**boring, weak, fast, and predictable**, with explicit escape hatches,
rather than clever-but-unreliable.

---

## 1. The unifying model: one prover, three ways to feed it context

Every proof obligation `O` is discharged by the **same** engine over three
inputs:

```
discharge(O)  =  Tactics  ∪  LocalContext  ∪  Cited
```

- **Tactics** — always on, never named. A fixed set of self-contained
  **decision/normalization procedures**, each carrying its own axioms
  internally; they do *not* consult the lemma database, which is exactly
  why they cannot reopen the global search:
  - ring/field normalization,
  - congruence closure,
  - linear arithmetic / order over an ordered field (à la
    Fourier–Motzkin / simplex): transitivity of `≤`, antisymmetry, and
    adding inequalities are *internal moves of the procedure*, baked in
    the way distributivity is baked into `ring` — never citable facts.
    Linear inequalities are in scope; **nonlinear** ones (AM-GM-shaped
    goals) are not — they stay cited or hand-proved.
  - classical propositional reasoning incl. **negation-normal-form
    rewriting** (DNE `¬¬P → P`, and the quantifier de Morgan dualities
    `¬∀x.P ⤳ ∃x.¬P`, `¬∃x.P ⤳ ∀x.¬P`). These are directed, terminating
    rewrites — not search.
- **LocalContext** — hypotheses, `suppose`-assumptions, every prior claimed
  statement / chain result in scope. **Always auto-searched.**
- **Cited** — exactly the global library lemmas named with `by L1, L2`.
  Nothing from the global imports enters automatically.

**The Tactics set is extended only at the language level, never per-lemma.**
A candidate may enter Tactics only if it is (1) a terminating decision or
normalization *procedure* (not a fact to match against the goal), (2)
self-contained (carries its own axioms, never reads the lemma database),
and (3) admitted by deliberate review of the *language*, not by a library
author tagging a declaration. There is deliberately **no `automatic`
marker** for promoting individual lemmas: a marked-automatic lemma is a
fact the prover must match and unify — i.e. search — and a keyword has no
natural stopping point, so it reassembles the global auto-search one tag
at a time. If a fact feels fundamental enough to be automatic (e.g.
transitivity of `≤`), it belongs *inside* a built-in tactic, not on a
markable list; everything a procedure cannot decide gets a `by`.

The surface constructs differ only in **how they extend the context**
before this one prover runs:

- bare `P` (or `name : P`) — prove `P` from the tactics + current local context.
  **This is a "claim": stating a fact proves it and adds it.**
- `P by L1, L2` — same, with `L1, L2` temporarily added to local context.
  The lightweight one-liner.
- `P { … }` — the `…` populate a child context, then `P` is discharged
  there. The structured form.

`by <lemma>` is therefore not a separate mechanism — it is "drop this named
fact into the local context for this obligation." `by` and `{ }` compose.

### Citation is a necessity claim, not a hint

A cleaner way to read the model: the built-in tactics are the **engine**,
not a third fact-set; the two fact-sources are `LocalContext` and `Cited`;
and a step may optionally pick which procedure runs. So every obligation is

```
prove(goal  |  LocalContext, Cited, selectedTactic?)
```

**Invariant: every cited fact must actually be used.** A citation is a
*necessity claim* — `by L` asserts "this step genuinely depends on L" — so
the prover must find a derivation that uses `L`, or the step is ill-formed
("`L` is unused — remove it"). Citing is never a suggestion the prover may
ignore.

**No-redundant-citation is therefore emergent, not special-cased.** It is
not a rule we write down; it falls straight out of the invariant. `ring`
proves a pure identity using *no* facts, so if `ring` would close a goal
while a citation sits unused, that discharge is rejected — which is exactly
why "`ring` does not fire once you have cited a lemma." Selecting `by ring`
*and* citing a fact is likewise an incoherent request: a zero-fact tactic
handed a fact. You never hardcode either case; both are the invariant
biting. This turns the old `--check-redundant-by` linter from a post-hoc
cleanup pass into a **typing rule**: a redundant citation is a failed proof,
so redundant citations cannot exist.

The invariant also sharpens the fact-free / fact-using split:

- **`ring` (named, fact-free)** — closes a pure ring identity, takes no
  facts; citing alongside it is an error.
- **the general engine (no tactic selected)** — ring-normalization +
  congruence + linear-arithmetic + propositional together; *this* is what
  consumes facts. Given `h : a = b`, proving `a·c + 1 = b·c + 1` is the
  engine's job (congruence consumes `h`, then ring normalizes), not bare
  `ring`'s.
- **fact-consuming named tactics** — `field(h₁, …)`, `linear_combination`,
  `by induction on n` (consuming the IH): by the invariant they must use
  *all* the facts handed to them. `linear_combination` is the archetype —
  every term you supply is load-bearing.

The deliberate cost is that this **kills shotgun citing**: you cannot list
five lemmas and let the prover sort out which it needs; you cite exactly the
necessary set. For this project that is the point, and the failure is
friendly. The precise reading of "used": the prover must find a proof that
uses *every* cited fact; if every proof ignores one, that is an error — so a
logically-redundant cite (already implied by another) is rejected, which is
correct, because it *is* redundant. (This keeps citation sets minimal, and
dovetails with the fingerprint suggester, which proposes the minimal set in
the first place.)

### Two things live in the `by` slot

`by <method>` is one uniform slot, but it holds two genuinely different kinds
of method, and the difference is what keeps "Lux has user-invoked tactics"
true without reopening tactic-soup:

1. **Naming an always-on tactic** — `by ring`, `by field`. The tactic runs
   anyway as part of every discharge, so naming it is *optional* and adds no
   power. Two legitimate uses: a **reader annotation** of the step's reason
   ("this is pure ring algebra"), and a **focusing directive** ("close this
   with ring specifically — do not grind the whole context"). Omit it and the
   step still proves.
2. **Invoking a directive method** — `by induction on n`, `by cases on x`,
   `by well-founded on <measure>`. These are *necessarily* named, because each
   demands a **choice the prover refuses to guess** (which variable to induct
   on, which measure descends) — the anchored-unification-yes,
   term-invention-no contract. The prover never silently inducts or
   case-splits; omit the method and the step is unprovable by the engine
   alone.

The invariant: the prover does category 1 on its own (you may still name it);
it does category 2 only when explicitly invoked. `by <lemma>` citation is a
third inhabitant of the same slot — a fact-consuming one, governed by the
must-use-all rule above. This is the precise sense in which Lux rejects
tactic-*soup* (imperative goal-state mutation as the authoring mode) while
keeping named methods.

### Pinning a cited lemma's arguments

The prover anchors a cited lemma's `∀`-variables by unifying against the
goal, and by contract **will not invent an unanchored one**. When a lemma
has an argument the goal does not pin — classically a **pivot**, the middle
term `b` of `∀ a b c, R a b → R b c → R a c` used to close `R a c` — supply
it by name:

```
P by L with b := m             -- "by L, with its b taken to be m"
P by L with b := m, k := n+1   -- pin several
```

- **Terms, not proofs.** `with` anchors `∀`-bound *variables* (`b := m` is
  a term). L's *hypotheses* discharge as usual — from context or via further
  citations (`by L, H with b := m`) — which keeps this clear of the
  no-positional-proofs rule.
- **Partial by design.** Pin only what unification cannot recover;
  everything the goal anchors stays inferred. Spelling out *every* argument
  is the positional-lemma-call smell the language avoids.
- **`with` binds to one lemma.** Common case: one lemma, one pivot. To pin
  args on more than one cited lemma, group: `by (L with b := m), N`.

### The predictability contract (write this down once, never revisit)

The prover does **goal-directed resolution over a bounded fact set**
(local context + cited lemmas), depth/step-budgeted. It does:

- normalization + congruence + classical propositional/NNF reasoning;
- discharge any goal entailed propositionally by the available facts;
- **goal-directed matching**: unify the goal against the *head* of a
  local/cited fact and propagate (so local `∀x, P x → Q x` plus `P a`
  closes goal `Q a` — the goal *anchors* `x := a`).

It explicitly does **not**:

- do **forward saturation** (derive all consequences of the context);
- invent an **unanchored witness** for a goal `∃x, P x` (nothing pins `x`);
- do **induction** or **case analysis on data**.

The line is *anchored unification, yes; term invention, no.* Everything
that needs anchoring gets explicit syntax: `take` / `obtain` /
`by_induction` / `cases`.

### The local/global split is the predictability lever

Auto-searching the (small, bounded) local context is cheap and its failures
are legible. Auto-searching the (thousands-of-lemmas) global library is the
slow, flaky, rot-prone thing — so it is **off by default**; a global lemma
enters only when cited with `by`. This also improves readability and
refactoring: proofs name their non-trivial dependencies, and a changed
lemma breaks at the cite site. (A curated opt-in hint database, `by *`,
could exist later but is never the default.)

**The boundary is the module.** "Local" means the whole current module: a
prior top-level lemma in the same file is in scope and auto-searched (it is
small, bounded, and cannot be perturbed by anything off the page). "Global"
means the import surface, which is large and rot-prone, so it is cite-only.
This cite boundary deliberately *coincides* with the interface/body split
and the incremental-rebuild unit — one module boundary serves privacy,
recompilation, and prover scope at once.

On failure, the error surfaces the local context: "couldn't close `P` from
local context + [cited]; facts in scope were …" — telling the user whether
to add a line or cite a lemma. Because global auto-search is gone, this
failure-time suggestion is load-bearing for discoverability: it should also
surface fingerprint-indexed "did you mean `by L`?" candidates from the
import surface (the same goal-shape index built to color ring searches —
see the auto-prover fingerprint plan). That index is the discovery path
that replaces global auto-search.

---

## 2. Blocks and statements

- Drop `:=`. A proof is a uniform block `{ … }`.
- A **statement** is `<proposition> <block?>`:
  - no block ⇒ the built-in tactics must close it;
  - with a block ⇒ the block closes it.
- **Named** local lemma: `name : P { … }`. **Anonymous**: `P { … }`.
  No new keyword needed — `name : P` already reads as "name is a proof of
  P," and dropping `:=` makes `{ … }` the proof. **`claim` disappears**;
  claiming is the default behavior of every statement.
- A block is **closed** at `}` when the prover proves the block's
  goal from its local context. The common case (last established fact *is*
  the goal) is the trivial/cheap call. No explicit "exact" needed.
- Grammar rule: a statement must be a `Prop`-typed term ("prove and add"),
  or a binder form (`let` / `obtain` / `take` / `suppose`). A
  bare non-`Prop` term establishes nothing and is an error.

---

## 3. Chains (replace `calc`)

Two **disjoint** chain kinds. `calc` as a keyword disappears; a chain is
just a statement.

### Term-relation chains

Relate **terms** over `=` / `<` / `≤` / `>` / `≥` / `∣` / `⊆` (the existing
mixed-relation composition lattice). Write the first term once; continuation
lines **start with the operator**; each step takes an optional `{ … }` (or
`by`) justification:

```
a
  = b   { … }
  < c
  = d   { … }
  < e
```

Asserts the **endpoint relation** `a < e` (added to context). Intermediate
facts are scaffolding and not added by default; name a step to keep it.

### Implication chains (`=>`)

Relate **propositions**. This is the keyword-free realization of forward
reasoning (Mizar's `then` / Isar's `this`): the previous line of the chain
is the antecedent, so the thread is positional and never named.

```
n even
  => n*n even          -- prover: from "n even" + context
  => n*n + n even       -- prover: from previous line
```

Semantics: a relation chain over the implication preorder; it asserts
`head => tail`. Because `head` is typically a standing fact, modus ponens
also hands you `tail` as a fact (MP-collapse).

**The two chain kinds do not interleave.** Each `=>` link is a *complete
proposition* (which may itself be a relation like `a + e < c + e`), never an
*open* relation chain. Mixing them — `a = b < c => a+e < c+e = f` — has no
defensible single meaning. No expressiveness is lost: monotonicity-style
reasoning relocates cleanly to a `=>` link where its justification is
explicit:

```
a < c
  => a + e < c + e     -- prover discharges via order-monotonicity
  => a + e < f          -- given c + e = f as a standing fact
```

---

## 4. Implication intro: `suppose`

> **Implemented in the current elaborator** (`for contradiction` and
> `to prove Q { … }` modifiers on `suppose`). The current forms keep `as h`
> (optional for the modifiers) and the explicit DNE step is inserted as
> `Logic.by_contradiction` rather than relying on a silent prover coercion —
> that coercion was deliberately dropped (see `Test/dne_bridge_test`). The
> rest of this section is the original design note.

Replaces `assume`. Two modes; `to prove` optional:

- **Backward** (current goal is already `P → Q`): `suppose P { … }` peels
  it, goal becomes `Q`.
- **Forward** (introduce a fresh implication): `suppose P to prove Q { … }`
  — sugar for stating `(P → Q) { suppose P … }`, adds `P → Q`.

There is **no** standalone `to prove Q { … }` (that is just `Q { … }`);
`to prove` exists only as the connective inside forward `suppose`.

### Contradiction

`suppose P for contradiction { … derive False … }` always produces `¬P`
(i.e. `P → False`) directly. One rule covers both uses, because the prover's
silent DNE finishes the rest:

- goal `¬Q`: the block yields `¬Q`, closes directly;
- goal `Q`: `suppose not Q for contradiction { … False … }` yields `¬¬Q`,
  and the prover silently closes `Q`.

No separate reductio keyword; classicality lives entirely in the prover.

---

## 5. Existentials: `obtain` / `take`

The elim/intro pair.

- **`obtain ⟨w, hw⟩ from <source>`** — eliminate an existential **in a
  proof**. `from` accepts a proposition; the prover proves it (tactics +
  context); then it is destructured, binding the witness `w` and the
  property `hw`. This is the workhorse (≈640 uses in the current library);
  the older `choose … such that` keyword is **retired** (0 uses). It is
  ordinary `Prop → Prop` elimination — **no axiom**, because a proof's goal
  is itself a `Prop`.
  - For an **opaque** predicate (e.g. `Divides`), register its
    characterizing lemma as a **destructor**, so `obtain ⟨q, …⟩ from (2 ∣ n)`
    works whether or not the predicate is transparent.
- **`take <witness> { … }`** — introduce an existential for the goal; the
  boring prover refuses to *guess* witnesses, so intro is always explicit.

```
2 ∣ n  to prove  4 ∣ n*n {
  obtain ⟨q, nEqualsTwoQ⟩ from (2 ∣ n)     -- n = 2*q
  n*n = (2*q)*(2*q) = 4*(q*q)
  take q*q                                  -- divides-intro; witness explicit
}
```

### Unique existence and definite description

`∃! x. P(x)` ("exactly one") packages `∃ x. P(x)` with uniqueness. In a
**proof**, `obtain ⟨x, hx, uniqueness⟩ from <∃! …>` extracts the witness,
its property, and uniqueness — again no axiom.

Turning a unique-existence proof into an actual **function** (building
**data**) is the one thing `obtain` cannot do: the recursor may not
eliminate a `Prop` into `Type`. That bridge is the definite-description
axiom — and it surfaces **only** as a binder inside a definition:

```
definition Real.limit (s : Sequence) : Real
  := unique x such that <s converges to x>      -- obligation: ∃! such x
```

The `∃!` obligation is discharged by the prover. The raw four-argument
operator `the(T, P, existence, uniqueness)` **never appears**, and neither
does the bare token `the`: a reader meets `Real.limit` everywhere and
`unique x such that …` only at this one definition site. We keep **unique**
choice only — there is deliberately no general Hilbert-ε `choose`; unique
choice is the weakest axiom that does the job, and the library already
lives within it.

---

## 6. Induction

In CIC, induction is an eliminator demanding a **motive** (the property as a
function of the induction variable). Three things leak through any naive
"induct on the goal" surface: (a) *which occurrences* of the variable to
abstract, (b) *strengthening* — the literal goal's induction hypothesis is
often too weak, (c) *reverting* — hypotheses mentioning the variable must be
folded in or the IH is useless.

**Resolution: induction abstracts the body of an explicitly-stated
proposition, never a guessed predicate.** One form:

```
<proposition> by induction on n { base { … } step (k, IH) { … } }
```

`induction on n` is a proof *method* in the same `by` slot as `by <lemma>`
(it just wants a block of case sub-proofs). The motive is the proposition's
body abstracted over `n` — no higher-order guessing, no `λ`, the word
"motive" never appears.

- **Goal-as-motive:** `goal by induction on n { … }`. `goal` is the existing
  statement-level sugar for "the current goal"; using it as the proposition
  collapses goal-as-motive and strengthening into one construct with no
  special case. It abstracts *all* occurrences of `n`, gives the *bare*
  goal (context hypotheses not auto-reverted), and tracks the theorem
  statement through refactors automatically.
- **Strengthening = state a stronger claim and induct on it.** The
  accumulator proof becomes `∀ a, sum_aux xs a = a + sum xs by induction on
  xs { … }`, then the original goal falls out by the local prover
  (`a := 0`). The generality lives in the quantifier the user wrote.
- **Reverting = put the hypothesis into the stated proposition**
  (`Q m → goal`, or sugar `… by induction on n generalizing h`).
- **Scheme selection by name** — `by induction on n`,
  `by strong_induction on n`, two-step, etc. The scheme (a mathematical
  choice) determines how its motive is built from the stated proposition;
  the plumbing stays hidden.

When `goal` gives too weak an IH, the experience is "strengthen the
statement" — the genuine mathematical lesson — not a foundations error.

---

## 7. Logic mode: classical, full stop

- **Classical everywhere; no constructive fragment.** LEM, definite
  description (unique choice, §5), and silent DNE / `¬¬`-elimination are all
  part of the built-in tactics. A mathematician never writes an extra step to
  get `P` from `¬¬P`. There is **no `constructively` badge** and **no
  per-step constructivity tracking**: the language is never used to compute,
  so constructivity's one payoff — program extraction — does not apply, and
  §8 already decouples *reasoning* from *computation* (definitions reason via
  their registered equations, not by reduction). Accepting a non-constructive
  step anywhere costs nothing here.
- **`decide` is uniformly classical.** Building data by deciding a
  proposition (`decide P`, §8 — e.g. `List.filter`) always uses classical
  decidability for *any* `P`, with no `Decidable`-instance plumbing. Such a
  value is noncomputable, which is irrelevant because we never compute it —
  reasoning goes through the defining equations.

---

## 8. Pattern-matching

Proofs and definitions get opposite answers.

- **Proofs: no raw pattern-matching.** `cases on x { … }` (and
  `cases … with`) and `by_induction` subsume every use and avoid the worst
  leak — **dependent matching** and its hand-written return motive (the
  "convoy" dance). Banned in proof position.
- **Definitions: keep equational by-cases / recursive definitions** —
  `length [] = 0` / `length (x :: xs) = 1 + length xs` is how a textbook
  defines a function and there is no more readable alternative. But remove
  the leaks by elaborating such a definition to:
  - an **opaque** function (no silent defeq unfolding — this is the
    `less_cic_plan` WS2 "kill-unfold" goal achieved at the language level);
  - its **defining equations as named characterizing lemmas / registered
    rewrite rules**. The prover reasons *and computes* via these equations
    (so `length [a,b,c]` reduces to `3` by rewriting, not defeq) — one
    predictable mechanism, never a surprise unfold.
  - **Exhaustiveness and non-overlap checked**, reported as math-level
    errors ("you didn't cover the empty list", "these equations overlap on
    `0`"), never as recursor/motive errors.
  - **Termination** is a real obligation but its discharge is mostly
    invisible: structural recursion checked silently; the escape is a named
    measure, `by well-founded on <measure>`, never the accessibility
    predicate.
- **Patterns appear in exactly one place — function definitions — and never
  in proofs.**

Residual hard case: **dependent definitions** (return type depends on the
scrutinee, e.g. length-indexed vectors) are the one genuinely CIC-ish
corner with no equational reframing. Keep them rare and behind interfaces
(as the finite-cardinals work already does with explicit witness pairs)
rather than making the surface pretend CIC isn't underneath.

---

## 9. What gets dropped

- `:=` for proofs — replaced by uniform `{ … }` blocks.
- `claim` — claiming is the default behavior of any statement.
- `calc` — replaced by bare term-relation chains and `=>` chains.
- `assume` — replaced by `suppose`.
- The **join idiom** (Isar `moreover`/`ultimately`) — unnecessary, because
  the prover always searches the *entire* local context goal-directed. Isar
  needs it only because its default implicit scope is the single previous
  fact; Lux has no such limitation, so to combine several earlier facts you
  just state the conclusion. (Reader-facing "this follows from those" is
  served by `since`/`note`, not a keyword.)
- Raw pattern-matching in **proofs**.
- The **`choose … such that` keyword** — `obtain ⟨…⟩ from …` is the sole
  existential-elimination form (§5).
- The **`constructively` badge** and all constructivity tracking — the
  language is classical, full stop (§7).
- The **bare `the(…)` operator** — definite description surfaces only as
  `unique x such that …` inside a definition (§5).

## 10. Residual leaks to keep contained (honest list)

CIC is not 100% hidden; these are where it is thinnest, each walled where
possible:

- **Dependent pattern-matching / dependent definitions** — §8; keep rare,
  behind interfaces.
- **Noncomputability of definite description** (`unique x such that …`,
  §5) — values built by description do not reduce; harmless because §8
  reasons through equations, never by computation. Document once.
- **Induction-hypothesis strengthening** — §6; genuinely mathematical, and
  surfaced as "strengthen the statement," not as motive editing.
- **Definitional-equality surprises** — largely removed by the
  opaque-definition + equations-as-rewrite-rules discipline (§1, §8); the
  prover's behavior is rewriting, not defeq.

---

## 11. Open / next

- Exact concrete syntax for the `cases` / `by_induction` case blocks
  (constructor enumeration, binder names for sub-data + IH).
- Layout/indentation rules for chain continuation lines and nested blocks.
- The destructor-registration mechanism for opaque predicates (so `obtain
  ⟨…⟩ from <opaque prop>` is uniform, §5).
- Depth/step budget defaults for the local-context search. The "facts in
  scope were …" failure message should additionally surface fingerprint-
  indexed "did you mean `by L`?" candidates from the import surface (§1) —
  the discovery path that replaces global auto-search.
- The concrete linear-arithmetic / order procedure and its reach:
  ordered-field (Fourier–Motzkin / simplex) vs. integer Presburger, the
  rational/real/natural/integer coverage, and its step budget (§1 Tactics).
- How `by <method>` generalizes: `by <lemma>`, `by induction on n`,
  `by cases on x`, `by well-founded on <measure>` all live in the same slot.
  (The lemma-argument form is decided — `by L with b := m`, §1; the
  induction/cases/well-founded case-block shapes are the open part.)

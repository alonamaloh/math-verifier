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
discharge(O)  =  Closure  ∪  LocalContext  ∪  Cited
```

- **Closure** — always on, never named:
  - ring/field normalization,
  - congruence closure,
  - classical propositional reasoning incl. **negation-normal-form
    rewriting** (DNE `¬¬P → P`, and the quantifier de Morgan dualities
    `¬∀x.P ⤳ ∃x.¬P`, `¬∃x.P ⤳ ∀x.¬P`). These are directed, terminating
    rewrites — not search.
- **LocalContext** — hypotheses, `suppose`-assumptions, every prior claimed
  statement / chain result in scope. **Always auto-searched.**
- **Cited** — exactly the global library lemmas named with `by L1, L2`.
  Nothing from the global imports enters automatically.

The surface constructs differ only in **how they extend the context**
before this one prover runs:

- bare `P` (or `name : P`) — prove `P` from closure + current local context.
  **This is a "claim": stating a fact proves it and adds it.**
- `P by L1, L2` — same, with `L1, L2` temporarily added to local context.
  The lightweight one-liner.
- `P { … }` — the `…` populate a child context, then `P` is discharged
  there. The structured form.

`by <lemma>` is therefore not a separate mechanism — it is "drop this named
fact into the local context for this obligation." `by` and `{ }` compose.

### The predictability contract (write this down once, never revisit)

The prover does **goal-directed resolution over a bounded fact set**
(local context + cited lemmas), depth/step-budgeted. It does:

- normalization + congruence + classical propositional/NNF closure;
- discharge any goal entailed propositionally by the available facts;
- **goal-directed matching**: unify the goal against the *head* of a
  local/cited fact and propagate (so local `∀x, P x → Q x` plus `P a`
  closes goal `Q a` — the goal *anchors* `x := a`).

It explicitly does **not**:

- do **forward saturation** (derive all consequences of the context);
- invent an **unanchored witness** for a goal `∃x, P x` (nothing pins `x`);
- do **induction** or **case analysis on data**.

The line is *anchored unification, yes; term invention, no.* Everything
that needs anchoring gets explicit syntax: `take` / `choose` /
`by_induction` / `cases`.

### The local/global split is the predictability lever

Auto-searching the (small, bounded) local context is cheap and its failures
are legible. Auto-searching the (thousands-of-lemmas) global library is the
slow, flaky, rot-prone thing — so it is **off by default**; a global lemma
enters only when cited with `by`. This also improves readability and
refactoring: proofs name their non-trivial dependencies, and a changed
lemma breaks at the cite site. (A curated opt-in hint database, `by *`,
could exist later but is never the default.)

On failure, the error surfaces the local context: "couldn't close `P` from
local context + [cited]; facts in scope were …" — telling the user whether
to add a line or cite a lemma.

---

## 2. Blocks and statements

- Drop `:=`. A proof is a uniform block `{ … }`.
- A **statement** is `<proposition> <block?>`:
  - no block ⇒ the closure prover must close it;
  - with a block ⇒ the block closes it.
- **Named** local lemma: `name : P { … }`. **Anonymous**: `P { … }`.
  No new keyword needed — `name : P` already reads as "name is a proof of
  P," and dropping `:=` makes `{ … }` the proof. **`claim` disappears**;
  claiming is the default behavior of every statement.
- A block is **closed** at `}` when the closure prover proves the block's
  goal from its local context. The common case (last established fact *is*
  the goal) is the trivial/cheap call. No explicit "exact" needed.
- Grammar rule: a statement must be a `Prop`-typed term ("prove and add"),
  or a binder form (`let` / `obtain` / `choose` / `take` / `suppose`). A
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

Replaces `assume`. Two modes; `to prove` optional:

- **Backward** (current goal is already `P → Q`): `suppose P { … }` peels
  it, goal becomes `Q`.
- **Forward** (introduce a fresh implication): `suppose P to prove Q { … }`
  — sugar for stating `(P → Q) { suppose P … }`, adds `P → Q`.

There is **no** standalone `to prove Q { … }` (that is just `Q { … }`);
`to prove` exists only as the connective inside forward `suppose`.

### Contradiction

`suppose P for contradiction { … derive False … }` always produces the
**constructive** thing, `¬P` (i.e. `P → False`). One rule covers both uses,
because the prover's silent DNE finishes the rest:

- goal `¬Q`: the block yields `¬Q`, closes directly;
- goal `Q`: `suppose not Q for contradiction { … False … }` yields `¬¬Q`,
  and the prover silently closes `Q`.

No separate reductio keyword; classicality lives entirely in the prover.

---

## 5. Existentials: `choose` / `take`

The elim/intro pair, both able to cross `Prop → data` via classical choice
(see §7).

- **`choose q such that <body> from <source>`** — eliminate an existential.
  `from` accepts a *proposition*; the prover proves it (closure + context),
  then the existential is destructed. Elaborates to
  `q := Classical.choose(h)` and hands back `Classical.choose_spec` as the
  proof of `<body>`.
  - The source must be massaged into existential form. For an **opaque**
    predicate (e.g. `Divides`), register its **characterizing lemma as a
    destructor** so `choose … from (2 | n)` works uniformly whether or not
    the predicate is transparent.
- **`take <witness> { … }`** — introduce an existential for the goal. The
  boring prover deliberately refuses to *guess* witnesses, so the intro side
  is always explicit. Example boundary case:

```
2 | n  to prove  4 | n*n {
  choose q such that n = 2*q from (2 | n)
  n*n
    = (2*q) * (2*q)
    = 4 * (q*q)
  take q*q  ⊢  n*n = 4*(q*q)     -- divides-intro; witness made explicit
}
```

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

## 7. Logic mode: classical by default, constructivity as a scoped badge

- **Default everywhere: classical.** LEM, classical choice, and silent
  DNE / `¬¬`-elimination are all part of closure. A mathematician never
  writes an extra step to get `P` from `¬¬P`.
  - **`Classical.choose`** (value extraction from a `Prop`-existential) is
    available, which dissolves the `Prop`/`Type` large-elimination wall for
    `choose`-as-data. Cost to document once: such values are
    **noncomputable** — `choose` and `decide`/evaluation live in different
    worlds; a definition that reaches for choice cannot later be unfolded to
    compute.
- **Constructivity is a scoped, certifiable property**, not (only) a global
  switch. A `constructively { … }` block locally drops LEM, choice, and the
  `¬¬` rewrites, and **errors at the exact offending step** ("this step uses
  double-negation elimination, unavailable under `constructively`"). That
  turns a non-constructive proof into a precise, teachable diagnostic, and
  lets a result *advertise* that it was proved constructively — like a
  `noncomputable` badge in reverse — without bifurcating the library. A
  global `--constructive` build can sit on top of the same mechanism.
  - Inside `constructively`, `choose`-as-data is no longer free: the witness
    must be carried in a `Σ`/`Type`-level existential from the start. The
    `Prop`/`Type` leak reappears *honestly and locally*, exactly where it
    should be visible.

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

## 10. Residual leaks to keep contained (honest list)

CIC is not 100% hidden; these are where it is thinnest, each walled where
possible:

- **Dependent pattern-matching / dependent definitions** — §8; keep rare,
  behind interfaces.
- **Noncomputability of `Classical.choose`** — §7; document the
  choice-vs-compute boundary once.
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
- The destructor-registration mechanism for opaque predicates (so `choose
  … from <opaque prop>` is uniform).
- Depth/step budget defaults for the local-context search, and the exact
  shape of the "facts in scope were …" failure message.
- How `by <method>` generalizes: `by <lemma>`, `by induction on n`,
  `by cases on x`, `by well-founded on <measure>` all live in the same slot.

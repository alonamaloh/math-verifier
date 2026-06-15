# Plan: opaque by default — definitions never leak their internals

**Vision.** A definition's *body* is an implementation detail. Downstream
mathematics should depend only on a definition's **published interface** —
its operators, its characterising lemmas, its algebraic laws — never on how
it happens to be built. Today the opposite holds: **20 of 510** definitions
are `opaque`; the other 490 leak their bodies into kernel reduction, so
proofs all over the library silently depend on a chosen recursion or
encoding. The goal is to invert that ratio: **opaque by default**, with a
small, explicitly-foundational layer permitted to see through the boundary.

This is the data-layer sibling of `PLAN_LESS_CIC_STYLE.md` ("make CIC an
implementation detail"). That plan hides the *substrate*; this one hides each
*definition's internals*.

**The worked pilot — `Natural.successor` vs `1 + n`.** `Natural.add` is
opaque, so `1 + n` is not defeq to `successor(n)`; the bridge is the
`Natural.one_add` lemma. But `successor` still appears **3391** times outside
the core `Natural` modules, because the algebraic interface was incomplete
(no `<`) and the induction/recursion principles were stated in constructor
form. We have already, as the pilot: added `Natural.<`/`>` (defined as
`successor(a) ≤ b`, defeq to the form the core uses, so retrofits are safe),
restated `Natural.strong_induction`'s interface with `<`, and stabilised the
one budget-edge proof that tipped (`padic_valuation:574`). This plan
generalises that exemplar to the whole library.

## Core principle: the boundary is the characterising lemmas

For each definition `Foo`, publish a *complete* set of **characterising
lemmas** — equations/laws that pin down `Foo`'s behaviour in user-facing
vocabulary — then mark `Foo` opaque. Consumers reason through the lemmas
(or `by … unfolding Foo` at a designated boundary), never through automatic
unfolding. This is already the documented discipline (`docs/conventions/
opaque.md`); the work is to *apply it everywhere*, in dependency order.

## Two kinds of leak (they need different fixes)

1. **Definition-body leaks** — a proof relies on `Foo(args)` δ-reducing
   (e.g. `1 + n` collapsing to `successor n`). **Fixable**: opacity +
   characterising lemmas. This is the bulk of the win.
2. **Constructor leaks** — `| successor(k) =>` patterns (~249 outside core)
   and `case successor(…)` (~154) in *recursive definitions* and induction.
   The constructor is the eliminator's vocabulary; it **cannot be removed**,
   only **confined**: provide `1+`-form / `<`-form induction principles and
   fold/recursor combinators so user-space defines and inducts without
   naming the constructor, leaving it sealed inside the combinator's core
   definition.

## Phases

### Phase A — Complete the algebraic interface (per type)
For each carrier (`Natural` → `Integer` → `Rational` → `Real` → `Polynomial`
→ …, in dependency order):
- Every relation/operation the type is used with has a user-facing operator
  (the `<`/`>` gap was an instance — Natural lacked strict order entirely).
- Every recursive operation has its recurrence published as a
  characterising lemma in user vocabulary (`f(1 + n) = …`, not relying on
  `f(successor n)` reducing).
- Acceptance: the type's *interface* file mentions no constructor of the
  carrier in any theorem **statement**.

### Phase B — Confine constructors (induction & recursion)
- `1+`-form / `<`-form induction principles (`strong_induction` done; do
  ordinary induction and `cases`-style views, e.g. a `n = 0 ∨ ∃k. n = 1+k`
  view so case analysis yields `1 + k`, never `successor k`).
- Fold/recursor combinators for ℕ-indexed (and list-indexed, …) definitions,
  so `partialSum`, `power`, `factorial`, finite sums/products are defined via
  the combinator and expose only `1+`-form recurrence lemmas — moving their
  `case successor` into one core combinator.
- Acceptance: outside core, `| successor(` / `case successor(` drop toward
  zero; remaining ones live only in the combinator/core layer.

### Phase C — Opacity rollout
- Walk definitions in dependency order. For each: confirm characterising
  lemmas are complete and cited by all consumers, then flip to `opaque
  definition`. Fix fallout by citing lemmas / `by … unfolding` at the
  boundary (never re-exposing the body).
- Start where leaks bite hardest and dependencies are shallow (`Natural.add`
  is already opaque — extend to `multiply`, `monus`, `divide`, `power`,
  `padic_valuation`, then up the tower).
- Acceptance: opaque/transparent ratio inverts; a transparent definition
  outside the foundational layer becomes the exception, justified in a
  comment.

### Phase D — Ratchet against new leaks
- A leak report (model on `scripts/cic_leak_report` + the `LEAK_BUDGET`
  Makefile ratchet) counting: a carrier's constructor used outside its owning
  module's statements; a non-opaque definition outside the foundational
  allowlist; a consumer piercing opacity outside a boundary lemma.
- Wire a no-increase ratchet into `make check`, re-armed at the measured
  baseline, so the number only goes down.

## Cross-cutting: budget-edge robustness (a prerequisite, not optional)

Every opacity/abstraction change perturbs the auto-prover's candidate
search; by-less steps riding the 1.2M-step budget then tip (as
`padic_valuation:574` did the instant `Natural.<` entered the environment).
If this isn't addressed, **each phase triggers a wave of stabilisation
churn**. Options, roughly in order of leverage:
- Drive expensive by-less steps to explicit citations (the `--check-
  redundant-by` sweep already exists; make low-cost search the norm).
- A cheap, local, no-WHNF congruence/leaf tactic so common "shared subterm,
  difference is a context fact" steps close without search (the
  `structuralDiff` prototype from this session — flag-off, validated — is a
  start; pattern 2 works, pattern 1 deferred).
- Make the auto-prover's candidate ordering insensitive to environment
  additions (so a new definition can't change which candidate is tried
  first), removing the perturbation at the source.

## Sequencing & validation
- One carrier at a time, bottom of the dependency tower up; within a carrier,
  Phase A → B → C.
- `make -j 16 tests` green at the **default** budget after every step (the
  4×-budget pass only proves soundness, not that the proofs are cheap — the
  cache does not record the budget, so re-verify clean when in doubt).
- Each definition flipped to opaque is one reviewable commit with its
  characterising lemmas.

## Definition of done
- Opaque-by-default: transparent definitions outside the foundational layer
  are rare and annotated.
- No carrier constructor appears in a theorem *statement* outside its owning
  module; `successor`/`1+` interchange is invisible to users.
- The Phase-D ratchet is armed and green in `make check`.

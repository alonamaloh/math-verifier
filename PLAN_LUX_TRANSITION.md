# PLAN_LUX_TRANSITION.md — the unified plan to bring the library to Lux

This is the single forward plan for the language transition. It replaces a
cluster of overlapping documents that each described one facet of the same
move (`claim_language`, `LANGUAGE_VISION`, `PLAN_ELIMINATE_SUCCESSOR`,
`PLAN_OPAQUE_BY_DEFAULT`, `LEAK_REDUCTION_FINDINGS`, `MATHINESS_SWEEP`).
The destination language itself is specified separately in
[`LUX_PLAN.md`](LUX_PLAN.md); this document is **how the library gets
there**.

---

## 1. The thesis: one transition, not five

Several long-running initiatives have been tracked as if independent, each
threatening its own library-wide sweep:

- **sealing `successor`** inside the core `Natural` modules,
- **opaque-by-default** definitions (publish characterising lemmas, hide
  bodies),
- **removing CIC leaks** so proofs read and fail as mathematics,
- a **predictable auto-prover** (local context + explicit citations, no
  global lemma search),
- the **Lux** surface language (drop `:=`/`calc`/`claim`/`assume`, chains,
  `suppose`/`obtain`/`take`, induction-as-method, pattern-matching only in
  definitions).

They are **not** independent. Three of them are the *same* transformation
seen at different zoom levels:

- successor-elimination's keystone is "redefine `by_induction` to the
  `1 + n` form; every recursive definition publishes a characterising
  lemma `f(1 + k) = …` and goes opaque."
- opaque-by-default is exactly that move applied to *all* definitions, not
  just `successor` — successor-elimination was always its named pilot.
- Lux §6 (induction-as-method over a stated proposition) and Lux §8
  (definitions elaborate to **opaque** functions + characterising lemmas as
  registered rewrite rules) *are* that same boundary discipline, now at the
  surface.

So sweeping them one at a time re-touches the same proof bodies two or three
times — and the bodies that hurt are the analysis bulk (`Real/` 18k lines,
`ComplexNumber/` 11k; together ~40% of the 72k-line library). Each extra
touch re-derives the same characterising-lemma reasoning in a changing
syntax. **That repeated re-touching is the cost we are eliminating.**

The kernel is *not* changing (see [`PLAN_KERNEL.md`](PLAN_KERNEL.md):
non-cumulative, near-exact Lean-4 shape, encoding stable). Lux is "C to the
kernel's assembly" — every option desugars to the **identical** CIC terms.
Two consequences:

1. A from-scratch rewrite buys nothing on the foundation (same target) while
   discarding the library's role as the elaborator's test surface and
   risking re-introduction of *math* bugs in content that is already
   correct. Rejected.
2. The genuinely new content of the transition — characterising lemmas and
   minimal citation sets — is unavoidable under *any* strategy. The only
   lever we control is **how many times we touch the bulk.** Minimise that.

---

## 2. The destination

The end state, all at once, per file:

- **Surface = Lux** ([`LUX_PLAN.md`](LUX_PLAN.md)): uniform `{ … }` blocks,
  no `:=`; term-relation and `=>` chains replacing `calc`; `suppose` /
  `obtain` / `take`; induction and case-analysis as `by`-methods over a
  *stated* proposition; pattern-matching confined to definitions; classical
  logic with silent DNE; definite description only as `unique x such that …`.
- **Definitions opaque by default**, each publishing a complete set of
  characterising lemmas; a small foundational layer
  ([`docs/foundational-layer.md`](docs/foundational-layer.md)) may see
  through the boundary.
- **`successor` sealed** in core `Natural`; user space sees `0`, `1 + n`,
  `<`/`≤`, decidable zero-tests, and induction/recursion *principles*.
- **Cite-only prover**: the prover auto-searches the **local context** (the
  whole current module) and the built-in decision/normalisation tactics;
  global library lemmas enter only via `by L`. Every cited fact must be
  used (redundant citation = failed proof). This is Lux §1.

A consumer proof in the end state never spells `successor`, never names
`Quotient.*`/`unfold`/`congruenceOf`, never relies on a definition body
δ-reducing, and names its non-trivial global dependencies explicitly.

---

## 3. What already exists (the foundation we build on)

Much of the elaborator infrastructure is shipped and stays. Detailed
status lives in the docs noted; summary:

- **CIC-leak boundary (Phases 1–2 of the old less-CIC plan, done).** The
  elaborator is authoritative at the kernel boundary (no kernel-tagged
  error reaches the user across the 31-case corpus); `change`, defeq-aware
  `rewrite`, symmetry/congruence/bounded-combining diff bridges, and the
  WS8 malformed-term guards all landed. Measurement infra exists:
  `scripts/cic_leak_report` (`make leak-report`/`leak-ratchet`), the
  foundational-layer manifest, and the error-corpus audit (`make corpus`).
  See [`PLAN_LESS_CIC_STYLE.md`](PLAN_LESS_CIC_STYLE.md) (status +
  Appendix A elaborator-navigation notes). **Still open there:** WS3
  first-class quotient types and WS6 universe transparency — both folded
  into this plan (they are Lux constructs).
- **Auto-prover predictability (fingerprint plan, done).**
  `proveAbstractRingAC` is an exact AC decision procedure over abstract
  `Ring`/`CommutativeRing` carriers; the worst blind-search sites are gone;
  effort budget + expensive-step warning are armed. See
  [`PLAN_AUTOPROVER_FINGERPRINT.md`](PLAN_AUTOPROVER_FINGERPRINT.md). This is
  the engine half of Lux's "boring, predictable prover"; Lux adds the
  **local/cited scoping** on top.
- **Readability ergonomics (done).** Operators on parametrised/abstract
  carriers, `ring`/`field`/`linear_combination` over bundles, rewrite-under-
  binder, defeq-aware rewriting, and goal-shape lemma search (`kernel
  search` + in-error suggestions). See
  [`PLAN_READABILITY.md`](PLAN_READABILITY.md) (record + its §1 "experience
  of proving", worth reading cold).
- **successor pilot (done).** `Natural.<`/`>` and `Natural.strong_induction`
  restated with `<`; `PAdic/absolute_value.math` and `PAdic/negation.math`
  fully successor-free; the two zero-test mechanisms and helper lemmas
  proven. Mechanics in memory `successor_elimination`.

These give us a strong starting elaborator. The transition is mostly
**surface + boundary discipline + one prover-scoping change**, not new
kernel power.

---

## 4. Strategy: baby library → iterate → translator → one sweep

Decided with the project owner (2026-06-15). Rationale: §1's cost model says
touch the bulk exactly once, after the design is proven; and Lux is **not**
design-complete — it benefits from iteration against real proofs before we
commit the bulk to it.

The shape:

```
Phase 0  Baby library: a small, deliberately representative set of files,
         rewritten end-to-end into the FULL final stack (Lux + opaque +
         successor-free + cite-only prover). Iterate the Lux design here.
Phase 1  Mechanical translator: script the syntactic churn (old → Lux).
Phase 2  One bottom-up sweep of the rest, directly to final form.
```

We keep the *old* model — "an isolated elaborator change plus a bounded
library cleanup, green throughout" — only for work that is genuinely
independent of the surface (e.g. remaining `PLAN_KERNEL.md` items). The
surface/opaque/successor cluster goes through Phases 0–2 as one transition.

We work on a long-lived branch; the surgery period is accepted. The old
library stays buildable on the old elaborator (its branch) as a **regression
oracle** for behaviour only the bulk exercises.

---

## 5. Phase 0 — the baby library (the proving ground)

A small set of files carved into a Lux build target, rewritten into the full
final stack, **chosen to exercise every complexity** — especially the
corners a small sample tends to miss (Lux §10's honest residual leaks, and
the recurring pain points below). This is where Lux's open design questions
(LUX_PLAN §11) get answered and where the cite-only prover is validated.

### 5.1 Selection criteria (cover each at least once)

| Complexity to exercise | Candidate file(s) | Why it must be in |
|---|---|---|
| Binary quotient lift (the 6-declaration worst case) | `Integer/addition.math` (+ `basics`) | WS3's stated hardest case; clearing it makes the ring laws follow |
| `1+n` induction + characterising lemma over a recursive def | one short Real series, e.g. `Real/harmonic_series` or `Real/triangular_series` | the **shared keystone**; the bulk's dominant pattern |
| Abstract-algebra tower (`Ring.carrier(s)`) | `Algebra/principal_ideal_domain.math` | the abstract-carrier prover path; cite-only behaviour over bundles |
| Dependent / indexed data (genuinely CIC-ish corner) | the `Set/finite` cardinals witnesses | Lux §10: a core omitting it would "prove" a design that breaks |
| Deeply-polymorphic quotient reasoning | a `Quotient.exact`-heavy site (e.g. `Rational/order_multiplication.math`) | universe-inference pain (WS6); the cite-only prover under polymorphism |
| Numeric/value-level successor leaks | `Rational/{enumerable,halve,reciprocal}.math` | the clean successor-removal target (categories 1–2) |

Keep the set ~10–15 files. Bottom-of-the-tower bias so dependencies are
shallow.

**Selected (2026-06-15)** — eight headliner files, carved as the `make baby`
target (verifies just these + their transitive deps, the fast Phase-0 loop):
`Integer/basics` + `Integer/addition` (binary quotient lift),
`Real/harmonic_series` (1+n induction + characterising lemma — the keystone
exemplar, and the spike named in the old successor plan),
`Algebra/principal_ideal_domain` (abstract `Ring.carrier`; the 956K-step
fingerprint worst case; the cite-only prover over bundles), `Set/finite`
(dependent cardinals), `Rational/order_multiplication` (polymorphic
`Quotient.exact` + heavy successor — the largest at 583 lines, the deliberate
hard case), and `Rational/{halve,reciprocal}` (small value-level successor
leaks). The list lives in the Makefile's `BABY_MATH_FILES`; grow it there if
a complexity turns out under-covered.

### 5.2 What must work end-to-end before leaving Phase 0

- The **keystone**: `by_induction` desugars to the `1 + n` form (step proves
  `P(1 + k)` from `IH : P(k)`), via a once-proved
  `Natural.induction_on_one_plus` inside `Natural` (bridging
  `successor(k) ↔ 1 + k` by `Natural.one_add`). No consumer proof spells
  `successor`. (This is an elaborator `*.cpp` change → re-verifies the whole
  library → must pass `make -j 16 tests`.)
- A recursive definition publishes its **characterising lemma**
  `f(1 + k) = f(k) ⊕ …` (proved by `unfold f` + `one_add`, no induction) and
  consumers reason through it. Confirm the opaque boundary holds.
- A **quotient** is formed and a **binary operation** defined with the Lux
  `well_defined by` form (WS3), with zero `Quotient.*` tokens outside the one
  definition file.
- The **cite-only prover** runs: a proof closes from local context + built-in
  tactics + explicit `by L`, with global auto-search off. **This is the
  riskiest single change** — it alters what proves automatically everywhere
  and kills shotgun citing. Validate the felt citation burden here, on ~15
  files, before committing the bulk. The failure message must surface
  in-scope facts + fingerprint-indexed "did you mean `by L`?" candidates
  (the discovery path that replaces global search).

### 5.3 The design questions Phase 0 must close (LUX_PLAN §11)

Concrete syntax for `cases`/`by_induction` case blocks; chain-continuation
and nested-block layout; the destructor-registration for `obtain` over
opaque predicates; local-context search depth/step budget; the
linear-arithmetic/order procedure's reach (ordered-field vs Presburger,
which carriers); and how `by <method>` generalises across
`by L` / `by induction on n` / `by cases on x` / `by well-founded on m`.
LANGUAGE_VISION's rule of thumb still governs: a sugar is not done until
several real proofs use it and the language *feels* right.

### 5.4 Phase-0 exit criterion

Every baby-library file verifies in the Lux build with: zero `successor`
outside core `Natural`; zero `Quotient.`/`unfold`/`congruenceOf` outside the
foundational layer; opaque definitions with complete characterising lemmas;
cite-only prover on. The design questions above are answered (record the
decisions back into `LUX_PLAN.md`). If the cite-only prover proves too
costly to author against, that is the moment to revisit — cheaply, on 15
files, not after the bulk.

---

## 6. Phase 1 — the mechanical translator

A large fraction of per-file churn is pure syntax mapping and is
scriptable. Prior campaign experience (the deleted `LEAK_REDUCTION_FINDINGS`
log) showed comment-aware rewriters work with the kernel as the safety net:
the `claim`-by-`calc` rewrite did 73→0 by script; argument-dropping and
positional→`calc` rewrites likewise. The lessons that transfer:

- **What scripts can do** (syntactic, kernel-checked): `calc` → term-relation
  / `=>` chains; `claim NAME : T by P` → statement / `as NAME`; `assume` →
  `suppose`; `:=`-bodies → `{ … }` blocks; numerals (`successor(0)`→`1`,
  etc.); `Exists.introduce`/`And.introduction` → `⟨…⟩`; redundant-`by` and
  redundant-arg drops. Track depth over `()[]{}⟨⟩`; handle nesting (a
  non-matching outer statement must still be scanned *inside*).
- **What scripts cannot do** (semantic, human): publishing characterising
  lemmas; choosing the minimal citation set under the cite-only prover;
  restructuring term-position helper applications; anything needing a term's
  *type* (e.g. premise hoisting). These are the genuine residue and are the
  same residue under any strategy.

Deliverable: a translator that absorbs the syntactic ~60–70% so the human
sweep in Phase 2 is only the semantic residue. The kernel re-checks every
rewrite, so a wrong transform fails to verify — the safety net is exact.

---

## 7. Phase 2 — the single bottom-up sweep

With the design settled and the translator in hand, rewrite the rest **once**,
into final form, bottom-up by dependency layer, `make -j 16 tests` green
after each coherent group, one reviewable commit per group:

1. **Integer / IntegerMod** — `Integer/{sign,cancellation,integral_domain,
   embedding,balanced_division}`, `IntegerMod/*`. Value-level successor leaks
   + numerals; first real use of the WS3 quotient forms.
2. **Rational** — `Rational/{enumerable,halve,reciprocal,
   order_multiplication,power,positive,basics,embedding}`, then
   `Rational/archimedean` + `PAdic/{cauchy_bounded,multiplication}`
   (reparameterise `Rational.absolute_value_le_succ_natural` to `1 + K`; it
   ripples here).
3. **Lists / Set** — `Lists/{range,length,map,distinct,pairing}`,
   `Set/finite*`. Mostly characterising lemmas (`length(1 + k) = …`, etc.).
4. **Polynomial** — degree/summation recursion → characterising lemmas.
5. **Real / ComplexNumber / GaussianInteger** — the induction-heavy bulk
   (`binomial_theorem`, `exponential*`, `trigonometric*`, `series`,
   `arithmetic_geometric_mean`, …); leans entirely on the keystone and the
   characterising lemmas published in layers 1–4. This is the 40% that gets
   touched exactly once.

`by_strong_induction` (already successor-free) remains the tool when a proof
recurses on an arbitrary smaller value rather than the predecessor.

### Ratchet against regression (after the sweep)
Re-arm the leak report at the new baseline and wire a no-increase ratchet
into `make check`: a carrier constructor outside its owning module's
statements, a non-opaque definition outside the foundational allowlist, or a
consumer piercing opacity outside a boundary lemma — the number only goes
down. (This was the old opaque-plan Phase D; it belongs at the end here.)

---

## 8. Merged-transition mechanics (shared internals)

These are the load-bearing details, preserved from the folded sub-plans.

### 8.1 The keystone (forces and enables the rest)
Redefining `by_induction` to `1 + n` means recursive definitions no longer
ι-reduce for free in the step (`sum(1 + k)` is stuck under opaque `add`). So
**every** successor-recursive definition (`sum`, `power`, `factorial`, list
`length`, polynomial `degree`, `IntegerMod` residues, …) must publish its
`f(1 + k) = …` characterising lemma. That obligation **is** opaque-by-default
arriving at the induction site — the bulk of the effort, demanded and enabled
by the one small `by_induction` change. No separate structural-induction
tactic: the raw eliminator stays a kernel primitive used only in a few
`Natural`-core sites (bootstrapping the principle; establishing add/multiply
reduction).

### 8.2 Branching on zero without a constructor split
Choose by data vs proof (full detail + helper-lemma locations in memory
`successor_elimination`):
- **Data** (result is a `Set`/`Type` value): `cases` on
  `Natural.decidable_is_zero(m)` (Type-valued, large-eliminates); reduce the
  `no` branch with `decidable_is_zero_no_of_ne`. Not for proofs (dependent
  witness).
- **Proof** (goal is a `Proposition`): `cases Natural.decides_equality(m)(0)`
  (the Prop-valued `m = 0 ∨ m ≠ 0`); `Or`-elim into a Prop goal substitutes
  no witness, so a calc from `at_rep(...)` still typechecks. Usually shorter.

`Natural.add` is opaque, so `1 + k` is **not** defeq to `successor(k)` (only
propositionally equal via `Natural.one_add`). The prover bridges them in calc
steps; defeq-sensitive spots (recursor ι, proof-term args) need the explicit
`one_add` bridge.

### 8.3 Opaque rollout discipline (Phase C of the old opaque plan)
Walk definitions bottom-up. For each: confirm characterising lemmas are
complete and cited by all consumers, then flip to `opaque definition`. Fix
fallout by citing lemmas / `by … unfolding` at the boundary — never by
re-exposing the body. Acceptance per type: the type's *interface* file
mentions no carrier constructor in any theorem **statement**. In Lux this is
automatic (§8: equational definitions elaborate to opaque + registered
equations), so under the Lux surface the opaque rollout and the surface
rewrite are *one* edit, not two — which is the whole point of merging.

### 8.4 The "binder accepts a pattern" principle
The unifying idea behind `take`/`suppose`/`obtain`/`cases`/`by_induction`
(from the retired LANGUAGE_VISION): every intro-and-destructure is "bind WITH
a pattern; the elaborator picks the eliminator from the type." Lux is the
matured expression of this; keep it as the test when designing any new
case-block syntax in Phase 0.

---

## 9. Risks & gates

- **Cite-only prover authoring cost** — the highest risk; gated by Phase 0
  (validate on ~15 files; the fingerprint suggester + in-scope failure
  message are the mitigations). If it bites, the fallback is a curated opt-in
  hint database (`by *`), never default global search.
- **Keystone re-verifies everything** — it is an elaborator change; always
  validate with a clean `make -j 16 tests`, not just `make library`.
- **Budget-edge churn** — opacity/abstraction perturbs the prover's candidate
  search; by-less steps riding the budget can tip. The fingerprint engine and
  the redundant-by sweep already exist to drive expensive by-less steps to
  explicit citations; do that as part of each file's rewrite.
- **Long-lived branch divergence** — accepted; keep the old library green as
  the oracle and rebase discipline tight.
- **Math reorganisation is out of scope** — this plan re-*expresses* content,
  it does not re-*organise* it. New math layers
  ([`PLAN_NULLSTELLENSATZ.md`](PLAN_NULLSTELLENSATZ.md),
  [`PLAN_CATEGORY_THEORY.md`](PLAN_CATEGORY_THEORY.md)) and diagnostic probes
  ([`STRESS_PROBES.md`](STRESS_PROBES.md)) are separate and should not ride
  the syntax sweep.

---

## 10. Document map (what this plan supersedes / what stays)

**Folded into this plan and deleted** (git history is the record):
`claim_language.md` (the 2026-05 v1 of Lux), `LANGUAGE_VISION.md` (the
binder-pattern vision, now in Lux + §8.4), `PLAN_ELIMINATE_SUCCESSOR.md` and
`PLAN_OPAQUE_BY_DEFAULT.md` (the two merged sub-streams, §5–§8),
`LEAK_REDUCTION_FINDINGS.md` (translator lessons, §6) and `MATHINESS_SWEEP.md`
(a completed-work ledger).

**Kept, single-purpose, referenced above:**
[`LUX_PLAN.md`](LUX_PLAN.md) (the language spec — the destination),
[`PLAN_LESS_CIC_STYLE.md`](PLAN_LESS_CIC_STYLE.md) and
[`PLAN_AUTOPROVER_FINGERPRINT.md`](PLAN_AUTOPROVER_FINGERPRINT.md) and
[`PLAN_READABILITY.md`](PLAN_READABILITY.md) (shipped-infrastructure
records), [`LANGUAGE.md`](LANGUAGE.md) (current idioms — the translation
source), and the genuinely separate concerns
([`PLAN_KERNEL.md`](PLAN_KERNEL.md),
[`PLAN_CATEGORY_THEORY.md`](PLAN_CATEGORY_THEORY.md),
[`PLAN_NULLSTELLENSATZ.md`](PLAN_NULLSTELLENSATZ.md),
[`STRESS_PROBES.md`](STRESS_PROBES.md),
[`SPEED_OPTIMIZATIONS.md`](SPEED_OPTIMIZATIONS.md),
[`HASH_USE_VS_LEAN.md`](HASH_USE_VS_LEAN.md), `TODO.md`).

Companion memory: `successor_elimination` (the two zero-test mechanisms,
helper-lemma locations, the opaque-`add` gotcha).

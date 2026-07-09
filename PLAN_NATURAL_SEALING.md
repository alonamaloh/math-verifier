# PLAN_NATURAL_SEALING.md — seal `Natural`, confine `successor`

`Natural` is the **last transparent primitive**. `Integer`, `Rational`,
`Real` are all already opaque, reasoned about only through a boundary API
(`opaque.md`); `Natural` is the outlier — a raw `inductive` whose
constructors (`zero`/`successor`) and auto-generated recursor leak into
~91 files outside `Natural/` (and most files inside it). This plan seals
`Natural` behind a characterising-lemma boundary the way `Real` was
sealed, so that only a handful of foundational `Natural/` modules speak
`successor`; everything else reasons through lemmas (`0`/`1`/`+`/`*`/`≤`,
induction-as-a-theorem).

**The linchpin is numeral desugaring.** Every numeral literal is a
`successor` chain today (`5 ≡ successor⁵(zero)`), so literals are the #1
source of `successor` in the library. Re-desugaring them to a compact
`successor`-free form (binary Horner, `2·n + b`) is both the largest
single reduction of `successor` uses AND the change that forces the
`norm_num`-style arithmetic tactic sealing needs anyway (post-seal, no
numeral arithmetic reduces by defeq regardless of encoding). So Stage 1
is literals + the decision procedure, landed together; the opaque wrap
sits on top.

**Why now:** completes the ℤ/ℚ/ℝ opacity pattern; kills the
`successor`-outside-`Natural` advisory class at the root; and the binary
representation lifts the `ring` unary-coefficient ceiling
(`O(Σ|coef|)` → `O(Σ log|coef|)`) as a by-product.

This file's **Status ledger is authoritative** — read and update it every
session, like `PLAN_LANGUAGE_IMPROVEMENT.md`.

---

## Status ledger

| Stage | Workstream | Status | Record |
|-------|------------|--------|--------|
| 0 | Audit: mechanism + ripple forensics | **not started** | Answer the four open questions below (seal mechanism; numeral/`decide`/`ring` behaviour under a sealed type; `by induction`/`cases` retargeting; the foundational-module inventory). Deliverable: this ledger's rows 1–5 turned from sketch into spec. |
| 1 | Binary literals + `norm_num` decision procedure | **not started** | Re-desugar numeric literals to binary Horner `2·n + b` over `0/1/2/+/*` (elaborator, `inference.cpp` numeral path); land the bit-recurrence lemma set + a `norm_num`-style tactic proving `=`/`≠`/`<`/`≤`/`+`/`*` on literals. Independently valuable (compact terms, ring-ceiling fix); de-risks the seal. **Lands before Stage 2.** **Mechanism undecided — see the Decision record below: GMP kernel extension vs. verified tactic.** |
| 2 | The sealed boundary (opaque wrap + characterising lemmas) | **not started** | `opaque definition Natural := Natural.Raw`; re-expose `zero`/`successor`, an `induction` theorem, and a primitive-`recursion` combinator as the ONLY boundary; complete the Peano set. Mechanism decision in §Mechanism. |
| 3 | Tactics speak the boundary | **not started** | `by induction` / `cases` on `Natural` emit the `induction`/`recursion` theorems, not the raw recursor; `decide`/numeral equality route through the Stage-1 tactic. Elaborator change. |
| 4 | Consumer migration | **not started** | Wean the ~91 external + interior `Natural/` files off `successor`, advisory-driven (the `successor`-outside-`Natural` signal is the worklist). A1-style sweep; gradual. |
| 5 | Flip the seal | **not started** | Mark the type opaque; fix fallout; reduce the `successor`-using set to the documented handful. |

**Overall:** design only. Nothing landed. Stage 1 is the recommended first
executable step; Stage 0 audit precedes it.

---

## Mechanism — sealing a primitive inductive (not a quotient)

`Real`/`Integer`/`Rational` were sealable cleanly because they are
**derived** types: `opaque definition Real := Quotient(...)`. `Natural`
is a **primitive `inductive`**, and CIC hands you the recursor (plus
pattern-matching and large elimination) automatically for any inductive.
So "seal it like `Real`" concretely means the **wrap**, mirroring how
`Integer`/`Rational` are opaque aliases over a raw representation
(`opaque_integer_boundary`, `rational_opaque_field_of_fractions`):

1. Keep the raw inductive in one foundational module, renamed out of the
   public namespace — `inductive Natural.Raw where | zero | successor`.
2. `opaque definition Natural := Natural.Raw`. The opaque head stops the
   kernel δ-unfolding to `Natural.Raw`, so consumers can't pattern-match
   or invoke the raw recursor through it (hard opacity — `opaque.md`).
3. Re-expose the boundary through opaque-aliased wrappers + theorems:
   - `Natural.zero`, `Natural.successor` (opaque-aliased constructors),
   - `Natural.induction` — the eliminator into `Proposition`, as a
     **theorem** (proved once under `unfold Natural`),
   - `Natural.recursion` — a primitive-recursion combinator into `Type`,
     also proved once under `unfold` (this is what `definition … | 0 => …
     | 1+k => …` desugars to for consumers),
   - the Peano characterising lemmas (mostly exist — see Inventory).

The **alternative** (module-discipline-only: keep the raw inductive
public but lint against importing it) is weaker — it's a convention, not
kernel-enforced, and the recursor stays reachable. Rejected unless Stage-0
audit finds the wrap infeasible (e.g. numeral literals can't be rebuilt
over the opaque alias cheaply).

**Open sub-question (Stage 0):** does `opaque definition Natural :=
Natural.Raw` let numeral literals and the Stage-1 binary desugar still
typecheck at type `Natural` without piercing the alias at every literal?
The `Integer`/`Rational` boundary already threads constructors through an
opaque alias (`difference_equal`/`fraction` boundary), so the pattern is
proven; confirm it holds for the numeral hot path.

---

## Stage 1 detail — binary literals + the decision procedure

### Desugar target

A literal `n` desugars to binary Horner over the exposed boundary
vocabulary: `n = 2·q + b`, `b ∈ {0, 1}`, recursively, bottoming at `0`/`1`.
E.g. `13 = 2·(2·(2·1 + 1) + 0) + 1`. Properties:

- **Size `O(log n)`** node count (vs unary `O(n)`).
- **`successor`-free** — built from `0`/`1`/`2`/`+`/`*` only.
- **Ring-native** — a literal is already a `+`/`*` expression the ring
  normaliser speaks; treat it as an atomic coefficient, not something to
  expand (see ring note below).

Rejected alternatives: **decimal Horner** (`10·d + …`) buys nothing over
binary — the pretty-printer already renders any internal encoding back to
decimal digits, so decimal-internal only makes the decision procedure
carry base-10 digits/carries for no gain. **Sum-of-ones** (`1+1+…`) fixes
the vocabulary but keeps `O(n)` size — strictly dominated by binary,
useful only as a smaller-diff fallback if binary proves too invasive.

### The `norm_num`-style decision procedure

Post-seal (and even under today's opaque `Natural.add`), literal
arithmetic does **not** reduce by defeq — it must be *proved*. Keyed to
the binary encoding, a tactic builds `O(log n)` proofs from bit-recurrence
lemmas. Lemma set to establish (Coq `N`/`positive` arithmetic, adapted to
`2·n + b` form):

- **Normalisation:** `double(n) = 2·n`, `bit0(n) = 2·n`, `bit1(n) = 2·n + 1`;
  a `no-leading-zero` well-formedness fact so each literal has a unique
  binary form (needed for `≠`).
- **Addition** (`L + M = N`): the four bit-carry recurrences
  `2a + 2b = 2(a+b)`, `2a + (2b+1) = 2(a+b)+1`,
  `(2a+1) + (2b+1) = 2(a+b+1)`, plus base cases with `0`/`1`.
- **Multiplication** (`L · M = N`): `2a · m = 2(a·m)`,
  `(2a+1)·m = 2(a·m) + m`; recurse on one factor's bits.
- **Order** (`L ≤ M`, `L < M`): bitwise comparison recurrences
  (`2a ≤ 2b ↔ a ≤ b`, `2a+1 ≤ 2b ↔ a < b`, …).
- **Equality / disequality** (`L = M`, `L ≠ M`): structural on the unique
  binary form (uses the no-leading-zero fact for `≠`).

The tactic dispatches on the outer bit constructors of its literal
operands and cites the matching recurrence, recursing — the proof depth
tracks the bit length. This is the tactic `arithmetic_decision_tactic_idea`
already wants; sealing forces it, and binary makes it tractable.

### Decision record — Stage-1 mechanism: GMP kernel extension vs. verified `norm_num`

**Status: OPEN — needs owner sign-off (it's a trusted-computing-base
call).** The rest of this section assumes Option B (verified tactic); this
record captures the fork so we choose it on purpose rather than by inertia.

**The question.** Literal arithmetic must stop being unary. There are two
mechanisms, and they differ in *what the kernel trusts*, not just in speed.

**Option A — GMP literal kernel extension (Lean 4's approach).** Add a
big-integer literal node to `Expr` (small values unboxed as machine words,
large ones boxed GMP `mpz`) and give the kernel *native* reduction rules for
a fixed set of `Natural` ops (`add`/`sub`/`multiply`/`compare`/`decEq`/…):
when both operands reduce to literals, the kernel computes the result with
GMP directly instead of unfolding the recursor. The `zero`/`successor`
inductive stays as the logical definition — the literal is *defeq* to its
unary form — and the kernel special-cases `Natural.rec`/pattern-match on a
literal to expose `successor(n-1)` on demand, so induction still works.

- *Pros:* fastest possible (native C++ arithmetic, no proof term to check);
  fully resolves the `ring` unary-coefficient ceiling
  (`ring_unary_coefficient_ceiling`); a well-trodden design (Lean 4 ships
  exactly this).
- *Cons:* **grows the TCB** — you now trust that GMP `add` really computes
  `Natural.add`, plus the literal↔`successor` recursor bridge (the fiddly,
  trust-sensitive part). This cuts directly against this project's stated
  value: *the kernel does the typechecking*, small trusted core.

**Option B — verified `norm_num` over binary-Horner literals (this plan's
current default).** Represent literals as `2·n + b` object-language terms
(§Desugar target) and prove each arithmetic fact with an `O(log n)`-depth
*checkable proof term* built from the bit-recurrence lemmas (§the decision
procedure). The kernel learns nothing new; it just checks the proof.

- *Pros:* **kernel stays small** — no new trusted arithmetic; every literal
  fact is a proof the existing kernel verifies (de Bruijn criterion).
  Compact `O(log n)` terms; ring-ceiling fixed if `ring` treats a binary
  literal as an atomic coefficient.
- *Cons:* slower (the kernel re-checks an `O(log n)` proof per fact rather
  than trusting one GMP op); the tactic + lemma set is real work to build
  and maintain.

**The axis** is the classic de Bruijn tradeoff: *fast kernel extension* vs.
*small kernel + verified tactic*. Speed and TCB size trade against each
other; both beat unary decisively.

**What each does and does NOT buy (don't over-attribute):**

- Both fix the **unary performance** blowup and both remove `successor` from
  **numerals** (the #1 `successor` source — this plan's linchpin).
- **Neither fixes the variable-`successor` asymmetry** that motivated this
  plan's ergonomics (`1 + i` not defeq `successor i`, the binomial
  restatement wart). That is about which argument `Natural.add` recurses on,
  not about literal representation — Lean has the identical asymmetry
  (`i + 1` reduces, `1 + i` does not) and its users bridge it with lemmas
  too. It is **Stage 3** (retarget `by induction`/`cases` to the `1 + n`
  principle), independent of the Stage-1 mechanism.
- **Option A is orthogonal to sealing.** Lean's `Nat` is deliberately
  *unsealed* — fully pattern-matchable — and still gets native numerals. So
  Option A delivers the performance + numeral-`successor` half **without
  requiring the opacity project at all**. It does *not* deliver
  encapsulation (goal A of the plan): anyone can still `match` on
  `successor`. If the driver is "read like a mathematician, no raw CIC
  leaks," Option A alone is insufficient; if the driver is performance and
  compact numerals, Option A may let us skip Stages 2/5 entirely for that
  benefit.

**Provisional lean (not a decision):** Option B fits the project's
small-kernel philosophy and is what the Stage-1 detail is written against.
Option A is the faster, more thorough performance fix and is independently
adoptable, but it is a TCB-growth decision that must be made explicitly by
the owner. Resolve this in the Stage-0 audit, before writing Stage-1 code.

### `ring` interaction (the by-product win)

`ring` holds coefficients in **unary** today (`ring_unary_coefficient_ceiling`):
proof size `O(Σ|coef|)`, the scalability ceiling behind field-clearing
OOMs. A binary literal/coefficient representation turns that into
`O(Σ log|coef|)`. Stage 1 should either (a) make `ring`'s coefficient
arithmetic call the binary decision procedure, or (b) at minimum ensure
`ring` treats a binary literal as an atomic coefficient (does not expand
its Horner form into the polynomial). Decide in Stage 0.

---

## Inventory — what already exists (don't re-derive)

- `inductive Natural` + `zero`/`successor`/`one`/`two` — `Natural/basics.math`.
- `Natural.add` is **already `opaque definition`** (registered reduction
  equations); `Natural.multiply` is still transparent.
- **Peano boundary** (`Natural/peano.math`): `successor_injective`,
  `successor_not_zero`, `zero_not_successor`, `zero_or_successor`,
  `predecessor`. (Gaps: a clean `n+1` induction/recursion pairing — only
  `1+n` exists; see below.)
- **Induction-as-a-theorem**: `Natural.induction_on_one_plus`
  (`Natural/one_plus_induction.math`, `1+n` form, `case base`/`case step`);
  `Natural.strong_induction`, `Natural.for_all_below`
  (`Natural/strong_recursion.math`).
- **Asymmetry to fix** (`one_plus_vs_plus_one_asymmetry`): only a `1+n`
  induction principle exists; `one_add` is automatic but `add_one` is not.
  The boundary should publish BOTH `1+n` and `n+1` induction/recursion so
  consumers pick the natural one, and mark `add_one` automatic.
- Numerals desugar to `successor` chains — `src/elaborator/inference.cpp`
  (the `SurfaceNumericLiteral` path, ~L2535). **This is what Stage 1 changes.**
- Scale: **421** files import `Natural.basics`; **91** files outside
  `Natural/` mention `successor(`.
- Related notes: `ring_unary_coefficient_ceiling`, `arithmetic_decision_tactic_idea`,
  `successor_elimination` (reframed: confine, don't delete), `opaque.md`
  (the sealing discipline + failure modes).

---

## Open questions (Stage 0 audit answers these)

1. **Seal mechanism** — does the `opaque definition Natural := Natural.Raw`
   wrap hold on the numeral hot path (literals typecheck at `Natural`
   without per-literal alias-piercing)? Confirm against the
   `Integer`/`Rational` opaque-alias precedent.
2. **`decide` / defeq arithmetic** — inventory every proof that relies on
   `Natural` computing (`decide`, defeq `2+3=5`, numeral comparisons); these
   become the Stage-1 tactic's acceptance set. How does `decide.math`
   currently prove numeral props, and what breaks under sealing?
3. **`by induction` / `cases` retargeting** — can the elaborator emit the
   `induction`/`recursion` theorems in place of the raw recursor
   transparently, so existing `by induction { case zero … case successor … }`
   proofs keep working against the boundary? What's the surface impact?
4. **The foundational handful** — which `Natural/` modules legitimately
   stay `successor`-using (the raw floor: `basics`, `peano`,
   `one_plus_induction`, `strong_recursion`, `monus`, `compare`, `order`,
   `decide` …)? Draw the line; everything above it migrates in Stage 4.
5. **Stage-1 mechanism** — resolve the GMP-kernel-extension vs.
   verified-`norm_num` fork (see the Decision record in §Stage 1 detail).
   TCB-growth call; owner sign-off. Note Option A is adoptable independently
   of sealing (it buys performance + numeral-`successor` without opacity), so
   this answer also reframes whether Stages 2/5 are on the critical path for
   the performance goal or only for encapsulation.

---

## Sequencing vs. the CIC-leak sweep

Independent tracks. The CIC-leak (direct-proof-lemma-call) sweep is
mechanical and low-risk; keep it running to completion — but in swept
files prefer lemma-based `Natural` reasoning over `successor` where it's a
free win, so the sweep stops *adding* debt. This sealing project is the
foundational track; **Stage 1 (binary literals + `norm_num`) is the
recommended first executable step** — it's independently valuable and
de-risks everything above it — with the Stage-0 audit immediately before.

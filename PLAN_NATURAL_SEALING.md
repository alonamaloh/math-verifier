# PLAN_NATURAL_SEALING.md — seal `Natural`, confine `successor`

`Natural` is the **last transparent primitive**. `Integer`, `Rational`,
`Real` are all already opaque, reasoned about only through a boundary API
(`opaque.md`); `Natural` is the outlier — a raw `inductive` whose
constructors (`zero`/`successor`) and auto-generated recursor leak into
consumer files (46 outside `Natural/` today, plus most of `Natural/`
itself). This plan seals `Natural` behind a characterising-lemma boundary
the way `Real` was sealed, so that only a documented foundational handful
of `Natural/` modules speak `successor`; everything else reasons through
lemmas (`0`/`1`/`+`/`*`/`≤`, induction-as-a-theorem).

**Why:** completes the ℤ/ℚ/ℝ opacity pattern and kills the
`successor`-outside-`Natural` advisory class at the root. This is now a
**pure encapsulation/readability project** — the performance and numeral
motivations this plan originally carried were delivered separately (see
the history note below).

This file's **Status ledger is authoritative** — read and update it every
session, like `PLAN_LANGUAGE_IMPROVEMENT.md`.

---

## History note (2026-07-10 refresh) — what changed since this plan was written

The original plan's linchpin was "Stage 1: binary-Horner literals + a
verified `norm_num` tactic", gated on an open TCB decision (GMP kernel
extension vs. verified tactic). That fork was **resolved by the owner as
the GMP kernel extension and fully landed via PLAN_FAST_NUMERALS**
(Stages 0–4, 2026-07-10):

- Numeric literals are GMP `NaturalLiteral` kernel nodes — **`O(1)`,
  `successor`-free**; the one-peel constructor view keeps induction and
  pattern-matching working over literals.
- Ground relations (`=`/`≠`/`<`/`≤` on literals) decide silently through
  the certificate tier; `ring`/`field` coefficients are mpz literals
  (the unary-coefficient ceiling is dead).
- The accelerated op table was subsequently **aligned with Lean's kernel
  and trimmed to 6 ops** (PLAN_KERNEL_EXPORT Stage 1: `add, multiply,
  monus, power, floor_divide, modulo`, Lean's `(dividend, divisor)`
  conventions, pow cap 2²⁴).

Consequences for this plan:

- The old Stage 1 (binary literals + `norm_num`) is **subsumed — deleted
  from the ledger**. Literals are already the #1-source-of-`successor`
  fix, and no decision procedure needs building.
- The old "Decision record" is **closed** (Option A, landed). The `ring`
  unary-ceiling by-product is likewise already delivered.
- What remains is exactly the **encapsulation half**: the opaque wrap,
  tactics speaking the boundary, consumer migration, and the flip.
- PLAN_KERNEL_EXPORT (all stages DONE) adds a new standing constraint:
  the full library replays through an external Lean-kernel checker
  (`make export-check`), and the exporter's name maps assume `Natural`
  is the raw two-constructor inductive. The seal must keep that gate
  green (audit question 2).

---

## Status ledger

| Stage | Workstream | Status | Record |
|-------|------------|--------|--------|
| 0 | Audit: mechanism + ripple forensics | **not started** | Answer the open questions below (seal mechanism on the literal hot path; kernel-literal machinery under the wrap; export-trail mapping under the wrap; `by induction`/`cases` retargeting; the foundational-module inventory; the defeq-arithmetic acceptance set). Deliverable: rows 1–4 turned from sketch into spec. |
| 1 | The sealed boundary (opaque wrap + characterising lemmas) | **not started** | `inductive Natural.Raw`; `opaque definition Natural := Natural.Raw`; re-expose `zero`/`successor`, BOTH `1+n` and `n+1` induction theorems, and a primitive-`recursion` combinator as the ONLY boundary; complete the Peano set. Mechanism in §Mechanism. |
| 2 | Tactics speak the boundary | **not started** | `by induction` / `cases` on `Natural` emit the boundary `induction`/`recursion` theorems, not the raw recursor; numeral facts keep routing through the kernel-literal table / ground-relation tier. Elaborator change. |
| 3 | Consumer migration | **not started** | Wean the 46 external + ~33 interior `Natural/` files off `successor`, advisory-driven (the `successor`-outside-`Natural` signal is the worklist). A1-style sweep; gradual. |
| 4 | Flip the seal | **not started** | Mark the type opaque; fix fallout; reduce the `successor`-using set to the documented raw floor. Acceptance: full `make -j 16 library tests error-tests` **and `make export-check`** green. |

**Overall:** design refreshed 2026-07-10; nothing landed. Stage 0 is the
next executable step.

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
   - **both** induction principles as theorems — the existing
     `Natural.induction_on_one_plus` (`1+n`) plus an `n+1` twin, so
     consumers pick the natural one
     (`one_plus_vs_plus_one_asymmetry`; mark `add_one` automatic),
   - `Natural.recursion` — a primitive-recursion combinator into `Type`,
     proved once under `unfold Natural` (what `definition … | 0 => … |
     1+k => …` desugars to for consumers),
   - the Peano characterising lemmas (mostly exist — see Inventory).

The **alternative** (module-discipline-only: keep the raw inductive
public but lint against importing it) is weaker — it's a convention, not
kernel-enforced, and the recursor stays reachable. Rejected unless the
Stage-0 audit finds the wrap infeasible on the kernel-literal hot path.

---

## Open questions (Stage 0 audit answers these)

1. **Seal mechanism on the literal hot path.** The GMP kernel-literal
   machinery is name-keyed to `Natural`: `NaturalLiteral` nodes infer
   type `Natural`, the one-peel constructor view produces
   `zero`/`successor(literal)`, `successor`-compaction re-forms
   literals, and the 6-op accelerated table keys on `Natural.add` etc.
   Under `opaque definition Natural := Natural.Raw`, which of these
   re-point to `Natural.Raw`, which stay on the alias, and does a
   literal still typecheck at `Natural` without piercing the alias?
   (The kernel's library-name coupling is exactly `zero`/`successor` +
   the 6-op table + `Quotient.lift`/`class_of` — this question is that
   list under renaming.)
2. **The export trail under the wrap.** `kernel export-lean4` maps
   `Natural` → `Nat` as the raw two-constructor inductive, and nanoda's
   Nat acceleration requires the builtin `Nat` to BE that inductive.
   Post-seal the natural mapping is `Natural.Raw` → `Nat` with
   `Natural` exporting as a transparent definition over it (the
   exporter already strips opacity), and the accelerated ops — defined
   at the sealed alias — must still export under `Nat.*` names with
   checker-replayable semantics. Confirm, and add `make export-check`
   to the flip's acceptance gate.
3. **Defeq-arithmetic acceptance set.** Inventory the proofs that rely
   on `Natural` computing by defeq beyond the literal table (`decide`
   uses, `cases`-on-expression over `Natural`, defeq `2+3=5` in
   ascriptions). Under the seal, defeq computation happens only through
   the table's literal path and the boundary lemmas — what breaks, and
   is the ground-relation certificate tier already the answer for all
   of it?
4. **`by induction` / `cases` retargeting.** Can the elaborator emit
   the boundary `induction`/`recursion` theorems in place of the raw
   recursor transparently, so existing `by induction { case base … case
   step … }` proofs keep working? What is the surface impact on the
   legacy `case zero` / `case successor(k)` spellings, and does
   `buildCaseLambda`'s recursor path need a boundary-theorem twin?
5. **The foundational handful.** Which `Natural/` modules legitimately
   stay `successor`-using (the raw floor: `basics`, `peano`,
   `one_plus_induction`, `strong_recursion`, `monus`, `compare`,
   `order`, `decide`, …)? Draw the line; everything above it migrates
   in Stage 3. (~33 `Natural/` files mention `successor(` today.)

---

## Inventory — what already exists (don't re-derive)

- `inductive Natural` + `zero`/`successor`/`one`/`two` —
  `Natural/basics.math`. `Natural.add` is **already `opaque
  definition`** (registered reduction equations); `Natural.multiply` is
  still transparent.
- **Numerals are already sealed in spirit**: literals are GMP kernel
  nodes (`successor`-free, `O(1)`); ground `=`/`≠`/`<`/`≤` decide via
  the certificate tier; `ring`/`field` coefficients are mpz. Nothing in
  this plan touches numeral representation.
- **Peano boundary** (`Natural/peano.math`): `successor_injective`,
  `successor_not_zero`, `zero_not_successor`, `zero_or_successor`,
  `predecessor`.
- **Induction-as-a-theorem**: `Natural.induction_on_one_plus`
  (`Natural/one_plus_induction.math`, `1+n` form, `case base`/`case
  step`); `Natural.strong_induction`, `Natural.for_all_below`
  (`Natural/strong_recursion.math`). Gap: the `n+1` twin
  (`one_plus_vs_plus_one_asymmetry`).
- **Kernel coupling to align** (audit Q1): the literal node type, the
  one-peel view, `successor`-compaction, the 6-op table
  (`evaluateAcceleratedNaturalOp`), and the numeral-table self-check
  (`MATH_CHECK_NUMERAL_TABLE`).
- Scale (re-measured 2026-07-10): **214** files import `Natural.basics`;
  **46** files outside `Natural/` mention `successor(` (was 91 when
  first drafted — the CIC-leak sweeps have been paying this down);
  **~33** files inside `Natural/` do.
- Related notes: `successor_elimination` (reframed: confine, don't
  delete), `one_plus_vs_plus_one_asymmetry`, `opaque.md` (the sealing
  discipline + failure modes), `kernel-export-plan` (the external-check
  gate this must keep green).

---

## Sequencing

- The CIC-leak / clean-cone sweeps are independent, mechanical tracks;
  keep them running — in swept files prefer lemma-based `Natural`
  reasoning over `successor` where it's a free win, so the sweeps keep
  *reducing* Stage-3's worklist (they already have: 91 → 46).
- PLAN_KERNEL_EXPORT is complete and orthogonal (exports are
  transparent), but its `make export-check` gate becomes part of this
  plan's acceptance from Stage 1 on — run it after every stage that
  touches `Natural/` or the kernel.
- **Stage 0 (the audit) is the next executable step**; it is a
  read-and-prototype session, no library changes.

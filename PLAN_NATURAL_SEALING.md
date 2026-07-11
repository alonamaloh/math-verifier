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
| 0 | Audit: mechanism + ripple forensics | **DONE 2026-07-10** | All five questions answered empirically — see §Stage-0 audit findings. Prototype (wrap + boundary probes, kernel re-point) lives on branch `scratch/natural-seal-stage0-probe` (3c65a529); the opaque-endpoint mechanics are validated end-to-end in `Natural/peano.math` there. |
| 1 | The sealed boundary (wrap + wrappers + characterising lemmas + kernel/exporter re-point) | **not started** | Spec in §Mechanism (validated). Land with a **transparent** alias first (`definition Natural := Natural.Raw`) so the whole library keeps building; the opacity keyword is Stage 4's flip. Includes: qualified wrappers `Natural.zero`/`Natural.successor`; two-layer ops (`Natural.Raw.<op>` pattern-def + alias wrapper, per-op opacity as today); the 2-gate kernel re-point; the 1-entry exporter map swap; self-check `transparencyNames` gains the `Natural.Raw.*` twins; the `n+1` induction twin + `Natural.recursion` combinator; Peano set restated via wrapper. Gate: library+tests+error-tests **and `make export-check`** green. Risk to test first: elaborator carrier keys that WHNF a type before reading its head would see `Natural.Raw` under the transparent alias (headConstantName-carrier gotcha) — audit which of ring/calc/ground-relations/dispatch keys normalize, and key both names during the transition if needed. |
| 2 | Tactics speak the boundary | **not started** | `case base:`/`case step(k):` already routes through `<Carrier>.induction_on_one_plus` and works at the sealed alias UNCHANGED (probe-validated). What must be built: (a) the modern `case n = 0` / `case n = k + 1` spellings parse to constructor patterns and take the RAW-recursor path (probe: fails at seal with "type 'Natural' is not an inductive", cases.cpp:1167) — retarget them, plus plain `cases n`, onto boundary theorems via an opaque-INDUCTIVE-alias probe (sibling of `engageOpaqueQuotientAlias`, cases.cpp:1101); `cases` needs a new `Natural.cases_on_one_plus`-style boundary theorem (only the induction one exists) and a boundary-layout twin of `buildCaseLambda` (or hand-assembly mirroring `elaborateByInductionOnePlus`, induction.cpp:1056-1081); (b) pattern-match definitions at the alias (`\| 0 => \| 1+k =>`, patterns.cpp:9) compile onto `Natural.recursion` incl. structural-recursion rewriting — the hardest piece; (c) the parse-time numeral-pattern desugar (parser.cpp:2725-2748, 4075-4089) emits bare `zero`/`successor` tokens that post-seal only match Raw scrutinees. |
| 3 | Consumer migration | **not started** | Classes + counts (measured 2026-07-10): 46 external files spell `successor(` (fail at the opaque flip: raw constructor at alias-typed args — clean error, probe-validated); 31 external files destructure Natural in pattern arms (proof `cases` → Stage-2 retarget; recursive defs — monoid/ring power, List.range, Polynomial padding, series partial sums, aggregation — → `Natural.recursion`); 6 external files use `case n = 0` spellings (Stage-2 retarget covers). External `decide(` uses: **zero**. Interior `Natural/`: 33 files, tiered in §findings Q5. Advisory-driven, gradual; the transparent-alias waypoint keeps everything green throughout. |
| 4 | Flip the seal | **not started** | One-keyword flip `definition` → `opaque definition` on the alias + fix stragglers; raw floor reduced to the documented set (§findings Q5). Acceptance: full `make -j 16 library tests error-tests`, `make check`, **and `make export-check`** green. |

**Overall:** Stage 0 done 2026-07-10 (this session); rows 1–4 are now
spec, not sketch. Stage 1 is the next executable step.

---

## Mechanism — sealing a primitive inductive (not a quotient)

`Real`/`Integer`/`Rational` were sealable cleanly because they are
**derived** types: `opaque definition Real := Quotient(...)`. `Natural`
is a **primitive `inductive`**, and CIC hands you the recursor (plus
pattern-matching and large elimination) automatically for any inductive.
So "seal it like `Real`" concretely means the **wrap**, mirroring how
`Integer`/`Rational` are opaque aliases over a raw representation
(`opaque_integer_boundary`, `rational_opaque_field_of_fractions`):

The spec below was **validated end-to-end by the Stage-0 prototype**
(branch `scratch/natural-seal-stage0-probe`, 3c65a529 — `basics.math` +
`peano.math` there are the worked example):

1. Keep the raw inductive in one foundational module, renamed out of the
   public namespace — `inductive Natural.Raw : Type(0) where | zero :
   Natural.Raw | successor : Natural.Raw → Natural.Raw`. The
   constructors **keep their bare global names** `zero`/`successor`
   (only their `inductiveName` changes): this leaves ALL of the kernel's
   bare-name literal machinery (one-peel view, compaction, defeq bridge,
   ground-spelling reader) and the exporter's `zero → Nat.zero` /
   `successor → Nat.succ` entries untouched, and it means post-flip the
   46 external `successor(` files fail loudly (raw constructor at
   alias-typed arguments) — the confinement the plan exists for.
2. `opaque definition Natural : Type(0) := Natural.Raw`. Hard opacity
   stops δ-unfolding, so consumers can't pattern-match or invoke the raw
   recursor through the alias (probe: "'Natural' is not an inductive
   type"). **Sequencing:** Stage 1 lands this line *transparent*
   (`definition`), so the library keeps building while consumers
   migrate; Stage 4 adds the keyword.
3. Re-expose the boundary at the alias:
   - `definition Natural.zero : Natural := unfold Natural in zero` and
     `definition Natural.successor : Natural → Natural := unfold Natural
     in successor` — **transparent** wrappers (they must δ-reduce onto
     the raw constructors so kernel defeq/compaction fire through them;
     an opaque wrapper would split `Natural.successor(x)` from
     `successor(x)`),
   - two-layer operations: `definition Natural.Raw.<op> : Natural.Raw →
     Natural.Raw → Natural.Raw | zero, … => …` (constructor-spelled
     bodies — a numeral body types at the ALIAS and cannot sit in a Raw
     position; numeral *patterns* are fine, they desugar at parse time)
     plus `opaque definition Natural.<op> : Natural → Natural → Natural
     := unfold Natural in Natural.Raw.<op>` (per-op opacity as today:
     `add` opaque, `multiply` transparent). The 6-op table keys on the
     wrapper names (`Natural.add`, …) and keeps firing — probe: `2 + 3 =
     5 := reflexivity(5)` green at the sealed alias,
   - **both** induction principles as theorems — the existing
     `Natural.induction_on_one_plus` (statement already all-alias; its
     raw-recursor proof survives verbatim wrapped in `unfold Natural in`,
     probe-validated) plus an `n+1` twin
     (`one_plus_vs_plus_one_asymmetry`; mark `add_one` automatic),
   - `Natural.recursion` — a primitive-recursion combinator into `Type`,
     proved once under `unfold Natural` (what `definition … | 0 => … |
     1+k => …` desugars to for consumers), plus a
     `Natural.cases_on_one_plus` case-analysis theorem for `cases`
     (Stage 2 needs it; only the induction theorem exists today),
   - the Peano characterising lemmas restated at the alias via
     `Natural.successor` (raw-floor spelling stays possible for the
     all-Raw halves; the alias-level halves are proved under
     `unfold Natural in` — both validated in the probe `peano.math`).
4. Kernel re-point — exactly **two gates**, nothing else:
   `isNaturalConstructor`'s `inductiveName == "Natural"` (kernel.cpp
   ~1120) and the recursor literal-view gate (kernel.cpp ~1343) become
   `"Natural.Raw"`. Literal typing (`makeConstant("Natural")`,
   kernel.cpp ~2402) **stays on the alias** — literals live at `Natural`
   everywhere; inside the raw floor they meet Raw-typed terms only under
   `unfold Natural`, where the flip makes the two convertible. All
   elaborator `"Natural"` carrier keys (ring, calc, ground relations,
   dispatch, diff bridges) key the PUBLIC name and survive unchanged.
5. Exporter re-point — a **one-entry swap** in `mapDeclarationName`
   (src/export_lean4.cpp:44): `{"Natural", "Nat"}` becomes
   `{"Natural.Raw", "Nat"}` (delete the old entry — the
   `registerDeclaredName` collision guard throws if both map to `Nat`).
   Constructor and op entries unchanged. The alias exports as a
   transparent `def Natural := Natural.Raw` (the exporter strips opacity
   unconditionally), and nanoda's Nat acceleration is purely name-keyed
   on `Nat`/`Nat.zero`/`Nat.succ`/`Nat.add`… — alias-typed op signatures
   are fine because the alias δ-unfolds checker-side.
6. The numeral-table self-check keeps working (probe: `Natural.add` 49
   samples / `Natural.multiply` 36 samples OK under the seal); extend
   `transparencyNames` (driver.cpp ~403) with the `Natural.Raw.*` twins
   of the step helpers when the remaining four ops move.

`unfold Natural in <body>` is the raw floor's escape hatch: it flips the
alias transparent for the remainder of the enclosing declaration
(dispatch.cpp:348-381), which rescues `cases`, `by induction`, and
mixed alias/raw terms in proof BODIES — probe: `cases n { | zero => … |
successor(k) => … }` under an all-alias statement works today with no
elaborator change. A theorem STATEMENT can never be rescued (it
elaborates before the body), so every public statement must be spelled
at the alias — wrapper `Natural.successor` or `1 + k`.

The **alternative** (module-discipline-only: keep the raw inductive
public but lint against importing it) is weaker — it's a convention, not
kernel-enforced, and the recursor stays reachable. The audit found the
wrap fully feasible on the kernel-literal hot path, so this fallback is
**rejected**. (A second rejected variant: giving the *wrappers* the bare
names and qualifying the raw constructors — it would keep the 46
external `successor(` files legal forever and re-key four kernel
bare-name checks plus two exporter entries for no confinement gain.)

---

## Stage-0 audit findings (2026-07-10) — the five questions, answered

Method: source reads of the kernel/elaborator/exporter couplings plus an
**empirical prototype** on `scratch/natural-seal-stage0-probe`
(3c65a529): the wrap declared for real in `basics.math`, `peano.math`
rebuilt as a probe bed, the kernel re-point applied, and each mechanism
exercised by a named probe theorem. Prototype `peano.math` builds green
and contains: raw-floor pattern-defs and all-Raw theorems, the
literal↔constructor bridge probe (`2 =
Natural.successor(Natural.successor(Natural.zero)) := unfold Natural in
reflexivity(2)`), `cases`-under-`unfold` with an all-alias statement,
the boundary induction theorem bootstrapped under the seal, a
consumer-spelling `case base/step` induction with NO unfold, the ground
table probe `2 + 3 = 5 := reflexivity(5)`, and the alias-level
characterising lemma `1 + a = Natural.successor(a) := done by unfolding
Natural.add`.

1. **Seal mechanism on the literal hot path — feasible; two-gate
   re-point.** The kernel's coupling splits cleanly: *inductive-keyed*
   gates (`isNaturalConstructor`, the recursor literal-view gate)
   re-point to `"Natural.Raw"`; *name-keyed* machinery (one-peel view,
   compaction, defeq bridge, ground-spelling reader — all on bare
   `zero`/`successor`; the 6-op table on `Natural.add`…) is untouched
   because constructors keep bare names and ops keep wrapper names.
   Literals **stay typed at the alias** (`makeConstant("Natural")` only
   requires the name to be declared, not inductive) — validated. The
   ground-relation certificate tier builds literal+lemma terms at the
   alias (no constructors) and survives; it declines gracefully where
   its lemmas aren't imported.
2. **Export trail — confirmed viable; one-entry map swap.** The
   exporter has NO structural assumption that `Natural` is inductive;
   renames funnel through `mapDeclarationName` applied at both
   declaration and reference chokepoints; opacity is stripped
   unconditionally (`stripOpacity`), so the alias exports as a
   transparent def and δ-unfolds checker-side; nanoda's acceleration is
   purely name-keyed (`Nat`, `Nat.zero`, `Nat.succ`, `Nat.add`… in its
   primitive table) and does not require op signatures to spell `Nat`
   literally. Required change: swap `{"Natural","Nat"}` →
   `{"Natural.Raw","Nat"}` — **delete, don't augment** (the mapped-name
   collision guard throws otherwise). `Natural.Raw_recursor → Nat.rec`
   falls out of the `_recursor` branch automatically. `make
   export-check` joins every stage's gate from Stage 1 on (it could not
   run against the prototype since the prototype deliberately leaves
   the library unbuilt past `peano`; first real run = Stage 1
   acceptance).
3. **Defeq-arithmetic acceptance set — small, loud, already covered.**
   External `decide(` uses: zero. Ground literal facts ride the table +
   certificate tier (probe-validated at the sealed alias). Open-term op
   reduction (δ/ι through transparent op bodies) is untyped and keeps
   working through the wrapper layer. What breaks does so at
   *elaboration time with clean errors*, in exactly three classes:
   pattern-defs/`cases`/legacy-induction on the sealed type ("'Natural'
   is not an inductive type"), raw `successor(` applied to alias-typed
   arguments (function-expects-Raw error), and alias/raw-mixed
   statements. No silent defeq loss was found; no new decision
   procedure is needed. One wrinkle: `absurd(...)` loses its
   expected-type inference in all-Raw reductio blocks (works at
   `Natural` today) — the raw floor uses the `done` idiom (house style
   anyway); root-cause if it ever bites elsewhere.
4. **`by induction`/`cases` retargeting — split verdict,
   probe-measured.** The `case base:`/`case step(k):` block already
   routes through `<Carrier>.induction_on_one_plus` (label-keyed
   vocabulary detection, then carrier-keyed lemma name) and **works at
   the sealed alias unchanged**. The surprise: the modern `case n = 0`
   / `case n = k + 1 for some k` spellings desugar AT PARSE TIME to
   `zero`/`successor` constructor patterns and take the raw-recursor
   path — they break at the seal and are Stage 2's main retargeting
   target, together with plain `cases` (which additionally needs a
   `Natural.cases_on_one_plus` boundary theorem — none exists) and
   pattern-match definitions (→ `Natural.recursion`).
   `buildCaseLambda` is hardwired to the recursor minor-premise layout
   and needs a boundary-layout twin, or `cases` gets hand-assembly
   mirroring `elaborateByInductionOnePlus`. The existing
   `engageOpaqueQuotientAlias` hook (cases.cpp:1101) is the template
   for an opaque-inductive-alias sibling. `by induction on E using
   <lemma>` and `strong induction` forms are already theorem-driven and
   unaffected.
5. **The raw floor — two tiers, not one handful.**
   *Permanent core* (pierces the seal forever): `basics` (Raw inductive
   + wrappers + add/multiply), `peano` (discriminators + injectivity +
   `zero_or_successor`), `arithmetic` (op characterising lemmas),
   `one_plus_induction` (+ the `n+1` twin), `strong_recursion` (+ the
   future `Natural.recursion`), `decide`/`classical_decidable`
   (decidability by recursion; may later ride `Natural.recursion`).
   *Op-defining tier* (stays raw only until Stage-2's
   combinator-backed pattern-defs land, then optionally re-bases at the
   alias): `monus`, `subtraction`, `compare`, `order`, `floor_divide`,
   `division` (step functions), `power`, `factorial`, `maximum`,
   `distance`, `pairing`, `triangular`.
   The remaining ~14 `successor`-mentioning `Natural/` files
   (`cancellation`, `add_order`, `multiply_order`, `multiply_bounds`,
   `euclid`, `bezout`, `divisibility`, `divides_subtract`,
   `factorization`, `prime_*`, `decide_divides`, `binomial`) are
   proof-level users and migrate to lemma-based reasoning in Stage 3.

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
- **Stage 1 (the sealed boundary) is the next executable step.** Start
  from the prototype branch `scratch/natural-seal-stage0-probe`
  (3c65a529) — its `basics.math`/`peano.math` are the worked example —
  but land with the alias TRANSPARENT (see the ledger) and check the
  headConstantName-carrier risk first.

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
| 1 | The sealed boundary (wrap + wrappers + boundary theorems + kernel/exporter re-point) | **DONE 2026-07-10** | Landed with the alias TRANSPARENT (`definition Natural := Natural.Raw`); the opacity keyword is Stage 4's flip. **The audit's orientation was revised during landing** (see §Mechanism): the raw constructors are QUALIFIED (`Natural.Raw.zero`/`Natural.Raw.successor`, the `IntegerRepresentative.make` pattern) and the historical bare names `zero`/`successor` are transparent alias-typed wrapper definitions — keeping bare constructor names made every raw-headed statement infer carrier `Natural.Raw` and broke structural matching library-wide (absurd shapes, lemma citation, calc `≤` dispatch). What landed: the wrap + wrappers in `basics.math` (ops unchanged — pattern-defs still compile through the transparent alias; the two-layer op split moves to the flip); kernel re-point (2 inductiveName gates + view/compaction/bridge/ground-reader/self-check keyed to the qualified names); exporter map `{"Natural.Raw","Nat"}` + qualified ctor entries; elaborator alignment (arm goals + destructured binder types spelled publicly in patterns.cpp; matcher name-normalization `constantNamesMatchModuloNaturalWrapper`; syntactic-head-first carrier resolution in `by induction`/`strong induction`; alias-resolving shadow guard; printer folds both spellings); boundary theorems `Natural.induction_on_plus_one` (the `n+1` twin) + `Natural.cases_on_one_plus`. `Natural.recursion` deferred to Stage 2 (its only consumer). Gates green: `make -j 16 library tests error-tests`, `make check`, `make export-check` (2527 decls). |
| 2 | Tactics speak the boundary | **DONE 2026-07-11** (proof-level; pattern-DEF compilation deferred to the flip) | What landed: (a) **`by induction` blocks in the constructor vocabulary** — `case zero:`/`case successor(k):` and the equation spellings `case n = 0:`/`case n = k + 1:` that desugar to them — route through the new constructor-spelled boundary theorem **`Natural.induction_on_successor`** whenever it is in scope, with graceful RAW-recursor fallback where it isn't (the raw floor below `one_plus_induction`, non-importing files, non-Natural carriers) — so no proof file changed and arm goals keep their constructor spelling byte-for-byte. Explicit `case base/step` still routes to `induction_on_one_plus`. A new `SurfaceCases.isInductionBlock` marker gates the routing so a plain `cases` over an inductive with a real `step` constructor (`LessOrEqual.step`) is never misrouted. The boundary path gained the `coerceToExpectedTypeViaDiff` arm coercion (mirroring `buildBodyForCase`), which bare stated-proposition arms need. (b) **plain propositional `cases n { \| zero => \| successor(k) => }`** on a local-binder scrutinee routes through the new **`Natural.cases_on_successor`** via `elaborateCasesViaBoundaryTheorem` (guards: Prop goal, plain block, two-arm vocabulary; Type-level results / `with`-equality / refining stay raw). (c) **`Natural.recursion`** landed in `basics.math` (defined via the raw recursor; step speaks the wrapper) + feature test `Test/natural_recursion_test.math` — ground computation through the table and BOTH defining equations hold definitionally. An early experiment re-spelling step goals as `P(1 + k)` broke defeq-reliant proofs (binomial's if-guard) — hence the constructor-spelled theorems; the `1+n`/`n+1` twins remain the CITATION forms. Residual for the flip: pattern-match definitions still compile via the recursor (patterns.cpp:9) — at the flip they compile onto `Natural.recursion` or move to the raw floor; `cases … with h` / Type-level cases likewise. Gates green: library+tests+error-tests, `make check`, export-check (2530 decls). |
| 3 | Consumer migration | **not started** | Classes + counts (measured 2026-07-10): 46 external files spell `successor(` (fail at the opaque flip: raw constructor at alias-typed args — clean error, probe-validated); 31 external files destructure Natural in pattern arms (proof `cases` → Stage-2 retarget; recursive defs — monoid/ring power, List.range, Polynomial padding, series partial sums, aggregation — → `Natural.recursion`); 6 external files use `case n = 0` spellings (Stage-2 retarget covers). External `decide(` uses: **zero**. Interior `Natural/`: 33 files, tiered in §findings Q5. Advisory-driven, gradual; the transparent-alias waypoint keeps everything green throughout. |
| 4 | Flip the seal | **not started** | One-keyword flip `definition` → `opaque definition` on the alias + fix stragglers; raw floor reduced to the documented set (§findings Q5). Acceptance: full `make -j 16 library tests error-tests`, `make check`, **and `make export-check`** green. |

**Overall:** Stages 0–2 done (0–1 on 2026-07-10, 2 on 2026-07-11). The
library builds with `Natural` as a transparent alias over the qualified
raw inductive; every `by induction` and plain propositional `cases` on a
Natural in lemma-importing files now emits boundary theorems instead of
the raw recursor; all gates green. Next: Stage 3 (consumer migration —
mechanical, advisory-driven) toward Stage 4's flip, whose remaining
technical prerequisite is compiling pattern-match definitions onto
`Natural.recursion` (or moving them to the raw floor).

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
   public namespace with **qualified constructors** — `inductive
   Natural.Raw : Type(0) where | Natural.Raw.zero : Natural.Raw |
   Natural.Raw.successor : Natural.Raw → Natural.Raw` — and re-expose
   the historical bare names as **transparent alias-typed wrappers**:
   `definition zero : Natural := Natural.Raw.zero`, `definition
   successor : Natural → Natural := Natural.Raw.successor`.
   (**Stage-1 revision of the audit's recommendation.** The audit
   proposed keeping the constructors' bare global names to avoid kernel
   re-keys; landing that showed every raw-headed statement —
   `successor(a) = zero` — then infers carrier `Natural.Raw` while the
   rest of the library speaks `Natural`, and though defeq bridges the
   two, STRUCTURAL machinery does not: the absurd shape recognizer,
   metavar-inferring lemma citation against WHNF'd hypotheses, and calc
   `≤` dispatch on destructured binders all broke. With wrappers owning
   the bare names, every consumer spelling keeps carrier `Natural` by
   construction; the kernel keys re-point to the qualified names — the
   machinery only ever sees raw constructors post-δ. Consequences:
   pattern labels match constructors by last component (`| successor(k)`
   ↔ `Natural.Raw.successor`); case-arm goals and destructured binder
   types are spelled publicly (patterns.cpp `publicConstructorSpelling`
   / `publicTypeSpelling`); structural matchers compare constants
   modulo the wrapper (`constantNamesMatchModuloNaturalWrapper`,
   term_utilities.hpp). Post-flip, bare-`successor` TERM uses keep
   elaborating (the wrapper survives) — term-level confinement is
   Stage 3's sweep plus retiring the bare wrappers at the end; the
   kernel-hard part of the seal is pattern-matching/recursor access,
   which the flip blocks either way.)
2. `opaque definition Natural : Type(0) := Natural.Raw`. Hard opacity
   stops δ-unfolding, so consumers can't pattern-match or invoke the raw
   recursor through the alias (probe: "'Natural' is not an inductive
   type"). **Sequencing:** Stage 1 lands this line *transparent*
   (`definition`), so the library keeps building while consumers
   migrate; Stage 4 adds the keyword.
3. Re-expose the boundary at the alias:
   - the bare wrapper definitions of point 1 (transparent on purpose:
     they must δ-reduce onto the raw constructors so kernel defeq and
     literal compaction fire through them; an opaque wrapper would
     split `successor(x)` from the constructor form),
   - operations: UNCHANGED through the transparent phase — the existing
     pattern-match definitions (`Natural.add` opaque, `Natural.multiply`
     transparent) still compile through the alias. The two-layer split
     (`Natural.Raw.<op>` + alias wrapper) belongs to the FLIP, and when
     it lands the raw bodies must reference the PUBLIC opaque ops in
     their recursive arms (a `Raw.add`-calling `Raw.multiply` changes
     the reduct shape `multiply(1, a) ⇝ add(a, …)` vs `Natural.add(a,
     …)` and breaks defeq-shaped proofs — measured in the Stage-1
     first attempt). Constructor-spelled bodies only at the raw floor
     (a numeral body types at the ALIAS and cannot sit in a Raw
     position; numeral *patterns* are fine, they desugar at parse
     time). The 6-op table keys on `Natural.add`… and keeps firing,
   - **both** induction principles as theorems — LANDED:
     `Natural.induction_on_one_plus` (pre-existing) and the `n+1` twin
     `Natural.induction_on_plus_one`, plus the case-analysis theorem
     `Natural.cases_on_one_plus`, all in
     `Natural/one_plus_induction.math`
     (`one_plus_vs_plus_one_asymmetry` is closed; `add_one` was already
     automatic),
   - `Natural.recursion` — a primitive-recursion combinator into `Type`
     (what `definition … | 0 => … | 1+k => …` compiles onto post-flip
     for consumers): DEFERRED to Stage 2, next to its only consumer,
   - the Peano characterising lemmas: unchanged through the transparent
     phase (they spell the bare wrappers, carrier `Natural`); at the
     flip their proofs gain `unfold Natural in` where they destructure.
4. Kernel re-point — LANDED: the two `inductiveName` gates
   (`isNaturalConstructor`, kernel.cpp ~1120; the recursor literal-view
   gate, ~1343) key `"Natural.Raw"`, and the literal machinery's
   constructor names (one-peel view, compaction, defeq bridge,
   ground-spelling reader, numeral-table self-check chains) key the
   QUALIFIED `Natural.Raw.zero`/`Natural.Raw.successor`. Literal typing
   (`makeConstant("Natural")`, kernel.cpp ~2402) **stays on the alias**
   — literals live at `Natural` everywhere. All elaborator `"Natural"`
   carrier keys (ring, calc, ground relations, dispatch, diff bridges)
   key the PUBLIC name and survive unchanged; the matchers additionally
   compare constants modulo the wrapper
   (`constantNamesMatchModuloNaturalWrapper`) because WHNF'd subjects
   spell raw heads while statement-side patterns spell wrappers.
5. Exporter re-point — LANDED: `{"Natural.Raw", "Nat"}`,
   `{"Natural.Raw.zero", "Nat.zero"}`, `{"Natural.Raw.successor",
   "Nat.succ"}` in `mapDeclarationName` (src/export_lean4.cpp:44); the
   old `{"Natural", "Nat"}` entry deleted (the `registerDeclaredName`
   collision guard throws if both map to `Nat`). Op entries unchanged.
   The alias and the bare wrappers export as transparent defs under
   their own names (the exporter strips opacity unconditionally), and
   nanoda's Nat acceleration is purely name-keyed on
   `Nat`/`Nat.zero`/`Nat.succ`/`Nat.add`… — alias-typed op signatures
   are fine because the alias δ-unfolds checker-side. Verified:
   `make export-check` green, 2527 declarations.
6. The numeral-table self-check keeps working (verified: `Natural.add`
   49 samples / `Natural.multiply` 36 samples OK); extend
   `transparencyNames` (driver.cpp ~403) with the `Natural.Raw.*` twins
   of the step helpers when the remaining four ops move at the flip.

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
**rejected**. (The audit had also rejected the bare-name-wrapper
orientation as "no confinement gain"; Stage 1 REVERSED that — see
point 1 — because the carrier-shift breakage of bare raw constructors
outweighed it, and term-level confinement is recoverable later by
retiring the bare wrappers once Stage 3 completes.)

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
- **Stage 3 (consumer migration) is the next executable step** — the
  advisory `successor`-outside-`Natural/` worklist, mechanical and
  gradual; the CIC-leak sweeps keep contributing. The scratch branch
  `scratch/natural-seal-stage0-probe` (3c65a529) still holds the
  opaque-endpoint probes (it predates the Stage-1 orientation flip; the
  validated mechanics — unfold-rescue, bridge, boundary routing — carry
  over).

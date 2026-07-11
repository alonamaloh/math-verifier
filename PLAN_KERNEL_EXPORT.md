# PLAN_KERNEL_EXPORT.md — align the kernel with Lean's, export a trail, check it externally

Owner directive (2026-07-10): our trusted kernel is already extremely close
to Lean 4's; rather than diverging further (e.g. `mpq_class` rationals —
Stage 5 of PLAN_FAST_NUMERALS, now permanently rejected), *"we may want to
try to match their kernel exactly, so that we can produce a trail of things
we send to the kernel in a standard format so that other Lean-kernel
implementations can check the correctness of our system."*

Design document for **dedicated implementation sessions**. The Status
ledger below is authoritative — read/update it every session, like
`PLAN_FAST_NUMERALS.md`.

**The goal, precisely.** Not a bit-for-bit reimplementation of Lean's
kernel. The target is the *kernel language* an external checker consumes
(normative reference: ammkrn's **"Type Checking in Lean 4"**,
https://ammkrn.github.io/type_checking_in_lean4/ — the spec that
`nanoda`-class checkers implement; Lean's `src/kernel/type_checker.cpp`
is the tie-breaker where the book is silent). We want the invariant:

> **Everything our kernel accepts, an external Lean-kernel checker
> accepts** — witnessed continuously by exporting our whole environment
> in the lean4export format (**NDJSON 3.1.0** — the Stage-0 PoC found
> the classic text format retired upstream) and replaying it through an
> independent checker in CI.

## Status ledger

| Stage | Workstream | Status | Record |
|-------|------------|--------|--------|
| 0 | Audit + toolchain proof-of-concept | **DONE 2026-07-10** | §A. All five gates settled with the owner: adopt Lean's subsingleton rule; pow cap 2²⁴; nanoda primary (lean4lean **dropped** — the PoC found it has no export-file frontend, .olean input only); full-library trail; `maximum` off the table. Inventory: ground uses of `factorial`/`maximum`/`predecessor` exist only in `Test/` with tiny arguments; no `power` exponent near the cap — all drops risk-free. PoC (notes: `docs/kernel-export-poc.md`): Lean 4.31.0 + lean4export v4.31.0 emit **NDJSON format 3.1.0** — the classic text format is retired upstream (ammkrn moved his own tooling to NDJSON, Dec 2025); `nanoda_bin` (0.4.10-beta) natively replays it — 58,703 declarations in 23 s, config-file driven, `nat_extension: true` required, axiom allowlist built in. Lean needs a 16 GB `ulimit -v` (per-thread VA reservations), not our default 8. |
| 1 | In-source op-table alignment (kernel + `Natural/`) | **DONE 2026-07-10** | §B. `floor_divide`/`modulo` now take **(dividend, divisor)** with `n / 0 = 0` (a `cases` guard in the definition; new `floor_divide_zero_divisor`/`modulo_zero_divisor` lemmas) and `n % 0 = n`; `factorial`/`maximum`/`predecessor` dropped from the table (replay-by-unfolding pinned in `Test/natural_literal_test.math`); `power` accelerated only below 2²⁴; self-check re-ranged with divisor 0 covered. Conventions pinned at the defeq level in `Test/lean_kernel_conventions_test.math`. Full `library tests error-tests` + numeral-table self-check green. |
| 2 | Kernel-semantics parity residuals | **DONE 2026-07-10** | §C. Lean's subsingleton criterion landed in `addInductive` (`kernel.cpp`): a one-constructor Prop inductive large-eliminates when every non-parameter field is a proposition or appears among the conclusion's indices — And/Iff-class recursors now match what a checker re-derives; Exists stays Prop-only (witness is data); the Accessible shape (field pinned by an index) covered. Unit tests pin all three shapes. Elaborator audit: every recursor-constructing site (`cases.cpp`, `patterns.cpp` ×2, `prover.cpp`) already keys off `recursor->universeParameters.size() > inductive->universeParameters.size()` — no Prop-only-motive assumption anywhere; one prover comment tightened. Full `library tests error-tests` green (self-tests carry 13 pre-existing failures — stale retired-keyword/pretty-printer tests, verified identical at HEAD). Audits: `docs/kernel-export-quotient-mapping.md` (export Quotient.* as transparent definitions over a `quot`+Sort-polymorphic-`Eq` prelude + two Equality↔Eq bridges — bare rename fails the checker's exact-signature validation on Type-vs-Sort universes; lift-defeq replays via δ+quot rule; **confirmed the library needs no `induct` reduction**) and `docs/kernel-export-axiom-inventory.md` (Stage-4 gate = exactly 5 axioms: propositional_extensionality, excluded_middle, the, the_satisfies, Quot.sound; **sorry burn-down found complete** — exporter omits `Internal.sorry*` so sorry-freedom becomes machine-checked; pre-seal hook = load full `.mathv` caches in `library-depends.mk` order, never `.iface`; closed-body scan asserted at export time). |
| 3 | The exporter (untrusted tool) | **DONE 2026-07-10** | §D. `kernel export-lean4` (`src/export_lean4.cpp`): full `.mathv` caches (never `.iface`; sealed placeholder-body/axiom stand-ins upgrade to the implementation's declarations), reference-driven DFS emission (caches are name-sorted), NDJSON 3.1.0 with continuous back-refs, `Nat`/`.rec` name maps, Sort-polymorphic `Eq`+`quot` prelude, `Equality`↔`Eq` bridges, `Quotient.*` wrapper definitions, inductive groups with re-derivable ι-rules. Landing it surfaced and fixed THREE kernel-parity gaps at the source: minor premises now bind fields first then IHs (3cb68a36), the motive level leads the recursor's universe params (1410dbd1), and `addInductive` enforces Lean's constructor-field universe bound (`levelLessOrEqual` gained the sound 0≤x / n≤succ / weakening rules; `Sum` was the lone violator — now `Type(MaxUniverse(u,v))`). Full library exports in ~2 s (17 MB, 338k lines). |
| 4 | External checking in CI | **DONE 2026-07-10 (manual target; nightly wiring pending)** | §E. `make export-check` (`scripts/export_check.sh`): exports the full library, replays through `nanoda_bin` (`NANODA_BIN` overridable; binary + format spec kept in `~/claude/export-tools/`), asserts the axiom report EXACTLY equals the 5-axiom inventory. **PASS: 2522 declarations, no errors, 0.34 s check time** — the plan's acceptance criterion holds for the complete library. `Internal.sorry*` omitted from the trail, so sorry-freedom is externally machine-checked. Trust story: `docs/kernel-export-trust.md`. Remaining: wire into nightly CI (owner infra). |

---

## Context — what we verified (2026-07-10 session)

A full read of `src/kernel/` (5,939 lines) against Lean's
`type_checker.cpp` and the book established:

**Already aligned (no work):** expression grammar (bvar/fvar/sort/pi/
lambda/app/const/let + Nat literal), universe levels with `imax`,
**non-cumulative** universes (adopted deliberately; `isSubtype` removed),
impredicative `Prop`, β/δ/ζ/ι/η, **definitional proof irrelevance**,
strict positivity, GMP `NaturalLiteral` with the one-peel constructor
view and eager `successor`-compaction (modeled on Lean's design), a
quotient computation rule, recursor argument layout (params, motive,
minors, indices, major).

**We are strictly stricter (no work — protect this):** no structure
projections / struct eta, no K-like reduction (`to_cnstr_when_K`), no
String literals, no mutual/nested inductives, no `Quot.ind` reduction
(we reduce only `Quotient.lift`), partial level-defeq normalization,
and **hard `opaque`** in kernel defeq. Every one of these makes our
defeq a *subset* of Lean's. Type-checking acceptance is monotone in
defeq strength (nothing accepts *because* a defeq check failed), so a
transparent export replays soundly. Opacity in particular needs **no
kernel change**: it remains our proof-hygiene discipline; the exporter
simply emits transparent definitions.

**The kernel's complete library-name coupling** (everything that must be
mapped or aligned): `zero`/`successor`, the 9-op accelerated table, and
`Quotient.lift`/`Quotient.class_of`. Nothing else in the trusted core
knows a library name.

**The genuine divergences (the work):**

1. **Op table set + conventions.** Ours: `add, multiply, monus, power,
   floor_divide, modulo, maximum, factorial, predecessor`. The book's
   core set (what every external checker implements): `Nat.succ, add,
   sub, mul, pow, div, mod, beq, ble` (current `type_checker.cpp` adds
   `gcd` + bitwise — do NOT rely on beyond-book ops). Deltas:
   - `floor_divide`/`modulo` take **(divisor, dividend)** — Lean's
     `div`/`mod` take (dividend, divisor); and our fuel convention gives
     `floor_divide(0, n) = n` where Lean has `n / 0 = 0` (our
     `modulo(0, n) = n` happens to match Lean's `n % 0 = n`).
   - `monus` = `Nat.sub` exactly (dividend-first, truncated) — name map
     only. `power(base, exponent)` = `Nat.pow` order — but Lean caps the
     accelerated exponent at 2²⁴ and we cap at `ulong`.
   - `factorial`/`maximum`/`predecessor` have no Lean counterpart.
2. **Elimination levels.** Our large-elim-from-Prop rule (empty, or one
   constructor with zero non-parameter arguments) is *stricter* than
   Lean's subsingleton rule (one constructor, every field a proposition
   or an output index). Being stricter is fine for defeq — but an
   external checker **re-derives recursors from the inductive spec**
   (the book's ch. 8; it does not trust shipped recursors), so for
   `And`/`Iff`-class inductives it derives a large-eliminating recursor
   where ours is Prop-motive-only → the *declaration* mismatches, not
   just defeq. This must be resolved, not worked around (§C).
3. **Acceleration is name-trusted at the checker.** External checkers
   accelerate `Nat.*` by NAME without verifying the exported definition
   bodies against GMP semantics. So exporting our ops under Lean's
   names is only sound if our definitions' *semantics* match Lean's
   conventions exactly — which is why Stage 1 aligns semantics
   in-source rather than having the exporter paper over argument orders
   at use sites (impossible for partial applications anyway). Our
   `MATH_CHECK_NUMERAL_TABLE` self-check is the standing guard that
   table semantics = definition semantics.

**Interaction with other plans.** PLAN_NATURAL_SEALING: orthogonal to
the export (exports are transparent), but do Stage 1 here *before* the
sealing migration so `Natural/` is touched once. PLAN_FAST_NUMERALS
Stage 5 (kernel ℤ/ℚ literals): **permanently rejected** by this plan —
ground ℤ/ℚ stays on the Stage-3 certificate route, which exports as
ordinary lemma applications and replays instantly.

---

## A. Stage 0 — audit + toolchain proof-of-concept

Decision gates to settle with the owner (§Open questions has the
recommendations), plus two pieces of groundwork:

1. **Table-op dependence inventory.** Instrument or grep-audit which
   proofs rely on kernel defeq through each beyond-core op:
   - `factorial`: arguments are tiny (≤ 20-ish; the table already
     declines past `ulong`) — replay-by-unfolding is ~n recursor steps
     with accelerated `multiply` at the leaves. Expect: safe to drop.
   - `maximum`: check the definition's reduction cost
     (`Natural/maximum.math`) — if it unfolds to `monus`/comparison
     shapes, replay is cheap; if it recurses unary on both arguments,
     ground uses with big literals must be found and re-routed through
     lemmas before the drop.
   - `predecessor`: O(1) unfold. Safe to drop.
   - `power` past 2²⁴ exponents: find any ground uses (expect none —
     `2^100` has exponent 100).
2. **Toolchain proof-of-concept, before any exporter code.** Install a
   real Lean 4, run `lean4export` on a trivial Lean library, and replay
   that file through the candidate external checkers (`nanoda_lib`;
   optionally `lean4lean`). Deliverables: the exact export-format
   version we target, the checker invocation, its runtime on a
   Lean-sized prelude, and its axiom-report format. This de-risks
   Stage 3 for the cost of an afternoon.

## B. Stage 1 — in-source op alignment (the time-sensitive stage)

All changes land together behind one full re-verify (any `src/` change
re-verifies the world; `.mathv` cache bump as usual).

- **`Natural.floor_divide`/`Natural.modulo`** (`Natural/floor_divide.math`,
  both `opaque` with characterising lemmas — the blast radius is the
  lemma set plus ~23 files):
  - flip to **(dividend, divisor)** argument order;
  - adopt `x / 0 = 0` (our current fuel convention gives `n`); `x % 0 = x`
    already matches — keep it through the re-plumb;
  - update the characterising lemmas (`*_zero_fuel`, `*_succ_fits`,
    `*_succ_too_big`, `floor_divide_modulo_decompose`, `modulo_bound`,
    divides bridges) and sweep consumers (Edit tool, not scripts);
  - update the kernel table entries (`evaluateAcceleratedNaturalOp`)
    and the ground-relation wrappers (`Natural.divide_evaluates` /
    `Integer.divide_evaluates` argument plumbing in
    `Rational/ground_arithmetic.math` + `ground_relations.cpp`).
- **Drop `factorial`/`maximum`/`predecessor` from the table** (the
  definitions stay; per the Stage-0 inventory, re-route any ground use
  whose replay would be unary-expensive). Our own kernel then replays
  them by unfolding too — acceptance unchanged, speed unchanged for the
  small arguments they actually see.
- **Adopt Lean's `pow` exponent cap (2²⁴)** in place of `ulong`: never
  certify by defeq what a checker can't replay. (Beyond-cap facts stay
  provable through lemmas, as today.)
- **Do NOT add** `beq`/`ble`/`gcd`/bitwise: our ground `<`/`≤`/`=`
  facts go through the Stage-3 certificate lemmas, which need nothing
  from the table; adding ops would grow the TCB for zero proofs.
- Update the `MATH_CHECK_NUMERAL_TABLE` self-check ranges/conventions.
- Acceptance: `make -j 16 library tests error-tests` green; the
  self-check green; a new `Test/` file pinning the aligned conventions
  at the defeq level (`(5 : ℕ) / 0 = 0` by reflexivity, argument-order
  sanity, `monus` truncation) so drift is caught locally, not nightly.

## C. Stage 2 — kernel-semantics parity residuals

- **Elimination levels (the one real kernel change).** Adopt Lean's
  subsingleton criterion in `addInductive`: large elimination for a
  Prop inductive with ≤1 constructor whose every field is a proposition
  or appears in the output indices. Strictly widens what we accept
  (monotone-safe) and makes our derived recursors match what an
  external checker derives. Fallout: `And`/`Iff`/`Exists`-class
  recursors change universe signature (`Exists` still fails the
  criterion — its witness field is data — so it stays Prop-only, same
  as Lean). Full re-verify + cache bump; audit any elaborator code that
  assumes Prop-only motives for these.
- **Quotient mapping audit.** Write down the exact
  `Quotient.class_of/lift/sound` ↔ `Quot.mk/lift/sound` correspondence
  (argument order, implicitness — ours are explicit-arity 3/6) and
  confirm the library never needs `Quot.ind`-style reduction (today's
  kernel has only the lift rule, so this is confirmation, not change).
- **Closed-declaration check.** Assert at export time that stored
  declaration bodies are FreeVariable-free (they should be; make the
  exporter fail loudly if not).
- **Axiom inventory.** Enumerate the axioms the trail will legitimately
  contain (quotient soundness, classical choice/decide substrate,
  `Internal.sorry*` for the burn-down list) and document it — Stage 4
  asserts the checker's axiom report equals exactly this list.
- **Interface modules (D-part sealing).** The exporter must consume the
  **pre-seal implementation environment**, not the sealed-interface
  view — otherwise sealed theorems export as bare axioms and the trail
  proves nothing about them. Locate the right hook in the cache/driver
  layering.

## D. Stage 3 — the exporter

A new **untrusted** tool (`kernel export --lean4`, or a separate
binary): walk the environment in declaration order and emit the
lean4export **NDJSON format 3.1.0** (pinned by the Stage-0 PoC; the
spec is `lean4export/format_ndjson.md` at tag v4.31.0, summarized in
`docs/kernel-export-poc.md` §f — one JSON object per line, a leading
`meta` line with the format version, three back-reference namespaces
keyed `"in"`/`"il"`/`"ie"`, declarations as `def`/`axiom`/`thm`/
`inductive`/`quot` objects, and nat literals as arbitrary-precision
decimal strings `{"natVal":"..."}`, onto which our GMP `NaturalLiteral`
maps 1:1).

- **Name maps** (mechanical, total):
  - `Natural` → `Nat`, `zero` → `Nat.zero`, `successor` → `Nat.succ`
    (the checker's literal acceleration is keyed to the builtin `Nat`,
    so our Natural must *become* Nat in the trail — it is a plain
    two-constructor inductive, so this is just renaming);
  - `Natural.add/multiply/monus/power/floor_divide/modulo` →
    `Nat.add/mul/sub/pow/div/mod` (sound only after Stage 1);
  - `Quotient.*` → `Quot.*` per the Stage-2 table;
  - everything else exports under its own name (only name-keyed kernel
    features need mapping — `Equality`, `Or`, etc. are ordinary
    inductives to a checker). Mangle any characters the format's name
    grammar rejects.
- All definitions export **transparent**; binder info defaults to
  explicit (checkers don't use it for checking); universe parameters
  carried as-is.
- **Incremental acceptance:** export `Logic/` + `Natural/` basics
  first and get that slice green through the external checker before
  scaling to the full library. Then full library; expect a large text
  file — measure, don't guess.

## E. Stage 4 — external checking in CI

- **Primary checker: `nanoda_lib`** (independent Rust implementation by
  the book's author, consumes the NDJSON export natively; validated in
  the Stage-0 PoC — invocation, config knobs, and axiom-report format
  in `docs/kernel-export-poc.md` §d; set `nat_extension: true` and
  drive the axiom policy through `permitted_axioms`).
  **`lean4lean` is dropped** (Stage-0 PoC verdict: it consumes `.olean`
  module data off the Lean search path only — no export-file frontend —
  so like `lean4checker` it can re-check Lean libraries, not our trail).
- `make export-check`: build the export, run the checker(s), require
  (i) zero errors and (ii) the axiom report **exactly equals** the
  Stage-2 documented inventory (so a stray `sorry` or accidental axiom
  is a CI failure, and burning down the sorry list is visible in the
  trail).
- Cadence: manual first, then nightly. Per-commit only if the checker
  turns out to be fast enough on the full trail; do not slow the
  inner `make tests` loop for this.
- Documentation: a short `docs/` note on the trust story — what the
  external check does and does not establish (it checks the *trail*;
  the exporter and name maps are untrusted but any unsoundness there
  produces a trail that fails to check or fails the axiom assertion,
  except semantic mis-mapping of accelerated ops — which is exactly
  why Stage 1 aligns semantics in-source and pins them with defeq
  tests).

---

## Open questions for the owner (Stage 0 gates) — ALL SETTLED 2026-07-10

1. **Elimination levels**: adopt Lean's subsingleton rule. → **Adopted**
   (Stage-2 work).
2. **`pow` cap**: adopt Lean's 2²⁴. → **Adopted** (landed in Stage 1;
   we decline exponents ≥ 2²⁴ — declining strictly more than Lean is
   always safe, accepting more never is).
3. **Checkers**: nanoda primary. → **Settled**; the lean4lean stretch
   goal died in the PoC (no export-file frontend).
4. **Trail scope**: full library from the start. → **Settled**. (The
   PoC also validated lean4export's *selective* mode — a two-theorem
   dependency cone is ~1000x smaller — as the model for fast
   per-theorem trails if we ever want them.)
5. **`maximum`** off the table. → **Confirmed** by the usage inventory
   (ground uses only in `Test/`, tiny arguments; library uses are all
   symbolic).

## Verification

1. Stage 1: full `make -j 16 library tests error-tests` (always
   `ulimit -v`); `MATH_CHECK_NUMERAL_TABLE` green; the new
   convention-pinning defeq tests green.
2. Stage 2: full re-verify after the elimination-level change; the
   quotient/axiom audits are documents, reviewed by the owner.
3. Stage 3: the `Logic`+`Natural` slice checks green externally before
   the full library does.
4. Stage 4 (the plan's acceptance): **the complete library trail
   checks green under an independent external Lean-kernel checker, and
   the axiom report matches the documented inventory exactly.**

# PLAN_FAST_NUMERALS.md — GMP-backed ground arithmetic in ℕ/ℤ/ℚ

Owner directive (2026-07-10): *"we need a serious effort to be able to quickly do
computations with specific numbers, at least in `Natural`, `Integer` and
`Rational`. This might involve using GMP's `mpz_class` and `mpq_class`. The fact
that this blows up the size of the 'trusted kernel' is of secondary importance."*

Design document for **dedicated implementation sessions** (not started). Sits
beside `PLAN_NATURAL_SEALING.md` (whose Stage-1 binary-literal + norm_num
linchpin this plan **subsumes**) and `PLAN_CALC_WIDENING.md` (whose honest
`-`/`/` made ground ℤ/ℚ facts routine to *state* — this plan makes them routine
to *prove*). The Status ledger below is authoritative — read/update it each
session.

## Status ledger

| Stage | Workstream | Status | Record |
|-------|------------|--------|--------|
| 0 | Design review + GMP build plumbing | **not started** | Owner sign-off on the open questions (§F); `-lgmpxx -lgmp` in the Makefile behind a thin wrapper header. |
| 1 | Kernel ℕ literals (mpz) + literal-aware WHNF/defeq | **not started** | §B: `NaturalLiteral` node, constructor view, accelerated-ops table, serializer bump. The heart of the plan. |
| 2 | Elaborator emits/consumes literals | **not started** | §C: `elaborateNumericLiteral` emits a literal; printer trivializes; matcher numeral-canonicalization simplifies. |
| 3 | Ground-relation decision procedure | **not started** | §D: silent `=`/`≠`/`≤`/`<` on ground ℕ directly, and on ground ℤ/ℚ via boundary-lemma certificates. |
| 4 | `ring`/`field` coefficients on mpz | **not started** | §E: kills the unary-coefficient ceiling at its root. |
| 5 | Native ℤ/ℚ literal values | **deferred — decide after 3** | Only if certificates prove too slow; see §D trade-off. |

---

## Context — why

Numerals today are unary successor chains: `elaborateNumericLiteral`
(`src/elaborator/inference.cpp:2546`) runs `std::stoi` (int-bounded!) and emits
N `Application` nodes. Everything downstream pays for that:

- **Ground facts don't close.** `(4:ℕ) - (5:ℕ) = -1` (2026-07-10 session) was
  unprovable by the auto-prover (budget exhausted walking successor chains) and
  by kernel defeq (the opaque ℤ quotient blocks lift-reduction of ground
  `add`/`negate`); it needed a hand-written chain through
  `Integer.from_difference` + `from_reverse_subtraction_witness(k := 1)`.
- **`ring`/`field` hold coefficients in unary** (`int` coefficient + successor
  towers, `src/elaborator/ring.cpp:2730`): proof size O(Σ|coef|), the
  field-clearing OOM class, the documented scalability ceiling.
- **Ground side conditions need ceremony.** ℚ `field` demands nonzero
  hypotheses in exactly-`¬(t = Rational.zero)` shape; `((2:ℕ):ℚ) ≠ 0` must be
  hand-stated even though it is decidable.
- **The kernel already burns time compressing chains back to decimals** at
  print time (`src/kernel/printer.cpp:241`).

The proof-carrying parts of the system are fine; it is *computation on specific
numbers* that has no fast path. GMP gives one; the owner accepts the
trusted-kernel growth.

## A. What already exists (reuse / replace, grounded)

- **Kernel expression nodes** (`src/kernel/expression.hpp:142-144`): an 8-way
  variant (BoundVariable, FreeVariable, Sort, Pi, Lambda, Application,
  Constant, Let) with bottom-up structural hashing — a new leaf node slots in
  cleanly. WHNF/defeq live in `src/kernel/kernel.cpp`
  (`weakHeadNormalForm`, `kernel.hpp:502`), with a kernel cache and hash-cons
  layer already in place.
- **Serializer version gate** (`src/kernel/serialize.cpp:17,664`): cache-format
  bumps are routine (mismatch ⇒ rebuild). A literal node needs a new tag + a
  bump.
- **Numeral elaboration**: `elaborateNumericLiteral` (`inference.cpp:2546`,
  successor chains, `stoi`-bounded); expected-type numeral handling and the
  numeral-at-carrier constants in `dispatch.cpp`; surface-level ground
  evaluation already exists for fold bounds (`dispatch.cpp:2686`).
- **Matcher numeral canonicalization**: `asNumeralLiteral`
  (`src/elaborator/diff_bridges.cpp:797`) — load-bearing for citations
  (`a680123`); becomes near-trivial over literal nodes.
- **The ℤ/ℚ boundary APIs** the certificate route (§D) composes:
  `Integer.from_difference` / `difference_equal` / `difference_equal_implies` /
  `from_subtraction_witness` / `from_reverse_subtraction_witness` /
  `Natural.subtract_from_difference`, and `Rational.fraction` /
  `fraction_equal` / `fraction_equal_implies`.
- **Stop-gaps to retire**: per-numeral `automatic` lemmas
  (`Real.two_is_nonzero`, `Integer.from_natural_add_one_nonzero`, …), the
  `decide`-based ground checks, the printer's chain compression.

## B. Stage 1 — kernel ℕ literals (the Lean-style trick)

New kernel node `NaturalLiteral { mpz_class value }`, typed at `Natural`.
The key idea (proven out by Lean 4's `Nat` literals): the literal is
**defeq-interchangeable with the constructor form, unfolded lazily**:

- `NaturalLiteral(0)` ⇝ `zero`; when a recursor / pattern-match needs a
  constructor head, WHNF of `NaturalLiteral(n>0)` yields
  `successor(NaturalLiteral(n−1))` — one peel at a time, on demand only.
- Conversely WHNF normalizes `successor(NaturalLiteral(n))` ⇝
  `NaturalLiteral(n+1)` eagerly, so terms re-compact.
- Structural equality / defeq on two literals is one mpz compare.

**Accelerated operations.** `Natural.add`/`multiply`/… are *library*
pattern-match definitions here (unlike Lean's kernel-known `Nat.add`), so the
kernel additionally carries a small built-in table: WHNF of
`<op>(NaturalLiteral a, NaturalLiteral b)` for `op` ∈ {`Natural.add`,
`Natural.multiply`, `Natural.monus`, `Natural.power`, `Natural.floor_divide`,
`Natural.modulo`, …} shortcuts to `NaturalLiteral(result)` via GMP. The
trust story: the table is part of the TCB (owner-accepted); a self-check test
mode re-verifies table entries against the library definitions by reducing a
sample range both ways (fast, run in `make tests`).

Mechanics: hashing (`hash.cpp`/`subtree_hash.cpp`) for the new node, a
serializer tag + `cacheVersion` bump, printer emits the decimal directly
(delete the compression walk). Unbounded digits fix the current `stoi`
ceiling for free.

Interaction with `PLAN_NATURAL_SEALING.md`: literals are exactly the
"numeral story" that plan's Stage 1 wanted (binary `2·n+b` literals +
norm_num); kernel literals are strictly stronger. Land literals **first**,
then sealing confines `successor` knowing numerals no longer need it.

## C. Stage 2 — elaborator emits/consumes literals

- `elaborateNumericLiteral` returns `NaturalLiteral(digits)` (mpz parses the
  digit string; drop the `Natural`/`zero`/`successor` environment check to a
  `Natural`-only check).
- Numeral-at-carrier constants and the expected-type numeral path
  (`dispatch.cpp`) unchanged in behavior; their ℕ-side legs become literals.
- `asNumeralLiteral` and the redundant per-numeral bridges simplify; the
  `2`-vs-`1+1` caveat class shrinks (defeq now decides `(2:ℕ) = 1+1`
  instantly — the ℝ-carrier caveat remains until §D/§5 reach it).
- ErrorTest/goal displays: literals print as decimals — audit expected-output
  files.

## D. Stage 3 — ground-relation decision procedure

Goal: ground `=`, `≠`, `≤`, `<` at ℕ/ℤ/ℚ close **silently** everywhere a
proof obligation can arise: by-less steps, citations' side premises, the `/`
nonzero discharge (`desugar_equality.cpp:737-792`), and `field`'s
nonzero-hypothesis shape (auto-supply ground `¬(t = Rational.zero)`).

- **ℕ**: nothing to synthesize — with Stage 1, ground ℕ relations are kernel
  defeq/`decide`-class facts; just give the auto-prover a cheap early tier
  that recognizes ground endpoints and emits the reflexivity/decide witness.
- **ℤ/ℚ — certificate route (recommended)**: normalize ground ℤ terms to
  `from_difference(a, b)` and ground ℚ terms to `fraction(n, d)` canonical
  forms by *composing the existing boundary lemmas* (the exact chain written
  by hand in `Test/honest_natural_arithmetic_test.math:four_minus_five`,
  emitted mechanically); equalities/orders then discharge via
  `difference_equal` / `fraction_equal` whose cross-multiplication premises
  are ground-ℕ defeq — instant after Stage 1. Proof terms stay small
  (a fixed lemma spine + literals). No new kernel types, no new trust.
- **Native ℤ/ℚ literals (Stage 5, only if needed)**: `IntegerLiteral(mpz)` /
  `RationalLiteral(mpq)` with kernel defeq to the quotient boundary forms.
  Cost: the kernel must know *library* names (`from_difference`,
  `fraction`) and their meaning through an opaque quotient — a much tighter
  kernel↔library coupling than §B's op table. Decide after measuring the
  certificate route.

## E. Stage 4 — `ring`/`field` on mpz

Switch the ring normalizer's coefficient type (`int`, `ring.cpp:~2730`) to
`mpz_class` (ℚ coefficients: `mpq_class`) and emit coefficient *literals*
instead of unary successor towers. This removes the
`ring_unary_coefficient_ceiling` and the small-common-multiple OOM dance in
field-clearing at the root, and unblocks the deferred symbolic-coefficient
rewrite if it is still wanted afterwards.

## F. Open questions for the owner (Stage 0 gate)

1. **GMP as a hard build dependency** (system `libgmp-dev`, link `-lgmpxx`)
   — acceptable? (Thin wrapper header keeps a future swap possible.)
2. **Trust story for the accelerated-op table**: fixed built-in list +
   self-check suite cross-checking against the library definitions —
   sufficient, or do you want the kernel to *verify* agreement once per
   definition (slower start-up, smaller leap of faith)?
3. **ℤ/ℚ**: certificate route first (recommended), or straight to native
   literal nodes?
4. **Ordering**: literals before `PLAN_NATURAL_SEALING` Stage 1 (recommended
   — sealing then never needs a successor-chain numeral story), agreed?

## Verification

1. **Micro**: `4 - 5 = -(1 : Integer)` by bare `done`;
   `(1:ℕ)/3 + (1:ℕ)/6 = (1:ℚ)/2` by `done`/`field` with no stated nonzeros;
   `factorial(20)`-scale ground facts; a numeral past 2³¹ (today's `stoi`
   ceiling) elaborates and computes.
2. **Regression**: the hand-written boundary chain in
   `Test/honest_natural_arithmetic_test.math` collapses to `done` (keep both
   forms as a before/after exhibit); `Test/calc_widening_test.math` unchanged.
3. **Perf**: full `make -j 16 library` wall-clock must not regress (expect a
   drop — printer compression + successor-chain traffic disappear); the
   self-check mode green in `make tests`.
4. **Global**: full `make -j 16 library tests error-tests` after every stage
   (any `src/` change re-verifies the world; always `ulimit -v`).

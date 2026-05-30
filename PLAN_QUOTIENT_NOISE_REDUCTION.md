# PLAN: Reduce surface noise in quotient-based constructions

Working brief for an assistant session (Claude Code). The goal is to make
proofs over quotient types (`Rational`, `Real`, `PAdic`) read like math
instead of like CIC plumbing, **without enlarging the trusted base**.

Pick one stage, land it, keep the build green, delete it from this file
when done (same convention as `TODO.md`).

## The one invariant that must not break

The kernel is the only trusted component. Every item below is either a
**surface desugaring** or an **inference/elaboration** change. None of them
may add reasoning power to the kernel or let the elaborator emit a term the
kernel would not otherwise check. After each stage:

```
make -j 16 library     # whole library must still verify
./kernel               # kernel + elaborator unit tests must pass
```

A change is only correct if the serialized `.mathv` terms are still
kernel-rechecked exactly as before. When in doubt, diff the emitted kernel
term for an affected theorem before/after — it should be identical (Stages
1, 2, 5) or a strictly-smaller def-eq check the kernel already supports
(Stage 3).

Also respect the project's stated design principles (see `README.md` →
"Design principles"): no abbreviations in declared names, coercions visible
at one syntactic site, embedding paths canonical not searched. Stage 4 is in
mild tension with the coercion principle and needs human sign-off before
building — see its note.

## Diagnosis: "quotient noise" is four separate leaks

All four co-occur in `library/Rational/triangle.math`; worth reading that
file plus `library/Real/cauchy_bounded.math` first.

1. **Introduction noise.** A rational is written
   `Quotient.mk(RationalRepresentative.make(n1, d1))`. The `mk` short form
   already infers `T`/`R`; what remains is the nominal constructor
   `RationalRepresentative.make`, which the mathematician never wants to see.
2. **Elimination noise.** Downstream theorems open with
   `cases x { | RationalRepresentative.make(n,d) => cases y { … } }`. The
   encoding leaks into every statement-proving theorem, not just construction.
3. **Respect-proof boilerplate.** ~30 lines per binary op converting
   `seqFn(add(rep1, rep2), m)` into `seqFn(rep1, m) + seqFn(rep2, m)` via
   manual `cases` + `reflexivity`. This is the existing `by bridge` item in
   `TODO.md`.
4. **Cast tax (rides along).** `(successor(d) : Integer)` repeated 6–8 times
   per calc, plus fully-applied order/algebra lemmas. Not quotient-specific,
   but it is what makes the quotient proofs read worst.

## Substrate that already exists (build on this, don't reinvent)

- `Quotient.mk(rep)` short form infers `T`/`R` from context.
  Entry point: `elaborator.cpp` around the `name == "Quotient.mk" &&
  argumentCount == 1` branch (~line 3809) and the short-form inference
  around lines 4464 / 4536. Known boundary holes are listed in `TODO.md`
  ("`Quotient.mk`-with-ascription in unusual operator positions").
- Coercion registry + `coercion (S, T) := F`. Entry point:
  `elaborateCoercionDeclaration` (`elaborator.cpp` ~line 967); registry
  consulted at the ascription site (~line 4370). Diamonds are rejected, not
  resolved — keep that.
- `operator (op) on (T, T) := F` dispatch (see declarations across
  `library/**/*.math`, e.g. `Integer/order.math:36`).
- `Quotient.induct_two` / `Quotient.induct_three` (term-level) in
  `library/Logic/quotient.math`. Stage 2 is their missing surface counterpart.
- Notation hook is **stubbed**: `elaborator.cpp` ~line 775
  ("notation resolution not implemented yet"). Stage 1 lives here.
- Implicit binders `{x : T}` on `definition`/`theorem`/`axiom` already work.
  Stage 5 just applies them.

---

## Stage 1 — `construction` / notation for quotient introduction

**Kills leak #1. Pure surface macro. Lowest risk. Ship first.**

Finish the line-775 notation hook enough to register an introduction form
that desugars to today's term. Target surface:

```
construction Rational.fraction(n : Integer, d : Natural)
  := Quotient.mk(RationalRepresentative.make(n, d))
```

optionally with a notation binding (e.g. `n /Q d`). `Rational.fraction(n1, d1)`
must elaborate to **exactly** the current
`Quotient.mk(RationalRepresentative.make(n1, d1))` term.

- Hook: the stubbed notation/`construction` statement handler near
  `elaborator.cpp:775`; reuse the surface-statement dispatch already there.
- Soundness: macro expansion only — emitted kernel term is byte-identical.
- Acceptance: replace one or two `Quotient.mk(RationalRepresentative.make(...))`
  call sites in `Rational/basics.math` (`Rational.zero`, `Rational.one`) with
  the new form; `make -j 16 library` and `./kernel` stay green; diff the
  serialized term to confirm identity.
- Effort: small. Risk: low.

## Stage 2 — `by_representatives` elimination tactic

**Kills leak #2. Highest readability payoff. Do after Stage 1** (so the
folded goal it produces prints in the new introduction notation).

Surface counterpart to the existing `induct_two`/`induct_three`. For a
Prop-valued goal over quotient values:

```
theorem Rational.triangle_inequality (x y : Rational)
        : abs(x + y) ≤ abs(x) + abs(y) :=
  by_representatives x as (n1, d1), y as (n2, d2) =>
    Rational.triangle_inequality_at_representatives(n1, n2, d1, d2)
```

replaces the nested `cases x { | …make(n1,d1) => cases y { … } }`.

- Desugaring target: `Quotient.induct` / `Quotient.induct_two` /
  `induct_three` (already in `Logic/quotient.math`) followed by the
  representative `cases`, binding the named fields and presenting the
  `mk`-folded goal.
- Soundness: emits the existing recursors; no new kernel capability.
- Acceptance: rewrite `Rational.triangle_inequality` and
  `Rational.absolute_value_multiplicative` in `Rational/triangle.math` to the
  new form; build + tests green; emitted terms unchanged.
- Effort: medium. Risk: low–medium (goal presentation / binder scoping).

## Stage 3 — `by computation` calc-step closer (unsticks the `by bridge` TODO)

**Kills leak #3. Most surgical, cleanest soundness story. Good first
prototype.**

The `by bridge` investigation in `TODO.md` got stuck trying to make
`rewrite`'s **structural** matcher locate a subterm inside a ι-reduced term
(routes (a) and (b) there). Sidestep it: a respect-proof step is a *whole-step*
definitional equality, so don't locate a subterm at all. Add a calc-step
justification that closes the step by calling the kernel's
`isDefinitionallyEqual(lhs, rhs)` directly (WHNF already does the deep β/ι
reduction).

```
calc seqFn(add(rep1, rep2), m)
   = seqFn(rep1, m) + seqFn(rep2, m)   by computation
```

- Entry point: the calc-step dispatch / auto-prover (`autoProveClaim` and the
  bare/`reflexivity` closer in `elaborator.cpp`). Add `by computation` as an
  explicit closer that invokes the existing def-eq check.
- Soundness: def-eq is a kernel primitive; the closer only **checks** a
  user-written equality, never synthesizes one. Strictly smaller than the
  "deep-β matching (expensive)" route already costed in `TODO.md`.
- Acceptance: collapse one binary-op respect proof in `Real/` (e.g. in
  `Real/addition.math` or `Real/multiplication.math`) from ~30 lines to the
  single `by computation` step; build + tests green.
- Effort: small–medium. Risk: low. **Recommended starting point.**

## Stage 4 — carrier-scoped regions for the cast tax  ⚠ needs sign-off

**Mitigates leak #4. In tension with the explicit-coercion principle — discuss
before building.**

Today the "one visible site" for a coercion is the *token*, so a calc living
entirely in `Integer` re-ascribes every term (`(successor(d) : Integer)` ×8).
Make the *block* the unit instead:

```
over Integer {
  calc successor(K) + Integer.one
     = ...
}
```

Inside the region, literals and `successor(…)` elaborate at the ambient
carrier; the coercion is shown once at the block boundary. Argument: this
*strengthens* "type changes visible at one site" (one boundary cast beats
eight inline). But it does move where the cast appears, so it needs a human
call.

- Zero-change interim available today: adopt a `CLAUDE.md` style rule —
  `let sd := (successor(d) : Integer)` at proof top, reuse `sd`. Ship this
  regardless; it removes most repetition with no elaborator work.
- Effort: medium (region elaboration) / trivial (the `let` style rule).
  Risk: medium + principle tension.

## Stage 5 — implicit "shape" arguments on order/algebra lemmas

**Compounds with everything. Lowest glamour, mechanical.**

Lemma calls like
`Rational.LessOrEqual.sum(abs(s(N)), succK, abs(…), one, proof1, proof2)`
pass value arguments that are determined by the proof arguments. Mark those
value binders implicit (`{…}`) so only the proofs are written.

- Uses the existing `{x : T}` implicit-binder feature; per-lemma edits in
  `Rational/order*.math`, `Integer/order.math`, `Algebra/*_lemmas.math`.
- Soundness: same term, args now inferred instead of written.
- Acceptance: `Real/cauchy_bounded.math`'s `cauchy_is_naturally_bounded`
  shrinks; build + tests green.
- Effort: small but spread out. Risk: low (watch for inference failures where
  the value isn't determined — leave those explicit).

---

## Recommended sequencing

- **Independent, shippable now:** Stage 1, Stage 5, and the Stage 4 `let`
  style rule.
- **Self-contained, unblocks a TODO, best prototype:** Stage 3.
- **Highest payoff, do after Stage 1:** Stage 2.
- **Decide before building:** Stage 4 region form.

## Open design decision for a human (not for the assistant to settle alone)

Leaks #1 and #2 exist because `RationalRepresentative` is **nominal and
exposed**. Stronger fix than Stages 1–2: make it an *opaque interface* —
expose only `fraction` (intro, Stage 1) and `by_representatives` (elim,
Stage 2), and forbid naming `RationalRepresentative.make` outside
`Rational/basics.math` (mirrors how Lean hides `Quotient.mk` behind `⟦·⟧` +
custom induction). Costs the occasional raw-constructor escape hatch. This is
an encapsulation-discipline call; flag it, don't unilaterally enforce it.

## Verify after every change

```
make -j 16 library
./kernel
```

Both green, and for Stages 1/2/5 the emitted kernel term for at least one
touched theorem is unchanged. If a stage can't keep both green, stop and
leave the stage half-done in a branch rather than weakening the kernel or the
coercion principle to force it through.

---

## Findings (2026-05-29) from the IntegerMod / Polynomial build

Two new quotient constructions landed this session — `IntegerMod(n) :=
Quotient(Integer, CongruentModulo n)` and `Polynomial(R) :=
Quotient(Coefficients(R), ExtensionallyEqual)` — both **parameterized
quotients** (the relation depends on a parameter). They exercised the
quotient surface hard and bear on the stages above:

- **Short `Quotient.{mk,lift,sound}` inference breaks for parameterized
  quotient *aliases* (relevant to Stage 1).** For `IntegerMod(m)`, the
  short `Quotient.mk(rep)` cannot recover the relation `R`: it unfolds the
  alias past `CongruentModulo(m)` into the relation's body (an `Exists`)
  and tries to use that as `R`. The whole IntegerMod/Polynomial code had to
  use the **verbose** `Quotient.mk(T, R, rep)` / `lift(T,R,U,…)` /
  `sound(T,R,…)` forms. This *raises* the value of Stage 1's
  `construction` form for parameterized quotients — and that form should
  emit the verbose internal term, not rely on short-form inference.

- **Single `Quotient.induct` / `cases` motive inference for
  parameterized quotients — RESOLVED (2026-05-29).** This was reported as
  a Pi-domain mismatch and a Stage 2 `by_representatives` blocker, but it
  no longer reproduces: `Quotient.induct(atRep, q)` and bare
  `cases q { | rep => … }` now infer the motive for `q : IntegerMod(m)`,
  and all six unary laws in `IntegerMod/ring.math` were rewritten from the
  verbose explicit-motive form to the short form (build green). So Stage 2
  does **not** need a special explicit-motive path for the single
  scrutinee. The short `Quotient.sound` / `lift` over-unfolding gap for
  parameterized aliases is **also fixed** (see
  `PLAN_STRUCTURES_AND_INSTANCES.md` Stage 0b) — `IntegerMod/operations.math`
  now uses the short `Quotient.{mk,lift,sound}` forms throughout, so the
  whole parameterized-quotient surface (intro, elim, construction) reads
  the same as the non-parameterized one.

- **Stage 3 `by computation` is lower-value than written.** A whole-step
  definitional equality is already closed by plain `reflexivity` (the
  kernel checks `rhs` def-eq `lhs`) and by the calc auto-prover's def-eq
  branch with no `by` at all. The genuine `by bridge` pain — abstract reps
  where `seqFn(add(rep1,rep2),m)` is *stuck* because the reps aren't
  constructors — is better addressed by the patterns already in use:
  (a) the **at-make** pattern (pattern-match reps to constructor form so
  β/ι fires, then `reflexivity`), and (b) **`unfold Foo in <calc>`** for
  opaque recursive helpers. The polynomial multiplication bridge leaned on
  `unfold Natural.monus in <calc>` exactly this way to make index
  arithmetic (`monus(k+1,j+1) ≡ monus(k,j)`) compute. So `by computation`
  would be sugar over `reflexivity`/`unfold`, not a new capability —
  deprioritize unless a concrete site wants the explicit spelling.

- **Calc ergonomics worth a future sugar (new, not in the stages above).**
  Two friction points recurred across all the lifted-law proofs:
  1. `congruenceOf(f, Equality.symmetry(…))` with an *inline* symmetry does
     NOT elaborate as a calc `by` step (the step's diff-inference interferes);
     it works in a plain term position. Workaround: bind the symmetry to a
     `claim` first, then `congruenceOf(f, thatClaim)`.
  2. A reverse-direction congruence fold inside a calc is fragile; the
     reliable idiom is to prove the all-forward "expanded ⇒ folded"
     direction and wrap the whole calc in a single `Equality.symmetry`.
  A calc that handled reverse congruence steps (or a `by reverse <lemma>`)
  would remove a lot of boilerplate in quotient-law proofs.

These don't change the stage *priorities* much (Stage 1 construction +
Stage 5 implicit shape args remain the cheap wins), but Stage 2 now has a
concrete blocker to design around, and Stage 3 should be reweighted down.

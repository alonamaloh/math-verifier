# Interface / Implementation Separation — Design Plan

Status: design draft (2026-06-21). Owner-initiated. First target: ℝ.

## 1. Goal

Give the library true **abstraction barriers**: a type and its operations are
presented to consumers as an *axiomatic interface* (a fixed set of operations
and proven properties), while the *construction* (the concrete representation
and the proofs) lives behind a seal that the rest of the library cannot see
through.

The motivating example is ℝ. Today `Real` is a transparent
`Quotient(CauchyRationalSequence, CauchyEquivalent)`, so any consumer can
`by_representatives` it, pull out a representative Cauchy sequence, and reason
about the encoding. We want instead:

- Consumers see ℝ the way Spivak's textbook presents it — a **complete ordered
  field** with a `ℚ ↪ ℝ` embedding — and *nothing else*.
- The Cauchy construction is one *implementation*. Swapping it for Dedekind
  cuts tomorrow must be invisible to every consumer: the IVT proof, the
  exponential, the complex numbers built on ℝ — none may change.

This is **representation independence**. The interface is the contract; the
implementation is a detail.

## 2. Where we already are

The library has been converging on this by convention; the proposal formalizes
it.

- **`opaque definition`** (`docs/conventions/opaque.md`) already seals an
  individual definition's body behind a *characterising lemma*.
- **Integer and Rational are already opaque quotients.** Consumers go through
  boundary lemmas (`difference_equal`, `fraction_equal`, `from_natural`,
  `to_natural`) and never name `Quotient.class_of`. The elaborator already
  "engages opaque quotient aliases" for the short forms.
- **The "quarantine the machinery / layer the file" discipline**
  (`docs/conventions/proof-style.md`) is this idea applied per-file.
- **Algebraic bundles** (`Ring`, `Field`, `IsField`) are the *semantic* version:
  a consumer of an abstract `Ring` can only use the axioms, because the axioms
  are all the bundle exposes. `Real.is_field` already proves
  `IsField(Real, Real.add, Real.zero, Real.negate, Real.multiply, Real.one)`.
- **The `successor`-outside-`Natural/` campaign** is a hand-rolled, lint-enforced
  prototype of exactly this barrier for `Natural`.

What's missing is (a) a way to seal the *carrier type itself* (so the quotient
can't be unfolded), (b) a way to bundle a whole interface (type + operations +
axioms) as one importable unit with first-class ergonomics (a real type `Real`
and real operators `x * y`, not `Ring.carrier(r)` / `Ring.multiply(r, x, y)`
noise), and (c) kernel-level — not lint-level — enforcement.

## 3. Principle: sealed, *proven*, not assumed

The interface's "axioms" are **theorems proved about the construction**, not
admitted axioms. Spivak takes completeness on faith; we *construct* ℝ and
*prove* it is a complete ordered field, then seal the proof and representation
away. Therefore:

> **The interface costs zero trust.** It hides representation and proofs; it adds
> no assumptions. A sealed ℝ is exactly as sound as the construction underneath.

This is the key distinction from an axiomatic foundation, and it is strictly
better: we get the *ergonomics* of axioms with the *soundness* of a
construction.

## 4. Surface design

Two module kinds, plus a sealing relation.

### 4.1 Interface module

Declares the public view: an abstract type, abstract operation constants
(no bodies), theorem *signatures* (the obligations the implementation must
discharge), and optionally some *transparent* derived definitions that are
public by construction.

```
interface module Real

  -- Abstract carrier. No construction is visible; cannot be `cases`/
  -- `by_representatives`-ed by consumers.
  type Real

  -- Operations: abstract constants. Bodies live in the implementation.
  constant Real.zero     : Real
  constant Real.one      : Real
  constant Real.add      : Real → Real → Real
  constant Real.negate   : Real → Real
  constant Real.multiply : Real → Real → Real
  constant Real.LessOrEqual : Real → Real → Proposition
  constant Rational.to_real : Rational → Real           -- the ℚ ↪ ℝ embedding

  operator (+) on (Real, Real) := Real.add
  operator (*) on (Real, Real) := Real.multiply
  operator (≤) on (Real, Real) := Real.LessOrEqual
  -- (negation, coercion, numerals wired as usual)

  -- Transparent derived notions are allowed in the interface (public defs).
  definition Real.LessThan (x y : Real) : Proposition :=
    Real.LessOrEqual(x, y) ∧ x ≠ y
  definition Real.IsUpperBound (S : Set(Real)) (b : Real) : Proposition := …
  definition Real.IsSupremum   (S : Set(Real)) (s : Real) : Proposition := …

  -- The axioms: theorem SIGNATURES the implementation must prove.
  theorem Real.is_ordered_field
        : IsOrderedField(Real, Real.add, Real.zero, Real.negate,
                          Real.multiply, Real.one, Real.LessOrEqual)

  theorem Real.complete
        : ∀ (S : Set(Real)).
            Real.IsNonempty(S) → Real.HasUpperBound(S) →
              ∃ (s : Real). Real.IsSupremum(S, s)

  -- The embedding is an ordered-field homomorphism.
  theorem Rational.to_real.preserves_add      : …
  theorem Rational.to_real.preserves_multiply : …
  theorem Rational.to_real.preserves_order    : …
  theorem Rational.to_real.injective          : …
```

What is **deliberately NOT** in the interface (consumers derive it from the
axioms): Archimedean property, density of ℚ in ℝ, Cauchy-completeness ⇔ LUB,
the intermediate value theorem, suprema of specific sets. Keeping the interface
minimal is the whole point — and it doubles as the acceptance test (§9).

### 4.2 Implementation module

Provides the concrete (opaque) construction and discharges every interface
obligation. `implements Real` names the interface it satisfies.

```
implementation module Real.cauchy implements Real

  import Real.sequence          -- CauchyRationalSequence, CauchyEquivalent, …
  -- (all the construction's internal imports)

  -- The construction. Opaque OUTSIDE this module; transparent INSIDE it
  -- (so the obligation proofs can compute through it).
  definition Real := Quotient(CauchyRationalSequence, CauchyEquivalent)
  definition Real.add      := …    -- the lifts we already have
  definition Real.multiply := …
  definition Real.LessOrEqual := …
  definition Rational.to_real := …

  -- Discharge each interface obligation. Type-checked against the interface
  -- signature; the proof may use the construction freely.
  theorem Real.is_ordered_field := <proof using representatives>
  theorem Real.complete         := <the Cauchy-completeness proof>
  theorem Rational.to_real.preserves_add := …
  …
```

### 4.3 Sealing / linking

`implements Real` is checked at module-load:

1. Every `constant`/`type` in the interface has a matching `definition` in the
   implementation, with a definitionally-equal type.
2. Every `theorem` *signature* in the interface has a matching `theorem`
   *proof* in the implementation whose type matches the signature.
3. After the check, the *interface view* is registered for export: downstream
   `import Real` sees the abstract constants, the transparent derived defs, and
   the theorems — but the operation *bodies are sealed* (no δ-reduction) and the
   carrier *type does not unfold* to the quotient.

A consumer writes `import Real` (the interface). The implementation module is
not on the ordinary import path; nothing downstream can name
`CauchyRationalSequence` or `Quotient.class_of` through ℝ.

## 5. Kernel / elaborator semantics

The cleanest kernel model is **module-scoped opacity** plus **obligation
checking** — both are small generalizations of machinery that already exists.

- **Scoped opacity.** Today `opaque definition` is a per-definition, global
  flag. Generalize it to a *visibility scope*: a definition's body is
  transparent *within its implementation module* and opaque *everywhere else*.
  The interface/implementation split is then exactly "the bodies are visible to
  the obligation proofs, sealed to consumers." The carrier type is sealed the
  same way `Integer`'s quotient alias already is (the elaborator already engages
  opaque quotient aliases) — so `cases`/`by_representatives`/`Quotient.class_of`
  on a sealed type are rejected outside the implementation.
- **Obligation discharge** reuses the type-equality check the library already
  runs when a `theorem`'s proof is matched against its declared type. The only
  new step is *pairing* interface signatures with implementation proofs by name
  and checking the set is complete (every obligation discharged, no extras
  silently ignored).
- **No new trust.** The kernel still checks every obligation proof in full. The
  seal only restricts *visibility* downstream; it never admits anything.

This means the feature is mostly an *elaborator/driver* change (module kinds,
the `implements` relation, scoped visibility in the environment) on top of the
existing opaque + bundle machinery, not a kernel-soundness change.

## 6. Eliminator export (sealed inductive types)

ℝ has no eliminator problem — you almost never *eliminate* a real, so a sealed
carrier with no exposed recursor costs nothing. `Natural` is the opposite:
**induction is the interface.** A truly-sealed `Natural` must export an
induction principle so `by_induction` / `cases` keep working without the raw
`successor` constructor.

The interface exports an induction principle **stated in `n + 1` form**, and the
implementation discharges it with the raw recursor:

```
interface module Natural
  type Natural
  constant Natural.zero : Natural          -- the literal 0
  constant Natural.add  : Natural → Natural → Natural
  -- NB: `successor` is NOT exported. Build naturals with `0`, `1`, `+`.

  theorem Natural.induction
        : ∀ (P : Natural → Proposition).
            P(0) → (∀ (k : Natural). P(k) → P(k + 1)) → ∀ (n : Natural). P(n)
```

```
implementation module Natural.peano implements Natural
  inductive Natural | zero | successor (Natural)     -- internal only
  definition Natural.add := …
  theorem Natural.induction := <the raw Natural_recursor, with k+1 ≡ successor k>
```

Then `by_induction on n with IH { case zero: … case k + 1: … }` desugars to
`Natural.induction`, and **the pattern-position `successor` floor disappears**:
`| successor(k) =>` becomes `case k + 1:`, routed through the exported
principle. This is the deep resolution of the `successor`-outside-`Natural/`
campaign — the lint barrier becomes a *kernel* barrier, and the one construct
the lint could never remove (constructor patterns) is removed by the eliminator
export.

Language support needed for this part: (a) `case k + 1:` / `n + 1` pattern
syntax that desugars to the exported recursor rather than the constructor, and
(b) numeral literals (`5`) elaborating via `0`/`1`/`+` (the interface), not via
iterated `successor`.

## 7. Worked example: ℝ (the first target)

ℝ is the ideal first target: it is a *leaf* (nothing inducts on a real), the
axiomatic interface is textbook, and the construction already exists and is
already proven to be a field.

### 7.1 Assets already in the tree
- `Real.is_field` proves the field axioms.
- `Real/order*.math` proves the ordered-field axioms.
- `Real/supremum.math`, `Real/cauchy_complete.math` prove completeness.
- `Rational/embedding`-style lemmas prove the `to_real` homomorphism + order.

So the implementation module is mostly *re-homing existing theorems* as
obligation discharges — not new proofs.

### 7.2 The split
- `interface module Real` — §4.1 (the abstract type, operations, the
  ordered-field + completeness + embedding obligations, the transparent order
  notions).
- `implementation module Real.cauchy implements Real` — the current
  `Real/{basics,sequence,addition,negation,multiplication,reciprocal,…}` content,
  with the carrier and operations made implementation-scoped-opaque and the
  headline theorems tagged as discharges.

### 7.3 The acceptance test
After sealing, **the entire IVT cone must re-verify using only the interface** —
`Real/intermediate_value.math` and everything it imports — with:
- no `by_representatives` / `cases` on a `Real`,
- no `Quotient.class_of` / `CauchyRationalSequence` / `sequenceFunction` reached
  through ℝ,
- every step justified by the interface's axioms + derived consumer lemmas.

If IVT (and the exponential, and ℂ-on-ℝ) still go through, the barrier is real
and complete. Files that *break* point at exactly the boundary lemmas the
interface is missing — that list is the deliverable of the prototype.

## 8. Enforcement: kernel opacity beats lint

The `successor` / leak linters are *advisory*. A sealed type is enforced by the
**kernel**: a consumer literally cannot δ-unfold `Real` to the quotient, so the
encoding cannot leak even by accident. This is strictly stronger than the
manifest/ratchet discipline, and it lets us *retire* the corresponding lint once
a type is sealed (the lint becomes "did you bypass the seal," which the kernel
already forbids).

## 9. Phased plan

**Phase 0 — prototype a sealed ℝ with today's machinery (no language change).**
Use an opaque bundle witness to seal ℝ behind existing `opaque definition` +
abbreviations: make the carrier and operations opaque outside their defining
files, route consumers through the field/order/completeness theorems, and run
the §7.3 acceptance test. Goal: *measure the boundary-lemma cost* and *find the
missing lemmas* before building syntax. This is doable now and de-risks
everything else.

**Phase 1 — language support for the file split (ℝ).**
`interface module` / `implementation module … implements …`, scoped opacity in
the environment, the `implements` obligation check, and the export view. Migrate
the Phase-0 ℝ prototype onto the real syntax. No eliminator work yet.

**Phase 2 — eliminator export, then `Integer`.**
Add interface-level induction/recursion export and the `case k + 1:` /
numeral-via-`+` desugaring. Seal `Integer` (opaque quotient already; modest
eliminator needs).

**Phase 3 — `Natural`.**
The hardest: seal `Natural` behind `0`/`1`/`+`/`induction`, retire the raw
`successor` from all consumers via the exported principle, and drop the
`successor` lint in favor of the kernel seal. This is where the
`successor`-elimination campaign and this plan converge.

**Phase 4 — the rest.** ℂ (on a sealed ℝ), finite fields, polynomials — each a
construction behind a clean interface.

## 10. Costs, risks, open questions

- **Loss of defeq / computation.** A sealed ℝ gives up the ι/δ reductions many
  current proofs lean on (e.g. `sequenceFunction(make(s,_), m) ≡ s(m)`,
  `to_real(a*b)` reductions). Every such step becomes a propositional boundary
  lemma. This is the *same* bill `opaque.md` documents for Integer/Rational,
  just larger — Phase 0 measures it. **Mitigation:** a generous, well-named set
  of boundary lemmas published *with* the interface.
- **Numerals and literals.** `0`/`1`/`2`/`n+1` for sealed types must elaborate
  via interface constants, not constructors. Designed for in §6; needs care so
  `ring`/`field`/`decide` still see numerals.
- **`ring` / `field` / `decide` over sealed carriers.** These tactics currently
  reach for structural forms. They already work over *abstract* ring bundles, so
  the path exists; verify they fire on a sealed carrier via the exposed axioms.
- **Interface minimality vs convenience.** Every lemma promoted into the
  interface is a promise to all future implementations. Keep it minimal (LUB +
  ordered field + embedding hom); let consumers derive the rest. Open question:
  is *Cauchy-completeness* or *LUB* the better primitive completeness axiom?
  (LUB is Spivak's; Cauchy-completeness is closer to the construction. They're
  equivalent over an Archimedean ordered field — pick LUB for the interface,
  prove the equivalence once.)
- **Uniqueness.** A complete ordered field is unique up to unique isomorphism,
  so the interface pins ℝ up to iso — good. Worth stating (and maybe proving)
  the categoricity lemma so "swap the construction" is a *theorem*, not a hope.
- **Tooling.** `--goal-at`, the leak/anon linters, and the clean manifest all
  need to understand the two module kinds. Mostly mechanical.

## 11. Next concrete step

Phase 0 on ℝ: stand up the sealed-ℝ prototype with existing `opaque` machinery,
run the IVT-cone acceptance test, and produce the missing-boundary-lemma list.
That artifact tells us how big the real cost is and feeds the Phase-1 syntax
design.

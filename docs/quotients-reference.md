# Quotients — complete reference and simplification analysis

Everything the language and library currently do with quotients, in one
place. The companion `docs/conventions/quotients.md` is the *how-to* (which
short form to write); this file is the *what-and-why* — the full surface, the
auto-prover machinery behind it, the cases it still can't express, and an
honest diagnosis of where the design has accreted bloat plus directions for a
smaller, more systematic replacement.

The bloat is real: there are **three** ways to introduce a class, **seven**
overlapping ways to eliminate one, and **two** directions between classes and
representatives each with a verbose form, a short form, *and* an auto-prover
bridge — most of which ultimately bottom out in the same two kernel
operations. That redundancy is the argument that a smaller core exists.

---

## 1. The object

`Quotient(T, R)` is `T` modulo a relation `R : T → T → Proposition` — the type
of equivalence classes. `Quotient.mk(x)` is the class `[x]`. The defining
fact is that `mk` is surjective and respects `R`: two representatives give the
same class exactly when they are `R`-related (for `R` an equivalence).

Everything else is how you (a) build a class, (b) use a class, and (c) move
between "the classes are equal" and "the representatives are related".

---

## 2. Kernel primitives (the trusted core)

Five axioms (`library/axioms.math`) plus a small derived layer
(`library/Logic/quotient.math`). Users should essentially never name these;
they are the intermediate representation the surface forms compile to.

| Primitive | Kind | Signature (informal) | Role |
|---|---|---|---|
| `Quotient.{u}` | axiom | `(T : Type u) → (R : T→T→Prop) → Type u` | the quotient type |
| `Quotient.mk.{u}` | axiom | `(T)(R)(x : T) → Quotient(T,R)` | class of a representative |
| `Quotient.sound.{u}` | axiom | `(T)(R)(x)(y) → R(x,y) → mk x = mk y` | related reps ⇒ equal classes |
| `Quotient.lift.{u,v}` | axiom | `(T)(R)(U)(f : T→U)(h : respect) → Quotient(T,R) → U` | eliminate to any `U` |
| `Quotient.induct.{u}` | axiom | `(motive)(atRep) → (q) → motive(q)` | eliminate to a `Prop` family |
| `Quotient.compute.{u,v}` | derived | `lift(f,h,mk x) = f(x)` | the β/ι rule for lift |
| `Quotient.exact.{u}` | derived | `{equiv} → (x)(y) → mk x = mk y → R(x,y)` | equal classes ⇒ related reps |
| `Quotient.induct_two/_three` | derived | n-ary induction | binary/ternary laws |
| `IsEquivalenceRelation.{u}` | derived | `(T)(R) → Prop` (refl/symm/trans bundle) | premise of `exact` |

Notes that matter for the design:
- **`sound` and `exact` are inverses.** `sound` needs nothing; `exact` needs an
  `IsEquivalenceRelation(T,R)` witness (so it's *derived*, not an axiom).
- **`lift` and `induct` are the same elimination** at different universes
  (`lift` to data `U`, `induct` to a `Prop` motive). `induct_two/_three` are
  just nested `induct`.
- **`compute`** is what makes a `lift`/`mk(g rep)` definition reduce on a
  concrete class — the reason `construction` forms are transparent and most
  operations are defeq on representatives.

---

## 3. The user surface

### 3a. Introduction — making a class `[x]`

Three forms, increasing in readability:

1. **Verbose** — `Quotient.mk(T, R, rep)`. Always works; names the axiom.
2. **Short** — `Quotient.mk(rep)`. `T` from `rep`'s type, `R` from the expected
   type. Has a *convertibility boundary* (§6): it doesn't fire as an operand
   of `-`/`+`/`*`/`=`/`≤`, inside polymorphic-function args, or in
   `transport_proposition`'s carrier slot; the workaround is an ascription
   `(Quotient.mk(rep) : T)`.
3. **`construction`** — `construction Name(args) : T := Quotient.mk(...)`.
   A *transparent* definition (δ-reduces to `mk`), so it's def-equal to the
   underlying class but reads as math: `Rational.fraction(n, d)` instead of
   `Quotient.mk(RationalRepresentative.make(n, d))`. The preferred public form.

### 3b. Elimination — using a class

This is where the bloat concentrates. **Seven** surface forms, all of which
compile to `Quotient.lift` or `Quotient.induct` (i.e. the recursor) with motive
inference:

1. **`Quotient.lift(f, h, q)`** (verbose/short) — eliminate to data `U`.
2. **`definition F by representatives rep ↦ body well_defined by proof`** —
   the preferred way to *define a function out of a quotient*. Parse-time sugar
   (`parser.cpp` `parseDefineByRepresentatives`) → `(x) ↦ lift((rep) ↦ body,
   proof, x)`. **Unary and binary** (binary → nested lift +
   first/second respect proofs). The `well_defined` proof may be the bare
   equivalence `R(g x, g y)` (auto-wrapped, see §4).
3. **`Quotient.induct(atRep, q)`** / **`induct_two`** / **`induct_three`** —
   eliminate to a `Prop` motive (the motive can be inferred from the goal).
4. **`by_representatives x as <pat>, y as <pat>, … => body`** — the preferred
   "WLOG pick representatives" form for *proving* something about classes.
   Desugars to nested quotient-`cases`. Pattern is a tuple `⟨n, d⟩`,
   constructor, or bare name.
5. **`cases x { | <pat> => … }`** — direct destructure; the one-scrutinee
   primitive `by_representatives` builds on.
6. **`cases x refining h1, h2 { … }`** — destructure *and* refine in-scope
   hypotheses about `x` to the representative form. This is what lets a
   hypothesis-threading `induct` (motive `… → P(x)`) become a `cases`.
7. **`take x as <pat> : T;`** / **`suppose P as <pat>;`** — statement-level
   intro that immediately destructures (dispatches to quotient-`cases` when
   `T`/`P` is a quotient).

Every one of 1–7 is "apply the recursor; infer the motive". They differ only
in surface ergonomics and whether the target is data or a proof.

### 3c. Between classes and representatives — the two directions

- **`sound` direction** (`R(x,y) ⇒ mk x = mk y`): write `Quotient.sound(x,y,p)`,
  *or* supply the bare equivalence `R(x,y)` where `mk x = mk y` is expected and
  the elaborator auto-wraps `sound` (§4).
- **`exact` direction** (`mk x = mk y ⇒ R(x,y)`): write `Quotient.exact(x,y,h)`,
  *or* let the auto-prover discharge a goal `R(a,b)` from an in-scope
  `mk a = mk b` fact (the exact-bridge, §4).

---

## 4. The auto-prover machinery (so you never name `sound`/`exact`)

Two strategies in `elaborator.cpp`, mirror images:

- **sound-coercion** — `tryQuotientSoundForClassEquality`: a `term : R(x,y)`
  supplied where `mk x = mk y` is expected is wrapped as
  `Quotient.sound(T,R,x,y,term)`. Fires in `coerceToExpectedTypeViaDiff` and at
  lambda bodies; this is what makes `well_defined by <bare-equivalence proof>`
  work, and what kept the `by representatives` definitions free of `sound`.
- **exact-bridge** — `tryQuotientExactBridge` (a last-resort `autoProveClaim`
  strategy): goal `R(a,b)` closes from a local `mk a = mk b` fact via
  `Quotient.exact`. It scans local equality hypotheses (non-throwing
  `Equality` head-peel), peels each endpoint to `mk(T,R,rep)` through WHNF
  (seeing through `construction`s and coercions), checks the goal is `R(a,b)`,
  resolves the `IsEquivalenceRelation` instance, assembles the term, and
  type-checks it before returning. A flipped fact (`mk b = mk a`) is caught via
  the symmetry-flip retry recursing onto `R(b,a)`.
  - **`resolveEquivalenceInstance`** handles both parameter-free instances
    (Integer/Rational/Real/PAdic reps) and parameterized ones
    (`IntegerMod.equivalence(m)` for `CongruentModulo(m)`) by opening the
    instance's parameter Pis as metavariables and unifying its
    `(carrier, relation)` against the actual ones.

The symmetry between these two strategies — one wraps `sound` when an equality
is *expected*, the other applies `exact` when a relation is *the goal* — is a
strong hint that they should be **one** bidirectional mechanism (§8).

---

## 5. The instance layer

`exact` needs `IsEquivalenceRelation(T, R)`. Each quotient registers one via
`instance X.equivalence` into the canonical-instance registry, keyed by
`(structureName="IsEquivalenceRelation", carrierHeadName)`. The elaborator
resolves it during normal implicit-argument inference and (now) inside the
exact-bridge. Parameterized instances (the modulus/ring/coset) are solved by
unification.

This layer is where the impedance lives: the registry is keyed by the
*carrier head constant*, which is ambiguous when one carrier type carries
several relations, and which mismatches when the carrier is itself an
application (`Ring.carrier(CommutativeRing.ring(c))`).

---

## 6. Convertibility boundaries — what still names a primitive, and why

These are the sites that, as of this writing, still spell a `Quotient.*`
primitive. They are the friction map and the test set for any redesign.

| Site(s) | Primitive | Why it resists the sugar |
|---|---|---|
| `Rational`/`Real.IsNonneg` | `lift` | the definition is `opaque` (deliberate — the `IsNonneg` abstraction boundary); `by representatives` produces a transparent def |
| `coefficientOf`, `reciprocal_at_integer` | `lift` | **multi-argument**: the quotient arg is not the sole argument, so the one-argument `by representatives` can't express "lift over *this* arg" |
| `RingModulo`/`ComplexNumber` embedding | `exact` | goal stated over `Ring.divides`/`Polynomial.ring(r)` while the fact's `mk` relation is `CongruentModulo` over `CommutativeRing.ring(c)` — needs **carrier defeq**, not syntactic unify |
| ~~`Algebra` second/third isomorphism~~ | ~~`exact`~~ | **CLEARED** — the exact-bridge now also consults *local* `IsEquivalenceRelation` hypotheses, so the locally-bound `Group.SameCoset.is_equivalence` is found |
| `Algebra` quotient_group / isomorphism maps | `lift` | parameterized group quotients; same carrier-application + local-instance issues as above |

The "short form doesn't fire as an operand / needs an ascription" caveat (§3a)
is a sixth boundary — a recurring papercut rather than a blocked site.

---

## 7. Why it feels bloated

Counting the surface against the core:

- **2 core operations** (`mk`, and the recursor `lift`≈`induct`) +
  **2 facts** (`sound`, `exact`, which are inverse and both determined by `R`).
- **3 intro forms** over `mk` (verbose, short, `construction`).
- **7 elimination forms** over the recursor (`lift`, define-by-reps,
  `induct`/`_two`/`_three`, `by_representatives`, `cases`, `cases refining`,
  `take`/`suppose`) — distinguished only by data-vs-prop target and surface
  ergonomics.
- **2 directions × 3 mechanisms** for class↔rep (`sound`/`exact`, each with
  verbose + short + an auto-prover coercion/bridge).
- A **fragile convertibility boundary** documented with many caveats, plus a
  string of one-off elaborator fixes the sugar required (the `closeBack` of a
  resolved instance, WHNF-ing a motive codomain before closing, the
  dependent-carrier `liftBoundVariables`, the arm-body coercion against a
  WHNF'd expected type, …).

None of these is wrong; each was added to clear real friction. But the *ratio*
— a dozen surface forms and two auto-prover strategies over two core operations
— is the tell that the abstractions don't yet factor cleanly.

---

## 8. Toward a smaller design

Directions, roughly in order of leverage. Each is a hypothesis to be validated,
not a committed plan.

1. **One elimination mechanism.** `lift`, `induct`, `induct_two/_three`,
   `by_representatives`, `cases`, `take`/`suppose` are all "apply the recursor,
   infer the motive, destructure the rep". Collapse to a single internal
   `eliminate(scrutinees, motive?, arms)` with two surface skins: an
   *expression* form (today's `by_representatives`/`cases`) and a *definition*
   form (today's `by representatives … well_defined`). Drop the n-ary `induct_*`
   (nesting is automatic) and the verbose `lift`/`induct` from user space.

2. **`mk`/`lift`/`sound`/`exact`/`induct` become pure IR.** Make `construction`
   (intro) and the unified eliminator (elim) the *only* names users write.
   Everything in §6 that still spells a primitive is then, by definition, a
   gap in the eliminator — a finite, enumerable to-do, not an open-ended
   convention.

3. **One bidirectional class↔rep bridge.** Replace the separate
   sound-coercion and exact-bridge with a single rule driven by the registered
   equivalence: *a goal/term of type `R(x,y)` and one of type `mk x = mk y` are
   interconvertible*, applied wherever a coercion or a claim needs it, in either
   direction, with the symmetry flip folded in. This removes the asymmetry
   between "expected equality" and "goal relation" that currently needs two
   code paths.

4. **Carrier-defeq instance resolution, keyed by the quotient type.** Re-key
   the equivalence registry by the *quotient* (or normalize the carrier) and
   resolve via defeq rather than syntactic unification. This is what unblocks
   the `RingModulo`/`ComplexNumber` impedance in §6 uniformly, and would also
   let the exact-bridge consult **local** `IsEquivalenceRelation` hypotheses
   (the `SameCoset` case) the same way.

5. **A single `quotient` declaration.** Today each new quotient type scatters a
   carrier, a relation, an `IsEquivalenceRelation` instance, a `construction`
   intro, and per-operation `by representatives` definitions across a module.
   A `quotient T modulo R by <equiv proof>` declaration could generate the
   intro name, register the instance, and expose the eliminator — so a new
   quotient is *one* declaration and the boilerplate (and its bugs) lives in
   one place. The number-tower (`Integer`/`Rational`/`Real`/`PAdic`) and the
   algebraic quotients (`IntegerMod`/`RingModulo`/quotient groups) would all
   instantiate the same declaration, which is the real test of whether the
   abstraction is right.

**Spike result (the "one bidirectional bridge" experiment).** Unifying the
sound-coercion and exact-bridge plumbing was prototyped: the three `Quotient.mk`
peelers collapsed to one `peelQuotientClass`, and the exact-bridge gained a
**local-instance fallback** (consult local `IsEquivalenceRelation` hypotheses
when the registry has none) — which cleared the Group isomorphism `exact`
sites above. But it came out **code-neutral** (the dedup was offset by the new
capability), and it did **not** touch the `RingModulo`/`ComplexNumber`
residue, because that block is a *goal-shape defeq* mismatch
(`Ring.divides(…, difference)` vs `CongruentModulo(…)` over
`CommutativeRing.ring(c)`), orthogonal to merging the two bridges. Lesson: the
class↔rep machinery is roughly **fixed-size** — consolidation buys capability,
not a smaller bridge. The leverage for the residue is **goal-shape / defeq
robustness** (and the bigger §8 #1/#5 reworks), not more bridge unification.

The acid test for any of these: it should make the §6 table *shrink* (fewer
blocked sites, fewer caveats) while *removing* surface forms, not adding them.

---

*Status when written: user-space CIC `Quotient.*` leaks are down to the §6
residue; the achievable `exact`/`lift`/`induct` sweeps are complete (see
`less_cic_plan_status` memory and `git log` for the per-site history). The
remaining work is the feature gaps in §6, which §8 argues are better addressed
by consolidation than by adding a sixth/seventh special case.*

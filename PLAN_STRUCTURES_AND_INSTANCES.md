# PLAN: Structure types + canonical instances (the abstraction-scaling prerequisite)

Working brief for an assistant session (Claude Code). Goal: make the
abstract-algebra layer ergonomic enough to *read like math*, and lay the one
piece of groundwork that makes a future category-theory layer feasible at
all — **without enlarging the trusted base and without abandoning the
reject-on-ambiguity design principle.**

This is the natural sequel to `PLAN_quotient_noise.md`. That plan reduces
noise in *concrete* proofs; this one reduces noise in *generic* proofs over
algebraic structures. Same invariant, same conventions: pick a stage, land
it, keep the build green, delete it when done.

## Why this matters (the problem, in current code)

The library already has concrete carriers and abstract algebra coexisting:
`Algebra/ring.math` defines `IsRing(carrier, add, zero, negate, multiply,
one)` as a predicate, each concrete type proves an instance
(`Integer.is_commutative_ring`, etc. in `*/instances.math`), and concrete
lemmas consume generic ones (Rational's annihilation lemmas derive from
`Ring.zero_multiply`). **The coexistence works.** What does NOT yet read
like math is the cost of *consuming* a generic structure. Two leaks:

1. **Explicit instance + carrier threading.** Every generic lemma call
   passes the carrier and all operations and the instance proof by hand:
   `Ring.zero_multiply(carrier, add, zero, negate, multiply, one, ringProof, x)`
   — 7 ceremony arguments before the real one.

2. **Manual structure projection.** `IsRing` is a nested conjunction
   (`IsAbelianGroup ∧ IsMonoid ∧ distrib ∧ distrib`), so every generic proof
   opens by digging fields out of the tuple:
   ```
   let ⟨abelianAdd, _, _, distributivityRight⟩ := ringProof;
   let ⟨addGroupProof, _⟩ := abelianAdd;
   let ⟨addMonoidProof, _, _⟩ := addGroupProof;
   let ⟨_, addIdentityLeft, addIdentityRight⟩ := addMonoidProof;
   ```
   This is `O(hierarchy depth)` of positional plumbing per proof, and it
   gets monotonically worse for module-over-ring, algebra-over-field, and
   (the real motivator) category → functor → natural-transformation, where
   math is relentlessly structured-over-structured. If this isn't fixed,
   "reads like math" dies exactly at the abstraction levels where research
   math lives.

## What already exists (build on this)

- **Anonymous constructor `⟨…⟩`** already builds these instances
  (`Integer.is_ring := ⟨add_is_abelian_group, multiply_is_monoid, …⟩`) and
  **anonymous destructuring `let ⟨…⟩ :=`** already takes them apart. So the
  *term-level* machinery for records exists; what's missing is a named,
  inferable surface over it.
- **Single-constructor inductives** are the de-facto record type today:
  `Logic/sigma.math` (`Sigma`), `Logic/exists.math` (`Exists`). A `structure`
  is exactly a single-constructor inductive with named projections — so this
  desugars to machinery the kernel already checks.
- **Universe polymorphism** `.{u, v}` works (see `Logic/quotient.math`),
  though it is comparatively under-exercised and has known elaborator holes
  (the `induct_three` universe fight; `registerGenericRewriteLemma` skips
  universe-parametric theorems — see `TODO.md`).
- **The coercion registry** (`elaborateCoercionDeclaration`, ~line 967 in
  `elaborator.cpp`) already implements **reject-on-ambiguity**: a diamond is
  refused, not silently resolved. The instance mechanism below MUST reuse
  this stance — it is the project's design principle, and it is *cleaner*
  than Mathlib's definitional-diamond juggling. Do not implement open-ended
  backtracking instance search.

## The invariant (unchanged from the other plans)

Every item is surface desugaring or elaboration/inference. None adds kernel
reasoning power. A `structure` is a single-constructor inductive; a named
projection is recursor application; an inferred instance is an argument the
elaborator fills with a term the kernel rechecks. After each stage:

```
make -j 16 library
./kernel
```

For Stages 1–2, the emitted kernel term for a touched theorem must be
identical to (or a trivially-equal rearrangement of) today's. For Stage 3,
the inferred instance argument must be the *same* instance term the user
writes by hand today — diff to confirm.

---

## Stage 1 — `structure` types with named projections

**Replaces the nested-`∧` encoding's projection plumbing. Pure surface over
single-constructor inductives.**

Add a `structure` declaration that desugars to a single-constructor
inductive plus named projection functions. Target:

```
structure IsMonoid.{u}
        (carrier : Type(u))
        (operation : carrier → carrier → carrier)
        (identity : carrier) where
  associative   : (x y z : carrier) → operation(operation(x, y), z)
                                       = operation(x, operation(y, z))
  identityLeft  : (x : carrier) → operation(identity, x) = x
  identityRight : (x : carrier) → operation(x, identity) = x
```

- `IsMonoid.associative(monoidProof)` etc. become the projection functions
  (recursor applications under the hood). This removes the positional
  `let ⟨_, idL, idR⟩ :=` cascade in favor of named access.
- Anonymous `⟨…⟩` construction must keep working (it already does for
  inductives), so `Integer.multiply_is_monoid := ⟨…, …, …⟩` is unchanged.
- For nested structures (`IsRing` has an `IsAbelianGroup` field), projection
  chains compose: `IsRing.additive(r)` then `IsAbelianGroup.group(...)` etc.
  Consider **flattened re-projections** (`IsRing.addIdentityLeft(r)`) as
  convenience definitions so consumers don't manually walk the hierarchy —
  this is the actual ergonomic win; the bare nested projections alone just
  rename the plumbing.
- Soundness: single-constructor inductive + recursor; kernel unchanged.
- Migration order: `IsMonoid` → `IsGroup` → `IsAbelianGroup` → `IsRing` →
  `IsCommutativeRing` → `IsField`, in `Algebra/`. Update the `*/instances.math`
  consumers and the `Algebra/*_lemmas.math` generic proofs as you go. Build
  green after each type.
- Acceptance: the four-line destructure at the top of `Ring.zero_multiply`
  (`Algebra/ring_lemmas.math`) collapses to named projections; emitted term
  unchanged; build + kernel green.
- Effort: medium. Risk: low–medium (parser + recursor-projection codegen).
- **Do this first — Stage 3 depends on having real structure types.**

## Stage 2 — bundled structures (carrier + operations inside the structure)

**Removes the carrier/operation threading (leak #1). Design decision
required: bundled vs. unbundled. Discuss before building.**

Today operations are *parameters* of `IsRing`, so they're threaded at every
call. The standard fix is a **bundled** structure carrying its data:

```
structure Ring.{u} where
  carrier  : Type(u)
  add      : carrier → carrier → carrier
  zero     : carrier
  negate   : carrier → carrier
  multiply : carrier → carrier → carrier
  one      : carrier
  isRing   : IsRing(carrier, add, zero, negate, multiply, one)
```

Then `Ring.zero_multiply(R, x)` instead of the 7-arg form.

**Tradeoff to decide (this is the human call):**
- *Unbundled* (today: operations as parameters) keeps statements close to
  the math-on-paper form `multiply(zero, x) = zero` with `multiply` a plain
  function, and avoids `R.carrier` projections littering proofs. Good for
  concrete reasoning; bad for genericity (threading).
- *Bundled* removes threading and is what makes generic lemmas short, but
  pushes `R.add` / `R.carrier` accessors into statements, which is its own
  noise and is *less* paper-like.
- *Mathlib uses a hybrid* (bundled typeclasses + unbundled notation via
  instance resolution). The clean math-verify answer is probably: keep
  unbundled predicates as the *definitional* core (Stage 1), add bundled
  structures as a *consumer-facing* layer, and let Stage 3's inference hide
  the threading rather than bundling to avoid it. **Recommendation: do NOT
  bundle as the primary representation; prefer Stage 3 inference over Stage 2
  bundling.** Bundle only if Stage 3 inference proves insufficient. Flag this
  decision; don't unilaterally bundle.
- Effort: medium. Risk: medium + representation lock-in. **Needs sign-off.**

## Stage 3 — canonical instance inference (the real ergonomic unlock)

**Removes instance + carrier threading the principled way. Reuses the
coercion registry's reject-on-ambiguity stance.**

Add implicit instance arguments resolved from a **canonical-instance
registry**, NOT by open-ended search:

```
instance Integer.is_commutative_ring   -- registers Integer ⇒ IsCommutativeRing(Integer, …)
```

- Mark the instance/operation arguments of generic lemmas implicit (`{…}`),
  so `Ring.zero_multiply(x)` infers carrier + ops + `ringProof` from the type
  of `x` and the registry.
- Resolution rule (mirror the coercion registry exactly): at most one
  registered instance per (structure, carrier) key. **Two candidate
  instances ⇒ REJECT with a diagnostic**, never guess and never backtrack.
  This is the design principle, and it sidesteps Mathlib's instance-diamond
  coherence burden entirely. Reuse the diamond-rejection logic from
  `elaborateCoercionDeclaration` (~line 1063 in `elaborator.cpp`).
- This is the consumer of Stage 1: inference needs real structure types with
  known projection/field shape to unify the instance against the goal.
- Connect to existing auto-prover work: the `TODO.md` "Hammer unification /
  fact stream" already wants library lemmas in a cost-ranked stream, and
  notes `registerGenericRewriteLemma` currently **skips universe-parametric
  theorems** — i.e. exactly the generic algebra lemmas. Closing that
  universe-instantiation gap is the same work as making generic lemmas
  indexable. Land instance inference and the polymorphic-lemma indexing
  together if practical.
- Soundness: the inferred instance term is identical to what the user writes
  by hand today; the elaborator is just filling an implicit. Diff the emitted
  term for `Rational`'s annihilation lemmas before/after — must match.
- Acceptance: a generic-lemma call site in `Rational/ring.math` drops its
  carrier/op/instance arguments; build + kernel green; emitted term identical.
- Effort: medium–large. Risk: medium (unifier extension + universe-arg
  inference). **Highest leverage item in this plan.**

---

## Category theory: what this plan unlocks, and what it does NOT

This plan is the *prerequisite* for a category-theory layer, not the layer
itself. With Stages 1 + 3 landed, category theory becomes *possible*; three
issues remain and should be separate future work, flagged here so the
session does not wander into them:

1. **Universe handling must mature first.** Categories, functor categories,
   and Yoneda need fluent universe polymorphism. The library is mostly
   `Type(0)` today and the elaborator has known universe-inference holes
   (`TODO.md`). Category theory will stress the least-tested part of the
   elaborator. Harden universe inference (start with the `induct_three`
   fight and polymorphic-lemma indexing) *before* attempting categories.

2. **Coherence automation is an open philosophical decision.** Category
   theory leans on automation (Mathlib's `aesop_cat`, coherence simp sets)
   to discharge diagram-chase / coherence obligations no one writes by hand.
   This is in tension with "minimal hidden automation." Someone has to decide
   how much coherence automation math-verify is willing to host. Do not
   settle this in code unilaterally — it touches the core philosophy.

3. **Structure-over-structure depth.** Functor = structure over two
   categories; natural transformation = structure over two functors. Stage 1
   named projections + Stage 3 inference are what keep this readable; without
   them it is positional-destructure hell. This plan is necessary but the
   depth should be validated on a small real example (e.g. formalize `Cat` of
   small categories, one adjunction) before committing to a full layer.

## Recommended sequencing

- **Stage 1 first** (structure types) — everything else depends on it.
- **Stage 3 next** (canonical instance inference) — the real unlock; pairs
  naturally with the `TODO.md` polymorphic-lemma indexing item.
- **Stage 2 (bundling) only if needed**, and only with sign-off — the
  recommendation is to prefer Stage 3 inference over bundling.
- **Category theory is downstream of all three + universe hardening +
  the coherence-automation decision.** Not in scope for this brief.

## Decisions for a human (do not settle these in code alone)

- Bundled vs. unbundled structures (Stage 2). Recommendation: unbundled core
  + inference, not bundling.
- How much coherence automation the project will host for category theory.
- Whether reject-on-ambiguity for instances is acceptable everywhere, given
  it forbids some legitimate multi-instance setups Mathlib allows. (It is
  consistent with the existing coercion stance, so the default is yes.)

## Verify after every change

```
make -j 16 library
./kernel
```

Both green; for Stages 1 and 3 the emitted kernel term for at least one
touched generic lemma is unchanged. If a stage can't keep both green, leave
it half-done in a branch rather than weakening the kernel or the
reject-on-ambiguity principle to force it through.

---

## Stage 0 — solidify leading-implicit insertion (PREREQUISITE for Stage 3)

**Evidence-driven. Stage 3 (instance inference) marks operation/instance
arguments implicit and fills them from a value's type — but the elaborator
does not reliably *insert* a leading implicit today, so instance inference
would sit on cracked ground. The cases below were all hit live while
building `library/IntegerMod/` (Z/(n) and F_p) on 2026-05-29, where
operations were parameterized by `{modulus : Natural}`.**

The common shape: a function `f {m : Natural} (x : C(m)) … : …` fails to get
`{m}` inserted, so the first *explicit* argument is mis-bound to the `m`
slot, producing `expected type: Natural / actual type: C(m)` (or the operand
type prints as `<unknown>`). It works only when an expected type or a
clearly-typed sibling pins `m` first. Minimal repros (carrier
`IntegerMod(modulus) := Quotient(Integer, Integer.CongruentModulo(modulus))`,
op `IntegerMod.add {modulus} (x y : IntegerMod(modulus))`):

1. **Bare implicit-leading function as a higher-order argument.**
   ```
   IsMonoid(IntegerMod(m), IntegerMod.add, IntegerMod.zero(m))
   --> kernel: Application: argument type does not match Pi domain
   --     expected type: Natural   actual type: IntegerMod modulus
   ```
   The implicit is never inserted; `IsMonoid`'s `operation` slot receives
   `IntegerMod.add` with `{modulus}` still open. **Workaround used:** wrap in
   a lambda that pins the carrier — `function (a b : IntegerMod(m)) => a + b`
   (the `+` *operator* dispatch does insert the implicit; the bare name does
   not). This is the direct blocker for Stage 3: a registry can't help if the
   inferred instance/op term can't be handed to the generic lemma's implicit
   slot in the first place.

2. **Direct call whose first explicit arg is an implicit-carrying constant.**
   `IntegerMod.zero {modulus} : IntegerMod(modulus)` as the first argument:
   ```
   IntegerMod.add(IntegerMod.zero, x)
   --> expected type: Natural
   --  actual type:   Π(modulus : Natural). IntegerMod modulus
   ```
   `IntegerMod.zero` (implicit open) is bound to `add`'s `{modulus}` slot.
   **Workaround used:** make nullary constants take `modulus` *explicitly*
   (`IntegerMod.zero(modulus)`), and state the law with the operator
   (`IntegerMod.zero(m) + x = x`) rather than `IntegerMod.add(IntegerMod.zero(m), x)`.

3. **Bottom-up operand inference under an operator.**
   ```
   IntegerMod.negate(x) + x        -- x : IntegerMod(m)
   --> expected type: Natural   actual type: IntegerMod modulus
   ```
   When `+` infers its left operand's type bottom-up, `IntegerMod.negate(x)`
   (implicit open) mis-binds `x` to the `{modulus}` slot — even though the
   *same* call succeeds inside `IntegerMod.subtract` where an expected type
   flows inward. **Workaround used:** make `negate` take `modulus` explicitly.

   Net resolution in the shipped code: `add`/`multiply` stay implicit (so the
   `+`/`*`/`-` operators work for end users), while `zero`/`one`/`negate`/
   `subtract` take `modulus` explicit, and instances pass the binary ops as
   `λ a b. a ∘ b` lambdas. That is a workaround, not a fix — Stage 3 needs the
   real fix so generic algebra can hand inferred ops to implicit slots.

**Acceptance for Stage 0:** all three snippets above elaborate with the
implicit inserted (first explicit arg binds to the first *explicit*
parameter), with no expected-type or sibling needed to disambiguate; the
emitted term is what the explicit-modulus form produces today. Re-run the
`IntegerMod` build with `add`/`multiply`/`zero`/`one`/`negate` all implicit
and confirm `instances.math` no longer needs lambda wrappers.

## Stage 0b — single `Quotient.induct` motive inference for parameterized quotients

**Also a Stage-2-of-the-quotient-plan blocker (`by_representatives`).** The
short forms `Quotient.induct_two` / `induct_three` infer their motive fine
for a parameterized quotient, but the **single** `Quotient.induct(atRep, q)`
(and bare `cases q`) does NOT when `q : C(param)` for a parameterized alias
`C`:
```
-- with x : IntegerMod(modulus):
Quotient.induct(function (a : Integer) => …, x)
--> expected type: Natural   actual type: Π(modulus:Natural). IntegerMod modulus
```
The verbose `Quotient.induct(Integer, Integer.CongruentModulo(modulus),
motive, atRep, x)` works (this is what `IntegerMod/ring.math` and `field.math`
use for every unary law). Two sub-issues, likely the same root cause —
the short-form T/R/motive recovery WHNF-unfolds `C(param)` too far:
  - it can't recover `R` from `IntegerMod(m)` (over-unfolds past
    `Integer.CongruentModulo` into the underlying `Integer.divides`
    *existential*, then tries to use `Exists` as the relation); the
    construction in `IntegerMod/operations.math` uses verbose
    `Quotient.{mk,lift,sound}` throughout for this reason;
  - the motive abstraction over a single scrutinee of parameterized-quotient
    type yields the mis-typed application above.

**Acceptance:** `Quotient.induct(atRep, x)` and `cases x { | a => … }` elaborate
for `x : IntegerMod(m)` with the motive inferred from the goal; rewrite the
unary laws in `IntegerMod/ring.math` back to the short form and keep the
build green.

(Both Stage 0 items are surface/elaboration only — no kernel change — and
each has a concrete green/red test in the shipped `IntegerMod` tree.)

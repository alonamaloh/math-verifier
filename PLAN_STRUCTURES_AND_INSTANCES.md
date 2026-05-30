# PLAN: Structure types + canonical instances (the abstraction-scaling prerequisite)

> **STATUS (2026-05-30): Stage 3 (concrete-carrier) LANDED; Stages 1, 2
> not built.**
> - **Stage 3 (canonical instance inference)** — landed for concrete
>   carriers. `instance <name>` registers a structure-predicate theorem as
>   the canonical instance for its `(structure, carrier)` pair
>   (reject-on-ambiguity, mirroring the coercion registry). A generic
>   lemma with implicit structure/operation/instance args has them filled
>   at a concrete call site from the registry, keyed by the carrier head;
>   the sibling operation/identity/inverse implicits are read off the
>   instance's type. Acceptance: `Test/instance_inference_test.math`
>   (`instance Integer.add_is_group` + `integer_cancel` with zero ceremony
>   args). See CLAUDE.md "Canonical instances".
>   **Follow-on (not built):** *local-instance search* — resolving a
>   structure-typed implicit from an in-scope hypothesis — is what would
>   let the existing GENERIC consumers (e.g. `Ring.zero_multiply` calling
>   `Group.cancel_left` over an abstract carrier) also drop their ceremony
>   args. v1 also restricts to non-parameterized (concrete-carrier)
>   instances. Prereqs F1 / Stage 0 (leading-implicit insertion) were
>   already landed.
> - **Stage 1 (`structure` keyword)** — NOT built. Per the 2026-05-29
>   evidence, single-constructor inductives already serve as record types
>   (`Algebra/ring_bundle.math`), and "reads like math" ranks instance
>   inference (Stage 3, touches every use) above the keyword (touches only
>   declarations). Stage 3 did not need it.
> - **Stage 2 (bundling)** — NOT built as a primary representation
>   (`ring_bundle.math` already provides a bundled `Ring` ad hoc); the
>   principle favours unbundled core + Stage 3 inference.
>
> The rest of this file is the original brief, kept for context.



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

  **NOTE (2026-05-29): the stated acceptance site is stale — pick a new
  one before building.** A survey of the library found **no** verbose
  hand-citations of generic `Ring.*` / `Group.*` lemmas: the `ring` /
  `field` tactics already fill the carrier/op/instance arguments
  internally, and the per-carrier wrappers were removed in favour of
  `:= ring`. So leak #1's threading pain is currently *hidden by the
  tactics*, and there is no existing `Rational/ring.math` call site for
  instance inference to simplify. H1 is still worthwhile as a
  *future-facing* feature (a later abstract-algebra / category-theory
  layer, or enabling hand-cited group/field lemmas that `ring` can't
  discharge — e.g. cancellation, inverse-uniqueness), but its immediate
  payoff is muted. Whoever picks this up should (a) choose a concrete
  target where the threading is actually written by hand — most likely
  the bundled `Ring` / `Polynomial` development in
  `Algebra/ring_bundle.math` + `Polynomial/*`, which threads `r : Ring`
  explicitly — and (b) write a fresh acceptance test, since the planned
  one no longer exists. F1 (leading-implicit insertion) — H1's
  prerequisite — is now landed, so the ground is ready when a target is
  chosen.

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

**STATUS (2026-05-29): LANDED for repros #1 and #3; #2 (bare nullary
constant as an operator operand) deliberately out of scope.** Two
elaborator touchpoints, surface/elaboration only, no kernel change:

- **Direct calls / bottom-up operands (repros #2-as-a-call, #3).** The
  leading-implicit inference block in `elaborateExpression`'s
  `SurfaceApplication` path now engages even with a *null* expectedType
  when the head declaration carries `{…}` implicit binders —
  `inferLeadingArguments`'s forward unification recovers the implicit
  prefix from the explicit args' types (e.g. `IntegerMod.negate(x)`
  bottom-up under `+`). Failure falls through to positional application,
  so explicitly-passed implicits (`PAdicEquivalent(p, primality)`) still
  work.
- **Bare higher-order argument (repro #1).** The `SurfaceIdentifier`
  path now inserts a bare constant's leading implicits and solves them by
  backward unification against the expected type — so `IntegerMod.add`
  handed to `IsMonoid`'s `operation` slot elaborates without a lambda
  wrapper.

Result: `IntegerMod`'s `add`/`multiply`/`negate` are all implicit and
`instances.math` / `field.math` / `integer_mod_test.math` pass the bare
names directly (lambda wrappers gone). Regression coverage:
`library/Test/implicit_args_test.math` (`tagged_identity_no_expected`,
`tagged_identity_bare_higher_order`).

**Residual (repro #2 proper — left for a follow-up).** `zero`/`one`
remain explicit-`modulus`. As nullary values written bare as the LEFT
operand of an operator (`IntegerMod.zero + x`), they are elaborated
bottom-up with *no* expected type and *no* argument to carry the
modulus, so the bare constant's type stays `Π{m}. IntegerMod(m)` and
operator dispatch can't see the `IntegerMod` head. Fixing this needs
operand-ordering work (defer the left operand's implicit resolution
until the operator/right operand pins `m`), which is a deeper change
than the two touchpoints above. Documented in
`IntegerMod/operations.math`.

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

**STATUS (2026-05-29): the induct/cases half is DONE; one residual on
`Quotient.sound`/`lift` remains.** Re-tested empirically: the single
`Quotient.induct(atRep, x)` and bare `cases x { | a => … }` now infer
their motive correctly for the parameterized alias `IntegerMod(modulus)`
— the Pi-domain mismatch the plan recorded no longer reproduces (verified
on the elaborator both before and after the Stage 0 implicit-insertion
work, so an intervening fix already closed it). All six unary laws in
`IntegerMod/ring.math` were rewritten from the verbose explicit-motive
`Quotient.induct(Integer, Integer.CongruentModulo(modulus), motive,
atRep, x)` to the short `Quotient.induct(atRep, x)`; build stays green.
Short `Quotient.mk(rep)` also recovers `R` from the expected
`IntegerMod(modulus)` correctly.

**Short `Quotient.{mk,sound,lift}` for parameterized aliases — now also
DONE.** Two elaborator fixes (surface/elaboration only, no kernel change):
  - `desugarQuotientSound`'s expected-type branch used
    `closeOverLocalBinders` on `decomp.relation`/`carrierType`, but those
    are sub-expressions of the (already closed) `expectedType` — exactly
    as `desugarQuotientMk` uses them directly. Re-closing shifted the
    `modulus` BoundVariable (`closeAtDepth` bumps any index `>= depth`),
    leaking `kernel: internal: bare BoundVariable reached inferType`. For
    non-parameterized relations (bare `Constant`s, no BoundVariables) the
    extra close was a silent no-op, which is why only parameterized
    aliases tripped it. Fix: use `decomp.*` directly.
  - `desugarQuotientSound`'s proof-type fallback (hit when no expected
    type is propagated — e.g. a short `Quotient.sound` inside a short
    `Quotient.lift` respect handler) WHNF-ed the proof's type *first*,
    over-unfolding a Definition-headed relation
    (`Integer.CongruentModulo(modulus)` → `Integer.divides` → `Exists`)
    and recovering the wrong head. Fix: extract `R` structurally from the
    proof type as written (where `R` already appears applied to its two
    args) and only WHNF as a secondary attempt.

  `IntegerMod/operations.math` now uses the short
  `Quotient.{mk,lift,sound}` forms throughout. Regression coverage:
  `short_mk` / `short_sound` in `library/Test/integer_mod_test.math`,
  plus the whole `operations.math` construction (the short lift +
  inner-sound-without-expected-type path). **Stage 0b is fully closed.**

---

## Update (2026-05-29) — a bundled `Ring` was built and validated

The `Polynomial(R)` construction (generic polynomials over an arbitrary
ring) needed *some* way to thread a ring's data, and the planned Stage 3
instance inference wasn't available — so a **bundled `Ring` was built
directly** (`library/Algebra/ring_bundle.math`) and used as the
parameterization for the whole polynomial development
(`library/Polynomial/*`). This is exactly Stage 2, which the plan above
recommended *against* as a primary representation. Real evidence now
exists; the recommendation should be **revisited, not assumed**:

- **A `structure` keyword was NOT needed.** `Ring` is a single-constructor
  inductive (`Ring.make : (carrier : Type(0)) → (add : …) → … → IsRing(…) →
  Ring`), built with the machinery that already exists. Field projections
  are `definition Ring.add (r) … := cases r { | Ring.make(…) => add }`.
  This validates the plan's "single-constructor inductive *is* the record
  type" claim — Stage 1's keyword is sugar over what works today.

- **Flattened law projections are the real ergonomic win, and they're
  cheap to hand-write.** `Ring.add_associative`, `Ring.zero_add`,
  `Ring.distributivity_left`, … (all 11 IsRing laws, plus derived
  `Ring.negate_zero` / `Ring.zero_multiply_left` / `Ring.multiply_zero_right`
  / `Ring.add_four_swap`) are each a few-line `let ⟨…⟩ := Ring.is_ring(r)`
  destructure. No new elaborator feature; `Ring.<law>(r, …)` reads clean.
  This is the "flattened re-projections" Stage 1 flagged as the actual
  payoff — confirmed, and obtainable without the `structure` keyword.

- **Bundling did NOT make statements unbearably noisy.** The feared
  `R.carrier` / `R.add` accessors (`Ring.carrier(r)`, `Ring.add(r, …)`)
  appear throughout, but the proofs still read as math because every law
  threads a single explicit `r : Ring`. Verbosity is real but mechanical.

- **Explicit `r : Ring` sidestepped the Stage 0 implicit-insertion bug.**
  Because operations take `r` *explicitly*, instances compose them
  directly (`IsMonoid(…, Polynomial.add(r), Polynomial.zero(r))`) with **no
  lambda wrappers** — the workaround the IntegerMod build needed (see Stage
  0). A bundled-but-explicit representation is a pragmatic way to get
  genericity *now* without first landing Stage 0 + Stage 3.

- **Codegen caveat (Stage 1 relevance).** Dependent field projections —
  where the result type mentions an earlier field, e.g. `Ring.add(r) :
  Ring.carrier(r) → Ring.carrier(r) → Ring.carrier(r)` — must be written
  with `cases r { … }`, NOT the pattern-match-definition form
  `| Ring.make(…) => …`. The latter's codegen does not build the dependent
  motive. A `structure` keyword (Stage 1) would need to emit the `cases`
  form for projections, not the pattern-match form.

**Net:** Stage 2 bundling is more viable than the plan assumed — it carried
an entire generic ring construction. The open question is no longer "does
bundling work" (it does) but "do we *also* want Stage 3 inference to hide
the `r` threading." A bundled core + Stage 3 inference (rather than Stage 3
*instead of* bundling) now looks attractive. Decision still belongs to a
human; this is evidence, not a verdict.

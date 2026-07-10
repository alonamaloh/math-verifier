# PLAN_KERNEL_EXPORT Stage-2 audit — quotient primitive mapping (2026-07-10)

The exact correspondence between our quotient primitives and Lean's, and
the export strategy that preserves the one definitional rule our kernel
implements. Reviewed facts, with the load-bearing decision flagged for the
Stage-3 exporter.

## Our side (what exists today)

Declared in `library/axioms.math` as five ordinary axioms, all with
**explicit** arguments:

| declaration | universe params | type |
|---|---|---|
| `Quotient.{u}` | u | `∀ (T : Type u). (R : T → T → Proposition) → Type u` |
| `Quotient.class_of.{u}` | u | `∀ (T : Type u) (R). T → Quotient(T, R)` — 3 value args |
| `Quotient.equivalent_implies_equal.{u}` | u | `∀ (T) (R) (x y : T). R(x, y) → class_of(T,R,x) = class_of(T,R,y)` |
| `Quotient.lift.{u, v}` | u, v | `∀ (T) (R) (U : Type v). (f : T → U) → (∀ x y. R(x,y) → f(x) = f(y)) → Quotient(T,R) → U` — 6 value args |
| `Quotient.induct.{u}` | u | `∀ (T) (R). (motive : Quotient(T,R) → Proposition) → (∀ x. motive(class_of(T,R,x))) → ∀ q. motive(q)` |

The kernel's **complete** quotient coupling is one WHNF rule
(`src/kernel/kernel.cpp` ~1418, name-keyed to `Quotient.lift` /
`Quotient.class_of` with arities 6/3):

```
Quotient.lift(T, R, U, f, h, Quotient.class_of(T, R, x))  ↝  f(x)
```

`Quotient.induct` is a plain axiom to the kernel — **no ι-style reduction
on `induct` exists, and the full library verifies green without one**
(that is the confirmation §C of the plan asked for; everything else —
`induct_two`, `induct_three`, `Quotient.compute` — is derived in
`library/Logic/quotient.math`, with `Quotient.compute` proved by
`reflexivity` through the WHNF rule).

## Lean's side (what a checker validates)

An external checker treats `Quot`, `Quot.mk`, `Quot.ind`, `Quot.lift` as a
special declaration kind (`quot`). It does **not** trust the exported
types: it validates them against hard-coded expected signatures
(type_checking book ch. 9; nanoda does exactly this), and it requires the
environment to already contain an `Eq` inductive of Lean's exact shape,
because the expected signature of `Quot.sound`-adjacent machinery is built
from it:

```
Quot      : {α : Sort u} → (α → α → Prop) → Sort u
Quot.mk   : {α : Sort u} → (r : α → α → Prop) → α → Quot r
Quot.ind  : {α : Sort u} → {r} → {β : Quot r → Prop}
            → (∀ a. β (Quot.mk r a)) → (q : Quot r) → β q
Quot.lift : {α : Sort u} → {r} → {β : Sort v} → (f : α → β)
            → (∀ a b. r a b → f a = f b) → Quot r → β
Quot.sound (ordinary axiom)
          : {α : Sort u} → {r} → {a b : α} → r a b → Quot.mk r a = Quot.mk r b
```

Checker-side reduction: `Quot.lift f h (Quot.mk r a) ↝ f a` **and**
`Quot.ind h (Quot.mk r a) ↝ h a`. The checker having the extra `ind` rule
is monotone-safe (it accepts strictly more defeq than we certify;
acceptance never depends on a defeq check *failing*).

## The two mismatches a bare rename cannot fix

1. **Universe placement.** Ours quantify over `Type u` = `Sort (u+1)`;
   Lean's over `Sort u`. `Quotient.{u}` is `Quot.{u+1}` instantiated —
   expressible, but only as a *definition*, not by renaming the axiom
   (the checker validates the `quot` declarations' types **exactly**).
2. **The equality inductive.** Our `Equality (A : Type u) (x : A) : A →
   Proposition` is also `Type`-bound, so it cannot itself be exported as
   the `Eq` the quot-initialization check demands (`{α : Sort u} → α → α
   → Prop`); and `Quot.lift`/`Quot.sound` speak Lean's `Eq` while our
   `lift`/`equivalent_implies_equal` speak our `Equality`. Distinct
   inductives, not defeq.

## The mapping (decision for Stage 3)

Export a small **quotient prelude**, then our five names as ordinary
**transparent definitions** over it. Nothing in the trusted kernel
changes; this is exporter-side only.

1. Emit a Lean-shaped `Eq : {α : Sort u} → α → α → Prop` inductive (fresh
   name, used only by the quot machinery — our own `Equality` continues
   to export as itself, an ordinary inductive).
2. Emit the four `quot`-kind declarations plus the `Quot.sound` axiom.
3. Emit two conversion bridges as ordinary definitions (each a one-case
   recursor application):
   - `eq_of_equality : Equality(A, a, b) → Eq a b`
   - `equality_of_eq : Eq a b → Equality(A, a, b)`
4. Emit the five `Quotient.*` names as transparent definitions:

   | ours | definition body (schematically) |
   |---|---|
   | `Quotient.{u} T R` | `Quot.{u+1} R` |
   | `Quotient.class_of T R x` | `Quot.mk R x` |
   | `Quotient.lift T R U f h q` | `Quot.lift f (λ x y hr. eq_of_equality(h x y hr)) q` |
   | `Quotient.induct T R motive base q` | `Quot.ind base q` |
   | `Quotient.equivalent_implies_equal T R x y hr` | `equality_of_eq(Quot.sound hr)` |

   Level arithmetic (`u+1` in constant universe arguments) is expressible
   in NDJSON 3.1.0 level expressions.

**Why the defeq trail replays.** Our only quotient defeq fact,
`lift(…, f, h, class_of(…, x)) ≡ f(x)`, becomes: δ-unfold `Quotient.lift`
and `Quotient.class_of` (transparent definitions), then the checker's
`Quot.lift f h' (Quot.mk r x) ↝ f x` rule fires — the respect argument
`h'` is not consulted by the reduction, so wrapping `h` in a conversion
is invisible to it. Every other use of the five names δ-unfolds to a
well-typed term. We rely on no other quotient defeq (verified above), and
the checker's surplus `Quot.ind` rule only widens acceptance.

**Rejected alternative:** renaming `Quotient.*` → `Quot.*` directly —
fails the checker's exact-signature validation on both mismatches above.

## Argument-order / implicitness sanity table

Binder implicitness is ignored by checking (Stage-3 note: we export all
binders explicit), so only *order* matters, and it matches everywhere:

| ours (explicit) | Lean (after implicits) | order |
|---|---|---|
| `class_of(T, R, x)` | `Quot.mk r x` — α implicit | T,R,x ↔ (α),r,x ✓ |
| `lift(T, R, U, f, h, q)` | `Quot.lift f h q` — α,r,β implicit | f,h,q in the same order ✓ |
| `induct(T, R, motive, base, q)` | `Quot.ind base q` — α,r,β implicit | motive ↔ β, base, q ✓ |
| `equivalent_implies_equal(T, R, x, y, proof)` | `Quot.sound proof` — α,r,a,b implicit | ✓ |

## What Stage 3 must additionally guarantee

- The prelude (`Eq`, quot block, bridges) is emitted **before** the first
  library declaration that mentions `Quotient.*`; `axioms.math` is at the
  bottom of the import graph, so emitting the prelude at the very front
  of the trail suffices.
- The exporter must **fail loudly** if the library ever grows a use of a
  `Quotient.*` name at an unexpected arity that its definition-wrapping
  cannot cover (impossible today — wrappers are total definitions and
  partial applications δ-unfold fine — but assert it anyway).
- `nat_extension: true` in nanoda's config is independent of all of this;
  the quot extension is always on in nanoda once the `quot` declarations
  appear.

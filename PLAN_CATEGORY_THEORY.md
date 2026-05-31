# PLAN_CATEGORY_THEORY.md — toward a category-theory layer (and the open structure questions)

Distilled (2026-05-31) from the now-removed `PLAN_STRUCTURES_AND_INSTANCES.md`,
keeping only the **forward-looking** material. The structure/instance
*implementation* that plan tracked is DONE and no longer needs a plan; this
file preserves the remaining open questions and the category-theory direction.

## What is already in place (so this isn't re-litigated)

- **Canonical instance inference** (`instance <name>`): a structure-predicate
  theorem is registered as the canonical instance for its `(structure,
  carrier)` pair, reject-on-ambiguity (mirrors the coercion registry). Keyed
  by carrier head; sibling operation/identity/inverse implicits read off the
  instance type. See CLAUDE.md "Canonical instances".
- **Parameterized-carrier instances + local-instance search**: instances over
  `IntegerMod(m)` / `Polynomial(r)` resolve with the leading parameter filled
  from the carrier's own argument; and a structure-typed implicit resolves
  from a *unique in-scope hypothesis* when the carrier is abstract
  (`elaborator.cpp:17374`, "Instance resolution (Stage 3 + local-instance
  follow-on)"). This is what lets a generic lemma consume another over its own
  abstract carrier with no ceremony.
- **Bundled `Ring`** (`Algebra/ring_bundle.math`): single-constructor
  inductive carrying carrier + ops + `IsRing`, with flattened law
  projections. Carried the entire generic `Polynomial` / `RingModulo`
  development. Stage-0 leading-implicit insertion is also landed.

So the "make generic algebra ergonomic" program succeeded *without* a
`structure` keyword and *without* bundling-as-primary. The two design
questions it left open, and the category-theory work it was a prerequisite
for, are below.

## Open design question 1 — a `structure` keyword (was Stage 1)

NOT built, deliberately: single-constructor inductives already serve as
record types, and the real ergonomic win (flattened, named projections like
`Ring.add_associative`) is obtained by hand-writing a few-line
`let ⟨…⟩ := Ring.is_ring(r)` per projection. A `structure` keyword would be
*sugar over what works today*.

Revisit it only if the projection plumbing becomes a genuine drag at the
abstraction depths category theory reaches (functor = structure over two
categories; natural transformation = structure over two functors). At that
depth the positional `let ⟨…⟩` cascades may justify the keyword. If built, it
must emit **`cases r { … }`** for dependent field projections (where a field's
type mentions an earlier field), NOT the pattern-match-definition form — the
latter's codegen does not build the dependent motive (learned building
`ring_bundle.math`).

## Open design question 2 — bundled vs. unbundled as primary (was Stage 2)

The bundled `Ring` exists and works, but as a *consumer-facing* layer over the
unbundled `IsRing` predicate, not as the primary representation. The standing
recommendation is **unbundled core + inference**, not bundling-to-avoid-
threading. Two pieces of newer evidence bear on this and should inform the
call:

- A **`CommutativeRing` / `Field` bundle** is now wanted independently (see
  `PLAN_READABILITY.md` E2): it lets a construction thread one value instead
  of `(r, commutativity, inverseExistence)`, and it is what lets
  `RingModulo.multiply` drop its explicit commutativity argument so that
  `PLAN_READABILITY.md` Track A1 can register a clean binary `*` operator.
- `PLAN_READABILITY.md` Track A (operators on parametrized ops, with the
  structure arg implicit) is precisely the "hide the `R.add` / `R.carrier`
  accessor noise" answer the bundling debate worried about. If A lands,
  bundled statements read as `x + y` and the anti-bundling argument weakens.

Net: decide bundled-vs-unbundled *after* `PLAN_READABILITY.md` A + E2 land,
with that experience in hand. Human call; reject-on-ambiguity stays.

## The category-theory layer itself (downstream of everything)

With instance inference + (if needed) a `structure` keyword in place,
category theory becomes *possible*. Three issues remain and are deliberately
separate future work:

1. **Universe handling must mature first.** Categories, functor categories,
   and Yoneda need fluent universe polymorphism. The library is mostly
   `Type(0)` and the elaborator has known universe-inference holes (the
   `induct_three` universe fight; generic/polymorphic-lemma indexing skipping
   universe-parametric theorems). Harden universe inference *before*
   attempting categories — it will stress the least-tested part of the
   elaborator.

2. **Coherence automation is an open philosophical decision.** Category theory
   leans on automation (Mathlib's `aesop_cat`, coherence simp sets) to
   discharge diagram-chase / coherence obligations nobody writes by hand. This
   is in tension with the project's "minimal hidden automation" stance.
   Someone must decide how much coherence automation the project will host.
   Do not settle this in code unilaterally — it touches core philosophy.

3. **Structure-over-structure depth.** This is what makes category theory the
   stress test for the structure/projection ergonomics above. Validate the
   depth on a small real example — e.g. formalize `Cat` of small categories
   and one adjunction — *before* committing to a full layer. If positional
   destructuring is painful there, that is the trigger to build the
   `structure` keyword (question 1).

## Suggested order if/when this is taken up

1. Land `PLAN_READABILITY.md` A + E2 (operators, `CommutativeRing`/`Field`
   bundle); then settle design questions 1 and 2 with that evidence.
2. Harden universe inference.
3. Decide the coherence-automation philosophy.
4. Prototype `Cat` + one adjunction; let that decide whether the `structure`
   keyword is worth building.

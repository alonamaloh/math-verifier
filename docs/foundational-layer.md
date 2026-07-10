# The foundational layer (the "assembly zone")

*Part of [PLAN_LESS_CIC_STYLE.md](../PLAN_LESS_CIC_STYLE.md), deliverable 0.1.*

## What this is

The overriding goal of the *less-CIC* effort is that a user writing
mathematics never needs to know the language is built on the Calculus of
Inductive Constructions. CIC is the substrate, not the surface — like
assembly under C.

But *some* code must drop to raw CIC primitives to scaffold the nicer
tools: the `Quotient.*` operations, `unfold`, explicit motives, `Sort` /
universe handling, `congruenceOf` / `transport_proposition`. That code is
the **foundational layer** — the designated assembly zone. Everything else
is **user space** and must stay CIC-free, in code *and* in errors.

This document is the human-readable rationale. The machine-readable list
the tooling actually consumes is
[`scripts/foundational_layer.txt`](../scripts/foundational_layer.txt); the
leak dashboard that measures everything *outside* the layer is
[`scripts/cic_leak_report`](../scripts/cic_leak_report) (`make leak-report`).

## Policy

1. **A file is foundational only if its *job* is to turn a CIC primitive
   into a usable mathematical tool.** Defining a quotient carrier, its
   equivalence, and the type itself qualifies. *Using* that carrier to
   prove `a + b = b + a` does not — even if the proof currently names
   `Quotient.lift`. Those use-site leaks are the work of Phases 2–3, not a
   reason to widen the layer.

2. **The layer is bounded and shrinking.** Removing a file from the
   manifest — because the CIC use it once needed was lifted into a nicer
   tool — is the measure of progress. The manifest never grows to
   accommodate a new leak; the leak gets fixed or the tool gets built.

3. **User space is CIC-free.** Any CIC-vocabulary token in a non-manifest
   file is a leak counted by `cic_leak_report`. Any CIC-shaped *error*
   reaching a user from non-manifest code is a defect (deliverable 0.3).

## What is on the list, and why

| Entry | Why it is foundational |
|-------|------------------------|
| `library/axioms.math` | The raw axioms (propositional extensionality, function extensionality, choice, …). The bedrock; nothing is more primitive. |
| `library/Logic/` | The CIC-machinery layer: `quotient`, `sigma`, `sum`, `product`, `extensionality`, … This is where `Quotient.mk/.sound/.lift/.induct` and friends are first dressed up. `Logic/quotient.math` alone holds the bulk of the legitimate `Quotient.` vocabulary. |
| Each type's **carrier file** | The single file per constructed type that defines the representative, the equivalence relation, and the `Quotient(...)` / subtype carrier. Listed: `Integer/basics`, `Rational/basics`, `Real/basics` (+ `Real/sequence` for the supporting sequence defs), `PAdic/basics`, `Polynomial/basics`, `IntegerMod/basics`, `RingModulo/basics`, `Set/subtype`. |

## What is deliberately *not* on the list

- **Operations, laws, and instances** built on top of the carriers
  (`Integer/addition.math`, `Real/ring.math`, `Rational/order_multiplication.math`,
  …). These are the largest source of `Quotient.lift/.sound` today — the
  *construction leak* that WS3 (first-class quotient types) removes. Keeping
  them in user space is what makes that leak measurable.

- **Files with an `opaque definition` and its characterizing lemmas**
  (`Real/order.math`, `Real/supremum.math`, `Natural/floor_divide.math`, …). The
  plan lists "opaque characterizing-lemma files" as candidates, but these
  files are *mixed*: a little legitimate `unfold` at the opacity boundary,
  surrounded by ordinary order theory. The foundational concept here is
  **line-level**, not file-level, and the manifest's granularity is the
  file. Rather than whitewash a whole order-theory file as foundational, we
  let its boundary `unfold`s count as leaks — which is honest, because WS2's
  entire job is to remove those use-site `unfold`s. Revisit if/when the
  manifest gains line-level granularity.

## How to read the dashboard

```
make leak-report            # per-category + per-file, never fails
make leak-ratchet           # fails if total exceeds LEAK_BUDGET
scripts/cic_leak_report --json
```

The baseline at the time of writing (Phase 0): **681 token occurrences
across 110 user-space files**, 20 foundational files excluded. That number
is the north star; every later workstream is judged by how far it moves it.

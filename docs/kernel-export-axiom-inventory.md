# PLAN_KERNEL_EXPORT Stage-2 audit — axiom inventory & export environment (2026-07-10)

What the full-library trail's axiom report must contain — **exactly** —
plus the two export-environment facts §C asked to be pinned down (the
closed-declaration check and the pre-seal hook). Stage 4 asserts the
checker's axiom report equals the list below; any drift is a CI failure.

## Ground truth in the source

`library/axioms.math` is the *only* module allowed to declare axioms (the
elaborator warns on axioms declared anywhere else; `Test/`/`ErrorTest/`
scaffolding axioms exist but those trees are outside the trail — the trail
scope is `LIBRARY_MATH_FILES` = `library/**` minus `Test/` and
`ErrorTest/`, exactly the `make library` set).

Its full contents, with export disposition:

| declaration | disposition in the trail |
|---|---|
| `Equality.propositional_extensionality` | **axiom** (Lean's `propext` analogue; ours is stated with two arrows rather than `Iff`, so it keeps its own name and shape — to a checker it is just an axiom) |
| `Logic.excluded_middle` | **axiom** (Lean derives `Classical.em` from choice+propext+funext; we have no choice axiom, so EM stays primitive) |
| `Quotient` / `Quotient.class_of` / `Quotient.equivalent_implies_equal` / `Quotient.lift` / `Quotient.induct` | **not axioms in the trail** — exported as transparent definitions over the `quot` prelude, which itself contributes the one genuine axiom `Quot.sound` (see `docs/kernel-export-quotient-mapping.md`) |
| `Logic.Decidable` | inductive, not an axiom (`Logic.classical_decidable` is a *theorem*, derived in `Natural/classical_decidable.math`) |
| `Logic.the` / `Logic.the_satisfies` | **axioms** (definite description / unique choice — strictly weaker than Lean's `Classical.choice`; exported under their own names) |
| `Internal.sorry` / `Internal.sorry_proposition` | **excluded from the trail** — see below |

## The expected axiom report (the Stage-4 gate)

```
Equality.propositional_extensionality
Logic.excluded_middle
Logic.the
Logic.the_satisfies
Quot.sound
```

Five axioms, nothing else. This list is nanoda's `permitted_axioms`
config value.

## `Internal.sorry*`: burn-down is complete — seal it

Audit result (2026-07-10): **zero uses** of `sorry` anywhere in the
mathematical library — the only occurrences under `library/` are in
`Test/`/`ErrorTest/` files that exercise the placeholder feature itself.
(The ~90-item burn-down list recorded when the sorry-reachability
soundness bug was fixed has since been fully cleared.)

Exporter policy: **do not emit** the two `Internal.sorry*` axiom
declarations. Then any body that references them produces a dangling name
and the trail fails to check — the current sorry-free state becomes a
machine-checked invariant rather than a habit, and the axiom report stays
at the five names above. (A `sorry` introduced during development still
works locally exactly as today; it just cannot survive into a green
trail.)

## Closed-declaration check (export-time assertion)

Stored declaration bodies and types must be FreeVariable-free: the kernel
constructs binders through fresh Internal-origin FreeVariables but
`closeBinder` re-binds them before anything is stored (see the recursor
builder discipline in `src/kernel/kernel.cpp`). No stored-declaration
leak is known. Stage 3 must still assert it: the exporter walks every
expression it emits and **fails loudly** on any FreeVariable node —
NDJSON 3.1.0 has no free-variable encoding, so this turns a silent
mis-export into a hard error. Cost: one linear scan of each declaration,
amortized into serialization.

## Pre-seal hook: which caches the exporter reads

The build writes two caches per module (`src/main.cpp`, cache-emission
block ~6216):

- **`build/….mathv`** — the full cache: every declaration with its real
  body. This is what a warm rebuild replays into the environment.
- **`build/….mathv.iface`** — the derived interface view: proof bodies
  stripped; and for D-part *sealed interface modules* (`implements …` /
  `export theorems of …`), obligation theorems re-emitted with the
  interface's stated type and a fixed **placeholder body** (`Sort 0`,
  `Opacity::Opaque`) — see the sealing block ~5755 and the
  `sealing note:` build messages.

**The exporter must load the full `.mathv` caches, never `.iface`** — a
sealed placeholder body exported as a theorem would (rightly) fail the
external checker and prove nothing about the real proof. Concretely,
Stage 3's driver mode loads every `LIBRARY_MATH_FILES` module's `.mathv`
in dependency order (the same topological order `build/library-depends.mk`
encodes), deduplicating by name with the first (implementation)
occurrence winning. Two consequences it must handle:

1. **Interface re-spellings.** Downstream modules were elaborated against
   an interface's *stated* types, which may be defeq-different spellings
   of the implementation's types. The trail carries the implementation
   spelling; every place the difference matters, the external checker
   re-does a defeq check our kernel already passed at seal time — and our
   defeq is a subset of the checker's, so this is monotone-safe.
2. **Hard opacity does not export.** `opaque` is proof-hygiene, not
   kernel semantics for the trail: all definitions export transparent
   (settled in the plan's context section). The `.mathv` caches carry the
   real bodies either way.

## Elaborator-facing metadata (not exported)

`automatic` flags, opacity marks, and the `.iface.srchash` freshness
sidecars are build/elaborator metadata with no NDJSON counterpart; the
exporter drops them. None affect checkability.

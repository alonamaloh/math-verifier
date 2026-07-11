# What `make export-check` does and does not establish

`make export-check` exports the entire verified library as a
lean4export **NDJSON 3.1.0** trail (`kernel export-lean4`, an untrusted
tool — `src/export_lean4.cpp`) and replays it through **nanoda**, an
independent Rust implementation of the Lean 4 kernel by the author of
the *Type Checking in Lean 4* book. It passes only if (i) every
declaration in the trail type-checks and (ii) the trail's axiom report
**exactly equals** the documented five-axiom inventory
(`docs/kernel-export-axiom-inventory.md`).

## What a green run establishes

- Every theorem in the library is accepted by a **second, independently
  written kernel** implementing the standard Lean 4 kernel language —
  our C++ kernel is no longer a single point of trust for the
  mathematics.
- The library is **sorry-free and axiom-tight**: `Internal.sorry*` is
  deliberately omitted from the trail, so any surviving use is a
  dangling reference (a hard check failure), and any new axiom anywhere
  in the library fails the exact-inventory assertion.
- The kernel-language alignments hold in practice: op-table semantics
  (Stage 1), subsingleton elimination and recursor shape — minor-premise
  layout, leading motive level, ι-rules (Stage 2/3), the constructor
  universe bound, and the quotient mapping.

## What it does not establish

- **The exporter and its name maps are untrusted.** A bug there
  produces a trail that fails to check or fails the axiom assertion —
  with one caveat: semantically mis-mapping an *accelerated* operator
  (`Natural.add` → `Nat.add`, …) could survive, because external
  checkers accelerate `Nat.*` by name without validating the exported
  definition bodies against GMP semantics. This is exactly why Stage 1
  aligned those semantics in-source and pinned them with defeq tests
  (`Test/lean_kernel_conventions_test.math`) and the
  `MATH_CHECK_NUMERAL_TABLE` self-check.
- It re-checks the **trail**, not the surface language: elaboration
  (tactics, coercions, the auto-prover) is validated only in the sense
  that its *output* type-checks; a surface-level misunderstanding that
  produces a valid proof of the wrong statement is out of scope (as it
  is for Lean itself).
- The five axioms themselves (propositional extensionality, excluded
  middle, unique choice ×2, quotient soundness) are assumed, exactly as
  documented.

## Mapping summary (details in kernel-export-quotient-mapping.md)

`Natural`→`Nat` (+ constructors/ops/recursor), `<T>_recursor`→`<T>.rec`,
all definitions transparent, sealed interfaces bypassed (the exporter
reads full `.mathv` caches and upgrades sealed stand-ins to the
implementation's declarations), `Quotient.*` exported as transparent
definitions over a Sort-polymorphic `Eq` + `quot` prelude with two
`Equality`↔`Eq` bridges.

## Running it

```sh
make export-check          # needs nanoda_bin; override NANODA_BIN=...
```

Builds `build/export/library.ndjson` (~17 MB, ~2 s to export, ~0.4 s to
check) and `build/export/nanoda-report.txt`. Cadence: manual/nightly —
it is deliberately not part of the inner `make tests` loop.

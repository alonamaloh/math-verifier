# Error-provenance golden corpus

*Part of [PLAN_LESS_CIC_STYLE.md](../../PLAN_LESS_CIC_STYLE.md), deliverable 0.3.*

## The question this answers

> **Does a CIC-shaped error ever reach the user?**

The plan's core principle is that the kernel is a *trusted re-checker, not a
diagnostician*: every user-facing error must originate in the elaborator or
the auto-prover, never in the kernel. A kernel error reaching the user is a
**defect** — a *deferral gap* where the elaborator built a term and let the
kernel type-check it first instead of checking it itself.

This corpus turns that principle into a CI-detectable invariant. It is a set
of representative *mistakes* — apply a non-function, wrong arity, type
mismatch, missing premise, bad motive, … — each a `.math` file under
[`cases/`](cases). For each, [`run`](run) captures the diagnostic into a
golden file under [`golden/`](golden).

## How provenance is detected

The elaborator funnels every kernel `TypeError` through one chokepoint,
`rethrowKernelError` (`elaborator.cpp`), which prefixes the message with
`"kernel: "`. **That prefix is the de-facto provenance tag** (see
PLAN_LESS_CIC_STYLE.md Appendix A): any user-facing error containing
`"kernel: "` is a deferral gap. The runner reads provenance straight off the
message text — no kernel change required. It also scans for raw CIC
vocabulary (`Pi type`, `BoundVariable`, `addDefinition`, `Application:`, …)
as a secondary signal and to label *which* CIC concept leaked.

## Usage

```
scripts/error_corpus/run               # compare to goldens, classify, report
scripts/error_corpus/run --update      # (re)write goldens from current output
scripts/error_corpus/run --audit       # exit 1 if any case is kernel-tagged
scripts/error_corpus/run --show NAME    # print one case's captured diagnostic
```

`make corpus` / `make corpus-audit` wrap the report and the gate.

Requires the library to be built (`make -j 16 library`) — each case imports
real modules whose `.mathv` caches the runner loads via `--deps`.

## Baseline (Phase 0, recorded 2026-06)

```
30 cases:  12 math-shaped,  18 kernel-tagged (CIC leak),  0 non-erroring
```

The 18 kernel-tagged cases are the WS1 work-list — each is a boundary where
the elaborator defers to the kernel. They cluster into three message
families, matching Appendix A:

- **`Application:` / `Pi type` / `Pi domain`** — applying a non-function, a
  wrong-typed argument, or wrong arity. Source: the `SurfaceApplication`
  dispatch builds the application and lets the kernel check it.
  (`apply_non_function`, `argument_is_a_proof`, `too_many_arguments`,
  `successor_of_a_proof`, `add_natural_and_proof`, `missing_premise_omitted`,
  `wrong_arity_lemma`, …)
- **`addDefinition: body type does not match`** — the proof's type doesn't
  match the declared theorem/definition type. Source: `addDefinition` is
  called before the elaborator diffs the two types itself.
  (`body_type_mismatch`, `lemma_wrong_conclusion`, `ascription_to_wrong_type`,
  `partial_application_as_proof`, `hypothesis_wrong_type`,
  `reflexivity_wrong_equation`, `type_in_value_position`,
  `proof_as_statement_type`, `duplicate_theorem`, …)
- **`calc step proof's type does not match`** — a calc step whose proof
  doesn't justify the claimed relation. (`calc_broken_step`)

## Acceptance (the audit passes when…)

`run --audit` exits 0 — i.e. **no golden error is kernel-tagged**. Today it
exits 1 with 18 leaks. WS1 drives that to zero by closing each deferral gap;
this corpus converts every remaining gap into a failing case that points at
exactly the unclosed site.

## The 12 already-math-shaped cases (the bar)

These produce elaborator/auto-prover messages with no CIC vocabulary —
`unknown identifier`, `claim … no library theorem with this conclusion shape
applies`, `missing pattern case for constructor`, `by substituting: … not an
equality`, `note … the auto-prover could not close …`. They are what
"math-shaped" looks like; WS1 brings the term-elaboration and
definition-finalization paths up to this bar.

## Maintaining the corpus

- Add a mistake: drop a `.math` file in `cases/`, then `run --update`.
- Every case **must** error; a case that verifies clean is reported as a
  `non-erroring` corpus defect.
- Goldens are normalized (absolute source path → `<case>`, repo root
  stripped) so they are machine-independent. After an intentional message
  change, `run --update` and review the diff.

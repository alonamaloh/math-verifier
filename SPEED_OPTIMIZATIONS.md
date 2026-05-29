# Speed optimizations — investigation notes

Findings from a session profiling `kernel verify` and evaluating
optimization ideas. Numbers are from May 2026, Apple Silicon,
16 logical cores, mimalloc linked.

## Baseline

`make -j 16 library` wall clock, after the intrusive-pointer fix below:

- **4.57s** wall, **11.0s** CPU (intrusive)
- 7.43s wall, 17.6s CPU (shared_ptr — for comparison)

CPU/wall ≈ **2.5 / 16** cores busy on average. Lots of parallelism slack.

## The intrusive-pointer fix (shipped this session)

`IntrusiveExpressionPointer::operator=` had a self-ownership UB. The
old body read `other.ptr_` AFTER doing `intrusiveSubRef(ptr_)`. If
`other` lived inside an Expression that `*this` transitively owned —
which happens whenever you write a peel loop like

```cpp
ExpressionPointer cursor = ...;
while (auto* application = std::get_if<Application>(&cursor->node)) {
    cursor = application->function;        // <-- UB read
    ...
}
```

— the SubRef can delete the storage backing `other`, and the
subsequent re-read is UB. With `shared_ptr`'s separate control block
the body lifetime is unrelated to `other`'s storage, so this hazard
never surfaced.

The fix caches `other.ptr_` in a local before the SubRef. Net win:
**−38% wall-clock**, **−37% CPU**.

## Per-file ceiling

Top-2 files (each ~2.3s wall, direct invocation post-build):

| File | Total | Slowest declaration |
|---|---|---|
| Real/supremum.math | 2.3s | `bisectionLimit_is_upper_bound_at_rep` 610ms |
| PAdic/absolute_value.math | 2.3s | `padic_absolute_value_triangle_at_reps_wlog_case_a` **1772ms** (78% of file) |

The PAdic file is gated by **one giant proof**. No intra-file parallelism
gets around it.

## Where the kernel time *actually* goes (the surprise)

I expected `addDefinition`'s final typecheck (the body inferType +
isSubtype) to dominate. It doesn't:

| File | Wall | `addDefinition` total | Share |
|---|---|---|---|
| Real/supremum.math | 3.7s | 667ms | **18%** |
| PAdic/absolute_value.math | 3.8s | 10ms | **0.3%** |
| Real/field.math | 60ms | 1ms | 2% |

(Wall times here are higher than `make -j 16` per-file because each
direct `./kernel verify` deserialises all transitive dep `.mathv`
files fresh — ~25ms — and runs in isolation.)

The other 80–99% is **elaborator-internal kernel calls**: every `by`
clause, every calc step, every type ascription, every `note goal : T`,
every overload resolution invokes the kernel (`inferType`, `WHNF`,
`isDefinitionallyEqual`). Those calls happen during elaboration, not
in the closing `addDefinition`.

## Where parallelism slack lives

Per-file timeline of a `make -j 16 library` run (max=16):

```
== Schedule envelope ==
  first start: 0.000s     total CPU: 14.46s
  last  end:   5.363s     files:     111

== Parallelism over time (100ms ticks, max=16) ==
  t= 0.00s  ##           2
  t= 0.50s  ####         4
  t= 1.00s  ##           2     ← never more than 4 cores busy
  t= 2.00s  ###          3
  t= 2.50s  ####         4
  t= 3.50s  ###          3
  t= 4.50s  ##           2

  Slowest files start late:
    Real/supremum.math               t=2.50s  end=4.94s  (2438ms)
    PAdic/absolute_value.math        t=2.32s  end=4.68s  (2355ms)
    Real/reciprocal.math             t=1.95s  end=4.17s  (2223ms)
```

Heavy files sit idle 2.0–2.5s waiting on import chains. 13 of 16 cores
are idle most of the time.

## Ideas evaluated

### 1. Inter-file parallelism via signature artifacts ★ promising

Ship a thin "signature artifact" (declaration types + definition
bodies needed for δ-reduction, but no proof bodies) so downstream
files can start as soon as their imports are *parsed/elaborated*
rather than *verified*. Decouples scheduling from proof-checking.

Realistic upside: floor drops from 4.57s toward ~2.5s (gated by the
slowest single file). ~2× wall-clock.

Wrinkle vs. C++ header analogy: `theorem` bodies are opaque
(proof-irrelevance) so clients only need the type. **`definition`
bodies must ship** — kernel δ-unfolds them in downstream files.

### 2. Intra-file parallelism

Independent theorems within a file are checkable in parallel. Win
depends on whether the file has many medium proofs or one giant one:

- Real/supremum.math (longest decl 610ms): could shrink ~2275ms → 610ms (**3.7×**).
- PAdic/absolute_value.math (longest decl 1772ms): could shrink ~2275ms → 1772ms (**1.3×**).

Implementation cost is higher than (1) — the `Elaborator` is stateful
(environment mutations, lemma index, registry sweeps run as each
declaration commits). Needs a snapshot-based fork model.

### 3. Auto-prover oracle / proof-term cache

**Auto-prover is NOT the bottleneck** — only 30–45ms out of 2.3s file
time on the heaviest files. Of *that*, the losing-tactic share is
5–24%. Caching the winning tactic saves milliseconds per file.

The interesting reframing: cache the *kernel's verdict on whole proof
terms*, not just tactic choices. See ideas (5) and (6) below.

### 4. Trust-cache for `addDefinition` only ✗ not worth shipping

What I almost built: `addDefinitionUnchecked` + a side-table keyed on
`(name, env_fingerprint, type_hash, body_hash)` recording "kernel
said OK." Skips the closing `inferType` pair.

Expected savings, per the table above:

- Real/supremum.math: 3.7s → ~3.0s (1.2×)
- PAdic/absolute_value.math: 3.8s → 3.8s (no win)

Not enough to justify the file-format work. **Don't build this in
isolation.**

### 5. Trust-cache that skips elaboration entirely ★ the real win

The olean / vos model. Hash each declaration's source range; if
unchanged AND the prior elaborated term is on disk AND its
`env_fingerprint` matches, load the cached `addDefinitionUnchecked`
result and skip both elaboration and kernel typecheck.

This is the only design that dodges the 80–99% of file time spent in
elaborator-internal kernel calls. It is the right target for the
"interactive editor feels instant" use case.

Bigger surgery: needs source-range tracking, elaborator-result
caching, stable hashing of `(env_fingerprint, source_hash)`, a
sibling file format. Gate behind `--trust-cache` so a clean
`make library` still does the real work.

### 6. Persistent `inferType` cache

The in-process `inferTypeCache` (keyed on
`(structuralHash, contextFingerprint)`) is already a huge win. Persist
it across runs in a per-file side-file: every call from this run's
elaborator that returns a kernel-verified type becomes a permanent
"trust me" entry.

Smaller code change than (5), but uncertain hit rate: every entry
that survives a re-run is a saved kernel call, but the keying has to
be stable across runs (Contexts include opened binders; their
internal names must be normalised). The hit rate on edited files is
hard to predict without prototyping.

## Realistic floor for the current pipeline

With (1) inter-file signatures + (2) intra-file parallelism + nothing
else: ~**1.8s** wall (gated by `padic_absolute_value_triangle_at_reps_wlog_case_a`).

To push below 1.8s: either (5) trust-cache the unchanged decls, or
make that one proof faster.

## Instrumentation left in place

All gated by env vars; zero-cost when off.

- `MATH_REPORT_ADDDECL=1` — per-file dep-load and `addDefinition` totals.
- `MATH_PROFILE_AUTOPROVER=1` — per-claim TSV plus `[autoprove-summary]`
  headline: losing-time vs winning-time share.
- `MATH_TIME_DECLARATIONS=1` — per-declaration ms (≥50ms only).
- `MATH_KERNEL_CACHE=1` / `MATH_HASH_CONS=1` / `MATH_KERNEL_PROFILE=1`
  — pre-existing kernel toggles.

## What the timeline-logging Makefile hack looked like

To regenerate the parallelism breakdown:

```makefile
$(BUILD_DIR)/%.mathv: %.math | kernel
	@mkdir -p $(dir $@)
	@t0=$$(python3 -c 'import time; print(time.time())'); \
	./kernel verify --source $< --output $@ --cache-root $(BUILD_DIR) $(VERIFY_FLAGS); \
	rc=$$?; \
	t1=$$(python3 -c 'import time; print(time.time())'); \
	echo "$$t0 $$t1 $<" >> $(BUILD_DIR)/timeline.log; \
	exit $$rc
```

Then a small python script that parses `build/timeline.log`, sorts by
start time relative to the earliest entry, and emits 100ms-tick
parallelism counts. Reverted from the Makefile after the measurement;
re-paste when needed.

# Default compiler per platform: clang++ on macOS, g++ on Linux. Both are
# C++20-capable. Override on the command line with `make CXX=...` if you
# want a specific toolchain (a command-line assignment beats this).
UNAME_S := $(shell uname -s)
ifeq ($(UNAME_S),Darwin)
CXX = clang++
else
CXX = g++
endif
CXXFLAGS = -std=c++20 -Wall -Wextra -Werror -O3 -g -Isrc -MMD -MP

OBJDIR := build/obj

# C++ sources, grouped by tier (kernel <- syntax <- elaborator). Object
# files mirror the source tree under build/obj/; header dependencies are
# tracked automatically via the compiler's -MMD -MP output (the .d files
# -included at the bottom of the build section), so there is no
# hand-maintained header list to drift.
SRCS := \
    src/kernel/level.cpp src/kernel/kernel.cpp src/kernel/printer.cpp \
    src/kernel/serialize.cpp src/kernel/hash.cpp \
    src/syntax/lexer.cpp src/syntax/parser.cpp \
    src/elaborator/elaborator.cpp src/elaborator/driver.cpp \
    src/elaborator/errors.cpp src/elaborator/dispatch.cpp \
    src/elaborator/statements.cpp src/elaborator/patterns.cpp \
    src/elaborator/induction.cpp src/elaborator/cases.cpp \
    src/elaborator/inference.cpp src/elaborator/desugar_equality.cpp \
    src/elaborator/levels.cpp \
    src/elaborator/ring.cpp src/elaborator/group.cpp \
    src/elaborator/module_normalise.cpp src/elaborator/calc.cpp \
    src/elaborator/prover.cpp src/elaborator/claim.cpp \
    src/elaborator/ground_relations.cpp \
    src/elaborator/coercion.cpp src/elaborator/cast_normal.cpp \
    src/elaborator/diff_bridges.cpp \
    src/elaborator/warnings.cpp src/elaborator/lemma_index.cpp \
    src/elaborator/normalization.cpp src/elaborator/rewrite.cpp \
    src/elaborator/desugar_eliminators.cpp src/elaborator/unification.cpp \
    src/elaborator/term_utilities.cpp src/elaborator/lemma_search.cpp \
    src/export_lean4.cpp \
    src/main.cpp

OBJS := $(patsubst src/%.cpp,$(OBJDIR)/%.o,$(SRCS))

# mimalloc — small-object allocator that's faster than the system
# malloc on node-heavy workloads (substitute/makeApplication create
# small Expression nodes constantly). Whole-archive-linked so malloc/free
# are overridden at link time without needing a runtime preload. Optional:
# if the static library isn't found the kernel still builds (just slower),
# so a fresh checkout with no mimalloc installed Just Works.
#
# macOS: located via Homebrew, force-loaded with the Apple-ld spelling.
# Linux: located via pkg-config, whole-archived with the GNU-ld spelling.
ifeq ($(UNAME_S),Darwin)
MIMALLOC_PREFIX := $(shell brew --prefix mimalloc 2>/dev/null)
ifeq ($(MIMALLOC_PREFIX),)
LDFLAGS_MIMALLOC :=
else
LDFLAGS_MIMALLOC := -Wl,-force_load,$(MIMALLOC_PREFIX)/lib/libmimalloc.a
endif
else
MIMALLOC_LIB := $(wildcard $(shell pkg-config --variable=libdir mimalloc 2>/dev/null)/libmimalloc.a)
ifeq ($(MIMALLOC_LIB),)
LDFLAGS_MIMALLOC :=
else
LDFLAGS_MIMALLOC := -Wl,--whole-archive $(MIMALLOC_LIB) -Wl,--no-whole-archive
endif
endif

# GMP (PLAN_FAST_NUMERALS): the kernel's NaturalLiteral node stores an
# mpz_class, so libgmpxx/libgmp are hard build dependencies (owner
# decision, 2026-07-10). Debian/Ubuntu: `apt install libgmp-dev`;
# macOS: `brew install gmp` (add -I/-L via CXXFLAGS if not on the
# default search path).
LDFLAGS_GMP := -lgmpxx -lgmp

kernel: $(OBJS)
	$(CXX) $(CXXFLAGS) -o $@ $(OBJS) $(LDFLAGS_MIMALLOC) $(LDFLAGS_GMP)

$(OBJDIR)/%.o: src/%.cpp
	@mkdir -p $(dir $@)
	$(CXX) $(CXXFLAGS) -c $< -o $@

-include $(OBJS:.o=.d)

clean:
	rm -rf $(OBJDIR) kernel

.PHONY: clean

# ----------------------------------------------------------------------
# compile_commands.json — feeds clangd (the editor / IDE language
# server) the real compile flags so it stops emitting phantom
# "can't find <header>" / c++20-syntax diagnostics. We strip -Werror
# from CXXFLAGS so clangd reports rather than hard-errors. Regenerate
# after adding/removing a .cpp.
CDB_FLAGS := $(filter-out -Werror -MMD -MP,$(CXXFLAGS))

compile_commands.json:
	@printf '[\n' > $@
	@first=1; for f in $(SRCS); do \
		if [ $$first -eq 0 ]; then printf ',\n' >> $@; fi; first=0; \
		printf '  { "directory": "%s", "file": "%s", "command": "%s -c %s" }' \
			"$(CURDIR)" "$$f" "$(CXX) $(CDB_FLAGS)" "$$f" >> $@; \
	done
	@printf '\n]\n' >> $@
	@echo "wrote $@"

.PHONY: compile_commands.json

# ----------------------------------------------------------------------
# Library verification.
#
# Each .math file under library/ becomes a .mathv cache under
# build/library/. `make library` (re)verifies the whole library, but
# uses the per-file caches so that only files that have actually
# changed (or whose dependencies have changed) get re-verified.
# `make -j N library` parallelises across files at the granularity of
# the dependency DAG.
#
# The .mathv targets are wired together by a dependency file generated
# from `kernel deps`. That file is itself a target, regenerated when
# any .math source changes.

BUILD_DIR := build
# ErrorTest/ holds intentionally-broken proofs for the error-message
# harness (`make error-tests`); they MUST fail to verify, so exclude them
# from the normal build/test globs.
MATH_FILES := $(shell find library -name '*.math' -not -path 'library/ErrorTest/*' | sort)
# Split: `library` verifies math content; `tests` verifies the elaborator-
# feature exercises under library/Test/. `library` is the inner loop —
# keep it fast and noise-free (the test files use `sorry` deliberately,
# which produces warnings at every build).
LIBRARY_MATH_FILES := $(filter-out library/Test/%,$(MATH_FILES))
TEST_MATH_FILES := $(filter library/Test/%,$(MATH_FILES))
LIBRARY_MATHV_FILES := $(patsubst %.math,$(BUILD_DIR)/%.mathv,$(LIBRARY_MATH_FILES))
TEST_MATHV_FILES := $(patsubst %.math,$(BUILD_DIR)/%.mathv,$(TEST_MATH_FILES))
# Interface caches (stage 1). Named as explicit goals so `make` treats them
# as persisted build products rather than throwaway intermediates it deletes
# at the end of a build (which would force a full rebuild next time). Listing
# the concrete files — rather than a blanket `.SECONDARY:` — avoids a
# pathological implicit-rule-chain search that makes even `make -n` hang.
LIBRARY_MATHV_IFACE_FILES := $(LIBRARY_MATHV_FILES:.mathv=.mathv.iface)
TEST_MATHV_IFACE_FILES := $(TEST_MATHV_FILES:.mathv=.mathv.iface)

.PHONY: library library-clean tests error-tests checker-tests \
        clean-check clean-status

# Bare `make` VERIFIES THE LIBRARY — not just builds the kernel binary. The
# first target in this file is `kernel` (the C++ build), so without this line
# `make` would default to it and silently skip proof verification: edit a
# `.math` file, run `make`, see no complaint, and wrongly conclude the change
# is correct (the stale `.mathv` is never rebuilt). `library` depends on
# `kernel` through every `.mathv` rule, so this still relinks the binary first
# when sources changed. Use `make kernel` for a binary-only build.
.DEFAULT_GOAL := library

library: $(LIBRARY_MATHV_FILES) $(LIBRARY_MATHV_IFACE_FILES)

tests: library $(TEST_MATHV_FILES) $(TEST_MATHV_IFACE_FILES) checker-tests

# ----------------------------------------------------------------------
# The clean set (see docs/CLEAN_STYLE_PLAN.md). `scripts/clean_manifest.txt`
# lists the files held to clean ("reads like math") style — a set that grows,
# bottom-up by dependency layer, toward whole-library coverage. The milestone
# theorems FTA -> Q-field -> R-field -> IVT each turn GREEN once their whole
# import cone is in the manifest. (Formerly the "baby library" — the manifest
# is seeded from that original headliner cone.)
#
# `make clean-status` prints the milestone dashboard.
# `make clean-check`  verifies the manifest files and ratchets their residual
#                     (intended-boundary) leak total — it must not exceed
#                     CLEAN_LEAK_BUDGET, so a cleaned file cannot regress.
CLEAN_MATH_FILES := $(shell grep -vE '^\#|^\s*$$' scripts/clean_manifest.txt)
CLEAN_MATHV_FILES := $(patsubst %.math,$(BUILD_DIR)/%.mathv,$(CLEAN_MATH_FILES))
# 2026-07-10: re-armed 204 → 205. e433b96f (Natural/binomial via
# if-then-else) added one intended `unfold Natural.add` — its commit
# message documents the residual (the `1 + n` head un-sticking gap) —
# and `make check` wasn't run to catch the ratchet.
# 2026-07-11: re-armed 205 → 207. Stage 2 of PLAN_NATURAL_SEALING landed
# `Natural.recursion.{u}` in Natural/basics.math — the boundary recursion
# combinator is universe-polymorphic by nature, so its two universe
# annotations are an intended boundary.
# 2026-07-11: re-armed 207 → 218. Stage 4 of PLAN_NATURAL_SEALING split the
# table ops into raw-floor recursions + alias wrappers (basics/monus/power/
# floor_divide): the eleven new `unfold Natural in` are the seal's own
# boundary plumbing — the raw floor piercing the alias it defines.
# 2026-07-11: re-armed 218 → 230. The Stage-4 flip itself: the raw floor's
# bootstraps (peano's zero_or_successor, arithmetic's coverage/cancellation
# splits, the five boundary theorems in one_plus_induction, binomial,
# multiply_order) destructure the now-sealed alias, so each gains the
# documented `unfold Natural in` escape hatch — twelve tokens, all below
# the boundary they bootstrap.
# 2026-07-12: 230 → 232. Algebra/field_bundle's `Field.reciprocal` /
# `reciprocal_multiplies` pass `Field.inverse_unique(f, x)` as the
# uniqueness DATA of `Logic.the` — the established `Real.reciprocal`
# definite-description idiom (Real/field.math carries the same two
# tokens inside the budget).
# 2026-07-16: 276 → 271. R3 application convention (`rep(n)` for wrapped
# functions) removed the `sequenceFunction` walls from Real/algebra.math,
# and Real/density.math's ∃-statement now speaks `seq(m)` directly.
# 2026-07-17: 271 → 272. LA wave 3: exchange_lemma polished to the bar
# (135 findings settled, ~90 hints/names dropped, 18 documented keeps)
# and MANIFEST-ADDED at a single counted leak.
# 2026-07-17: 272 → 274. LA wave 3: basis_pruning polished (154 findings,
# 4 documented false-positive reverts) and MANIFEST-ADDED at two counted
# leaks (both structural: the injective-appeal symmetrization blocks).
# 2026-07-17: 274 → 297. LA wave 3 complete: rank_nullity (2159 lines,
# the library's largest file) polished (290 findings, zero reverts) and
# MANIFEST-ADDED at 23 counted leaks — all hypothesis applications whose
# arguments are the content (independent/eIndependent/selectionInjective
# data instantiations) plus named-arg skipValue_bound sites at
# un-inferable slots; the det/perm-documented structural class.
# 2026-07-17: 297 → 367. Polynomial cone MANIFEST-ADDED (all 19 files) —
# the season's notation sweeps + ≈ package left only 8 checker findings
# and 3 expensive-step items, all settled; 2 of 3 Equality.symmetry
# tells fixed (the quotient_field one is a legitimate DATA argument to
# the congruence lemma — the flipped RingModulo equation — and stays).
# The +71 are thin direct proof-lemma calls (1-13/file) + 4 Quotient
# tokens. Follow-up noted: a det/perm-style argument-free citation pass
# on the 3 heaviest (bezout 11, quotient_field 9, instances 8) could
# reclaim ~25.
CLEAN_LEAK_BUDGET ?= 368
# Second, independent axis: user-written `⟨…⟩` over a logical connective
# (`And`/`Exists`) — the "connectives are secretly tuples" tell, counted by the
# elaborator under MATH_CHECK_ANON_TUPLES (see `clean-anon-ratchet`). Held at the
# current floor of 0: every conjunction leg in the manifest is now taken as a
# bare claim (`P as name;` — a context conjunction's legs are facts on their
# own, no `by` and no `⟨…⟩` needed). Ratchets *down* as cleaned.
CLEAN_ANON_BUDGET ?= 0

clean-status:
	@python3 scripts/clean_status.py

clean-check: $(CLEAN_MATHV_FILES)
	@python3 scripts/clean_status.py --ratchet $(CLEAN_LEAK_BUDGET)

# The redundancy checker's speculative re-proofs must not corrupt later
# kernel judgements (environment-owner cache guard): this file verifies
# plain AND must stay green under --check-redundant-by. It once failed
# there — a failing re-proof's lemma search (whole-library snapshot
# environment) poisoned the WHNF/defeq caches and a kernel-true boundary
# equality came back false.
checker-tests: library $(TEST_MATHV_FILES)
	@./kernel verify 	    --source library/Test/redundant_check_cache_isolation_test.math 	    --output build/checker-tests.mathv --cache-root build 	    --check-redundant-by --no-check-unused-names > /dev/null 2>&1 	  && echo "checker-tests: PASS" 	  || { echo "checker-tests: FAIL — a clean file broke under --check-redundant-by"; exit 1; }
	@bash scripts/redundancy_probe_test.sh
	@MATH_CHECK_NUMERAL_TABLE=1 ./kernel verify \
	    --source library/Test/numeral_table_check.math \
	    --output build/numeral-table-check.mathv --cache-root build \
	    > /dev/null 2> build/numeral-table-check.log \
	  && echo "numeral-table-check: PASS" \
	  || { echo "numeral-table-check: FAIL — the accelerated GMP op table disagrees with the library definitions:"; cat build/numeral-table-check.log; exit 1; }

# B3.4 — morphism-packet audit: re-verify the audit surface module
# (which imports every packet-lemma home) with the audit flag on and
# print one report line per registered coercion hop, naming the packet
# slots the cast tiers would fail to discover. A report, not a gate —
# some absences are structural (ℕ has no subtraction).
audit-coercions: library
	@MATH_AUDIT_COERCION_PACKETS=1 ./kernel verify 	    --source library/Test/coercion_packet_audit.math 	    --output build/coercion-audit.mathv --cache-root build 	    2>&1 | grep "coercion-packet" 	  || { echo "audit-coercions: the audit module failed to verify"; exit 1; }

# Error-message regression suite: each library/ErrorTest/<name>.math is an
# intentionally-broken proof paired with a <name>.expected sidecar listing
# substrings its error MUST contain. `make error-tests` asserts each file
# fails to verify AND that its message still says the informative thing.
# Needs the library caches present (imports resolve from build/).
error-tests: library
	@bash scripts/error_tests.sh

# Verification flags. The redundant-`by` check is OFF by default: it
# re-runs the auto-prover speculatively on every `by` annotation, which
# on math-heavy files (e.g. PAdic/absolute_value.math) adds a 10-15x
# overhead — incompatible with real-time edit feedback. Opt in with
# `CHECK_REDUNDANT_BY=1` for tidy-up sweeps. Doesn't affect cache
# contents; warnings just go to stderr.
VERIFY_FLAGS :=
ifeq ($(CHECK_REDUNDANT_BY),1)
VERIFY_FLAGS := --check-redundant-by
endif
ifeq ($(CHECK_REDUNDANT_BY_NON_EQ),1)
VERIFY_FLAGS := --check-redundant-by --check-redundant-by-non-eq
endif

# ring_test's Gaussian-division crux builds a giant certificate whose
# UNSHARED construction peaks at 7.6 GB RSS / ~50 s; hash-consing drops
# that to 545 MB / 35 s. Hash-consing stays opt-in globally (it is
# 60-75% SLOWER on ordinary heavy files — measured 2026-06-12 on
# arithmetic_geometric_mean/derivative/euclidean), so enable it for
# exactly this target.
build/library/Test/ring_test.mathv: export MATH_HASH_CONS=1

# The unused-name check is always-on (the library is clean). But Test/
# fixtures deliberately exercise named claims, unused `let`s, and local
# abbreviations — that named/unused shape is exactly what they verify —
# so opt the Test/ targets out to keep their output free of expected noise.
$(TEST_MATHV_FILES): VERIFY_FLAGS += --no-check-unused-names

# The `automatic` auto-prover restriction (on by default) is a library-
# authoring discipline: across modules the prover only uses `automatic`
# lemmas unprompted. Test/ fixtures exercise the FULL auto-prover (numeral
# citation, bare claims drawing on any imported lemma) — that capability is
# what they verify — so run them with the restriction off, mirroring the
# unused-name opt-out above.
$(TEST_MATHV_FILES): export MATH_AUTOMATIC = 0
$(TEST_MATHV_IFACE_FILES): export MATH_AUTOMATIC = 0

# Recipe for a .mathv. The pattern rule provides the .math prerequisite;
# the .mathv prerequisites — listed by the included dependency file —
# drive `make`'s staleness tracking but are NOT passed to `kernel
# verify` on the command line: the kernel resolves the source file's
# `import` declarations against `--cache-root` directly.
#
# The kernel binary is a NORMAL prerequisite: any change to the
# elaborator/kernel/parser relinks `kernel`, which then re-verifies every
# .mathv. This costs a full re-verification after each source change, but
# it is the only way `make` can catch a behavior change that breaks a
# .math file whose source didn't change. (It was previously order-only,
# which let a broken elaborator change pass an incremental build and only
# fail on a clean rebuild — a real trap.) Note `kernel` itself only
# relinks when an object file actually changes, so warm rebuilds with no
# source edits don't re-verify anything.
# Two-stage verification.
#
# Stage 1 — interface. `MATH_STATEMENTS_ONLY=1` elaborates each module's
# statements (declared types) and definition bodies but skips proofs,
# writing ONLY the interface cache `<module>.mathv.iface` (write-if-changed).
# Its prerequisites are its imports' interfaces (the interface DAG, emitted
# by `kernel deps`). Cheap (~4% of total work) and proof-independent.
$(BUILD_DIR)/%.mathv.iface: %.math kernel
	@mkdir -p $(dir $@)
	@MATH_STATEMENTS_ONLY=1 ./kernel verify --source $< \
	    --output $(BUILD_DIR)/$*.mathv --cache-root $(BUILD_DIR)

# Stage 2 — proofs. Verifies the module's proofs against its own interface
# (from stage 1) plus its imports' interfaces, writing the full `.mathv`.
# `--no-interface` leaves stage 1's interface untouched. Because a module
# depends on its imports' *interfaces* (not their full caches), an upstream
# proof-only edit — which leaves those interfaces byte-identical — does not
# re-verify this module; every module's stage 2 is otherwise independent of
# every other's, so they parallelise freely.
$(BUILD_DIR)/%.mathv: %.math $(BUILD_DIR)/%.mathv.iface kernel
	@mkdir -p $(dir $@)
	@./kernel verify --source $< --output $@ --cache-root $(BUILD_DIR) \
	    --no-interface $(VERIFY_FLAGS)

-include $(BUILD_DIR)/library-depends.mk

# Depends generation covers ALL math files (library + tests) so the
# included rule set works whether the user invokes `library` or `tests`.
$(BUILD_DIR)/library-depends.mk: $(MATH_FILES) | kernel
	@mkdir -p $(BUILD_DIR)
	@echo "  deps     regenerating $@"
	@./kernel deps --cache-root $(BUILD_DIR) $(MATH_FILES) > $@

library-clean:
	rm -rf $(BUILD_DIR)/library $(BUILD_DIR)/library-depends.mk

# ----------------------------------------------------------------------
# Proof-style leak dashboard (PLAN_LESS_CIC_STYLE.md, Phase 0.2). Counts
# CIC-vocabulary tokens, structural smells (claim-by-calc), and direct
# proof-lemma calls (any positional arity) in user-space `.math` files — the
# north-star metric the plan drives to zero. Non-failing report by default;
# `leak-ratchet` fails if the total exceeds LEAK_BUDGET (the no-increase ratchet).
# 2026-06-12: re-armed at the measured total (2518). The previous 1642
# predated the linter tightening that counts EVERY direct-call arity
# (baseline 2017 at the time); the budget was never updated and `make
# check` wasn't being run, so the gate had silently rotted. The
# less-CIC campaign (PLAN_LESS_CIC_STYLE.md) owns driving this down —
# the ratchet's job is only to stop new leaks.
LEAK_BUDGET ?= 2518

leak-report:
	@scripts/cic_leak_report --by-file

leak-ratchet:
	@scripts/cic_leak_report --max $(LEAK_BUDGET)

# `successor`-outside-Natural ratchet (independent of the CIC-leak total).
# `successor` is the Natural constructor; outside the Natural/ definitional
# modules it is leakage — speak `n + 1` / numerals. Stage 3 of
# PLAN_NATURAL_SEALING drove this to its floor, and the Stage-4 flip
# settled the survivors: all 11 tokens are ErrorTest fixtures that
# deliberately exercise constructor patterns — the four Stage-3 survivors
# kept verbatim (pattern_shadows_constructor, cases_with_eq_retired,
# choose_from_ambiguous_premise, refining_retired) plus the two fixtures
# locking the seal's own teaching errors (sealed_natural_pattern_match,
# sealed_natural_cases).
SUCCESSOR_BUDGET ?= 11

successor-ratchet:
	@scripts/cic_leak_report --successor-max $(SUCCESSOR_BUDGET)

# NOTE: `cases` on a computed expression is no longer a ratcheted style leak —
# the elaborator REJECTS it outright (the scrutinee must be a variable; see
# src/elaborator/cases.cpp and docs/conventions/proof-style.md). No make target
# is needed: an offending `cases` simply fails to build, like any type error.
# `library/ErrorTest/cases_on_computed_expression.math` locks the message.

# Type-aware audit: every user-written `⟨…⟩` that builds or destructures a
# logical connective (`And`/`Exists`) — the "conjunctions are secretly tuples"
# tell. The check lives in the elaborator (it needs the expected/scrutinee
# type), gated off by default so normal builds stay quiet; this target turns it
# on and re-verifies the whole library, grouping the warnings by file.
# Restricted to the clean manifest (the bounded "reads like math" set), not the
# whole library — the manifest is exactly the set we hold to this standard.
anon-tuple-report:
	@rm -f $(CLEAN_MATHV_FILES)
	@MATH_CHECK_ANON_TUPLES=1 $(MAKE) clean-check 2>&1 \
	  | grep "not publicly a tuple" \
	  | sed -E 's/^warning: ([A-Za-z0-9_.]+):[0-9]+: ⟨…⟩ (builds|destructures) a .(And|Exists).*/\2 \3  \1/' \
	  | sort | uniq -c | sort -rn

# Ratchet companion to `anon-tuple-report`: fail if the manifest's
# connective-`⟨…⟩` count exceeds CLEAN_ANON_BUDGET. Wired into `check` so a new
# tuple over an `And`/`Exists` cannot land in the clean set; the budget only
# moves down. Mirrors the report's build (rm + rebuild with the audit on).
clean-anon-ratchet:
	@rm -f $(CLEAN_MATHV_FILES)
	@MATH_CHECK_ANON_TUPLES=1 $(MAKE) clean-check 2>&1 \
	  | grep "not publicly a tuple" > $(BUILD_DIR)/anon-tuples.log || true; \
	  n=$$(wc -l < $(BUILD_DIR)/anon-tuples.log); \
	  if [ $$n -gt $(CLEAN_ANON_BUDGET) ]; then \
	    echo "anon-tuple ratchet FAIL: $$n connective-⟨…⟩ site(s) in the clean manifest > budget $(CLEAN_ANON_BUDGET):"; \
	    sed -E 's/^warning: /  /' $(BUILD_DIR)/anon-tuples.log; \
	    exit 1; \
	  fi; \
	  echo "anon-tuple ratchet OK: $$n connective-⟨…⟩ site(s) <= budget $(CLEAN_ANON_BUDGET)"

.PHONY: leak-report leak-ratchet successor-ratchet anon-tuple-report clean-anon-ratchet

# ----------------------------------------------------------------------
# Error-provenance audit (PLAN_LESS_CIC_STYLE.md, Phase 0.3). Runs the
# mistake corpus and classifies each diagnostic as math-shaped or
# kernel-tagged (a CIC leak). `corpus` reports; `corpus-audit` fails if
# any case is kernel-tagged (the WS1 acceptance gate — GREEN as of the
# WS1 work). Both need the library built. See scripts/error_corpus/README.md.
corpus: library
	@scripts/error_corpus/run

corpus-audit: library
	@scripts/error_corpus/run --audit

corpus-update: library
	@scripts/error_corpus/run --update

.PHONY: corpus corpus-audit corpus-update

# ----------------------------------------------------------------------
# Aggregate gate. Verifies the library + test feature files, then enforces
# the less-CIC invariants: no kernel-tagged error reaches the user (WS1
# provenance gate) and the CIC leak count has not increased (Phase 0
# ratchet). This is the "CI" entry point — run it before committing
# elaborator/kernel changes.
check: tests self-tests corpus-audit leak-ratchet successor-ratchet clean-check clean-anon-ratchet
	@echo "check: library + tests + self-tests verified; provenance gate, leak ratchet, clean set, and anon-tuple ratchet OK"

# The kernel binary's built-in C++ test suite (./kernel with no args).
# Wired into `check` 2026-06-12 after three expectation drifts sat
# unnoticed — nothing else runs the bare suite.
self-tests: kernel
	@./kernel > /dev/null 2>&1 \
	  && echo "self-tests: PASS" \
	  || { echo "self-tests: FAIL — run ./kernel for details"; exit 1; }

.PHONY: self-tests

# PLAN_KERNEL_EXPORT Stage 4: export the full library as a lean4export
# NDJSON trail, replay it through an independent Lean-kernel checker
# (nanoda), and assert the axiom report exactly matches the documented
# inventory. Manual/nightly — not part of the inner `tests` loop.
# Override NANODA_BIN if the checker lives elsewhere.
NANODA_BIN ?= $(HOME)/claude/export-tools/nanoda_bin
export-check: library
	@scripts/export_check.sh ./kernel build/export $(NANODA_BIN)

.PHONY: export-check

.PHONY: check

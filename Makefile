CXX = clang++
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
    src/elaborator/ring.cpp src/elaborator/calc.cpp \
    src/elaborator/prover.cpp src/elaborator/claim.cpp \
    src/elaborator/coercion.cpp src/elaborator/diff_bridges.cpp \
    src/elaborator/warnings.cpp src/elaborator/lemma_index.cpp \
    src/elaborator/normalization.cpp src/elaborator/rewrite.cpp \
    src/elaborator/desugar_eliminators.cpp src/elaborator/unification.cpp \
    src/elaborator/term_utilities.cpp src/elaborator/lemma_search.cpp \
    src/main.cpp

OBJS := $(patsubst src/%.cpp,$(OBJDIR)/%.o,$(SRCS))

# mimalloc — small-object allocator that's faster than the system
# malloc on node-heavy workloads (substitute/makeApplication create
# small Expression nodes constantly). Linked as a force_load on the
# static library so malloc/free are overridden at link time without
# needing DYLD_INSERT_LIBRARIES at runtime.
MIMALLOC_PREFIX := $(shell brew --prefix mimalloc 2>/dev/null)
ifeq ($(MIMALLOC_PREFIX),)
LDFLAGS_MIMALLOC :=
else
LDFLAGS_MIMALLOC := -Wl,-force_load,$(MIMALLOC_PREFIX)/lib/libmimalloc.a
endif

kernel: $(OBJS)
	$(CXX) $(CXXFLAGS) -o $@ $(OBJS) $(LDFLAGS_MIMALLOC)

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
MATH_FILES := $(shell find library -name '*.math' | sort)
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

.PHONY: library library-clean tests

library: $(LIBRARY_MATHV_FILES) $(LIBRARY_MATHV_IFACE_FILES)

tests: library $(TEST_MATHV_FILES) $(TEST_MATHV_IFACE_FILES)

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
	MATH_STATEMENTS_ONLY=1 ./kernel verify --source $< \
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
	./kernel verify --source $< --output $@ --cache-root $(BUILD_DIR) \
	    --no-interface $(VERIFY_FLAGS)

-include $(BUILD_DIR)/library-depends.mk

# Depends generation covers ALL math files (library + tests) so the
# included rule set works whether the user invokes `library` or `tests`.
$(BUILD_DIR)/library-depends.mk: $(MATH_FILES) | kernel
	@mkdir -p $(BUILD_DIR)
	./kernel deps --cache-root $(BUILD_DIR) $(MATH_FILES) > $@

library-clean:
	rm -rf $(BUILD_DIR)

# ----------------------------------------------------------------------
# Proof-style leak dashboard (PLAN_LESS_CIC_STYLE.md, Phase 0.2). Counts
# CIC-vocabulary tokens, structural smells (claim-by-calc), and positional
# lemma calls (>=3 args) in user-space `.math` files — the north-star metric
# the plan drives to zero. Non-failing report by default; `leak-ratchet`
# fails if the total exceeds LEAK_BUDGET (the no-increase ratchet).
LEAK_BUDGET ?= 1312

leak-report:
	@scripts/cic_leak_report --by-file

leak-ratchet:
	@scripts/cic_leak_report --max $(LEAK_BUDGET)

.PHONY: leak-report leak-ratchet

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
check: tests corpus-audit leak-ratchet
	@echo "check: library + tests verified; provenance gate and leak ratchet OK"

.PHONY: check

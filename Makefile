CXX = clang++
CXXFLAGS = -std=c++20 -Wall -Wextra -Werror -O3 -g
OBJS = level.o kernel.o printer.o lexer.o parser.o elaborator.o hash.o serialize.o lemma_search.o main.o

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

level.o: level.cpp level.hpp
	$(CXX) $(CXXFLAGS) -c $< -o $@

kernel.o: kernel.cpp kernel.hpp expression.hpp level.hpp
	$(CXX) $(CXXFLAGS) -c $< -o $@

printer.o: printer.cpp printer.hpp expression.hpp level.hpp
	$(CXX) $(CXXFLAGS) -c $< -o $@

lexer.o: lexer.cpp lexer.hpp
	$(CXX) $(CXXFLAGS) -c $< -o $@

parser.o: parser.cpp parser.hpp surface.hpp lexer.hpp
	$(CXX) $(CXXFLAGS) -c $< -o $@

elaborator.o: elaborator.cpp elaborator.hpp surface.hpp kernel.hpp expression.hpp level.hpp lemma_search.hpp
	$(CXX) $(CXXFLAGS) -c $< -o $@

hash.o: hash.cpp hash.hpp
	$(CXX) $(CXXFLAGS) -c $< -o $@

serialize.o: serialize.cpp serialize.hpp expression.hpp kernel.hpp level.hpp
	$(CXX) $(CXXFLAGS) -c $< -o $@

lemma_search.o: lemma_search.cpp lemma_search.hpp expression.hpp kernel.hpp level.hpp
	$(CXX) $(CXXFLAGS) -c $< -o $@

main.o: main.cpp expression.hpp kernel.hpp printer.hpp level.hpp lexer.hpp surface.hpp parser.hpp elaborator.hpp hash.hpp serialize.hpp lemma_search.hpp
	$(CXX) $(CXXFLAGS) -c $< -o $@

clean:
	rm -f kernel $(OBJS)

.PHONY: clean

# ----------------------------------------------------------------------
# compile_commands.json — feeds clangd (the editor / IDE language
# server) the real compile flags so it stops emitting phantom
# "can't find <header>" / c++20-syntax diagnostics. We strip -Werror
# from CXXFLAGS so clangd reports rather than hard-errors. Regenerate
# after adding/removing a .cpp.
CDB_FLAGS := $(filter-out -Werror,$(CXXFLAGS))

compile_commands.json:
	@printf '[\n' > $@
	@first=1; for f in $(OBJS:.o=.cpp); do \
		if [ $$first -eq 0 ]; then printf ',\n' >> $@; fi; first=0; \
		printf '  { "directory": "%s", "file": "%s", "command": "%s -c %s -o %s" }' \
			"$(CURDIR)" "$$f" "$(CXX) $(CDB_FLAGS)" "$$f" "$${f%.cpp}.o" >> $@; \
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

.PHONY: library library-clean tests

library: $(LIBRARY_MATHV_FILES)

tests: library $(TEST_MATHV_FILES)

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
$(BUILD_DIR)/%.mathv: %.math kernel
	@mkdir -p $(dir $@)
	./kernel verify --source $< --output $@ --cache-root $(BUILD_DIR) $(VERIFY_FLAGS)

-include $(BUILD_DIR)/library-depends.mk

# Depends generation covers ALL math files (library + tests) so the
# included rule set works whether the user invokes `library` or `tests`.
$(BUILD_DIR)/library-depends.mk: $(MATH_FILES) | kernel
	@mkdir -p $(BUILD_DIR)
	./kernel deps --cache-root $(BUILD_DIR) $(MATH_FILES) > $@

library-clean:
	rm -rf $(BUILD_DIR)

# ----------------------------------------------------------------------
# CIC-leak dashboard (PLAN_LESS_CIC_STYLE.md, Phase 0.2). Counts CIC-
# vocabulary tokens in user-space `.math` files — the north-star metric
# the plan drives to zero. Non-failing report by default; `leak-ratchet`
# fails if the total exceeds LEAK_BUDGET (the no-increase ratchet).
LEAK_BUDGET ?= 628

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

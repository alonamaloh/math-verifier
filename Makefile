CXX = clang++
CXXFLAGS = -std=c++20 -Wall -Wextra -Werror -O3 -g
OBJS = level.o kernel.o printer.o lexer.o parser.o elaborator.o hash.o serialize.o main.o

kernel: $(OBJS)
	$(CXX) $(CXXFLAGS) -o $@ $(OBJS)

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

elaborator.o: elaborator.cpp elaborator.hpp surface.hpp kernel.hpp expression.hpp level.hpp
	$(CXX) $(CXXFLAGS) -c $< -o $@

hash.o: hash.cpp hash.hpp
	$(CXX) $(CXXFLAGS) -c $< -o $@

serialize.o: serialize.cpp serialize.hpp expression.hpp kernel.hpp level.hpp
	$(CXX) $(CXXFLAGS) -c $< -o $@

main.o: main.cpp expression.hpp kernel.hpp printer.hpp level.hpp lexer.hpp surface.hpp parser.hpp elaborator.hpp hash.hpp serialize.hpp
	$(CXX) $(CXXFLAGS) -c $< -o $@

clean:
	rm -f kernel $(OBJS)

.PHONY: clean

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

# Recipe for a .mathv. The pattern rule provides the .math prerequisite;
# explicit .mathv prerequisites come from the included dependency file
# (built from `kernel deps`). The kernel binary is an order-only prereq —
# we want it present, but bumping it shouldn't invalidate every cache
# (the cache file format is versioned; format bumps will fail to load
# old caches and force a rebuild explicitly).
$(BUILD_DIR)/%.mathv: %.math | kernel
	@mkdir -p $(dir $@)
	./kernel verify --source $< --output $@ --deps $(filter %.mathv,$^)

-include $(BUILD_DIR)/library-depends.mk

# Depends generation covers ALL math files (library + tests) so the
# included rule set works whether the user invokes `library` or `tests`.
$(BUILD_DIR)/library-depends.mk: $(MATH_FILES) | kernel
	@mkdir -p $(BUILD_DIR)
	./kernel deps --cache-root $(BUILD_DIR) $(MATH_FILES) > $@

library-clean:
	rm -rf $(BUILD_DIR)

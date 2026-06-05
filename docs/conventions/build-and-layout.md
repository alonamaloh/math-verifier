# Build and file layout

How to build the library, how the C++ sources are organised, and how
`library/` is organised.

*(Part of the project conventions; see `CLAUDE.md` for the index.)*

## Build

`make -j 16 library` from the project root. The dep graph is parallel;
warm rebuilds are sub-second. Always use `-j 16` (don't use bare `make`).

Objects land under `build/obj/` (mirroring `src/`); header dependencies
are tracked automatically by the compiler (`-MMD -MP` + `-include`), so
there is no hand-maintained header list in the Makefile.

## C++ source organization

The kernel + elaborator C++ lives under `src/`, in tiers that mirror the
dependency direction (each tier depends only on the ones above it):

```
src/
  kernel/      -- trusted core: expression, level, kernel (typecheck +
                  WHNF), printer, serialize, hash, subtree_hash
  syntax/      -- lexer, surface (the surface AST), parser
  elaborator/  -- surface -> kernel translation (see below)
  main.cpp     -- CLI entry point
```

Includes are path-qualified and resolved via `-Isrc`, e.g. `#include
"kernel/expression.hpp"` — an include names the tier it comes from.

### The elaborator

`elaborator.hpp` is the public API (two free functions). `internal.hpp`
declares `class Elaborator` — the surface→kernel translator. It is one
class because of a pervasive `Environment&` dependency plus a tail of
narrowly-used context state (goal stack, diagnostic frames, caches,
recursion guards). The header is the **interface** (declarations + nested
types + data members); each method's body lives out-of-line in a topical
`.cpp` slice that defines `Elaborator::method(...)`:

```
dispatch        the core elaborateExpression dispatch
statements      top-level declarations (definitions, axioms, instances, ...)
patterns        pattern-matching definitions + inductive types
induction       by-induction / strong-induction / choose / structured-claim
cases           cases-on-expression family + sorry / note / decide / tuple
inference       identifier + leading-argument/hole inference, lambda/Pi
prover          the auto-prover (context facts/equalities, bridges)
claim           claim-by-substitution / claim-by-cases
calc            the calc tactic + per-step diff proving
coercion        coerce-to-expected-type + quotient/equivalence bridges
diff_bridges    diff-based proof bridges + pattern match
rewrite         rewrite + simplify tactics
normalization   WHNF / opaque forcing, beta reduction, occurrence abstraction
desugar_equality       arithmetic + reflexivity/symmetry/transitivity
desugar_eliminators    absurd / overload / quotient & logic eliminators
unification     type/level unification, parameter/universe inference
ring            the ring / field tactic + polynomial machinery (its own TU)
levels          universe-level elaboration
term_utilities  pure term surgery, as FREE functions (no class state)
lemma_index     lemma-index lookup during proving
warnings        unused-name / unused-binder warnings
driver          run* entry points + profiling + setters
errors          error formatting + the diagnostic frame stack
lemma_search    the goal-shape lemma search index
```

A method stays inline in the header only when it must: the two templates
(`runTactic`, `collectMentionsInSurface`), the constructor, and trivial
accessors. The next step beyond relocation is decoupling — turning pure /
`Environment`-only helpers into free functions and the big tactics into
engines with a narrow interface + an injected error reporter; see the
`elaborator_split_status` memory.

## Library (math) organization

```
library/
  axioms.math          -- foundational axioms (propext, function ext, etc.)
  Logic/               -- Equality, Quotient machinery, exists, etc.
  Natural/             -- Naturals, all the way to bezout, padic_valuation
  Integer/             -- Integers as Natural × Natural quotient
  Rational/            -- Rationals as (Integer, Natural) quotient
  Real/                -- Reals as Cauchy quotient of Rationals
  PAdic/               -- p-adics as p-adic-Cauchy quotient of Rationals
  Algebra/             -- IsMonoid, IsGroup, IsRing, IsCommutativeRing
  Test/                -- small test files for features (not math content)
```

Each module's files are layered (basics → operations → laws →
instances). Imports flow up; you can't import a layer above you.

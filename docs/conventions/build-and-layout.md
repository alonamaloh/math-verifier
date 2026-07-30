# Build and file layout

How to build the library, how the C++ sources are organised, and how
`library/` is organised.

*(Part of the project conventions; see `LANGUAGE.md` for the index.)*

## Build

`make -j 16 library` from the project root. The dep graph is parallel;
warm rebuilds are sub-second. Always use `-j 16` (don't use bare `make`).

`make -j 16 projects` builds everything under `projects/` (see "Projects"
below), and `make -j 16 all` builds both. `library` is the inner loop and
deliberately does not depend on `projects`.

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
induction       induction / strong induction / choose / structured statements
cases           cases-on-expression family + sorry / note / if-conditional / tuple
inference       identifier + leading-argument/hole inference, lambda/Pi
prover          the auto-prover (context facts/equalities, bridges)
proofs          structured statements, substitution, and case splits
chains          relation chains and per-step difference proving
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

An area may **nest** when it grows a self-contained sub-area:
`library/Plane/Graph/basics.math` declares `module Plane.Graph.basics`, gets
its own `README.md`, and needs no build change — the Makefile's `find` is
recursive and import resolution just maps dots to slashes
(`modulePathWithExtension` in `src/main.cpp`). Nest to keep a large flat area
readable, not by default.

## Projects

A development that *uses* the library without being part of it lives under
`projects/<Name>/`, laid out exactly like `library/`. The Fifteen Theorem is
the first one.

```
projects/
  FifteenTheorem/      Algebra/, Test/, fifteen-theorem.md
```

The test is reuse, not importance. Library content is re-verified on every
kernel or elaborator change, so its cost is paid over and over; a project is
a destination that nothing else will cite — often dominated by
machine-generated case tables — and belongs outside that loop. Moving the
fifteen theorem out took `library/` from 832 files / 424k lines to 401 files
/ 102k lines, and left exactly one generated file behind.

Each project directory is its own **source root**. Imports resolve against
that root first and `library/` second, so a project may reuse the library's
namespace: `import Algebra.rank_four_pilot` finds the project's copy and
`import Algebra.matrix` falls through to the library. That ordering is the
kernel's repeatable `--source-root DIR` flag, which the Makefile attaches to
every project target; a library file passes none and keeps the single-rooted
resolution it always had. `kernel deps` needs no flag — it resolves imports
by module name across every source it is given.

The one hard rule: **`library/` never imports a project.** Full guide, incl.
adding a project: `projects/README.md`.

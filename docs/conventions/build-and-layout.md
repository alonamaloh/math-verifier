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
  elaborator/  -- surface -> kernel translation:
                  elaborator (public API) + internal.hpp (the class),
                  topical slices levels.cpp / ring.cpp / term_utilities,
                  and lemma_search
  main.cpp     -- CLI entry point
```

Includes are path-qualified and resolved via `-Isrc`, e.g. `#include
"kernel/expression.hpp"` — an include names the tier it comes from. The
elaborator is being broken out of one large class (`internal.hpp`) into
out-of-line `.cpp` slices and free-function/engine modules; see the
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

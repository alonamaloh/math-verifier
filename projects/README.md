# projects/

A **project** is a development that uses the library without being part of
it. It imports the library freely; the library never imports a project.

The distinction is about reuse, not importance. Library content is
vocabulary and results other developments will build on, and it is
re-verified on every kernel or elaborator change — so its cost is paid
again and again. A project is a destination: a large body of proof, often
dominated by machine-generated case tables, that nothing else will cite.
Keeping it out of `library/` is what makes the inner loop fast.

```
projects/
  FifteenTheorem/     the Conway–Schneeberger Fifteen Theorem
```

## Layout

Each project directory is its own **source root**, laid out exactly like
`library/`: a module `Algebra.rank_four_pilot` lives at
`projects/FifteenTheorem/Algebra/rank_four_pilot.math`.

A project's imports resolve against its own root first and `library/`
second, so `import Algebra.rank_four_pilot` finds the project's copy while
`import Algebra.matrix` falls through to the library. That is the kernel's
`--source-root` flag, which the Makefile passes for every project file.

Because resolution is own-root-first, a project may reuse the library's
namespace — which is how the fifteen theorem kept `Algebra.*` when it moved
out. A project-local namespace (`Fifteen.*`) is clearer and collision-proof,
and is where this is headed.

## Building

```
make -j 16 library        # the library alone — the inner loop
make -j 16 projects       # every project (builds the library first)
make -j 16 project-FifteenTheorem
make -j 16 all            # library + projects
make -j 16 project-tests  # the projects' own generated-table gates
```

`make tests` covers the library and its `library/Test/` feature exercises
only; a project's own `Test/` files are built by `make projects`.

## Adding a project

1. `mkdir -p projects/<Name>/` and lay modules out by namespace under it.
2. Nothing else. The Makefile globs `projects/**/*.math`, `kernel deps`
   resolves imports by module name across every root, and the
   `--source-root library/` flag is attached to all project targets.

If the project needs a library-side prerequisite, put that prerequisite in
`library/` — a project file must never be imported from `library/`.

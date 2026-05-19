# Continuous background rebuild

The library is incremental — `make -j 16 library` only re-verifies files
whose `.math` source or `.mathv` dependencies have changed. A cold
rebuild is a few seconds; a warm rebuild after editing one file is
sub-second. So you can run it in a tight loop and let your editor
surface the resulting errors.

## With `fswatch` (macOS, Linux)

```sh
fswatch -or library/ axioms.math | xargs -n1 -I{} make -j 16 library
```

`fswatch` is a single Homebrew install: `brew install fswatch`.

## With `entr`

`entr` is lighter weight if you prefer:

```sh
fd .math library/ axioms.math | entr -c make -j 16 library
```

`brew install entr fd`. `fd` is just used to enumerate the input — you
can use `find` instead.

## Output format

Errors are emitted in the canonical compiler format every editor
problem matcher knows:

```
<file>:<line>:<column>: <kind>: <breadcrumb-and-message>
```

For example:

```
library/Real/basics.math:96:1: elaborate error: ring at line 96
    context:
      a : Rational
      b : Rational
      c : Rational
    goal: Equality.{0} Rational (Rational.add ...) (Rational.subtract a c)
  theorem 'Rational.subtract_chain'
  `ring`: the two sides do not have equal polynomial canonical forms
```

The first line lets your editor jump to and highlight the failing
position. The subsequent indented lines are the breadcrumb stack with
local context and goal at each frame; show them as a hover or in a side
panel.

See `docs/editor/vscode.md` and `docs/editor/emacs.md` for editor-
specific recipes.

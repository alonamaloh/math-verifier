# opaque definitions

When (and when not) to mark a definition `opaque`, the characterising-lemma discipline, and the failure modes to expect.

*(Part of the project conventions; see `CLAUDE.md` for the index.)*

## `opaque definition` — hide a function's body from kernel reduction

The kernel normally δ/ι-reduces freely during typechecking. For a
function defined by recursion on a constructor, this means a goal
of the form `monus(succ k, succ j) ≤ ...` silently collapses to
`monus(k, j) ≤ ...` the instant the kernel peels the outer
constructors. Goal/term shapes the user wrote then aren't there
when `rewrite` or pattern-match-on-goal tries to find them.

**`opaque definition Foo : ... := ...`** marks `Foo` so the kernel
won't δ-unfold it. The term `Foo(args...)` stays as a stuck
application; the kernel treats it like an axiom for reduction
purposes. Downstream proofs are forced to reason about `Foo`
through **characterising lemmas** — published equations that
describe `Foo`'s behaviour — rather than relying on automatic
unfolding.

**`unfold Foo in <body>`** is the escape hatch: temporarily flips
`Foo` to transparent while elaborating `<body>`. Used only inside
the characterising lemmas themselves (which need to peek at `Foo`'s
body exactly once) and in the rare proof that genuinely needs the
unreduced view.

### When to mark a definition opaque

Recursive-on-constructor functions where downstream proofs would
get tangled by the kernel's automatic reduction. Concrete markers:

- The function pattern-matches on its first/structural arg and
  recurses.
- Proofs about it use `rewrite` against goal terms containing the
  function applied to constructor-shaped args.
- The function's defining equations (`f(0) = …`, `f(succ k) = …`)
  are already published as named theorems.

If those three apply, opacity removes a class of "where did the
term go" surprises.

Currently opaque: `Natural.monus`, `Natural.divide_step`,
`Natural.modulo_step`, `Natural.padic_valuation_step`,
`Natural.power`.

### When NOT to mark opaque — the cost / benefit lesson

Tried and reverted: `Natural.distance`. The pattern is the same
(recursive, defines `distance(0,_)=_`, `distance(succ,succ)=…`)
but proofs about distance are *computational* — they evaluate
distance on concrete pieces toward a value, not pattern-match
against goals that mention distance. Opacity forced ~200 lines of
bridge rewrites (`Equality.transport_proposition` with explicit
motives, because intermediate `LessOrEqual.reflexivity(x)` proofs
had `x` appearing twice and `rewrite` couldn't disambiguate)
without removing any real surprise.

Heuristic: opacity helps when the proof shape SAYS something
about `f(args)` and would prefer the kernel not to silently
restructure it. Opacity hurts when the proof shape COMPUTES
`f(args)` and benefits from the kernel completing the
computation.

In practice: convert one candidate, audit the failures, count the
bridge sites. If most fixes look like "I added an explicit lemma
citation that makes the proof clearer," keep going. If most fixes
look like "I wrapped reflexivity in transport_proposition with a
synthetic motive because two `b`s collided," revert.

### Discipline at the opacity boundary

1. Mark `Foo` `opaque definition`.
2. Write the **characterising lemmas** — one per defining
   equation. Each one's body is `unfold Foo in
   reflexivity(<expected RHS>)` (or `unfold Foo in
   Equality.transport_proposition(...)` when the equation
   case-splits on something).
   Example for `Natural.monus`:
   ```math
   theorem Natural.monus_zero_left (b : Natural)
           : Natural.monus(0, b) = 0 :=
     unfold Natural.monus in reflexivity(Natural, 0)
   theorem Natural.monus_succ_zero (k : Natural)
           : Natural.monus(successor(k), 0) = successor(k) :=
     unfold Natural.monus in reflexivity(Natural, successor(k))
   theorem Natural.monus_succ_succ (k j : Natural)
           : Natural.monus(successor(k), successor(j))
             = Natural.monus(k, j) :=
     unfold Natural.monus in
       reflexivity(Natural, Natural.monus(k, j))
   ```
3. Audit downstream proofs. Each `reflexivity` that used to close
   via `Foo`'s ι-reduction now needs a citation to a
   characterising lemma. Common idioms:
   - `claim equation_for_foo : Foo(args) = explicit_value by
     <characterising lemma>` then continue.
   - Bridge `rewrite` failures by ascribing the goal's `Foo(…)`
     subexpression to the form the lemma produces.
   - For inductively recursive proofs that previously rode the
     kernel's ι, add an explicit calc step `Foo(succ k) =
     <recursive case body> by <succ_succ lemma>`.

### Failure modes to expect

- **`addDefinition: body type does not match declared type`** at
  the theorem boundary — the proof's inferred type sits in the
  unfolded view and the declared type in the opaque view. Wrap the
  proof body in `unfold Foo in <body>` if it really should compute,
  or add a characterising-lemma citation to bridge.
- **`rewrite(eq, term): left endpoint does not appear`** — the
  goal type was the un-reduced opaque shape but you handed
  `rewrite` an equation whose LHS is from the unfolded view. Apply
  the characterising lemma first to align shapes.
- **`Application: argument type does not match Pi domain`** when
  recursing — the recursive call expects the un-reduced shape but
  you fed it the reduced one. Bridge with the appropriate
  characterising lemma (typically `Foo_succ_succ` or
  `Foo_succ_fits`).

### The Test/opaque_test.math demo

`library/Test/opaque_test.math` covers the smallest end-to-end:
`myDouble` opaque, `unfold myDouble in reflexivity(4)` to prove
`myDouble(2) = 4`. Read that file first if the discipline above
feels abstract.
